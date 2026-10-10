//! air2lean: write the AIR of one function as JSON.
//! Enabled by the `ZIG_AIR_JSON_DIR` environment variable. One file per function:
//! Safe short names use `<dir>/<fully qualified name>.json`; other names use a SHA-256
//! basename (see docs/export-names.md), as does every function of a module other than `root`
//! and `std`. JSON retains the full name and its module (`identity.zig`).
//! `ZIG_AIR_JSON_FILTER=<prefix>,<prefix>,…` limits output
//! to functions whose fully qualified name starts with one of the prefixes. Instructions outside
//! the air2lean subset are written with their tag and `"unsupported": true`, so the reader can
//! reject them. Types are interned into a `types` table; everywhere a type appears in the
//! body it is written as an integer ID (an index into that table).
//!
//! One source for every supported Zig version (`zig-patch/versions.toml`). The version
//! differences are all in `Compat` below; the rest of the file does not depend on the version.

const std = @import("std");
const build_options = @import("build_options");
const Allocator = std.mem.Allocator;
const Zcu = @import("../Zcu.zig");
const Value = @import("../Value.zig");
const Type = @import("../Type.zig");
const Air = @import("../Air.zig");
const InternPool = @import("../InternPool.zig");
const target_util = @import("../target.zig");
const PtrOffset = @import("pointer-offset.zig");
const Identity = @import("identity.zig");

/// The differences between the supported Zig versions (0.14.1, 0.15.2, 0.16.0, 0.17.0). The
/// compiler is built by a host zig of its own version (`zig-patch/build.sh`), so
/// `builtin.zig_version` is the version being patched. Each `if` on `v14`/`v16`/`v17` is
/// comptime-known, so a version analyses only its own branch. `v16` and `v17` mean "this
/// version or later": 0.17.0 keeps every 0.16.0 API the exporter uses unless a `v17` branch
/// says otherwise.
const Compat = struct {
    const zv = @import("builtin").zig_version;
    const v14 = zv.minor == 14;
    const v16 = zv.minor >= 16;
    const v17 = zv.minor >= 17;
    comptime {
        // A new version needs its own review of every branch below (PLAN.md §Zig version support).
        if (zv.major != 0 or zv.minor < 14 or zv.minor > 17)
            @compileError("air2lean exporter: Zig version without a Compat branch");
    }

    const Dir = if (v16) std.Io.Dir else std.fs.Dir;
    const File = if (v16) std.Io.File else std.fs.File;
    /// 0.14.1 has no `std.json.Stringify`: its writer is a generic type over the file writer.
    const Json = if (v14)
        std.json.WriteStream(std.fs.File.Writer, .{ .checked_to_fixed_depth = 256 })
    else
        std.json.Stringify;
    const WriteError = if (v14) std.fs.File.WriteError else std.Io.Writer.Error;
    /// 0.15.2 changed the `format` contract: a type's own `format` needs `{f}`.
    const fmt_value = if (v14) "{}" else "{f}";

    /// 0.16.0 has no global environment: the compilation holds it.
    fn getEnv(pt: Zcu.PerThread, name: []const u8) ?[]const u8 {
        return if (v16) pt.zcu.comp.environ_map.get(name) else std.posix.getenv(name);
    }

    fn openDir(pt: Zcu.PerThread, path: []const u8) !Dir {
        return if (v16)
            std.Io.Dir.cwd().createDirPathOpen(pt.zcu.comp.io, path, .{})
        else
            std.fs.cwd().makeOpenPath(path, .{});
    }

    fn closeDir(pt: Zcu.PerThread, dir: *Dir) void {
        if (v16) dir.close(pt.zcu.comp.io) else dir.close();
    }

    fn createFile(pt: Zcu.PerThread, dir: Dir, name: []const u8) !File {
        const options: if (v16) Dir.CreateFileOptions else File.CreateFlags = .{ .read = true, .exclusive = true, .lock = .exclusive, .lock_nonblocking = true };
        return if (v16) dir.createFile(pt.zcu.comp.io, name, options) else dir.createFile(name, options);
    }

    fn openExistingFile(pt: Zcu.PerThread, dir: Dir, name: []const u8) !File {
        const options: if (v16) Dir.OpenFileOptions else File.OpenFlags = .{ .mode = .read_write, .lock = .exclusive, .lock_nonblocking = true };
        return if (v16) dir.openFile(pt.zcu.comp.io, name, options) else dir.openFile(name, options);
    }

    fn statPath(pt: Zcu.PerThread, dir: Dir, name: []const u8) !File.Stat {
        return if (v16) dir.statFile(pt.zcu.comp.io, name, .{}) else dir.statFile(name);
    }

    fn statFile(pt: Zcu.PerThread, file: File) !File.Stat {
        return if (v16) file.stat(pt.zcu.comp.io) else file.stat();
    }

    fn readFile(pt: Zcu.PerThread, file: File, bytes: []u8) !usize {
        return if (v16) file.readPositionalAll(pt.zcu.comp.io, bytes, 0) else file.preadAll(bytes, 0);
    }

    fn truncateFile(pt: Zcu.PerThread, file: File) !void {
        if (v16) try file.setLength(pt.zcu.comp.io, 0) else try file.setEndPos(0);
    }

    fn closeFile(pt: Zcu.PerThread, file: File) void {
        if (v16) file.close(pt.zcu.comp.io) else file.close();
    }

    /// The JSON writer on an open file. 0.14.1 writes unbuffered; 0.15.2+ buffer and need
    /// `flush`.
    const Sink = if (v14) struct {
        j: Json,

        fn init(s: *Sink, _: Zcu.PerThread, file: File) void {
            s.j = std.json.writeStream(file.writer(), .{ .whitespace = .indent_1 });
        }

        fn flush(_: *Sink) WriteError!void {}
    } else struct {
        buf: [64 * 1024]u8,
        fw: File.Writer,
        j: Json,

        fn init(s: *Sink, pt: Zcu.PerThread, file: File) void {
            s.fw = if (v16) file.writer(pt.zcu.comp.io, &s.buf) else file.writer(&s.buf);
            s.j = .{ .writer = &s.fw.interface, .options = .{ .whitespace = .indent_1 } };
        }

        fn flush(s: *Sink) WriteError!void {
            try s.fw.interface.flush();
        }
    };

    /// `Air.extra` is a slice in 0.14.1 and an array list in 0.15.2+.
    fn extra(air: *const Air) []const u32 {
        return if (v14) air.extra else air.extra.items;
    }

    /// 0.14.1 has no ZIR parameter index. Recover the runtime parameter position, preserving
    /// parameters with one possible value, which Sema omits from the AIR `arg` instructions.
    fn argIndex(w: *W, inst: Air.Inst.Index) Error!u32 {
        if (v14) {
            while (w.arg_count < w.param_types.len) {
                const index = w.arg_count;
                w.arg_count += 1;
                if (try Type.fromInterned(w.param_types[index]).onePossibleValue(w.pt) == null)
                    return index;
            }
            unreachable; // Sema emitted an argument for one of these runtime parameters.
        } else return w.data(inst).arg.zir_param_index;
    }

    fn writeInt(w: *W, val: Value) Error!void {
        var space: Value.BigIntSpace = undefined;
        // Before 0.16, @sizeOf/@alignOf can remain lazy until layout is needed. Resolve them
        // through the PerThread API rather than printing their diagnostic source expression.
        const integer = if (v16) val.toBigInt(&space, w.pt.zcu) else try val.toBigIntSema(&space, w.pt);
        const text = try std.fmt.allocPrint(w.gpa, "{d}", .{integer});
        try w.j.write(text);
    }

    fn isBitpack(key: InternPool.Key) bool {
        return if (v16) key == .bitpack else false;
    }

    /// `runtime_nav_ptr` (0.15.2+; 0.14.1 has a constant pointer to a `threadlocal` global).
    fn isRuntimeNavPtr(tag: Air.Inst.Tag) bool {
        return if (v14) false else tag == .runtime_nav_ptr;
    }

    /// A `ty_op` tag that does not exist in every version: `int_from_float_safe` (0.15.2+).
    /// 0.17.0 renamed `bitcast`/`intcast`/`intcast_safe` to `bit_cast`/`int_cast`/
    /// `int_cast_safe` and split the other casts that `bitcast` covered into their own tags
    /// (`zig-patch/0.17.0/TAGS.md`). Each branch names only its own version's tags.
    fn isNewTyOp(tag: Air.Inst.Tag) bool {
        return if (v14)
            tag == .bitcast or tag == .intcast or tag == .intcast_safe
        else if (v17)
            tag == .int_from_float_safe or tag == .bit_cast or tag == .bit_cast_safe or
                tag == .int_cast or tag == .int_cast_safe or tag == .ptr_cast or
                tag == .ptr_from_int or tag == .int_from_ptr or tag == .error_cast or
                tag == .error_from_int or tag == .int_from_error or tag == .union_from_enum or
                tag == .array_to_vector
        else
            tag == .int_from_float_safe or tag == .bitcast or tag == .intcast or tag == .intcast_safe;
    }

    /// A `bin_op` tag that does not exist in every version: `memmove` (0.15.2+), `div_ceil`
    /// (0.17.0+), `bool_and`/`bool_or` (before 0.17.0).
    fn isNewBinOp(tag: Air.Inst.Tag) bool {
        return if (v14)
            tag == .bool_and or tag == .bool_or
        else if (v17)
            tag == .memmove or tag == .div_ceil
        else
            tag == .memmove or tag == .bool_and or tag == .bool_or;
    }

    /// `struct_field_val`, renamed `agg_field_val` in 0.17.0 (`ty_pl`, payload `StructField`).
    fn isFieldVal(tag: Air.Inst.Tag) bool {
        return if (v17) tag == .agg_field_val else tag == .struct_field_val;
    }

    /// A lane pointer whose lane is runtime-known: `VectorIndex.runtime`, which 0.16.0 removed.
    fn isRuntimeLane(vector_index: InternPool.Key.PtrType.VectorIndex) bool {
        return if (v16) false else vector_index == .runtime;
    }

    /// The type of a `ty_pl` instruction: an `Air.Inst.Ref` before 0.17.0, a `Type` since.
    fn tyPlType(ty_pl: anytype) Type {
        return if (v17) ty_pl.ty else ty_pl.ty.toType();
    }

    /// The integer tag type of an enum: `intTagType` was renamed `backingIntType` in 0.17.0.
    fn enumTagType(ty: Type, zcu: *Zcu) Type {
        return if (v17) ty.backingIntType(zcu) else ty.intTagType(zcu);
    }

    /// The printers of a value and a type take a `Zcu.PerThread` before 0.17.0, a `*Zcu` since.
    fn fmtValue(pt: Zcu.PerThread, val: Value) @TypeOf(val.fmtValue(if (v17) pt.zcu else pt)) {
        return val.fmtValue(if (v17) pt.zcu else pt);
    }
    fn fmtType(pt: Zcu.PerThread, ty: Type) Type.Formatter {
        return ty.fmt(if (v17) pt.zcu else pt);
    }

    /// The fully qualified name of a container type. 0.17.0 returns both the short `name` and
    /// the `fqn`; before, the one name it returns is the fully qualified one.
    fn containerTypeName(ty: Type, ip: *const InternPool) []const u8 {
        const name = ty.containerTypeName(ip);
        return (if (v17) name.fqn else name).toSlice(ip);
    }

    /// `profile.build_mode`. 0.17.0 renamed the `std.lang.Optimize` tags (`debug`, `safe`,
    /// `fast`, `small`); the JSON keeps the build-mode names of `-O`.
    fn buildMode(mode: anytype) []const u8 {
        return if (v17) switch (mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        } else @tagName(mode);
    }

    /// `@shuffle` on 0.14.1: one `shuffle` tag, mask is a comptime `@Vector(mask_len, i32)`
    /// (`Air.Shuffle`). 0.15.2+ split it into `shuffle_one` (single source) and `shuffle_two`
    /// (two sources), each with a runtime-decodable mask (`unwrapShuffleOne`/`unwrapShuffleTwo`).
    fn isShuffle14(tag: Air.Inst.Tag) bool {
        return if (v14) tag == .shuffle else false;
    }
    fn isShuffleOne(tag: Air.Inst.Tag) bool {
        return if (v14) false else tag == .shuffle_one;
    }
    fn isShuffleTwo(tag: Air.Inst.Tag) bool {
        return if (v14) false else tag == .shuffle_two;
    }

    /// Is the layout of `ty` known, so that `abiSize`, `abiAlignment` and `structFieldOffset`
    /// are valid? Those functions assert it. 0.16.0 sets `want_layout` right before it resolves
    /// a container layout (`PerThread.ensureTypeLayoutUpToDate`); before 0.16.0 the container
    /// type has a status.
    fn hasLayout(zcu: *Zcu, ty: Type) bool {
        const ip = &zcu.intern_pool;
        return switch (ip.indexToKey(ty.toIntern())) {
            .int_type, .ptr_type, .simple_type, .error_set_type, .inferred_error_set_type => true,
            .array_type => |a| hasLayout(zcu, Type.fromInterned(a.child)),
            .vector_type => |v| hasLayout(zcu, Type.fromInterned(v.child)),
            .opt_type => |c| hasLayout(zcu, Type.fromInterned(c)),
            .error_union_type => |eu| hasLayout(zcu, Type.fromInterned(eu.payload_type)),
            .tuple_type => |t| for (t.types.get(ip)) |f| {
                if (!hasLayout(zcu, Type.fromInterned(f))) break false;
            } else true,
            .struct_type => if (v16)
                ip.loadStructType(ty.toIntern()).want_layout
            else
                ip.loadStructType(ty.toIntern()).haveLayout(ip),
            .union_type => if (v16)
                ip.loadUnionType(ty.toIntern()).want_layout
            else
                ip.loadUnionType(ty.toIntern()).haveLayout(ip),
            .enum_type => if (v16) ip.loadEnumType(ty.toIntern()).want_layout else true,
            else => false,
        };
    }

    /// Are the fields of the struct or union `ty` known? 0.16.0 asserts `want_layout` in
    /// `structFieldCount` and `unionTagTypeHypothetical`; before 0.16.0 the fields are known
    /// once the type exists. A tuple always has its fields.
    fn hasFields(zcu: *Zcu, ty: Type) bool {
        if (!v16) return true;
        return switch (zcu.intern_pool.indexToKey(ty.toIntern())) {
            .struct_type, .union_type => hasLayout(zcu, ty),
            else => true,
        };
    }

    /// The hidden tag of a bare union (`ReleaseSafe`): the tag type if the union has a safety
    /// tag. 0.16.0 has no `unionTagTypeSafety`; its `unionTagTypeRuntime` is null for a tag
    /// without runtime bits (one field), where 0.14.1 and 0.15.2 give the `u0` tag.
    fn unionSafetyTag(zcu: *Zcu, ty: Type) ?Type {
        if (ty.unionTagType(zcu) != null) return null;
        if (v16) {
            const u = zcu.intern_pool.loadUnionType(ty.toIntern());
            return if (u.tag_usage == .safety) Type.fromInterned(u.enum_tag_type) else null;
        }
        return ty.unionTagTypeSafety(zcu);
    }

    const NavInfo = struct {
        ty: InternPool.Index,
        is_const: bool,
        is_threadlocal: bool,
        is_extern: bool,
        /// The initial value; `null` if Sema has not resolved it yet.
        init: ?InternPool.Index,
    };

    /// A global's type, flags and initial value. 0.16.0 keeps them in `Nav.resolved`; before
    /// 0.16.0, `Nav.status` has them, and the value of a `var` is a `variable` key that holds the
    /// initial value.
    fn navInfo(zcu: *Zcu, nav_index: InternPool.Nav.Index) NavInfo {
        const ip = &zcu.intern_pool;
        const nav = ip.getNav(nav_index);
        if (v16) {
            const r = nav.resolved.?;
            const is_extern = r.is_extern_decl or
                (r.value != .none and ip.indexToKey(r.value) == .@"extern");
            return .{
                .ty = r.type,
                .is_const = r.@"const",
                .is_threadlocal = r.@"threadlocal",
                .is_extern = is_extern,
                .init = if (r.value == .none or is_extern) null else r.value,
            };
        }
        return switch (nav.status) {
            .unresolved => unreachable, // a pointer to the global has its type
            .type_resolved => |r| .{
                .ty = r.type,
                .is_const = r.is_const,
                .is_threadlocal = r.is_threadlocal,
                .is_extern = r.is_extern_decl,
                .init = null,
            },
            // 0.14.1 has no `is_const` here: a `var` has a `variable` value.
            .fully_resolved => |r| switch (ip.indexToKey(r.val)) {
                .variable => |v| .{
                    .ty = v.ty,
                    .is_const = if (v14) false else r.is_const,
                    .is_threadlocal = v.is_threadlocal,
                    .is_extern = false,
                    .init = v.init,
                },
                .@"extern" => |e| .{
                    .ty = e.ty,
                    .is_const = if (v14) e.is_const else r.is_const,
                    .is_threadlocal = e.is_threadlocal,
                    .is_extern = true,
                    .init = null,
                },
                else => .{
                    .ty = ip.typeOf(r.val),
                    .is_const = if (v14) true else r.is_const,
                    .is_threadlocal = false,
                    .is_extern = false,
                    .init = r.val,
                },
            },
        };
    }

    /// The `assembly` AIR instruction, normalized. 0.16.0 has a convenience `Air.unwrapAsm`;
    /// 0.15.2 has no such helper, and its extra-data order differs (outputs, inputs, output
    /// constraint/name pairs, input constraint/name pairs, source — 0.16.0 instead puts the
    /// source right after inputs, before either constraint/name block). Not called for 0.14.1:
    /// M21 does not support inline asm there.
    const AsmData = struct {
        outputs: []const Air.Inst.Ref,
        inputs: []const Air.Inst.Ref,
        /// `constraint\0name\0` pairs, u32-padded, one per output, in `outputs` order.
        output_names: []const u32,
        /// Same, one per input, in `inputs` order.
        input_names: []const u32,
        source: []const u8,
        clobbers: InternPool.Index,
        is_volatile: bool,
    };

    fn unwrapAsm(air: *const Air, inst: Air.Inst.Index) AsmData {
        if (v16) {
            const u = air.unwrapAsm(inst);
            return .{
                .outputs = u.outputs,
                .inputs = u.inputs,
                .output_names = u.output_constraint_names,
                .input_names = u.input_constraint_names,
                .source = u.source,
                .clobbers = u.clobbers,
                .is_volatile = u.is_volatile,
            };
        }
        const ty_pl = air.instructions.items(.data)[@intFromEnum(inst)].ty_pl;
        const asm_extra = air.extraData(Air.Asm, ty_pl.payload);
        const outputs_len = asm_extra.data.flags.outputs_len;
        const inputs_len = asm_extra.data.inputs_len;
        var i = asm_extra.end;
        const outputs: []const Air.Inst.Ref = @ptrCast(extra(air)[i..][0..outputs_len]);
        i += outputs_len;
        const inputs: []const Air.Inst.Ref = @ptrCast(extra(air)[i..][0..inputs_len]);
        i += inputs_len;
        const output_names_start = i;
        for (0..outputs_len) |_| i += asmNamePairLen(extra(air)[i..]);
        const input_names_start = i;
        for (0..inputs_len) |_| i += asmNamePairLen(extra(air)[i..]);
        const source_start = i;
        return .{
            .outputs = outputs,
            .inputs = inputs,
            .output_names = extra(air)[output_names_start..input_names_start],
            .input_names = extra(air)[input_names_start..source_start],
            .source = std.mem.sliceAsBytes(extra(air)[source_start..])[0..asm_extra.data.source_len],
            .clobbers = asm_extra.data.clobbers,
            .is_volatile = asm_extra.data.flags.is_volatile,
        };
    }

    /// The clobbered register/flag names of a comptime `std.builtin.assembly.Clobbers` value.
    /// 0.16.0 stores it as a packed integer (`Value.toBigInt`); 0.15.2 as an aggregate of
    /// per-field `bool_true`/`bool_false` (`InternPool.Key.Aggregate`).
    fn writeClobbers(w: *W, clobbers: InternPool.Index) Error!void {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        try w.j.beginArray();
        if (v16) {
            const clobbers_val: Value = .fromInterned(clobbers);
            const clobbers_ty = clobbers_val.typeOf(zcu);
            var buf: Value.BigIntSpace = undefined;
            const bigint = clobbers_val.toBigInt(&buf, zcu);
            const limb_bits = @bitSizeOf(std.math.big.Limb);
            for (0..clobbers_ty.structFieldCount(zcu)) |field_index| {
                if (field_index / limb_bits >= bigint.limbs.len) continue;
                const bit: u1 = @truncate(bigint.limbs[field_index / limb_bits] >> @intCast(field_index % limb_bits));
                if (bit == 0) continue;
                try w.j.write(clobbers_ty.structFieldName(field_index, zcu).toSlice(ip).?);
            }
        } else {
            const aggregate = ip.indexToKey(clobbers).aggregate;
            const struct_type: Type = .fromInterned(aggregate.ty);
            switch (aggregate.storage) {
                .elems => |elems| for (elems, 0..) |elem, field_index| {
                    if (elem != .bool_true) continue;
                    try w.j.write(struct_type.structFieldName(field_index, zcu).toSlice(ip).?);
                },
                .repeated_elem => |elem| if (elem == .bool_true) {
                    for (0..struct_type.structFieldCount(zcu)) |field_index|
                        try w.j.write(struct_type.structFieldName(field_index, zcu).toSlice(ip).?);
                },
                else => {},
            }
        }
        try w.j.endArray();
    }
};

/// The u32-word length of one `constraint\0name\0` pair (padded: even an exact 4-byte fit still
/// uses the next word for the terminator). Shared layout in every version.
fn asmNamePairLen(words: []const u32) usize {
    const bytes = std.mem.sliceAsBytes(words);
    const constraint = std.mem.sliceTo(bytes, 0);
    const name = std.mem.sliceTo(bytes[constraint.len + 1 ..], 0);
    return (constraint.len + name.len + (2 + 3)) / 4;
}

/// One `constraint\0name\0` pair read from the start of `words`, and its u32-word length.
fn readAsmNamePair(words: []const u32) struct { constraint: []const u8, name: []const u8, len: usize } {
    const bytes = std.mem.sliceAsBytes(words);
    const constraint = std.mem.sliceTo(bytes, 0);
    const name = std.mem.sliceTo(bytes[constraint.len + 1 ..], 0);
    return .{ .constraint = constraint, .name = name, .len = asmNamePairLen(words) };
}

const Error = Compat.WriteError || Zcu.SemaError;

// Reserve '~' for hashes: direct names and fallback names cannot collide. The cap
// includes .json and is portable to filesystems with a 255-byte component limit.
const output_name_capacity = @min(255, std.fs.max_name_bytes);
const hashed_name_prefix = "~air2lean-sha256-";

fn outputFileName(fqn: []const u8, buffer: *[output_name_capacity]u8) []const u8 {
    var direct = fqn.len > 0 and fqn.len <= output_name_capacity - ".json".len;
    for (fqn) |byte| {
        if (!std.ascii.isAlphanumeric(byte) and byte != '_' and byte != '-' and byte != '.') direct = false;
    }
    // Leading dots are hidden by shell globs; leading hyphens are CLI-unsafe.
    if (fqn.len > 0 and (fqn[0] == '.' or fqn[0] == '-')) direct = false;
    const stem = fqn[0 .. (std.mem.indexOfScalar(u8, fqn, '.') orelse fqn.len)];
    if (std.ascii.eqlIgnoreCase(stem, "con") or std.ascii.eqlIgnoreCase(stem, "prn") or
        std.ascii.eqlIgnoreCase(stem, "aux") or std.ascii.eqlIgnoreCase(stem, "nul")) direct = false;
    if (stem.len == 4 and stem[3] >= '1' and stem[3] <= '9' and
        (std.ascii.eqlIgnoreCase(stem[0..3], "com") or std.ascii.eqlIgnoreCase(stem[0..3], "lpt"))) direct = false;
    if (direct) return std.fmt.bufPrint(buffer, "{s}.json", .{fqn}) catch unreachable;
    var digest: [std.crypto.hash.sha2.Sha256.digest_length]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(fqn, &digest, .{});
    @memcpy(buffer[0..hashed_name_prefix.len], hashed_name_prefix);
    const alphabet = "0123456789abcdef";
    for (digest, 0..) |byte, i| {
        buffer[hashed_name_prefix.len + i * 2] = alphabet[byte >> 4];
        buffer[hashed_name_prefix.len + i * 2 + 1] = alphabet[byte & 15];
    }
    const end = hashed_name_prefix.len + digest.len * 2;
    @memcpy(buffer[end .. end + 5], ".json");
    return buffer[0 .. end + 5];
}

// Exclusive creation protects fresh files. Repeated analysis may export the same
// function again: permit this only after validating its existing full JSON name,
// without truncating first. The advisory lock coordinates cooperating exporters.
fn openOwnedOutput(pt: Zcu.PerThread, dir: Compat.Dir, name: []const u8, fqn: []const u8, module: []const u8) !Compat.File {
    return Compat.createFile(pt, dir, name) catch |err| {
        if (err != error.PathAlreadyExists) return err;
        // Reject stable nonregular paths before a potentially blocking open.
        if ((try Compat.statPath(pt, dir, name)).kind != .file) return error.ExistingOutputNotRegular;
        const file = try Compat.openExistingFile(pt, dir, name);
        errdefer Compat.closeFile(pt, file);
        const stat = try Compat.statFile(pt, file);
        if (stat.kind != .file) return error.ExistingOutputNotRegular;
        if (stat.size > 64 * 1024 * 1024) return error.ExistingOutputTooLarge;
        // Validation storage must be released before the writer arena grows.
        var validation_arena = std.heap.ArenaAllocator.init(pt.zcu.gpa);
        defer validation_arena.deinit();
        const allocator = validation_arena.allocator();
        const bytes = try allocator.alloc(u8, @as(usize, @intCast(stat.size)) + 1);
        defer allocator.free(bytes);
        const count = try Compat.readFile(pt, file, bytes);
        if (count != stat.size) return error.ExistingOutputChanged;
        const parsed = try std.json.parseFromSlice(std.json.Value, allocator, bytes[0..count], .{ .duplicate_field_behavior = .@"error" });
        defer parsed.deinit();
        if (parsed.value != .object) return error.OutputIdentityCollision;
        const identity = parsed.value.object.get("name") orelse return error.OutputIdentityCollision;
        if (identity != .string or !std.mem.eql(u8, identity.string, fqn)) return error.OutputIdentityCollision;
        // The module completes the identity (docs/air-json.md §Identity).
        const existing_module = parsed.value.object.get("module") orelse return error.OutputIdentityCollision;
        if (existing_module != .string or !std.mem.eql(u8, existing_module.string, module)) return error.OutputIdentityCollision;
        try Compat.truncateFile(pt, file);
        return file;
    };
}

pub fn dumpToDir(air: *const Air, pt: Zcu.PerThread, func_index: InternPool.Index) void {
    const dir_path = Compat.getEnv(pt, "ZIG_AIR_JSON_DIR") orelse return;
    const zcu = pt.zcu;
    const ip = &zcu.intern_pool;
    const func = zcu.funcInfo(func_index);
    const fqn = ip.getNav(func.owner_nav).fqn.toSlice(ip);

    if (Compat.getEnv(pt, "ZIG_AIR_JSON_FILTER")) |prefixes| {
        var it = std.mem.splitScalar(u8, prefixes, ',');
        while (it.next()) |prefix| {
            if (std.mem.startsWith(u8, fqn, prefix)) break;
        } else return;
    }

    // A function without a file must not pass silently: warn on every failure.
    var dir = Compat.openDir(pt, dir_path) catch |err| {
        std.log.warn("air2lean: cannot open {s}: {s}", .{ dir_path, @errorName(err) });
        return;
    };
    defer Compat.closeDir(pt, &dir);
    var arena = std.heap.ArenaAllocator.init(zcu.gpa);
    defer arena.deinit();
    const module = Identity.navModule(zcu, func.owner_nav);
    const storage = Identity.storageName(arena.allocator(), module, fqn) catch |err| {
        std.log.warn("air2lean: no JSON for {s}: {s}", .{ fqn, @errorName(err) });
        return;
    };
    var name_buf: [output_name_capacity]u8 = undefined;
    const file_name = outputFileName(storage, &name_buf);
    Identity.claim(zcu, .output, "", file_name, @intFromEnum(func.owner_nav));
    const file = openOwnedOutput(pt, dir, file_name, fqn, module) catch |err| {
        std.log.warn("air2lean: no JSON for {s} at {s}: {s}", .{ fqn, file_name, @errorName(err) });
        return;
    };
    defer Compat.closeFile(pt, file);
    var sink: Compat.Sink = undefined;
    sink.init(pt, file);

    var w: W = .{ .pt = pt, .air = air, .j = &sink.j, .gpa = arena.allocator() };
    // A partly written file is invalid JSON; say which one, like the open failures above.
    w.writeFunc(fqn, Type.fromInterned(func.ty), func) catch |err| {
        std.log.warn("air2lean: incomplete JSON for {s}: {s}", .{ fqn, @errorName(err) });
        return;
    };
    sink.flush() catch |err| {
        std.log.warn("air2lean: incomplete JSON for {s}: {s}", .{ fqn, @errorName(err) });
    };
}

const W = struct {
    pt: Zcu.PerThread,
    air: *const Air,
    j: *Compat.Json,
    gpa: Allocator,
    /// Number of `arg` instructions written so far (`Compat.argIndex`, 0.14.1 only).
    arg_count: u32 = 0,
    param_types: []const InternPool.Index = &.{},
    /// Maps an interned type to its ID (its index in `queue`, and thus in the emitted
    /// `types` array).
    ids: std.AutoHashMapUnmanaged(InternPool.Index, u32) = .empty,
    /// Types in first-encounter order. Grows while draining it in `writeFunc`: writing a
    /// type entry can discover further types, which get appended and drained in turn.
    queue: std.ArrayListUnmanaged(InternPool.Index) = .empty,
    /// The globals that pointer constants point into, in first-encounter order: the `globals`
    /// table. Grows while `writeFunc` drains it, like `queue`.
    globals: std.ArrayListUnmanaged(Global) = .empty,
    /// The extern functions this body calls, in first-encounter order: the `externs` table.
    externs: std.ArrayListUnmanaged(InternPool.Index) = .empty,

    const Global = union(enum) {
        nav: InternPool.Nav.Index,
        uav: InternPool.Key.Ptr.BaseAddr.Uav,
    };

    /// The owning module controls build settings. The backend describes this AIR dump's
    /// compiler configuration, not a qualified correspondence with any shipping binary.
    fn writeProfile(w: *W, owner_nav: InternPool.Nav.Index) Error!void {
        const zcu = w.pt.zcu;
        const file = zcu.navFileScope(owner_nav);
        const mod = if (Compat.v14) file.mod else file.mod.?;
        const target = &mod.resolved_target.result;
        const triple = try target.zigTriple(w.gpa);
        const backend = if (Compat.v14)
            target_util.zigBackend(target.*, zcu.comp.config.use_llvm)
        else
            target_util.zigBackend(target, zcu.comp.config.use_llvm);
        try w.j.beginObject();
        try w.field("name");
        try w.j.write("abi64-le-v1");
        try w.field("target_triple");
        try w.j.write(triple);
        try w.field("pointer_bits");
        try w.j.write(target.ptrBitWidth());
        try w.field("endian");
        try w.j.write(@tagName(target.cpu.arch.endian()));
        try w.field("abi");
        try w.j.write(@tagName(target.abi));
        try w.field("zig_version");
        try w.j.write(build_options.version);
        try w.field("backend");
        try w.j.write(@tagName(backend));
        try w.field("cpu");
        try w.j.write(target.cpu.model.name);
        try w.field("features");
        try w.j.beginArray();
        for (target.cpu.arch.allFeaturesList()) |feature| {
            if (target.cpu.features.isEnabled(feature.index)) try w.j.write(feature.name);
        }
        try w.j.endArray();
        try w.field("build_mode");
        try w.j.write(Compat.buildMode(mod.optimize_mode));
        try w.field("float_mode");
        try w.j.write("per-instruction");
        try w.field("error_set_bits");
        try w.j.write(zcu.errorSetBits());
        try w.field("error_layout");
        try w.j.write("type-table");
        try w.field("error_tracing");
        try w.j.write(mod.error_tracing);
        try w.field("export_stage");
        try w.j.write("analyzed-air");
        try w.j.endObject();
    }

    /// The declaration site of a function (`src`): its file relative to the owning module's
    /// root, the module name, and the 1-based line of the declaration. A `dbg_stmt` line is
    /// relative to it (line 1 is the declaration line), as in the LLVM backend's `base_line`.
    fn writeSrc(w: *W, nav: InternPool.Nav.Index) Error!void {
        const zcu = w.pt.zcu;
        const file = zcu.navFileScope(nav);
        const mod = if (Compat.v14) file.mod else file.mod.?;
        try w.j.beginObject();
        try w.field("file");
        try w.j.write(file.sub_file_path);
        try w.field("module");
        try w.j.write(mod.fully_qualified_name);
        try w.field("decl_line");
        try w.j.write(zcu.navSrcLine(nav) + 1);
        try w.j.endObject();
    }

    fn writeFunc(w: *W, fqn: []const u8, fn_ty: Type, func: InternPool.Key.Func) Error!void {
        const owner_nav = func.owner_nav;
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        try w.j.beginObject();
        try w.field("schema");
        try w.j.write(12);
        try w.field("zig_version");
        try w.j.write(build_options.version);
        try w.field("target_endian");
        try w.j.write(@tagName(zcu.getTarget().cpu.arch.endian()));
        try w.field("profile");
        try w.writeProfile(owner_nav);
        try w.field("name");
        try w.j.write(fqn);
        try w.field("module");
        try w.j.write(Identity.navModule(zcu, owner_nav));
        try w.field("src");
        try w.writeSrc(owner_nav);
        try w.writeInstanceKey("instance_key", func);
        try w.field("params");
        try w.j.beginArray();
        const fn_info = ip.indexToKey(fn_ty.toIntern()).func_type;
        const param_types = fn_info.param_types.get(ip);
        w.param_types = param_types;
        for (param_types) |param_ty| try w.writeTypeRef(Type.fromInterned(param_ty));
        try w.j.endArray();
        // The `noalias` parameters, as indices into `params` (the LLVM backend's `noalias`
        // argument attribute). Only the first 32 parameters can be `noalias`.
        try w.field("noalias");
        try w.j.beginArray();
        for (0..@min(param_types.len, 32)) |i| {
            if (@as(u1, @truncate(fn_info.noalias_bits >> @as(u5, @intCast(i)))) != 0) try w.j.write(i);
        }
        try w.j.endArray();
        try w.field("ret");
        try w.writeTypeRef(fn_ty.fnReturnType(zcu));
        // An `export fn`: the linker symbol it defines, which an extern call elsewhere in the
        // program can resolve to (docs/air-json.md §Extern calls).
        if (w.exportedName(owner_nav)) |symbol| {
            try w.field("export");
            try w.j.beginObject();
            try w.field("name");
            try w.j.write(symbol);
            try w.field("cc");
            try w.j.write(@tagName(ip.indexToKey(fn_ty.toIntern()).func_type.cc));
            try w.j.endObject();
        }
        try w.field("body");
        try w.writeBody(w.air.getMainBody());
        // Only a function that calls an extern function has externs.
        if (w.externs.items.len > 0) {
            try w.field("externs");
            try w.j.beginArray();
            for (w.externs.items) |e| try w.writeExternEntry(ip.indexToKey(e).@"extern");
            try w.j.endArray();
        }
        // Only a function with a pointer constant has globals.
        if (w.globals.items.len > 0) {
            try w.field("globals");
            try w.j.beginArray();
            var g: usize = 0;
            while (g < w.globals.items.len) : (g += 1) try w.writeGlobalEntry(w.globals.items[g]);
            try w.j.endArray();
        }
        try w.field("types");
        try w.j.beginArray();
        var i: usize = 0;
        while (i < w.queue.items.len) : (i += 1) {
            try w.writeTypeEntry(Type.fromInterned(w.queue.items[i]));
        }
        try w.j.endArray();
        try w.j.endObject();
    }

    /// The symbol of a function declared with the `export` keyword (`export fn f` defines the
    /// symbol `f`), else null. `@export` aliases are not reported: an extern call to one stays
    /// unbound, which the translator rejects.
    fn exportedName(w: *W, nav_index: InternPool.Nav.Index) ?[]const u8 {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        const nav = ip.getNav(nav_index);
        const analysis = nav.analysis orelse return null;
        const inst = analysis.zir_index.resolve(ip) orelse return null;
        const zir = zcu.navFileScope(nav_index).zir orelse return null;
        if (zir.getDeclaration(inst).linkage != .@"export") return null;
        return nav.name.toSlice(ip);
    }

    /// One `externs` entry: an extern function's linker identity and full function type.
    fn writeExternEntry(w: *W, e: InternPool.Key.Extern) Error!void {
        const ip = &w.pt.zcu.intern_pool;
        const fn_info = ip.indexToKey(e.ty).func_type;
        try w.j.beginObject();
        try w.field("name");
        try w.j.write(e.name.toSlice(ip));
        try w.field("library");
        try w.j.write(e.lib_name.toSlice(ip));
        try w.field("cc");
        try w.j.write(@tagName(fn_info.cc));
        try w.field("params");
        try w.j.beginArray();
        for (fn_info.param_types.get(ip)) |param_ty| try w.writeTypeRef(Type.fromInterned(param_ty));
        try w.j.endArray();
        try w.field("ret");
        try w.writeTypeRef(Type.fromInterned(fn_info.return_type));
        try w.field("varargs");
        try w.j.write(fn_info.is_var_args);
        try w.j.endObject();
    }

    fn data(w: *W, inst: Air.Inst.Index) Air.Inst.Data {
        return w.air.instructions.items(.data)[@intFromEnum(inst)];
    }

    fn writeBody(w: *W, body: []const Air.Inst.Index) Error!void {
        try w.j.beginArray();
        for (body) |inst| try w.writeInst(inst);
        try w.j.endArray();
    }

    fn field(w: *W, name: []const u8) Error!void {
        try w.j.objectField(name);
    }

    /// The content-addressed key of a generic instance (`Identity.instanceKey`), if it has one.
    fn writeInstanceKey(w: *W, name: []const u8, f: InternPool.Key.Func) Error!void {
        const key = Identity.instanceKey(w.pt.zcu, w.gpa, f) orelse return;
        try w.field(name);
        try w.j.write(key[0..]);
    }

    fn writeInst(w: *W, inst: Air.Inst.Index) Error!void {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        const tag = w.air.instructions.items(.tag)[@intFromEnum(inst)];
        try w.j.beginObject();
        try w.field("id");
        try w.j.write(@intFromEnum(inst));
        try w.field("tag");
        try w.j.write(@tagName(tag));
        switch (tag) {
            .inferred_alloc, .inferred_alloc_comptime => {},
            else => {
                try w.field("ty");
                try w.writeTypeRef(w.air.typeOfIndex(inst, ip));
            },
        }
        switch (tag) {
            .add,
            .add_safe,
            .add_wrap,
            .add_sat,
            .sub,
            .sub_safe,
            .sub_wrap,
            .sub_sat,
            .mul,
            .mul_safe,
            .mul_wrap,
            .mul_sat,
            .div_float,
            .div_trunc,
            .div_floor,
            .div_exact,
            .rem,
            .mod,
            .bit_and,
            .bit_or,
            .xor,
            .cmp_lt,
            .cmp_lte,
            .cmp_eq,
            .cmp_gte,
            .cmp_gt,
            .cmp_neq,
            .store,
            .store_safe,
            .array_elem_val,
            .slice_elem_val,
            .ptr_elem_val,
            .shl,
            .shl_exact,
            .shl_sat,
            .shr,
            .shr_exact,
            .min,
            .max,
            .set_union_tag,
            .memset,
            .memset_safe,
            .memcpy,
            // Pointer (lhs), element (rhs). The order is the tag name's suffix.
            .atomic_store_unordered,
            .atomic_store_monotonic,
            .atomic_store_release,
            .atomic_store_seq_cst,
            => {
                const b = w.data(inst).bin_op;
                try w.writeArgs(&.{ b.lhs, b.rhs });
            },
            .atomic_load => {
                const al = w.data(inst).atomic_load;
                try w.writeArgs(&.{al.ptr});
                try w.field("order");
                try w.j.write(@tagName(al.order));
            },
            .atomic_rmw => {
                const pl_op = w.data(inst).pl_op;
                const extra = w.air.extraData(Air.AtomicRmw, pl_op.payload).data;
                try w.writeArgs(&.{ pl_op.operand, extra.operand });
                try w.field("op");
                try w.j.write(@tagName(extra.op()));
                try w.field("order");
                try w.j.write(@tagName(extra.ordering()));
            },
            .cmpxchg_weak, .cmpxchg_strong => {
                const extra = w.air.extraData(Air.Cmpxchg, w.data(inst).ty_pl.payload).data;
                try w.writeArgs(&.{ extra.ptr, extra.expected_value, extra.new_value });
                try w.field("success_order");
                try w.j.write(@tagName(extra.successOrder()));
                try w.field("failure_order");
                try w.j.write(@tagName(extra.failureOrder()));
            },
            .is_null,
            .is_non_null,
            .is_err,
            .is_non_err,
            .ret,
            .ret_safe,
            .ret_load,
            .neg,
            .is_named_enum_value,
            .is_null_ptr,
            .is_non_null_ptr,
            .tag_name,
            .error_name,
            .is_err_ptr,
            .is_non_err_ptr,
            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .floor,
            .ceil,
            .round,
            .trunc_float,
            => {
                try w.writeArgs(&.{w.data(inst).un_op});
            },
            .not,
            .load,
            .trunc,
            .slice_ptr,
            .slice_len,
            .array_to_slice,
            .clz,
            .ctz,
            .popcount,
            .byte_swap,
            .bit_reverse,
            .abs,
            .optional_payload,
            .wrap_optional,
            .unwrap_errunion_payload,
            .unwrap_errunion_err,
            .wrap_errunion_payload,
            .wrap_errunion_err,
            .struct_field_ptr_index_0,
            .struct_field_ptr_index_1,
            .struct_field_ptr_index_2,
            .struct_field_ptr_index_3,
            .ptr_slice_len_ptr,
            .ptr_slice_ptr_ptr,
            .fptrunc,
            .fpext,
            .int_from_float,
            .float_from_int,
            .get_union_tag,
            .optional_payload_ptr,
            .optional_payload_ptr_set,
            .splat,
            .unwrap_errunion_payload_ptr,
            .unwrap_errunion_err_ptr,
            .errunion_payload_ptr_set,
            => try w.writeArgs(&.{w.data(inst).ty_op.operand}),
            .reduce, .reduce_optimized => {
                const r = w.data(inst).reduce;
                try w.writeArgs(&.{r.operand});
                try w.field("op");
                try w.j.write(@tagName(r.operation));
            },
            .cmp_vector, .cmp_vector_optimized => {
                const extra = w.air.extraData(Air.VectorCmp, w.data(inst).ty_pl.payload).data;
                try w.writeArgs(&.{ extra.lhs, extra.rhs });
                try w.field("op");
                try w.j.write(@tagName(extra.compareOperator()));
            },
            .select => {
                const pl_op = w.data(inst).pl_op;
                const b = w.air.extraData(Air.Bin, pl_op.payload).data;
                try w.writeArgs(&.{ b.lhs, b.rhs, pl_op.operand });
            },
            .union_init => {
                const extra = w.air.extraData(Air.UnionInit, w.data(inst).ty_pl.payload).data;
                try w.writeArgs(&.{extra.init});
                try w.field("index");
                try w.j.write(extra.field_index);
            },
            .mul_add => {
                const pl_op = w.data(inst).pl_op;
                const b = w.air.extraData(Air.Bin, pl_op.payload).data;
                try w.writeArgs(&.{ b.lhs, b.rhs, pl_op.operand });
            },
            .arg => {
                try w.field("param");
                try w.j.write(try Compat.argIndex(w, inst));
            },
            .block, .loop => {
                const extra = w.air.extraData(Air.Block, w.data(inst).ty_pl.payload);
                try w.field("body");
                try w.writeBody(@ptrCast(Compat.extra(w.air)[extra.end..][0..extra.data.body_len]));
            },
            .dbg_inline_block => {
                const extra = w.air.extraData(Air.DbgInlineBlock, w.data(inst).ty_pl.payload);
                // The body's `dbg_stmt` lines are relative to the inlined function's declaration.
                try w.field("src");
                try w.writeSrc(w.pt.zcu.funcInfo(extra.data.func).owner_nav);
                try w.field("body");
                try w.writeBody(@ptrCast(Compat.extra(w.air)[extra.end..][0..extra.data.body_len]));
            },
            .add_with_overflow,
            .sub_with_overflow,
            .mul_with_overflow,
            .shl_with_overflow,
            .slice_elem_ptr,
            .ptr_elem_ptr,
            .ptr_add,
            .ptr_sub,
            .slice,
            => {
                const b = w.air.extraData(Air.Bin, w.data(inst).ty_pl.payload).data;
                try w.writeArgs(&.{ b.lhs, b.rhs });
            },
            .call, .call_always_tail, .call_never_tail, .call_never_inline => {
                const pl_op = w.data(inst).pl_op;
                const extra = w.air.extraData(Air.Call, pl_op.payload);
                try w.field("callee");
                try w.writeRef(pl_op.operand);
                try w.writeArgs(@ptrCast(Compat.extra(w.air)[extra.end..][0..extra.data.args_len]));
            },
            .dbg_var_ptr, .dbg_var_val, .dbg_arg_inline => {
                const pl_op = w.data(inst).pl_op;
                const name: Air.NullTerminatedString = @enumFromInt(pl_op.payload);
                try w.writeArgs(&.{pl_op.operand});
                try w.field("name");
                try w.j.write(name.toSlice(w.air.*));
            },
            .struct_field_ptr => try w.writeStructField(inst),
            .field_parent_ptr => {
                const extra = w.air.extraData(Air.FieldParentPtr, w.data(inst).ty_pl.payload).data;
                try w.writeArgs(&.{extra.field_ptr});
                try w.field("index");
                try w.j.write(extra.field_index);
            },
            .aggregate_init => {
                const ty_pl = w.data(inst).ty_pl;
                const ty = Compat.tyPlType(ty_pl);
                const len: usize = switch (ty.zigTypeTag(zcu)) {
                    .@"struct" => ty.structFieldCount(zcu),
                    else => @intCast(ty.arrayLen(zcu)),
                };
                try w.writeArgs(@ptrCast(Compat.extra(w.air)[ty_pl.payload..][0..len]));
            },
            .br, .switch_dispatch => {
                const br = w.data(inst).br;
                try w.field("target");
                try w.j.write(@intFromEnum(br.block_inst));
                try w.writeArgs(&.{br.operand});
            },
            .repeat => {
                try w.field("target");
                try w.j.write(@intFromEnum(w.data(inst).repeat.loop_inst));
            },
            .cond_br => {
                const pl_op = w.data(inst).pl_op;
                const extra = w.air.extraData(Air.CondBr, pl_op.payload);
                const then_body: []const Air.Inst.Index = @ptrCast(Compat.extra(w.air)[extra.end..][0..extra.data.then_body_len]);
                const else_body: []const Air.Inst.Index = @ptrCast(Compat.extra(w.air)[extra.end + then_body.len ..][0..extra.data.else_body_len]);
                try w.writeArgs(&.{pl_op.operand});
                try w.field("then");
                try w.writeBody(then_body);
                try w.field("else");
                try w.writeBody(else_body);
            },
            .@"try", .try_cold => {
                const pl_op = w.data(inst).pl_op;
                const extra = w.air.extraData(Air.Try, pl_op.payload);
                try w.writeArgs(&.{pl_op.operand});
                try w.field("body");
                try w.writeBody(@ptrCast(Compat.extra(w.air)[extra.end..][0..extra.data.body_len]));
            },
            .try_ptr, .try_ptr_cold => {
                const ty_pl = w.data(inst).ty_pl;
                const extra = w.air.extraData(Air.TryPtr, ty_pl.payload);
                try w.writeArgs(&.{extra.data.ptr});
                try w.field("body");
                try w.writeBody(@ptrCast(Compat.extra(w.air)[extra.end..][0..extra.data.body_len]));
            },
            .switch_br, .loop_switch_br => {
                const sw = w.air.unwrapSwitch(inst);
                try w.writeArgs(&.{sw.operand});
                try w.field("cases");
                try w.j.beginArray();
                var it = sw.iterateCases();
                while (it.next()) |case| {
                    try w.j.beginObject();
                    try w.field("items");
                    try w.j.beginArray();
                    for (case.items) |item| try w.writeRef(item);
                    try w.j.endArray();
                    try w.field("ranges");
                    try w.j.beginArray();
                    for (case.ranges) |range| {
                        try w.j.beginArray();
                        try w.writeRef(range[0]);
                        try w.writeRef(range[1]);
                        try w.j.endArray();
                    }
                    try w.j.endArray();
                    try w.field("body");
                    try w.writeBody(case.body);
                    try w.j.endObject();
                }
                try w.j.endArray();
                try w.field("else");
                try w.writeBody(it.elseBody());
            },
            .dbg_stmt => {
                const d = w.data(inst).dbg_stmt;
                try w.field("line");
                try w.j.write(d.line + 1);
                try w.field("column");
                try w.j.write(d.column + 1);
            },
            .assembly => if (Compat.v14) {
                // M21: no inline asm support for 0.14.1.
                try w.field("unsupported");
                try w.j.write(true);
            } else {
                try w.writeAsm(inst);
            },
            .alloc, .ret_ptr, .unreach, .trap, .dbg_empty_stmt => {},
            // A tag that some version lacks or names differently: each `Compat.is*` helper
            // names only the tags of the version being built.
            else => if (Compat.isNewTyOp(tag)) {
                try w.writeArgs(&.{w.data(inst).ty_op.operand});
            } else if (Compat.isNewBinOp(tag)) {
                const b = w.data(inst).bin_op;
                try w.writeArgs(&.{ b.lhs, b.rhs });
            } else if (Compat.isFieldVal(tag)) {
                try w.writeStructField(inst);
            } else if (!Compat.v14) {
                // `@shuffle`: 0.14.1 has one `shuffle` tag; 0.15.2+ split it into
                // `shuffle_one` (single source) and `shuffle_two` (two sources). The two forms
                // use unrelated declarations (`Air.Shuffle` vs `unwrapShuffleOne`/
                // `unwrapShuffleTwo`), so each is behind its own comptime-known `Compat.v14`
                // branch (only the live Zig version's declarations are ever referenced).
                if (tag == .shuffle_one) {
                    const s = w.air.unwrapShuffleOne(zcu, inst);
                    try w.writeArgs(&.{s.operand});
                    try w.writeShuffleOneMask(s.mask);
                } else if (tag == .shuffle_two) {
                    const s = w.air.unwrapShuffleTwo(zcu, inst);
                    try w.writeArgs(&.{ s.operand_a, s.operand_b });
                    try w.writeShuffleTwoMask(s.mask);
                } else if (Compat.isRuntimeNavPtr(tag)) {
                    // A runtime pointer to a `Nav` (`threadlocal var`, or an `extern` that needs a
                    // runtime address): the global's entry in `globals`, whose flags say which.
                    try w.field("global");
                    try w.j.write(try w.globalId(.{ .nav = w.data(inst).ty_nav.nav }));
                } else {
                    try w.field("unsupported");
                    try w.j.write(true);
                }
            } else if (tag == .shuffle) {
                const extra = w.air.extraData(Air.Shuffle, w.data(inst).ty_pl.payload).data;
                try w.writeArgs(&.{ extra.a, extra.b });
                try w.writeShuffle14Mask(extra);
            } else {
                try w.field("unsupported");
                try w.j.write(true);
            },
        }
        try w.j.endObject();
    }

    /// `struct_field_ptr`, `struct_field_val` (`agg_field_val` in 0.17.0): operand and index.
    fn writeStructField(w: *W, inst: Air.Inst.Index) Error!void {
        const extra = w.air.extraData(Air.StructField, w.data(inst).ty_pl.payload).data;
        try w.writeArgs(&.{extra.struct_operand});
        try w.field("index");
        try w.j.write(extra.field_index);
    }

    /// `assembly`: source, per-output/-input constraint+name+operand, clobbers, volatile.
    /// An output whose operand is `.none` is the asm expression's own result (no `ref`).
    fn writeAsm(w: *W, inst: Air.Inst.Index) Error!void {
        const a = Compat.unwrapAsm(w.air, inst);
        try w.field("source");
        try w.j.write(a.source);
        try w.field("volatile");
        try w.j.write(a.is_volatile);
        try w.field("clobbers");
        try Compat.writeClobbers(w, a.clobbers);
        try w.field("outputs");
        try w.j.beginArray();
        {
            var names = a.output_names;
            for (a.outputs) |ref| {
                const pair = readAsmNamePair(names);
                names = names[pair.len..];
                try w.j.beginObject();
                try w.field("constraint");
                try w.j.write(pair.constraint);
                try w.field("name");
                try w.j.write(pair.name);
                if (ref != .none) {
                    try w.field("ref");
                    try w.writeRef(ref);
                }
                try w.j.endObject();
            }
        }
        try w.j.endArray();
        try w.field("inputs");
        try w.j.beginArray();
        {
            var names = a.input_names;
            for (a.inputs) |ref| {
                const pair = readAsmNamePair(names);
                names = names[pair.len..];
                try w.j.beginObject();
                try w.field("constraint");
                try w.j.write(pair.constraint);
                try w.field("name");
                try w.j.write(pair.name);
                try w.field("ref");
                try w.writeRef(ref);
                try w.j.endObject();
            }
        }
        try w.j.endArray();
    }

    /// Format into a string, then write it as an escaped JSON string.
    fn writeFmt(w: *W, v: anytype) Error!void {
        const text = try std.fmt.allocPrint(w.pt.zcu.gpa, Compat.fmt_value, .{v});
        defer w.pt.zcu.gpa.free(text);
        try w.j.write(text);
    }

    /// Write a float constant's bit pattern as a lowercase hex string, zero-padded to the
    /// storage width (e.g. 8 digits for f32, 20 for f80).
    fn writeFloatBits(w: *W, storage: InternPool.Key.Float.Storage) Error!void {
        const gpa = w.pt.zcu.gpa;
        const text = switch (storage) {
            .f16 => |v| try std.fmt.allocPrint(gpa, "0x{x:0>4}", .{@as(u16, @bitCast(v))}),
            .f32 => |v| try std.fmt.allocPrint(gpa, "0x{x:0>8}", .{@as(u32, @bitCast(v))}),
            .f64 => |v| try std.fmt.allocPrint(gpa, "0x{x:0>16}", .{@as(u64, @bitCast(v))}),
            .f80 => |v| try std.fmt.allocPrint(gpa, "0x{x:0>20}", .{@as(u80, @bitCast(v))}),
            .f128 => |v| try std.fmt.allocPrint(gpa, "0x{x:0>32}", .{@as(u128, @bitCast(v))}),
        };
        defer gpa.free(text);
        try w.j.write(text);
    }

    fn writeArgs(w: *W, refs: []const Air.Inst.Ref) Error!void {
        try w.field("args");
        try w.j.beginArray();
        for (refs) |r| try w.writeRef(r);
        try w.j.endArray();
    }

    /// A shuffle mask entry: `{"a": i}` (index into the first/only source), `{"b": i}` (index
    /// into the second source), `{"u": true}` (undefined lane), or `{"v": Ref}` (comptime-known
    /// value lane; `shuffle_one` only).
    fn writeShuffleOneMask(w: *W, mask: []const Air.ShuffleOneMask) Error!void {
        try w.field("mask");
        try w.j.beginArray();
        for (mask) |m| {
            try w.j.beginObject();
            switch (m.unwrap()) {
                .elem => |idx| {
                    try w.field("a");
                    try w.j.write(idx);
                },
                .value => |ip_index| {
                    try w.field("v");
                    try w.writeRef(Air.internedToRef(ip_index));
                },
            }
            try w.j.endObject();
        }
        try w.j.endArray();
    }

    fn writeShuffleTwoMask(w: *W, mask: []const Air.ShuffleTwoMask) Error!void {
        try w.field("mask");
        try w.j.beginArray();
        for (mask) |m| {
            try w.j.beginObject();
            switch (m.unwrap()) {
                .a_elem => |idx| {
                    try w.field("a");
                    try w.j.write(idx);
                },
                .b_elem => |idx| {
                    try w.field("b");
                    try w.j.write(idx);
                },
                .undef => {
                    try w.field("u");
                    try w.j.write(true);
                },
            }
            try w.j.endObject();
        }
        try w.j.endArray();
    }

    /// 0.14.1's `shuffle`: the mask is a comptime `@Vector(mask_len, i32)`. A non-negative lane
    /// indexes the first source; a negative lane `n` indexes the second source at `~n` (see
    /// `codegen/llvm.zig`'s `airShuffle`, which undoes the same encoding). An undefined lane
    /// has no `value`/`b` counterpart: it is always `{"u": true}`.
    fn writeShuffle14Mask(w: *W, extra: Air.Shuffle) Error!void {
        const zcu = w.pt.zcu;
        const mask_val = Value.fromInterned(extra.mask);
        try w.field("mask");
        try w.j.beginArray();
        for (0..extra.mask_len) |i| {
            const elem = try mask_val.elemValue(w.pt, i);
            try w.j.beginObject();
            if (elem.isUndef(zcu)) {
                try w.field("u");
                try w.j.write(true);
            } else {
                const idx = elem.toSignedInt(zcu);
                if (idx >= 0) {
                    try w.field("a");
                    try w.j.write(idx);
                } else {
                    try w.field("b");
                    try w.j.write(~idx);
                }
            }
            try w.j.endObject();
        }
        try w.j.endArray();
    }

    fn writeRef(w: *W, ref: Air.Inst.Ref) Error!void {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        try w.j.beginObject();
        if (ref.toIndex()) |idx| {
            try w.field("inst");
            try w.j.write(@intFromEnum(idx));
        } else {
            const ip_index = ref.toInterned().?;
            const val = Value.fromInterned(ip_index);
            try w.field("ty");
            try w.writeTypeRef(val.typeOf(zcu));
            switch (ip.indexToKey(ip_index)) {
                .func => |f| {
                    try w.field("func");
                    try w.j.write(ip.getNav(f.owner_nav).fqn.toSlice(ip));
                    try w.field("module");
                    try w.j.write(Identity.navModule(zcu, f.owner_nav));
                    try w.writeInstanceKey("instance_key", f);
                    try w.field("noreturn");
                    try w.j.write(Type.fromInterned(f.ty).fnReturnType(zcu).zigTypeTag(zcu) == .noreturn);
                    // A generic instantiation (e.g. `std.Thread.spawn`'s `function` comptime
                    // parameter) carries its comptime arguments. The one that is itself a
                    // function value is the callee the model must dispatch to
                    // (`docs/std-models.md` §Thread model).
                    if (f.generic_owner != .none) {
                        for (f.comptime_args.get(ip)) |carg| {
                            if (carg == .none) continue;
                            switch (ip.indexToKey(carg)) {
                                .func => |cf| {
                                    try w.field("comptime_fn");
                                    try w.j.write(ip.getNav(cf.owner_nav).fqn.toSlice(ip));
                                    try w.field("comptime_fn_module");
                                    try w.j.write(Identity.navModule(zcu, cf.owner_nav));
                                    try w.writeInstanceKey("comptime_fn_instance_key", cf);
                                    break;
                                },
                                else => {},
                            }
                        }
                    }
                },
                // An extern function: its symbol; the `externs` table has its declaration.
                .@"extern" => |e| if (ip.isFunctionType(e.ty)) {
                    try w.field("extern");
                    try w.j.write(e.name.toSlice(ip));
                    try w.field("noreturn");
                    try w.j.write(Type.fromInterned(e.ty).fnReturnType(zcu).zigTypeTag(zcu) == .noreturn);
                    if (std.mem.indexOfScalar(InternPool.Index, w.externs.items, ip_index) == null)
                        try w.externs.append(w.gpa, ip_index);
                } else {
                    try w.field("val");
                    try w.writeFmt(Compat.fmtValue(w.pt, val));
                },
                .err => |e| {
                    try w.field("err");
                    try w.j.write(e.name.toSlice(ip));
                },
                .error_union => |eu| switch (eu.val) {
                    .err_name => |name| {
                        try w.field("err");
                        try w.j.write(name.toSlice(ip));
                    },
                    .payload => |payload_index| {
                        try w.field("payload");
                        try w.writeRef(Air.internedToRef(payload_index));
                    },
                },
                .float => |f| {
                    try w.field("fbits");
                    try w.writeFloatBits(f.storage);
                },
                .int => {
                    try w.field("val");
                    try Compat.writeInt(w, val);
                },
                .enum_tag => |e| {
                    try w.field("enum");
                    try Compat.writeInt(w, Value.fromInterned(e.int));
                },
                .un => |u| {
                    // `tag` is `.none` for a union without a runtime tag.
                    if (u.tag != .none) {
                        try w.field("utag");
                        try w.writeRef(Air.internedToRef(u.tag));
                    }
                    try w.field("uval");
                    try w.writeRef(Air.internedToRef(u.val));
                },
                .opt => |o| if (o.val == .none) {
                    try w.field("null");
                    try w.j.write(true);
                } else {
                    try w.field("some");
                    try w.writeRef(Air.internedToRef(o.val));
                },
                .ptr => |p| {
                    try w.field("ptr");
                    try w.writePtr(p);
                },
                .slice => |s| {
                    try w.field("slice_ptr");
                    try w.writeRef(Air.internedToRef(s.ptr));
                    try w.field("slice_len");
                    try w.writeRef(Air.internedToRef(s.len));
                },
                .aggregate => |a| {
                    // An array has its sentinel as the last element; a vector has no sentinel.
                    const ty = Type.fromInterned(a.ty);
                    const tag = ty.zigTypeTag(zcu);
                    const is_array = tag == .array;
                    const is_vector = tag == .vector;
                    if (is_array or is_vector or tag == .@"struct") {
                        const len = if (is_array)
                            ty.arrayLenIncludingSentinel(zcu)
                        else if (is_vector)
                            ty.vectorLen(zcu)
                        else
                            ty.structFieldCount(zcu);
                        try w.field("elems");
                        try w.j.beginArray();
                        for (0..@intCast(len)) |i| {
                            const elem = if (is_array or is_vector) try val.elemValue(w.pt, i) else try val.fieldValue(w.pt, i);
                            try w.writeRef(Air.internedToRef(elem.toIntern()));
                        }
                        try w.j.endArray();
                    } else {
                        try w.field("val");
                        try w.writeFmt(Compat.fmtValue(w.pt, val));
                    }
                },
                else => if (Compat.isBitpack(ip.indexToKey(ip_index)) and
                    val.typeOf(zcu).zigTypeTag(zcu) == .@"struct")
                {
                    try w.field("val");
                    try Compat.writeInt(w, val);
                } else if (val.isUndef(zcu)) {
                    try w.field("undef");
                    try w.j.write(true);
                } else {
                    try w.field("val");
                    try w.writeFmt(Compat.fmtValue(w.pt, val));
                },
            }
        }
        try w.j.endObject();
    }

    /// Get (or assign) `ty`'s ID and write it as a JSON integer. `ty` is enqueued for a
    /// full `writeTypeEntry` the first time it is seen; see the drain loop in `writeFunc`.
    fn writeTypeRef(w: *W, ty: Type) Error!void {
        try w.j.write(try w.typeId(ty));
    }

    const ResolvedPtr = union(enum) {
        global: struct { base: Global, off: u64, payload_base: bool },
        null,
        unsupported: []const u8,
    };

    fn sizedLayout(zcu: *Zcu, ty: Type) bool {
        if (!Compat.hasLayout(zcu, ty) or ty.comptimeOnly(zcu)) return false;
        return ty.abiSize(zcu) != 0;
    }

    /// Resolve addresses only; this does not read or initialize an optional/error payload.
    /// Canonical parent pointers are const/volatile/allowzero align(1) in InternPool in
    /// every supported version. Their volatile bit is address metadata, not an access.
    /// Only the actual leaf pointer may authorize a memory access, and it is checked below.
    fn resolvePtr(w: *W, p: InternPool.Key.Ptr) ResolvedPtr {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        var base = p.base_addr;
        var walk: PtrOffset.Walk = .{ .off = p.byte_offset };
        var payload = false;
        // Each projection consumes one interned parent. The bound rejects both cycles and
        // excessively nested acyclic constants, without allocating during error reporting.
        while (true) switch (base) {
            .nav, .uav => {
                const g: Global = switch (base) {
                    .nav => |nav| .{ .nav = nav },
                    .uav => |uav| .{ .uav = uav },
                    else => unreachable,
                };
                if (payload) {
                    const leaf_ty = Type.fromInterned(p.ty);
                    if (leaf_ty.zigTypeTag(zcu) != .pointer) return .{ .unsupported = "payload_pointer_type" };
                    const leaf = leaf_ty.ptrInfo(zcu);
                    if (leaf.flags.is_volatile) return .{ .unsupported = "payload_volatile" };
                    if (leaf.packed_offset.host_size != 0 or leaf.packed_offset.bit_offset != 0 or
                        leaf.flags.vector_index != .none) return .{ .unsupported = "payload_packed" };
                    if (leaf.flags.address_space != .generic) return .{ .unsupported = "payload_address_space" };
                    const child = leaf_ty.childType(zcu);
                    if (!sizedLayout(zcu, child)) return .{ .unsupported = "payload_layout" };
                    const root_ty = switch (g) {
                        .nav => |nav| blk: {
                            const info = Compat.navInfo(zcu, nav);
                            if (info.init == null or info.is_extern or info.is_threadlocal)
                                return .{ .unsupported = "payload_unbacked" };
                            break :blk Type.fromInterned(info.ty);
                        },
                        .uav => |uav| Value.fromInterned(uav.val).typeOf(zcu),
                    };
                    if (!sizedLayout(zcu, root_ty)) return .{ .unsupported = "payload_global_layout" };
                    const end = PtrOffset.Walk.add(walk.off, child.abiSize(zcu)) catch
                        return .{ .unsupported = "payload_overflow" };
                    if (end > root_ty.abiSize(zcu)) return .{ .unsupported = "payload_bounds" };
                }
                return .{ .global = .{ .base = g, .off = walk.off, .payload_base = payload } };
            },
            .int => return if (!payload and walk.off == 0) .null else .{ .unsupported = "int" },
            .field, .eu_payload, .opt_payload => {
                const parent_index = switch (base) {
                    .field => |f| f.base,
                    .eu_payload, .opt_payload => |idx| idx,
                    else => unreachable,
                };
                const key = ip.indexToKey(parent_index);
                if (key != .ptr) return .{ .unsupported = "projection_parent" };
                const parent = key.ptr;
                const parent_ty = Type.fromInterned(parent.ty);
                if (parent_ty.zigTypeTag(zcu) != .pointer) return .{ .unsupported = "projection_parent_type" };
                const info = parent_ty.ptrInfo(zcu);
                if (info.packed_offset.host_size != 0 or info.packed_offset.bit_offset != 0 or
                    info.flags.vector_index != .none) return .{ .unsupported = "projection_packed" };
                if (info.flags.address_space != .generic) return .{ .unsupported = "projection_address_space" };
                const agg = parent_ty.childType(zcu);
                const delta: u64 = switch (base) {
                    .field => |f| switch (agg.zigTypeTag(zcu)) {
                        .pointer => if (agg.ptrSize(zcu) == .slice and f.index < 2) f.index * 8 else
                            return .{ .unsupported = "field" },
                        .@"struct" => blk: {
                            if (agg.containerLayout(zcu) == .@"packed" or !Compat.hasLayout(zcu, agg))
                                return .{ .unsupported = "field" };
                            if (f.index >= agg.structFieldCount(zcu) or agg.structFieldIsComptime(f.index, zcu))
                                return .{ .unsupported = "field" };
                            break :blk agg.structFieldOffset(@intCast(f.index), zcu);
                        },
                        else => return .{ .unsupported = "field" },
                    },
                    .opt_payload => blk: {
                        payload = true;
                        if (agg.zigTypeTag(zcu) != .optional or !sizedLayout(zcu, agg) or
                            agg.optionalReprIsPayload(zcu)) return .{ .unsupported = "optional_payload_layout" };
                        if (!sizedLayout(zcu, agg.optionalChild(zcu))) return .{ .unsupported = "optional_payload_layout" };
                        // Type.abiSizeInnerOptional (14/15) and abiSize (16): child first,
                        // presence byte second, with trailing padding to child alignment.
                        break :blk 0;
                    },
                    .eu_payload => blk: {
                        payload = true;
                        if (agg.zigTypeTag(zcu) != .error_union or !sizedLayout(zcu, agg))
                            return .{ .unsupported = "error_payload_layout" };
                        const child = agg.errorUnionPayload(zcu);
                        if (!sizedLayout(zcu, child)) return .{ .unsupported = "error_payload_layout" };
                        const ca = child.abiAlignment(zcu);
                        const ea = Type.anyerror.abiAlignment(zcu);
                        const es = Type.anyerror.abiSize(zcu);
                        // Use the same exact layout helper as the compiler's lowerPtr.
                        const compiler_off = @import("../codegen.zig").errUnionPayloadOffset(child, zcu);
                        const payload_align = ca.toByteUnits() orelse return .{ .unsupported = "error_payload_layout" };
                        const model_off = if (payload_align >= 2) 0 else ca.forward(2);
                        // ZigLean.errUnionOffsets now puts nonzero equal-alignment payloads
                        // first. Keep the general compiler/model comparison fail-closed.
                        if (es != 2 or ea.toByteUnits() != 2 or compiler_off != model_off)
                            return .{ .unsupported = "error_payload_model_layout" };
                        break :blk compiler_off;
                    },
                    else => unreachable,
                };
                walk.project(delta, parent.byte_offset) catch |err| return .{ .unsupported = switch (err) {
                    error.Overflow => "projection_overflow",
                    error.Depth => "projection_depth",
                } };
                base = parent.base_addr;
            },
            // InternPool explicitly defines arr_elem as COMPTIME-ONLY in 14/15/16.
            // Runtime array addressing uses the ordinary base plus byte_offset instead.
            .arr_elem => return .{ .unsupported = "arr_elem" },
            else => return .{ .unsupported = @tagName(base) },
        };
    }

    /// A pointer constant preserves one existing global identity and its checked offset.
    /// Failed resolution never calls globalId and therefore cannot invent a block.
    fn writePtr(w: *W, p: InternPool.Key.Ptr) Error!void {
        try w.j.beginObject();
        var off: u64 = p.byte_offset;
        switch (w.resolvePtr(p)) {
            .global => |resolved| {
                try w.field("global");
                try w.j.write(try w.globalId(resolved.base));
                off = resolved.off;
                if (resolved.payload_base) {
                    try w.field("payload_base");
                    try w.j.write(true);
                }
            },
            .null => {
                try w.field("null");
                try w.j.write(true);
            },
            .unsupported => |reason| {
                try w.field("unsupported");
                try w.j.write(reason);
            },
        }
        try w.field("off");
        try w.j.write(off);
        try w.j.endObject();
    }

    fn globalId(w: *W, g: Global) Error!u32 {
        for (w.globals.items, 0..) |x, i| {
            const same = switch (x) {
                .nav => |n| g == .nav and g.nav == n,
                .uav => |u| g == .uav and g.uav.val == u.val and g.uav.orig_ty == u.orig_ty,
            };
            if (same) return @intCast(i);
        }
        try w.globals.append(w.gpa, g);
        return @intCast(w.globals.items.len - 1);
    }

    /// One entry of the `globals` table. A `nav` is a container-level `var` or `const`; a `uav`
    /// is an unnamed constant (a string literal, or the value behind `&.{…}`).
    fn writeGlobalEntry(w: *W, g: Global) Error!void {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        try w.j.beginObject();
        switch (g) {
            .nav => |nav| {
                const info = Compat.navInfo(zcu, nav);
                const name = ip.getNav(nav).fqn.toSlice(ip);
                const module = Identity.navModule(zcu, nav);
                Identity.claim(zcu, .global, module, name, @intFromEnum(nav));
                try w.field("name");
                try w.j.write(name);
                try w.field("module");
                try w.j.write(module);
                try w.field("ty");
                try w.writeTypeRef(Type.fromInterned(info.ty));
                try w.field("const");
                try w.j.write(info.is_const);
                try w.field("threadlocal");
                try w.j.write(info.is_threadlocal);
                try w.field("extern");
                try w.j.write(info.is_extern);
                if (info.init) |init| {
                    try w.field("init");
                    try w.writeRef(Air.internedToRef(init));
                }
            },
            .uav => |uav| {
                try w.field("ty");
                try w.writeTypeRef(Value.fromInterned(uav.val).typeOf(zcu));
                try w.field("const");
                try w.j.write(true);
                try w.field("init");
                try w.writeRef(Air.internedToRef(uav.val));
            },
        }
        try w.j.endObject();
    }

    fn typeId(w: *W, ty: Type) Error!u32 {
        const gop = try w.ids.getOrPut(w.gpa, ty.toIntern());
        if (!gop.found_existing) {
            gop.value_ptr.* = @intCast(w.queue.items.len);
            try w.queue.append(w.gpa, ty.toIntern());
        }
        return gop.value_ptr.*;
    }

    /// The `name` and `module` of a struct, enum or union type entry: an identity of this
    /// type only.
    fn writeTypeName(w: *W, ty: Type) Error!void {
        const zcu = w.pt.zcu;
        const name = Compat.containerTypeName(ty, &zcu.intern_pool);
        const module = Identity.typeModule(zcu, ty);
        Identity.claim(zcu, .type, module, name, @intFromEnum(ty.toIntern()));
        try w.field("name");
        try w.j.write(name);
        try w.field("module");
        try w.j.write(module);
    }

    /// Write one full type entry (this type's array element in `types`). Child types are
    /// written via `writeTypeRef`, i.e. as IDs, never nested inline.
    fn writeTypeEntry(w: *W, ty: Type) Error!void {
        const zcu = w.pt.zcu;
        const ip = &zcu.intern_pool;
        try w.j.beginObject();
        try w.field("k");
        switch (ty.zigTypeTag(zcu)) {
            .int => {
                const info = ty.intInfo(zcu);
                try w.j.write("int");
                try w.field("signed");
                try w.j.write(info.signedness == .signed);
                try w.field("bits");
                try w.j.write(info.bits);
            },
            .bool => try w.j.write("bool"),
            .void => try w.j.write("void"),
            .noreturn => try w.j.write("noreturn"),
            .float => {
                try w.j.write("float");
                try w.field("bits");
                try w.j.write(ty.floatBits(zcu.getTarget()));
            },
            .pointer => {
                try w.j.write("ptr");
                try w.field("size");
                try w.j.write(@tagName(ty.ptrSize(zcu)));
                try w.field("const");
                try w.j.write(ty.isConstPtr(zcu));
                try w.field("child");
                try w.writeTypeRef(ty.childType(zcu));
                const info = ty.ptrInfo(zcu);
                // The `align(N)` of the pointer type. The natural alignment needs the child's
                // layout (`ptrAlignment` asserts it).
                if (info.flags.alignment != .none or Compat.hasLayout(zcu, ty.childType(zcu))) {
                    try w.field("ptr_align");
                    try w.j.write(ty.ptrAlignment(zcu).toByteUnits() orelse 0);
                }
                try w.field("volatile");
                try w.j.write(info.flags.is_volatile);
                try w.field("allowzero");
                try w.j.write(info.flags.is_allowzero);
                // Every pointer names its address space (`generic` for ordinary memory), so
                // `*addrspace(.gs) T` cannot be read as a generic pointer.
                try w.field("address_space");
                try w.j.write(@tagName(info.flags.address_space));
                try w.field("sentinel");
                try w.j.write(info.sentinel != .none);
                // allocSentinel(u8, n, s): the result pointer type contains the exact
                // comptime argument s. Export it explicitly; presence alone cannot model it.
                if (Compat.v16 and info.sentinel != .none and ty.childType(zcu).toIntern() == .u8_type) {
                    try w.field("sentinel_byte");
                    try Compat.writeInt(w, Value.fromInterned(info.sentinel));
                }
                // A bit-pointer (`&packed_struct.field`): the size of its host integer in bytes.
                try w.field("host_size");
                try w.j.write(info.packed_offset.host_size);
                // Its field's first bit in the host integer (schema 11).
                if (info.packed_offset.host_size != 0) {
                    try w.field("bit_offset");
                    try w.j.write(info.packed_offset.bit_offset);
                }
                // A pointer to one lane of a vector (`&v[i]`): its `host_size` is the vector
                // length, not bytes, and the lane is only in the type. Before 0.17.0 only a lane
                // that is not a whole power-of-two number of bytes gets one; 0.17.0 uses it for
                // every lane. A bit-pointer always has the field, `null` for a packed field
                // pointer: an export without it cannot tell the two apart, so the translator
                // then accepts only bit-pointers that it sees made.
                if (info.flags.vector_index != .none) {
                    try w.field("vector_index");
                    if (Compat.isRuntimeLane(info.flags.vector_index))
                        try w.j.write("runtime")
                    else
                        try w.j.write(@intFromEnum(info.flags.vector_index));
                } else if (info.packed_offset.host_size != 0) {
                    try w.field("vector_index");
                    try w.j.write(null);
                }
            },
            .array => {
                try w.j.write("array");
                try w.field("len");
                try w.j.write(ty.arrayLen(zcu));
                try w.field("child");
                try w.writeTypeRef(ty.childType(zcu));
                try w.field("sentinel");
                try w.j.write(ty.sentinel(zcu) != null);
            },
            .vector => {
                try w.j.write("vector");
                try w.field("len");
                try w.j.write(ty.vectorLen(zcu));
                try w.field("child");
                try w.writeTypeRef(ty.childType(zcu));
            },
            .optional => {
                try w.j.write("optional");
                try w.field("child");
                try w.writeTypeRef(ty.optionalChild(zcu));
            },
            .error_union => {
                try w.j.write("error_union");
                try w.field("error");
                try w.writeTypeRef(ty.errorUnionSet(zcu));
                try w.field("payload");
                try w.writeTypeRef(ty.errorUnionPayload(zcu));
            },
            .error_set => {
                try w.j.write("error_set");
                // An inferred error set (`!T`) can still be unresolved here (this function is
                // written during another function's analysis); `errorSetNames` asserts it is
                // resolved, so write `inferred` instead of names.
                const unresolved = switch (ty.toIntern()) {
                    .adhoc_inferred_error_set_type => true,
                    else => switch (ip.indexToKey(ty.toIntern())) {
                        .inferred_error_set_type => |i| ip.funcIesResolvedUnordered(i) == .none,
                        else => false,
                    },
                };
                if (unresolved) {
                    try w.field("inferred");
                    try w.j.write(true);
                } else if (ty.isAnyError(zcu)) {
                    try w.field("any");
                    try w.j.write(true);
                } else {
                    const NullTerminatedString = InternPool.NullTerminatedString;
                    const sorted = try w.gpa.dupe(NullTerminatedString, ty.errorSetNames(zcu).get(ip));
                    std.mem.sortUnstable(NullTerminatedString, sorted, ip, struct {
                        fn lessThan(ip_: *InternPool, a: NullTerminatedString, b: NullTerminatedString) bool {
                            return std.mem.lessThan(u8, a.toSlice(ip_), b.toSlice(ip_));
                        }
                    }.lessThan);
                    try w.field("errors");
                    try w.j.beginArray();
                    for (sorted) |name| try w.j.write(name.toSlice(ip));
                    try w.j.endArray();
                }
            },
            .@"struct" => {
                const is_tuple = ty.isTuple(zcu);
                try w.j.write(if (is_tuple) "tuple" else "struct");
                if (!is_tuple) {
                    try w.writeTypeName(ty);
                    try w.field("layout");
                    try w.j.write(@tagName(ty.containerLayout(zcu)));
                }
                // A struct that is only behind a pointer can have no known fields (0.16.0).
                if (!Compat.hasFields(zcu, ty)) {
                    try w.field("no_fields");
                    try w.j.write(true);
                    try w.j.endObject();
                    return;
                }
                // A packed struct has bit offsets, not byte offsets.
                const offsets = Compat.hasLayout(zcu, ty) and
                    (is_tuple or ty.containerLayout(zcu) != .@"packed");
                try w.field("fields");
                try w.j.beginArray();
                for (0..ty.structFieldCount(zcu)) |i| {
                    try w.j.beginObject();
                    if (ty.structFieldName(i, zcu).toSlice(ip)) |name| {
                        try w.field("name");
                        try w.j.write(name);
                    }
                    try w.field("ty");
                    try w.writeTypeRef(ty.fieldType(i, zcu));
                    // A comptime field has no runtime storage (its offset overlaps others).
                    if (ty.structFieldIsComptime(i, zcu)) {
                        try w.field("comptime");
                        try w.j.write(true);
                    }
                    if (offsets) {
                        try w.field("offset");
                        try w.j.write(ty.structFieldOffset(i, zcu));
                    }
                    try w.j.endObject();
                }
                try w.j.endArray();
            },
            .@"enum" => {
                try w.j.write("enum");
                try w.writeTypeName(ty);
                try w.field("tag");
                try w.writeTypeRef(Compat.enumTagType(ty, zcu));
                try w.field("exhaustive");
                try w.j.write(!ty.isNonexhaustiveEnum(zcu));
                try w.field("fields");
                try w.j.beginArray();
                for (0..ty.enumFieldCount(zcu)) |i| {
                    const tag_val = try w.pt.enumValueFieldIndex(ty, @intCast(i));
                    try w.j.beginObject();
                    try w.field("name");
                    try w.j.write(ty.enumFieldName(i, zcu).toSlice(ip));
                    try w.field("value");
                    try Compat.writeInt(w, Value.fromInterned(ip.indexToKey(tag_val.toIntern()).enum_tag.int));
                    try w.j.endObject();
                }
                try w.j.endArray();
            },
            .@"union" => {
                try w.j.write("union");
                try w.writeTypeName(ty);
                try w.field("layout");
                try w.j.write(@tagName(ty.containerLayout(zcu)));
                if (!Compat.hasFields(zcu, ty)) {
                    try w.field("no_fields");
                    try w.j.write(true);
                    try w.j.endObject();
                    return;
                }
                // The field names are the names of the tag enum, also for an untagged union.
                const names_ty = ty.unionTagTypeHypothetical(zcu);
                if (ty.unionTagType(zcu)) |tag_ty| {
                    try w.field("tag");
                    try w.writeTypeRef(tag_ty);
                } else if (Compat.unionSafetyTag(zcu, ty)) |tag_ty| {
                    try w.field("safety_tag");
                    try w.writeTypeRef(tag_ty);
                }
                try w.field("fields");
                try w.j.beginArray();
                for (0..names_ty.enumFieldCount(zcu)) |i| {
                    try w.j.beginObject();
                    try w.field("name");
                    try w.j.write(names_ty.enumFieldName(i, zcu).toSlice(ip));
                    try w.field("ty");
                    try w.writeTypeRef(ty.unionFieldTypeByIndex(i, zcu));
                    try w.j.endObject();
                }
                try w.j.endArray();
            },
            else => {
                try w.j.write("other");
                try w.field("name");
                try w.writeFmt(Compat.fmtType(w.pt, ty));
            },
        }
        // The size and alignment in bytes, for the types that can be in memory.
        const in_memory = switch (ty.zigTypeTag(zcu)) {
            .int,
            .bool,
            .void,
            .float,
            .pointer,
            .array,
            .vector,
            .optional,
            .error_union,
            .error_set,
            .@"struct",
            .@"enum",
            .@"union",
            => true,
            else => false,
        };
        if (in_memory and Compat.hasLayout(zcu, ty)) {
            try w.field("abi_size");
            try w.j.write(ty.abiSize(zcu));
            try w.field("abi_align");
            try w.j.write(ty.abiAlignment(zcu).toByteUnits() orelse 0);
        }
        try w.j.endObject();
    }
};
