//! air2lean: the identity of exported declarations (docs/air-json.md §Identity).
//!
//! A fully qualified name (`util.helper`) is a path inside one module, so an identity is the
//! pair (module, name). The module is `root` for the main module, `std` for the standard
//! library, else the module's `fully_qualified_name` (`fileModule`). The exporter writes it
//! next to every name that identifies a function, type or global.
//!
//! One compilation never exports two different declarations under one identity. Each module
//! name, output file, named type and named global that the exporter writes is claimed by the
//! declaration that wrote it first. A claim by a different declaration is a hard error: the
//! process exits with status 1, so that a later translation cannot silently use one
//! declaration for the other.

const std = @import("std");
const Zcu = @import("../Zcu.zig");
const Type = @import("../Type.zig");
const InternPool = @import("../InternPool.zig");

const zv = @import("builtin").zig_version;

/// The kinds of claimed identities. Each has its own namespace.
pub const Kind = enum(u8) { module, output, type, global, instance };

/// The declaration that claimed an identity: its compilation and an ID that is unique there
/// (a `Nav.Index`, an `InternPool.Index` or a module address).
const Owner = struct { zcu: *const Zcu, id: usize };

/// 0.16.0 has no `std.Thread.Mutex`. The lock is held only for a hash map update.
const Lock = if (zv.minor >= 16) struct {
    m: std.atomic.Mutex = .unlocked,
    fn lock(l: *@This()) void {
        while (!l.m.tryLock()) std.atomic.spinLoopHint();
    }
    fn unlock(l: *@This()) void {
        l.m.unlock();
    }
} else std.Thread.Mutex;

// The claims live as long as the process. Sub-compilations (compiler_rt, …) analyse on other
// threads, so the table is locked.
var lock: Lock = .{};
var arena: std.heap.ArenaAllocator = .init(std.heap.page_allocator);
var claims: std.StringHashMapUnmanaged(Owner) = .empty;

/// Record that `id` of `zcu` writes the identity `<module>:<name>` of `kind` (`module` is
/// empty for a module or an output file). Exits the process if a different declaration
/// already wrote it. An output file is shared by every compilation of the process (one
/// output directory); the other identities belong to one compilation, so a sub-compilation
/// (compiler_rt) has its own `root` and `std`.
pub fn claim(zcu: *const Zcu, kind: Kind, module: []const u8, name: []const u8, id: usize) void {
    lock.lock();
    defer lock.unlock();
    const a = arena.allocator();
    const scope: usize = if (kind == .output) 0 else @intFromPtr(zcu);
    const separator: []const u8 = if (module.len == 0) "" else ":";
    const key = std.mem.concat(a, u8, &.{ std.mem.asBytes(&scope), &.{@intFromEnum(kind)}, module, separator, name }) catch fatalOom();
    const identity = key[@sizeOf(usize) + 1 ..];
    const gop = claims.getOrPut(a, key) catch fatalOom();
    if (!gop.found_existing) {
        gop.value_ptr.* = .{ .zcu = zcu, .id = id };
        return;
    }
    const previous = gop.value_ptr.*;
    if (previous.zcu == zcu and previous.id == id) return;
    std.log.err("air2lean: two different declarations export the {s} identity '{s}' " ++
        "(the exported AIR would describe only one of them; docs/air-json.md §Identity)", .{ @tagName(kind), identity });
    std.process.exit(1);
}

fn fatalOom() noreturn {
    std.log.err("air2lean: out of memory while recording an exported identity", .{});
    std.process.exit(1);
}

/// The module name of `file`: `root` for the main module and `std` for the standard library
/// (whatever the compiler calls them: 0.16.0 names the main module of `zig build-obj x.zig`
/// `x`), else the module's `fully_qualified_name`. Two different modules of one compilation
/// can have the same name (each module's `builtin`), so the first module exported claims it.
fn fileModule(zcu: *Zcu, file: *const Zcu.File) []const u8 {
    const mod = if (zv.minor == 14) file.mod else file.mod.?;
    const name = if (mod == zcu.main_mod) "root" else if (mod == zcu.std_mod) "std" else mod.fully_qualified_name;
    claim(zcu, .module, "", name, @intFromPtr(mod));
    return name;
}

/// The module of a function or global.
pub fn navModule(zcu: *Zcu, nav: InternPool.Nav.Index) []const u8 {
    return fileModule(zcu, zcu.navFileScope(nav));
}

/// The module of a struct, enum or union type: the module of the file that declares it (of
/// its union, for a generated union tag).
pub fn typeModule(zcu: *Zcu, ty: Type) []const u8 {
    const inst = ty.typeDeclInstAllowGeneratedTag(zcu).?;
    return fileModule(zcu, zcu.fileByIndex(inst.resolveFile(&zcu.intern_pool)));
}

/// The storage identity of a function (its output filename's source, docs/export-names.md):
/// the name itself in the `root` and `std` modules (the historical filenames), else
/// `<module>:<name>`, whose `:` makes the filename a SHA-256 name.
pub fn storageName(a: std.mem.Allocator, module: []const u8, name: []const u8) ![]const u8 {
    if (std.mem.eql(u8, module, "root") or std.mem.eql(u8, module, "std")) return name;
    return std.mem.concat(a, u8, &.{ module, ":", name });
}

// Generic instances (docs/air-json.md §Instances).
//
// The compiler names a generic instance `<generic fqn>__anon_<n>`, where `n` is the instance's
// InternPool index: it depends on everything the compilation analysed before. The
// `instance_key` is intrinsic: the SHA-256 of a canonical encoding of what makes the instance
// (the InternPool's own instance identity): the generic declaration (module, fqn), each comptime
// argument, and the instance's function type (an `anytype` parameter's type, `noinline`). A
// type is encoded by its stable identity (a named container by (module, name), every other
// type structurally), a value canonically (an integer by its magnitude, an aggregate by its
// elements, a pointer by its base and offset), never by an InternPool index. So the same
// instance has the same key in every program that uses it and in every source order, and two
// different instances have different keys.
//
// An argument without a stable identity (a container whose compiler-made name has a number,
// `__struct_<n>`; a pointer into comptime-mutable memory; a lazy `@sizeOf`) gives no key: the
// instance has no `instance_key` and keeps the compiler's name. One compilation never gives
// two different instances one key (the `instance` claim).

const Sha256 = std.crypto.hash.sha2.Sha256;

/// The version of the encoding, hashed into every key: a changed encoding changes every key.
const encoding_version = "air2lean-instance-v1";

/// The `instance_key` of function `f`: 64 lower-case hex digits, or `null` if `f` is not a
/// generic instance or an argument has no stable identity.
pub fn instanceKey(zcu: *Zcu, gpa: std.mem.Allocator, f: InternPool.Key.Func) ?[64]u8 {
    if (f.generic_owner == .none) return null;
    var e: Encoder = .{ .zcu = zcu, .gpa = gpa, .h = Sha256.init(.{}) };
    e.str(encoding_version);
    e.instance(f, 0) catch |err| switch (err) {
        error.Unstable => return null,
        error.OutOfMemory => fatalOom(),
    };
    const key = std.fmt.bytesToHex(e.h.finalResult(), .lower);
    const ip = &zcu.intern_pool;
    const owner = ip.funcDeclInfo(f.generic_owner).owner_nav;
    const name = std.mem.concat(gpa, u8, &.{ ip.getNav(owner).fqn.toSlice(ip), "#", &key }) catch fatalOom();
    claim(zcu, .instance, navModule(zcu, owner), name, @intFromEnum(f.owner_nav));
    return key;
}

/// Does `name` (a fqn or type name) have no per-compilation number? The compiler numbers
/// generic instances (`__anon_<n>`) and containers without a declaration name (`__struct_<n>`,
/// `__enum_<n>`, `__union_<n>`, `__opaque_<n>`).
fn stableName(name: []const u8) bool {
    for ([_][]const u8{ "__anon_", "__struct_", "__enum_", "__union_", "__opaque_" }) |marker| {
        var rest = name;
        while (std.mem.indexOf(u8, rest, marker)) |i| {
            rest = rest[i + marker.len ..];
            if (rest.len > 0 and std.ascii.isDigit(rest[0])) return false;
        }
    }
    return true;
}

/// A prefix-free encoding into the hash: every item starts with a tag byte, and every string
/// and sequence with its length.
const Encoder = struct {
    zcu: *Zcu,
    gpa: std.mem.Allocator,
    h: Sha256,

    const Error = error{ Unstable, OutOfMemory };
    /// Deeper nesting (a type of a type of …) gives no key.
    const max_depth = 64;

    fn tag(e: *Encoder, t: u8) void {
        e.h.update(&.{t});
    }

    fn int(e: *Encoder, x: u64) void {
        var bytes: [8]u8 = undefined;
        std.mem.writeInt(u64, &bytes, x, .little);
        e.h.update(&bytes);
    }

    fn str(e: *Encoder, s: []const u8) void {
        e.int(s.len);
        e.h.update(s);
    }

    /// A compiler value without InternPool indices (`CallingConvention` and its options): by
    /// field, enum tags by name.
    fn plain(e: *Encoder, x: anytype) void {
        const T = @TypeOf(x);
        switch (@typeInfo(T)) {
            .void => {},
            .bool => e.tag(@intFromBool(x)),
            .int => |i| e.int(@as(std.meta.Int(.unsigned, i.bits), @bitCast(x))),
            .optional => if (x) |payload| {
                e.tag(1);
                e.plain(payload);
            } else e.tag(0),
            .@"enum" => |info| if (info.is_exhaustive) e.str(@tagName(x)) else e.int(@intFromEnum(x)),
            .@"struct" => |info| inline for (info.fields) |field| e.plain(@field(x, field.name)),
            .@"union" => switch (x) {
                inline else => |payload, t| {
                    e.str(@tagName(t));
                    e.plain(payload);
                },
            },
            else => @compileError("air2lean: no canonical encoding for " ++ @typeName(T)),
        }
    }

    /// A declaration: (module, fqn). A compiler-made fqn has no stable identity.
    fn nav(e: *Encoder, index: InternPool.Nav.Index) Error!void {
        const ip = &e.zcu.intern_pool;
        const fqn = ip.getNav(index).fqn.toSlice(ip);
        if (!stableName(fqn)) return error.Unstable;
        e.str(navModule(e.zcu, index));
        e.str(fqn);
    }

    /// A generic instance: its generic declaration, comptime arguments and parameter types.
    /// The uncoerced type: a coerced function value is the same instance.
    fn instance(e: *Encoder, f: InternPool.Key.Func, depth: u32) Error!void {
        const ip = &e.zcu.intern_pool;
        try e.nav(ip.funcDeclInfo(f.generic_owner).owner_nav);
        const args = f.comptime_args.get(ip);
        e.int(args.len);
        for (args) |arg| try e.optValue(arg, depth + 1);
        // The return type follows from the rest; it can be this instance's inferred error set.
        try e.fnType(ip.indexToKey(f.uncoerced_ty).func_type, false, depth + 1);
    }

    fn func(e: *Encoder, f: InternPool.Key.Func, depth: u32) Error!void {
        if (f.generic_owner == .none) {
            e.tag('d');
            try e.nav(f.owner_nav);
        } else {
            e.tag('g');
            try e.instance(f, depth);
        }
    }

    fn fnType(e: *Encoder, t: InternPool.Key.FuncType, with_return: bool, depth: u32) Error!void {
        const ip = &e.zcu.intern_pool;
        const params = t.param_types.get(ip);
        e.int(params.len);
        for (params) |param| try e.ty(param, depth + 1);
        e.int(t.comptime_bits);
        e.int(t.noalias_bits);
        e.plain(t.cc);
        e.plain(t.is_var_args);
        e.plain(t.is_noinline);
        if (with_return) try e.ty(t.return_type, depth + 1);
    }

    fn ty(e: *Encoder, index: InternPool.Index, depth: u32) Error!void {
        if (depth > max_depth) return error.Unstable;
        const ip = &e.zcu.intern_pool;
        const d = depth + 1;
        switch (ip.indexToKey(index)) {
            .int_type => |t| {
                e.tag('i');
                e.plain(t.signedness);
                e.int(t.bits);
            },
            .ptr_type => |t| {
                e.tag('p');
                // Size, alignment, const, volatile, allowzero, address space, vector lane.
                e.int(@as(u32, @bitCast(t.flags)));
                e.int(@as(u32, @bitCast(t.packed_offset)));
                try e.optValue(t.sentinel, d);
                try e.ty(t.child, d);
            },
            .array_type => |t| {
                e.tag('a');
                e.int(t.len);
                try e.optValue(t.sentinel, d);
                try e.ty(t.child, d);
            },
            .vector_type => |t| {
                e.tag('v');
                e.int(t.len);
                try e.ty(t.child, d);
            },
            .opt_type => |child| {
                e.tag('o');
                try e.ty(child, d);
            },
            .anyframe_type => |child| {
                e.tag('F');
                if (child == .none) e.tag(0) else {
                    e.tag(1);
                    try e.ty(child, d);
                }
            },
            .error_union_type => |t| {
                e.tag('e');
                try e.ty(t.error_set_type, d);
                try e.ty(t.payload_type, d);
            },
            .simple_type => |t| {
                e.tag('s');
                e.str(@tagName(t));
            },
            .struct_type, .union_type, .enum_type, .opaque_type => {
                const t = Type.fromInterned(index);
                const name = t.containerTypeName(ip).toSlice(ip);
                if (!stableName(name)) return error.Unstable;
                const module = typeModule(e.zcu, t);
                // One (module, name) is one type in a compilation, as in a type table.
                claim(e.zcu, .type, module, name, @intFromEnum(index));
                e.tag('c');
                e.str(module);
                e.str(name);
            },
            .tuple_type => |t| {
                e.tag('t');
                const types = t.types.get(ip);
                e.int(types.len);
                for (types, t.values.get(ip)) |field_ty, field_val| {
                    try e.ty(field_ty, d);
                    try e.optValue(field_val, d);
                }
            },
            .func_type => |t| {
                e.tag('f');
                try e.fnType(t, true, d);
            },
            .error_set_type => |t| {
                e.tag('E');
                // By name: the InternPool sorts them by string index.
                const names = try e.gpa.alloc([]const u8, t.names.len);
                defer e.gpa.free(names);
                for (names, t.names.get(ip)) |*n, s| n.* = s.toSlice(ip);
                std.mem.sort([]const u8, names, {}, lessThan);
                e.int(names.len);
                for (names) |n| e.str(n);
            },
            .inferred_error_set_type => |owner| {
                e.tag('I');
                try e.func(ip.indexToKey(owner).func, d);
            },
            else => return error.Unstable,
        }
    }

    fn lessThan(_: void, a: []const u8, b: []const u8) bool {
        return std.mem.lessThan(u8, a, b);
    }

    fn optValue(e: *Encoder, index: InternPool.Index, depth: u32) Error!void {
        if (index == .none) return e.tag(0);
        e.tag(1);
        try e.value(index, depth);
    }

    /// A comptime value: a type by its identity, any other value by its type and contents.
    fn value(e: *Encoder, index: InternPool.Index, depth: u32) Error!void {
        if (depth > max_depth) return error.Unstable;
        const ip = &e.zcu.intern_pool;
        const d = depth + 1;
        const value_ty = ip.typeOf(index);
        if (value_ty == .type_type) {
            e.tag('T');
            return e.ty(index, d);
        }
        e.tag('V');
        try e.ty(value_ty, d);
        const key = ip.indexToKey(index);
        switch (key) {
            .undef => e.tag('u'),
            .simple_value => |v| {
                e.tag('s');
                e.str(@tagName(v));
            },
            .int => |v| {
                e.tag('i');
                try e.bigInt(v.storage);
            },
            .float => |v| {
                e.tag('f');
                switch (v.storage) {
                    inline else => |x| {
                        const bits: u128 = @as(std.meta.Int(.unsigned, @bitSizeOf(@TypeOf(x))), @bitCast(x));
                        e.int(@bitSizeOf(@TypeOf(x)));
                        e.int(@truncate(bits));
                        e.int(@truncate(bits >> 64));
                    },
                }
            },
            .err => |v| {
                e.tag('r');
                e.str(v.name.toSlice(ip));
            },
            .error_union => |v| switch (v.val) {
                .err_name => |name| {
                    e.tag('r');
                    e.str(name.toSlice(ip));
                },
                .payload => |payload| {
                    e.tag('P');
                    try e.value(payload, d);
                },
            },
            .enum_literal => |name| {
                e.tag('l');
                e.str(name.toSlice(ip));
            },
            .enum_tag => |v| {
                e.tag('n');
                try e.value(v.int, d);
            },
            .func => |f| {
                e.tag('F');
                try e.func(f, d);
            },
            .ptr => |p| {
                e.tag('p');
                e.int(p.byte_offset);
                switch (p.base_addr) {
                    .nav => |n| {
                        e.tag('n');
                        try e.nav(n);
                    },
                    .uav => |u| {
                        e.tag('u');
                        try e.ty(u.orig_ty, d);
                        try e.value(u.val, d);
                    },
                    .comptime_field => |v| {
                        e.tag('c');
                        try e.value(v, d);
                    },
                    .int => e.tag('i'),
                    .eu_payload => |base| {
                        e.tag('E');
                        try e.value(base, d);
                    },
                    .opt_payload => |base| {
                        e.tag('O');
                        try e.value(base, d);
                    },
                    .field => |b| {
                        e.tag('f');
                        try e.value(b.base, d);
                        e.int(b.index);
                    },
                    .arr_elem => |b| {
                        e.tag('a');
                        try e.value(b.base, d);
                        e.int(b.index);
                    },
                    // Comptime-mutable memory is not a value of the instance.
                    .comptime_alloc => return error.Unstable,
                }
            },
            .slice => |s| {
                e.tag('S');
                try e.value(s.ptr, d);
                try e.value(s.len, d);
            },
            .opt => |o| {
                e.tag('o');
                try e.optValue(o.val, d);
            },
            .aggregate => |a| switch (a.storage) {
                // The InternPool keeps one storage form per value.
                .bytes => |bytes| {
                    e.tag('b');
                    e.str(bytes.toSlice(ip.aggregateTypeLenIncludingSentinel(a.ty), ip));
                },
                .elems => |elems| {
                    e.tag('A');
                    e.int(elems.len);
                    for (elems) |elem| try e.value(elem, d);
                },
                .repeated_elem => |elem| {
                    e.tag('R');
                    try e.value(elem, d);
                },
            },
            .un => |u| {
                e.tag('U');
                try e.optValue(u.tag, d);
                try e.value(u.val, d);
            },
            else => {
                // 0.16.0's packed struct and union values.
                if (zv.minor >= 16) {
                    if (key == .bitpack) {
                        e.tag('k');
                        return e.value(key.bitpack.backing_int_val, d);
                    }
                }
                return error.Unstable;
            },
        }
    }

    /// An integer: its sign, then its magnitude's little-endian bytes without trailing zeros.
    /// A lazy `@sizeOf`/`@alignOf` (before 0.16.0) gives no key.
    fn bigInt(e: *Encoder, storage: InternPool.Key.Int.Storage) Error!void {
        var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        const big: std.math.big.int.Const = switch (storage) {
            inline else => |x, t| if (t == .big_int)
                x
            else if (t == .u64 or t == .i64)
                std.math.big.int.Mutable.init(&space.limbs, x).toConst()
            else
                return error.Unstable,
        };
        e.tag(@intFromBool(big.positive or big.eqlZero()));
        // Limbs least significant first, each little-endian: the magnitude's little-endian bytes.
        comptime std.debug.assert(@import("builtin").cpu.arch.endian() == .little);
        const bytes = std.mem.sliceAsBytes(big.limbs);
        var len = bytes.len;
        while (len > 0 and bytes[len - 1] == 0) len -= 1;
        e.str(bytes[0..len]);
    }
};
