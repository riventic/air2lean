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
pub const Kind = enum(u8) { module, output, type, global };

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
