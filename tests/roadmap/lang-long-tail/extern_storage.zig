//! L12: pointer-bearing `extern` storage (`docs/generated-code.md` §Globals). The program
//! declares the globals; another object (`provider_extern_storage.c` natively) defines them and
//! the storage their pointers reach. The translation takes their initial values and that storage
//! as the explicit `ext : ExternInit` of `mem0`.
pub const Node = extern struct { v: u32, next: ?*Node };

extern var ext_counter: u32;
extern var ext_head: ?*Node;
extern const ext_name: [*:0]const u8;
extern var ext_slot: *u32;

var local_node: Node = .{ .v = 100, .next = null };

/// The sum of the list that starts at `ext_head`.
pub fn sumList() u32 {
    var n = ext_head;
    var s: u32 = 0;
    while (n) |p| : (n = p.next) s +%= p.v;
    return s;
}

/// The length of the external C string `ext_name`.
pub fn nameLen() u32 {
    var i: u32 = 0;
    while (ext_name[i] != 0) i += 1;
    return i;
}

/// The value `ext_slot` points to.
pub fn slotValue() u32 {
    return ext_slot.*;
}

/// Pushes the program's own node onto the external list, increments the external counter and
/// the cell `ext_slot` points to, and returns the new sum of the list.
pub fn pushLocal() u32 {
    local_node.next = ext_head;
    ext_head = &local_node;
    ext_slot.* +%= 1;
    ext_counter +%= 1;
    return sumList();
}

/// The external counter.
pub fn counter() u32 {
    return ext_counter;
}

comptime {
    _ = &sumList;
    _ = &nameLen;
    _ = &slotValue;
    _ = &pushLocal;
    _ = &counter;
}
