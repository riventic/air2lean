// Q01 heavy differential, seeds 18, 19 and 39 (shrunk from seed 19): a comptime-known tagged-union
// local whose address is taken (`_ = un;`) becomes a constant global. Native Zig passes; translation
// emits an invalid Gen.lean (no `Zig.Enc U` instance for the constant block, and the pointer
// constants into it become `Zig.ptrFromAddr 0`). OPEN translator bug, see docs/fuzzing.md.
// Reproduce: scripts/translate.sh tests/roadmap/fuzz/known-failures/fuzz_s19.zig -o /tmp/G.lean --namespace K
const U = union(enum) { a: u32, b: i32 };

fn work(p0: u32, p1: u32) u32 {
    _ = p0;
    _ = p1;
    const un5: U = .{ .b = @as(i32, 0) };
    _ = un5;
    return @as(u32, 0);
}

pub fn entry(a: u32, b: u32) u32 {
    return work(a, b);
}

comptime {
    _ = &entry;
}
