// B1 regression: the root module and the dependency module `other` both have a `util.zig` with a
// `helper`. Both are exported as `util.helper`; only the module tells them apart.
const util = @import("util.zig");
const other = @import("other");

export fn entry(x: u32) u32 {
    return util.helper(x) +% other.util.helper(x);
}
