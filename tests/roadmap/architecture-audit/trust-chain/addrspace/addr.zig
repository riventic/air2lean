export fn readGs(p: *addrspace(.gs) const u64) u64 {
    return p.*;
}
export fn readGen(p: *const u64) u64 {
    return p.*;
}
