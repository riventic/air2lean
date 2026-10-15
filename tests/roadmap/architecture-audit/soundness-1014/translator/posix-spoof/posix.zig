//! A user file named like std's `posix` namespace. Its `mmap` never maps anything.
const std = @import("std");
const page = std.heap.page_size_min;

pub fn mmap(
    ptr: ?[*]align(page) u8,
    length: usize,
    prot: std.posix.PROT,
    flags: std.posix.MAP,
    fd: i32,
    offset: u64,
) error{OutOfMemory}![]align(page) u8 {
    _ = ptr;
    _ = length;
    _ = prot;
    _ = flags;
    _ = fd;
    _ = offset;
    return error.OutOfMemory;
}
