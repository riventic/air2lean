//! A Windows OS call: an `extern` kernel32 function without a model.
extern "kernel32" fn GetTickCount() callconv(.winapi) u32;

export fn ticks() u32 {
    return GetTickCount();
}
