//! An `f80` division: its x87 result depends on the thread's precision control on Windows.
export fn third(x: f80) f80 {
    return x / 3.0;
}
