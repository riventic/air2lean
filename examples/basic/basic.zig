pub const Job = struct {
    duration: u32,
    due: u32,
    weight: u8,
};

export fn scale(a: u32, b: u8) u32 {
    return a * b;
}

export fn clampAdd(a: u16, b: u16) u16 {
    return a +| b;
}

export fn absDiff(a: i32, b: i32) u32 {
    if (a > b) return @intCast(a - b);
    return @intCast(b - a);
}

pub fn tardiness(end: u32, due: u32) u32 {
    return if (end > due) end - due else 0;
}

pub fn weightedTardiness(job: Job, start: u32) u32 {
    const end = start + job.duration;
    return tardiness(end, job.due) * job.weight;
}

pub fn sum(xs: []const u32) u64 {
    var total: u64 = 0;
    for (xs) |x| total += x;
    return total;
}

pub fn totalWeightedTardiness(jobs: []const Job) u64 {
    var t: u32 = 0;
    var cost: u64 = 0;
    var i: usize = 0;
    while (i < jobs.len) : (i += 1) {
        cost += weightedTardiness(jobs[i], t);
        t += jobs[i].duration;
    }
    return cost;
}

pub fn classify(x: u8) u8 {
    return switch (x) {
        0 => 0,
        1...9 => 1,
        else => 2,
    };
}

comptime {
    _ = &tardiness;
    _ = &weightedTardiness;
    _ = &sum;
    _ = &totalWeightedTardiness;
    _ = &classify;
}
