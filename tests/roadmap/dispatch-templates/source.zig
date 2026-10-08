//! A tokenizer written as a labelled-switch state machine (`continue :sw` dispatch).
//! `TokenizerProof.lean` proves `countTokens` on its fresh compiler-exported translation.
const std = @import("std");

const State = enum(u8) { start, ident, number, done };

fn isAlpha(c: u8) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or c == '_';
}

fn isDigit(c: u8) bool {
    return c >= '0' and c <= '9';
}

/// The number of identifier (`[A-Za-z_][A-Za-z0-9_]*`) and number (`[0-9]+`) tokens.
export fn countTokens(ptr: [*]const u8, len: usize) u32 {
    const input = ptr[0..len];
    var i: usize = 0;
    var count: u32 = 0;
    sw: switch (State.start) {
        .start => {
            if (i == input.len) continue :sw .done;
            const c = input[i];
            i += 1;
            if (isAlpha(c)) {
                count +%= 1;
                continue :sw .ident;
            }
            if (isDigit(c)) {
                count +%= 1;
                continue :sw .number;
            }
            continue :sw .start;
        },
        .ident => {
            if (i < input.len and (isAlpha(input[i]) or isDigit(input[i]))) {
                i += 1;
                continue :sw .ident;
            }
            continue :sw .start;
        },
        .number => {
            if (i < input.len and isDigit(input[i])) {
                i += 1;
                continue :sw .number;
            }
            continue :sw .start;
        },
        .done => {},
    }
    return count;
}

const sample_a = "ab 12 c";
const sample_b = "x1+22y_z;;9";
const sample_c = "";
const sample_d = "  __init__ 0x1F 007 a.b";

export fn sampleA() u32 {
    return countTokens(sample_a.ptr, sample_a.len);
}
export fn sampleB() u32 {
    return countTokens(sample_b.ptr, sample_b.len);
}
export fn sampleC() u32 {
    return countTokens(sample_c.ptr, sample_c.len);
}
export fn sampleD() u32 {
    return countTokens(sample_d.ptr, sample_d.len);
}

test "tokenizer state machine" {
    try std.testing.expectEqual(@as(u32, 3), sampleA());
    try std.testing.expectEqual(@as(u32, 4), sampleB());
    try std.testing.expectEqual(@as(u32, 0), sampleC());
    try std.testing.expectEqual(@as(u32, 6), sampleD());
}
