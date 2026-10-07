// Reference source of the hand-written fixtures in air/ (make-fixtures.py). Each
// air/bitsN directory is this file at the error width of one `--error-limit`:
//   bits16: default (65534), bits8: 255, bits10: 1000, bits17: 100000.
// The fixtures are written by hand, not exported; see README.md for what is qualified.
pub const Failure = error{ Bad, Other };

pub fn storeError(cell: *Failure, e: Failure) Failure {
    cell.* = e;
    return cell.*;
}

pub fn storeOptional(cell: *?Failure, e: ?Failure) bool {
    cell.* = e;
    return cell.* != null;
}

pub fn loadOptional(cell: *?Failure) ?Failure {
    return cell.*;
}

pub fn unionTry8(cell: *Failure!u8, v: Failure!u8) Failure!u8 {
    cell.* = v;
    return (&(try cell.*)).*;
}

pub fn unionTry64(cell: *Failure!u64, v: Failure!u64) Failure!u64 {
    cell.* = v;
    return (&(try cell.*)).*;
}

pub fn setPayload(cell: *Failure!u8, x: u8) bool {
    cell.* = x;
    return if (cell.*) |_| false else |_| true;
}

pub fn loadUnion(cell: *Failure!u8) Failure!u8 {
    return cell.*;
}
