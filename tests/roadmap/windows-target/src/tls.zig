//! A `threadlocal` counter: Windows TLS (the PE TLS directory) has no model yet.
threadlocal var counter: u32 = 0;

export fn bump() u32 {
    counter += 1;
    return counter;
}
