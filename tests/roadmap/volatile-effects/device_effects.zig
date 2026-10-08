//! L13 device-effect fixture (docs/volatile-effects.md §Device contract). A UART-style
//! driver over a memory-mapped register block. Translated with
//! `--device-contract tests/roadmap/volatile-effects/uart.json`, every volatile access is a
//! device event; without the contract every accessing function is rejected (VOLATILE_ACCESS).

/// The register block: a read-only status register and a write-only data register.
pub const Uart = extern struct {
    status: u32,
    data: u32,
};

/// Status bit 0: the transmitter accepts a byte.
pub const tx_ready: u32 = 1;

/// Poll the status register until the transmitter is ready, then write one byte.
pub fn putc(uart: *volatile Uart, c: u8) void {
    while (uart.status & tx_ready == 0) {}
    uart.data = c;
}

/// Write every byte, in order.
pub fn writeAll(uart: *volatile Uart, bytes: []const u8) void {
    for (bytes) |c| putc(uart, c);
}

/// Two status reads: two device events, never one merged read.
pub fn statusTwice(uart: *volatile Uart) u32 {
    const a = uart.status;
    const b = uart.status;
    return a ^ b;
}

/// A read whose value is unused (a read-to-clear register): still one device event.
pub fn clearStatus(uart: *volatile Uart) void {
    _ = uart.status;
}

/// A write, then a read: the read happens after the write.
pub fn sendThenStatus(uart: *volatile Uart, c: u8) u32 {
    uart.data = c;
    return uart.status;
}

comptime {
    _ = &putc;
    _ = &writeAll;
    _ = &statusTwice;
    _ = &clearStatus;
    _ = &sendThenStatus;
}
