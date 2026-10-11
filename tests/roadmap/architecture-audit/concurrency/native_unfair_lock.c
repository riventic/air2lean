/* Architecture audit (concurrency): the OS primitive under Zig 0.15.2's macOS
 * std.Thread.Mutex (DarwinImpl). The model's contract (Zig.osUnfairUnlockC) is an ownerless
 * release xchg of 0; the real os_unfair_lock records the owner and aborts on a foreign unlock.
 * Build: cc -O2 native_unfair_lock.c -o native_unfair_lock; run: ./native_unfair_lock */
#include <os/lock.h>
#include <pthread.h>
#include <stdio.h>

static os_unfair_lock lock = OS_UNFAIR_LOCK_INIT;

static void *locker(void *arg) {
  (void)arg;
  os_unfair_lock_lock(&lock);
  return NULL;
}

int main(void) {
  pthread_t t;
  pthread_create(&t, NULL, locker, NULL);
  pthread_join(t, NULL);
  os_unfair_lock_unlock(&lock); /* model: fine; native: abort */
  printf("unlock by non-owner returned (model behaviour)\n");
  return 0;
}
