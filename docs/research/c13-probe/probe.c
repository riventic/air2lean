// C13 probe: what a futex-backed mutex (the algorithm of Zig 0.17 std.Io.Mutex) and futex wait
// guarantee natively. Two observations:
//   1. barging: a thread that unlocks and immediately relocks keeps the lock; a waiter gets few
//      or no acquisitions (no fairness, no starvation freedom).
//   2. a futex wait returns without a wake: a signal gives EINTR (Linux) / -EINTR (macOS ulock)
//      with the word unchanged (the "spurious" return that std callers must loop on).
// Build: cc -O2 -pthread probe.c -o probe   (Linux: gcc/clang in a container)
#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#ifdef __linux__
#include <linux/futex.h>
#include <sys/syscall.h>
static int fwait(_Atomic uint32_t *p, uint32_t e) {
  return syscall(SYS_futex, p, FUTEX_WAIT_PRIVATE, e, NULL, NULL, 0);
}
static void fwake(_Atomic uint32_t *p, int n) { syscall(SYS_futex, p, FUTEX_WAKE_PRIVATE, n, NULL, NULL, 0); }
#else
extern int __ulock_wait(uint32_t op, void *addr, uint64_t val, uint32_t timeout_us);
extern int __ulock_wake(uint32_t op, void *addr, uint64_t val);
#define UL_COMPARE_AND_WAIT 1
#define ULF_WAKE_ALL 0x100
static int fwait(_Atomic uint32_t *p, uint32_t e) {
  int r = __ulock_wait(UL_COMPARE_AND_WAIT, (void *)p, e, 0);
  if (r < 0 && errno == 0) errno = -r;   // libsystem sets errno; fall back to -errno
  return 0;
}
static void fwake(_Atomic uint32_t *p, int n) { __ulock_wake(UL_COMPARE_AND_WAIT | (n > 1 ? ULF_WAKE_ALL : 0), (void *)p, 0); }
#endif

static _Atomic uint32_t m; // 0 unlocked, 1 locked_once, 2 contended (std.Io.Mutex.State)
static _Atomic int stop;
static _Atomic long acq[2];

static void lock(void) {
  uint32_t z = 0;
  if (atomic_compare_exchange_strong_explicit(&m, &z, 1, memory_order_acquire, memory_order_relaxed)) return;
  if (z == 2) fwait(&m, 2);
  while (atomic_exchange_explicit(&m, 2, memory_order_acquire) != 0) fwait(&m, 2);
}
static void unlock(void) {
  if (atomic_exchange_explicit(&m, 0, memory_order_release) == 2) fwake(&m, 1);
}
static _Atomic long maxwait_ns;
static long now_ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1000000000L + t.tv_nsec; }
// id 0 hogs: it holds the lock for a short critical section and relocks at once.
// id 1 is the victim: it does ~2us of work outside the lock between acquisitions.
static void *worker(void *a) {
  long id = (long)a, worst = 0;
  while (!atomic_load(&stop)) {
    long t0 = now_ns();
    lock();
    long w = now_ns() - t0; if (w > worst) worst = w;
    atomic_fetch_add_explicit(&acq[id], 1, memory_order_relaxed);
    for (volatile int i = 0; i < 50; i++) {}
    unlock();
    if (id == 1) { long e = now_ns() + 2000; while (now_ns() < e) {} }
  }
  if (id == 1) atomic_store(&maxwait_ns, worst);
  return NULL;
}

static _Atomic uint32_t w; static _Atomic int waiting, eintr, other;
static void noop(int s) { (void)s; }
static void *sleeper(void *a) {
  (void)a;
  atomic_store(&waiting, 1);
  errno = 0; int r = fwait(&w, 0);               // nobody ever wakes; the word never changes
  int e = errno;
  fprintf(stderr, "fwait returned %d errno=%d\n", r, e);
  if (e == EINTR) atomic_store(&eintr, 1); else atomic_store(&other, 1);
  return NULL;
}

int main(void) {
  pthread_t t0, t1;
  pthread_create(&t0, NULL, worker, (void *)0);
  pthread_create(&t1, NULL, worker, (void *)1);
  sleep(2);
  atomic_store(&stop, 1);
  pthread_join(t0, NULL); pthread_join(t1, NULL);
  printf("hog vs victim, 2s: hog=%ld victim=%ld acquisitions, victim worst wait=%ld ns\n", acq[0], acq[1], atomic_load(&maxwait_ns));

  struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_handler = noop; sigaction(SIGUSR1, &sa, NULL);
  pthread_t s; pthread_create(&s, NULL, sleeper, NULL);
  while (!atomic_load(&waiting)) {}
  usleep(200000);
  pthread_kill(s, SIGUSR1);
  usleep(200000);
  printf("futex wait, word unchanged, no wake, one signal: returned_with_EINTR=%d other_return=%d\n",
         atomic_load(&eintr), atomic_load(&other));
  if (!atomic_load(&eintr)) { fwake(&w, 1); }
  pthread_join(s, NULL);
  return 0;
}
