#!/usr/bin/env python3
"""scripts/par.py: bounded workers, output in job order for any worker count, exit statuses,
log files, memory and CPU bounds, and cancellation. Offline: the jobs are small shell commands."""
import importlib.util
import io
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
PAR = ROOT / 'scripts/par.py'
spec = importlib.util.spec_from_file_location('par', PAR)
par = sys.modules["par"] = importlib.util.module_from_spec(spec)
spec.loader.exec_module(par)

# Each job writes interleaved stdout/stderr lines, sleeping so that later jobs finish first.
JOB = ('n={}; for i in 1 2 3; do echo "out $n.$i"; echo "err $n.$i" >&2; '
       'sleep 0.0$((7 - n)); done; [ "$n" != 3 ] || exit 7; [ "$n" != 5 ] || kill -TERM $$')


def run_par(*args, env=None):
    result = subprocess.run([sys.executable, '-B', str(PAR), *args], capture_output=True,
                            env=dict(os.environ, **(env or {})))
    return result.returncode, result.stdout.decode(), result.stderr.decode()


class Output(unittest.TestCase):
    def test_same_streams_for_any_worker_count(self):
        items = [str(n) for n in range(1, 7)]
        runs = [run_par('--jobs', str(jobs), '--', 'bash', '-c', JOB, ':::', *items) for jobs in (1, 3, 6)]
        self.assertEqual(runs[0], runs[1])
        self.assertEqual(runs[0], runs[2])
        code, out, err = runs[0]
        self.assertEqual(out, ''.join(f'out {n}.{i}\n' for n in range(1, 7) for i in (1, 2, 3)))
        self.assertTrue(err.startswith(''.join(f'err {n}.{i}\n' for n in range(1, 7) for i in (1, 2, 3))))
        # The first failure in job order gives the status; a signal is 128 + its number.
        self.assertEqual(code, 7)
        self.assertIn('par: 2 of 6 jobs failed: 3 (exit 7), 5 (exit 143)', err)

    def test_stream_interleaving_within_a_job_is_kept(self):
        out, err = io.BytesIO(), io.BytesIO()
        merged = []

        class Tee:
            def __init__(self, name, sink):
                self.name, self.sink = name, sink

            def write(self, data):
                merged.append((self.name, data))
                self.sink.write(data)

            def flush(self):
                pass

        jobs = [par.Job(str(n), ['bash', '-c', f'echo a{n}; sleep 0.05; echo b{n} >&2; sleep 0.05; echo c{n}'])
                for n in range(3)]
        self.assertEqual(par.run(jobs, 3, Tee('out', out), Tee('err', err)), [0, 0, 0])
        text = [(name, data.decode()) for name, data in merged]
        self.assertEqual(text, [(stream, f'{line}{n}\n') for n in range(3)
                                for stream, line in (('out', 'a'), ('err', 'b'), ('out', 'c'))])

    def test_item_substitution_and_log_dir(self):
        with tempfile.TemporaryDirectory() as tmp:
            code, out, _ = run_par('--jobs', '2', '--log-dir', tmp, '--', 'echo', 'x{}y', ':::', 'a', 'b c')
            self.assertEqual((code, out), (0, 'xay\nxb cy\n'))
            self.assertEqual(sorted(p.name for p in Path(tmp).iterdir()), ['a.log', 'b_c.log'])
            self.assertEqual((Path(tmp) / 'b_c.log').read_text(), 'xb cy\n')
            self.assertEqual(run_par('--', 'echo', ':::', 'a', 'b')[1], 'a\nb\n')  # appended
        self.assertEqual(run_par('--', 'echo', ':::')[0], 0)
        self.assertNotEqual(run_par('--', 'echo', ':::', 'a', 'a')[0], 0)
        self.assertNotEqual(run_par('--', 'echo')[0], 0)

    def test_missing_command(self):
        code, _, err = run_par('--', '/nonexistent/tool', ':::', 'x')
        self.assertEqual(code, 127)
        self.assertIn('cannot start', err)

    def test_jobs_run_concurrently_up_to_the_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            # Each job records how many jobs are running when it starts.
            job = (f'touch {tmp}/run.$$; ls {tmp} | grep -c run >> {tmp}/seen.{{}}; sleep 0.3; '
                   f'rm {tmp}/run.$$')
            started = time.monotonic()
            self.assertEqual(run_par('--jobs', '3', '--', 'bash', '-c', job, ':::', *'abcdef')[0], 0)
            elapsed = time.monotonic() - started
            seen = [int((Path(tmp) / f'seen.{c}').read_text()) for c in 'abcdef']
        self.assertLessEqual(max(seen), 3)
        self.assertLess(elapsed, 6 * 0.3)

    def test_jobs_see_a_single_worker(self):
        self.assertEqual(run_par('--jobs', '4', '--', 'bash', '-c', 'echo $AIR2LEAN_JOBS', ':::', 'x')[1], '1\n')


class Workers(unittest.TestCase):
    def test_bounds(self):
        with mock.patch.dict(os.environ, {'AIR2LEAN_JOBS': '6', 'AIR2LEAN_MEM_MIB': '4000'}):
            self.assertEqual(par.workers(), 6)
            self.assertEqual(par.workers(mem_mib=1000), 4)
            self.assertEqual(par.workers(mem_mib=8000), 1)
            self.assertEqual(par.workers(jobs=2, mem_mib=1000), 2)
            self.assertEqual(par.workers(count=3), 3)
            self.assertEqual(par.workers(count=0), 1)
        with mock.patch.dict(os.environ, {'AIR2LEAN_JOBS': 'two'}):
            with self.assertRaises(SystemExit):
                par.workers()

    def test_cgroup_limits(self):
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(par, 'CGROUP', Path(tmp)), \
                mock.patch.dict(os.environ, {'AIR2LEAN_MEM_MIB': ''}):
            (Path(tmp) / 'cpu.max').write_text('400000 100000\n')
            (Path(tmp) / 'memory.max').write_text(str(10 << 30) + '\n')
            self.assertEqual(par.cpu_count(), min(4, par.cpu_count()))
            self.assertLessEqual(par.cpu_count(), 4)
            self.assertEqual(par.memory_budget_mib(), int((10 << 30) * par.MEM_FRACTION) >> 20)
            (Path(tmp) / 'cpu.max').write_text('max 100000\n')
            (Path(tmp) / 'memory.max').write_text('max\n')
            self.assertGreaterEqual(par.memory_budget_mib(), 1)
            self.assertGreaterEqual(par.cpu_count(), 1)

    def test_print_jobs(self):
        self.assertEqual(run_par('--print-jobs', '--jobs', '5', '--count', '2')[1], '2\n')
        self.assertEqual(run_par('--print-jobs', env={'AIR2LEAN_JOBS': '3'})[1], '3\n')


class Cancel(unittest.TestCase):
    def test_signal_stops_every_job(self):
        with tempfile.TemporaryDirectory() as tmp:
            job = f'echo $$ > {tmp}/pid.{{}}; trap "" TERM; while :; do sleep 0.05; done'
            process = subprocess.Popen([sys.executable, '-B', str(PAR), '--jobs', '3', '--', 'bash', '-c', job,
                                        ':::', 'a', 'b', 'c'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            deadline = time.monotonic() + 20
            while len(list(Path(tmp).glob('pid.*'))) < 3:
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.05)
            pids = [int(p.read_text()) for p in Path(tmp).glob('pid.*')]
            process.send_signal(signal.SIGTERM)
            process.communicate(timeout=60)
            self.assertEqual(process.returncode, 128 + signal.SIGTERM)
            for pid in pids:
                with self.assertRaises(ProcessLookupError):
                    os.kill(pid, 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
