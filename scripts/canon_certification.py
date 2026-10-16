"""Check fresh canonicalization certificates from gen-integrity's actual translations.

There is no case inventory or success cache here. gen-integrity supplies every case and
its Translator; each invocation compiles the actual snapshots and runs fresh Assurance
kernel replay for the complete batch. Run under the caller's standard build guard.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent


def lean(path, compile_module=False):
    output = [f"--root={path.parent}", "-o", str(path.with_suffix(".olean"))] if compile_module else []
    return subprocess.run(["lake", "env", "lean", *output, str(path)], cwd=ROOT,
                          capture_output=True, text=True, timeout=900)


def roundtrip_source(source, translator, index):
    namespaces = re.findall(r"^namespace (.+)$", source, re.M)
    if len(namespaces) != 1:
        raise ValueError("canonicalization certificate must have exactly one namespace")
    namespace, = namespaces
    arguments = ", ".join(json.dumps(a, ensure_ascii=False) for a in translator.arguments[index])
    directory = json.dumps(str(translator.inputs[index]), ensure_ascii=False)
    wrapper = ("import Air2Lean.Main\n" + source + "\n#eval do\n"
               f"  let args ← IO.ofExcept (Air2Lean.parseArgs [{arguments}])\n"
               f"  let changed ← Air2Lean.CanonCertificate.checkDirectory {directory} args.allocatorModel "
               f"{namespace}.snapshots\n"
               f'  IO.println s!"canon-snapshot-count:{{{namespace}.snapshots.size}}"\n'
               '  IO.println s!"canon-debug-changes:{changed}"\n')
    return namespace, wrapper


def compile_certificate(source, translator, index, case):
    namespace, wrapper = roundtrip_source(source, translator, index)
    path = translator.work / f"RoundTrip{index}.lean"
    path.write_text(wrapper)
    start = time.monotonic()
    result = lean(path, compile_module=True)
    if result.returncode != 0:
        raise ValueError(f"{case.label}: canonicalization certificate failed\n"
                         + result.stdout + result.stderr)
    counts = re.findall(r"^canon-snapshot-count:(\d+)$", result.stdout, re.M)
    changes = re.findall(r"^canon-debug-changes:(true|false)$", result.stdout, re.M)
    if len(counts) != 1 or len(changes) != 1:
        raise ValueError(f"{case.label}: missing native snapshot binding result\n" + result.stdout)
    olean = path.with_suffix(".olean")
    with olean.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    elapsed = time.monotonic() - start
    print(f"{case.label}: kernel proof and both native snapshots check "
          f"({len(source.encode())} certificate bytes; {elapsed:.3f}s)", flush=True)
    return dict(module=path.stem, namespace=namespace, count=int(counts[0]),
                olean=str(olean.resolve()), olean_sha256=digest,
                changed=changes[0] == "true", seconds=elapsed, bytes=len(source.encode()))


def reject_mutant(source, work):
    """The real equality obligation must reject a changed live argument definition ID."""
    for target in re.finditer(r"^def before_body_(\d+) : Array Inst :=\n(.*?)\n\ndef after_body_",
                              source, re.M | re.S):
        binding = re.match(r"\s*#\[\{ id := (\d+),\s*ty := \d+,\s*op := Air2Lean\.Op\.arg\b", target[2])
        if binding:
            break
    else:
        return False
    after = re.search(rf"^def after_body_{target[1]} : Array Inst :=\n(.*?)\n\ndef after_",
                      source, re.M | re.S)
    if after is None:
        raise ValueError("missing mapped target body in wrong-canonicalization control")
    start, end = after.span(1)
    replacement = f"  ({after[1].strip()}).modify 0 (fun i => {{ i with id := i.id + 1000000 }})"
    mutant = source[:start] + replacement + source[end:]
    path = work / "WrongCanonicalization.lean"
    path.write_text(mutant)
    result = lean(path)
    output = result.stdout + result.stderr
    if result.returncode == 0:
        raise ValueError("wrong canonicalization still checks")
    lines = mutant.splitlines()
    proof = next((i + 1 for i, line in enumerate(lines)
                  if line.startswith(f"theorem erased_{target[1]} :")), None)
    next_proof = next((i + 1 for i, line in enumerate(lines)
                       if line.startswith(f"theorem preserves_{target[1]} ")), None)
    errors = [int(match[1]) for match in re.finditer(
        rf"^{re.escape(str(path))}:(\d+):\d+: error:", output, re.M)]
    if proof is None or next_proof is None or not errors or not proof <= errors[0] < next_proof:
        raise ValueError("wrong-canonicalization control failed outside its actual equality obligation\n"
                         + output)
    return True


def check_audit(report, records):
    """Bind every actual function to its two checked theorem roots, including shared Gen cases."""
    expected_modules = sorted({"Air2Lean.CanonSem", "Air2Lean.CanonCertificate",
                               *(record["module"] for record in records)})
    replay = report.get("kernel_replay", {})
    if (report.get("status") != "pass" or report.get("violations") != []
            or report.get("modules") != expected_modules or replay.get("status") != "pass"
            or replay.get("rejected") != [] or replay.get("reused") != []):
        raise ValueError("canonicalization Assurance audit did not freshly accept its complete scope")
    theorems = report.get("theorems", [])
    if any(not theorem.get("allowed") for theorem in theorems):
        raise ValueError("canonicalization Assurance audit contains a rejected theorem")
    roots = {(theorem["module"], theorem["name"]) for theorem in theorems}
    artifacts = {row["module"]: row for row in report.get("freshness", {}).get("artifacts", [])}
    for record in records:
        artifact = artifacts.get(record["module"], {})
        olean = Path(artifact.get("olean", ""))
        if not olean.is_absolute():
            olean = ROOT / olean
        if (olean.resolve() != Path(record["olean"]).resolve()
                or artifact.get("olean_sha256") != record["olean_sha256"]):
            raise ValueError(f"{record['module']}: replay did not bind the freshly compiled certificate artifact")
        expected = {(record["module"], f"{record['namespace']}.{kind}_{index}")
                    for index in range(record["count"]) for kind in ("erased", "preserves")}
        missing = expected - roots
        if missing:
            raise ValueError(f"{record['module']}: missing per-function canonicalization proofs: "
                             + ", ".join(name for _, name in sorted(missing)))


def audit_certificates(work, records):
    environment = dict(os.environ)
    environment["LEAN_PATH"] = str(work) + (os.pathsep + environment["LEAN_PATH"]
                                             if environment.get("LEAN_PATH") else "")
    environment["AIR2LEAN_REPLAY_JOBS"] = environment.get("AIR2LEAN_JOBS", "1")
    modules = sorted({"Air2Lean.CanonSem", "Air2Lean.CanonCertificate",
                      *(record["module"] for record in records)})
    path = work / "audit.json"
    arguments = [str(ROOT / "scripts/assumptions.sh"), "--no-build", "--output", str(path)]
    for module in modules:
        arguments += ["--module", module]
    start = time.monotonic()
    # No --replay-cache: every selected artifact and non-toolchain dependency is replayed now.
    result = subprocess.run(arguments, cwd=ROOT, env=environment, capture_output=True,
                            text=True, timeout=7200)
    if result.returncode != 0:
        raise ValueError("canonicalization Assurance audit failed\n" + result.stdout + result.stderr)
    check_audit(json.loads(path.read_text()), records)
    for record in records:
        with Path(record["olean"]).open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != record["olean_sha256"]:
            raise ValueError(f"{record['module']}: compiled certificate changed during its audit")
    print(f"canonicalization: fresh Assurance audit/replay {time.monotonic() - start:.3f}s", flush=True)


def certify(translator, indexed_cases):
    records = []
    mutated = False
    for index, case in indexed_cases:
        difference = translator.matches(index, case, case.path)
        if difference is not None:
            raise ValueError(f"{case.label}: generated module changed ({difference})")
        source = translator.certificate(index, case).decode()
        records.append(compile_certificate(source, translator, index, case))
        if not mutated:
            mutated = reject_mutant(source, translator.work)
    if not records:
        raise ValueError("no translation cases selected for canonicalization certification")
    if not mutated:
        raise ValueError("selected cases did not exercise the wrong-canonicalization control")
    if not any(record["changed"] for record in records):
        raise ValueError("selected cases did not change any actual debug definition ID")
    audit_certificates(translator.work, records)
    print(f"canonicalization: {len(records)} cases, {sum(r['count'] for r in records)} functions, "
          f"{sum(r['bytes'] for r in records)} certificate bytes checked; "
          "wrong canonicalization rejected", flush=True)
