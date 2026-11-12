#!/usr/bin/env python3
"""Measure a fresh project check in an isolated Linux temporary directory.

Run with WSL Python 3 from any directory. Agda 2.8.0 and registered stdlib
2.4 are required. Only project interfaces are cold; installed stdlib
interfaces are retained. No interfaces in the original checkout are changed.
If the bounded heap is exhausted, check the interrupted module separately
and rerun the root, as documented in AGENTS.md. Record every attempt.
"""

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "vqupit" / "notes" / "validation"


def run_check(scratch, target, number):
    log = OUT / f"check-{number}.log"
    timing = OUT / f"check-{number}-time.log"
    command = ["agda", "+RTS", "-M5G", "-c", "-RTS", target]
    start = time.monotonic()
    with log.open("w", encoding="utf-8") as stream:
        result = subprocess.run(
            ["/usr/bin/time", "-v", "-o", str(timing), *command],
            cwd=scratch, stdout=stream, stderr=subprocess.STDOUT,
            check=False,
        )
    elapsed = time.monotonic() - start
    stats = timing.read_text(encoding="utf-8")
    peak = re.search(r"Maximum resident set size \(kbytes\): (\d+)", stats)
    return {
        "target": target, "exit_code": result.returncode,
        "elapsed_seconds": round(elapsed, 3),
        "peak_rss_kib": int(peak[1]) if peak else None,
    }, log.read_text(encoding="utf-8")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    sources = sorted(p for p in ROOT.rglob("*.agda")
                     if not any(x.startswith(".") or x in {"_build", "MAlonzo"}
                                for x in p.relative_to(ROOT).parts))
    sources += [ROOT / "qupit.agda-lib"]
    digest = hashlib.sha256()
    scratch = Path(tempfile.mkdtemp(prefix="vqupit-check-"))
    for source in sources:
        relative = source.relative_to(ROOT)
        data = source.read_bytes()
        digest.update(relative.as_posix().encode() + b"\0" + data + b"\0")
        destination = scratch / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    cpu = next((line.split(":", 1)[1].strip()
                for line in Path("/proc/cpuinfo").read_text().splitlines()
                if line.startswith("model name")), "unknown")
    report = {
        "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source_sha256": digest.hexdigest(),
        "agda_files": len(sources) - 1,
        "agda_version": subprocess.check_output(
            ["agda", "--version"], text=True).splitlines()[0],
        "standard_library": "2.4 (registered installation; interfaces retained)",
        "project_interfaces": "absent at start; isolated copy on Linux filesystem",
        "kernel": platform.release(), "cpu": cpu,
        "logical_cpus_visible": os.cpu_count(),
        "memory_visible_kib": int(re.search(
            r"MemTotal:\s+(\d+)", Path("/proc/meminfo").read_text())[1]),
        "heap_limit": "5 GiB, compacting GC", "attempts": [],
    }
    try:
        for recovery in range(4):
            attempt, output = run_check(scratch, "MainTheorems.agda",
                                        len(report["attempts"]) + 1)
            report["attempts"].append(attempt)
            print(json.dumps(attempt), flush=True)
            if attempt["exit_code"] == 0:
                break
            if recovery == 3 or not any(x in output for x in
                                       ("Heap exhausted", "heap exhausted")):
                break
            checked = re.findall(r"Checking [^\n]+ \(([^\n]+\.agda)\)", output)
            if not checked:
                break
            stopped = Path(checked[-1]).resolve()
            if not stopped.is_relative_to(scratch.resolve()):
                break
            target = stopped.relative_to(scratch).as_posix()
            attempt, output = run_check(scratch, target,
                                        len(report["attempts"]) + 1)
            report["attempts"].append(attempt)
            print(json.dumps(attempt), flush=True)
            if attempt["exit_code"] != 0:
                break
        report["success"] = (report["attempts"][-1]["target"] == "MainTheorems.agda"
                             and report["attempts"][-1]["exit_code"] == 0)
        report["total_elapsed_seconds"] = round(sum(
            a["elapsed_seconds"] for a in report["attempts"]), 3)
        report["max_peak_rss_kib"] = max(
            a["peak_rss_kib"] or 0 for a in report["attempts"])
        (OUT / "fresh-check.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(report), flush=True)
    finally:
        shutil.rmtree(scratch)
    raise SystemExit(0 if report["success"] else 1)


if __name__ == "__main__":
    main()
