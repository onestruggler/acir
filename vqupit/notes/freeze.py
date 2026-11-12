#!/usr/bin/env python3
"""Freeze the working sources and paper into a PRIVATE, hashed snapshot.

Run under WSL from any directory. Includes tracked files and nonignored
new files, plus the validation logs. Excludes Git history and interfaces.
The archive is deliberately NOT an anonymous submission supplement.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "vqupit/notes/validation/freeze-manifest.json"


def main():
    gitdir = ROOT / ".git"
    if gitdir.is_file():
        pointer = gitdir.read_text().strip().removeprefix("gitdir: ")
        if re.match(r"^[A-Za-z]:/", pointer):
            pointer = "/mnt/" + pointer[0].lower() + pointer[2:]
        gitdir = (ROOT / pointer).resolve()
    listed = subprocess.check_output([
        "git", f"--git-dir={gitdir}", f"--work-tree={ROOT}",
        "ls-files", "-z", "--cached", "--others", "--exclude-standard",
    ]).decode().split("\0")
    paths = {ROOT / name for name in listed if name}
    paths.update((ROOT / "vqupit/notes/validation").glob("*.log"))
    paths = sorted(p for p in paths if p.is_file() and p != REPORT)
    now = datetime.now(timezone.utc)
    archive = ROOT.parent / (ROOT.name + "-private-" +
                             now.strftime("%Y%m%dT%H%M%SZ") + ".zip")
    files = {}
    with zipfile.ZipFile(archive, "x", zipfile.ZIP_DEFLATED) as bundle:
        for path in paths:
            data = path.read_bytes()
            name = path.relative_to(ROOT).as_posix()
            files[name] = {"bytes": len(data),
                           "sha256": hashlib.sha256(data).hexdigest()}
            bundle.writestr(name, data)
        manifest = {
            "created_utc": now.isoformat(),
            "kind": "private working-tree snapshot; not anonymized",
            "git_head": subprocess.check_output([
                "git", f"--git-dir={gitdir}", "rev-parse", "HEAD"
            ], text=True).strip(),
            "working_tree_changes_included": True,
            "files": files,
        }
        bundle.writestr("SNAPSHOT-MANIFEST.json",
                        json.dumps(manifest, indent=2) + "\n")
        bundle.writestr("PRIVATE-SNAPSHOT.txt",
                        "PRIVATE snapshot. Contains author identities and "
                        "conflict notes. Do not upload as anonymous material.\n")
    with zipfile.ZipFile(archive) as bundle:
        assert bundle.testzip() is None
        for name, info in files.items():
            assert hashlib.sha256(bundle.read(name)).hexdigest() == info["sha256"]
    manifest["archive"] = str(archive)
    manifest["archive_sha256"] = hashlib.sha256(archive.read_bytes()).hexdigest()
    REPORT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"archive": str(archive), "files": len(files),
                      "sha256": manifest["archive_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
