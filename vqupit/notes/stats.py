#!/usr/bin/env python3
"""Count retained Agda sources, excluding excerpts and external dependencies.

Run from any directory with Python 3. Counts include comments and blank
lines, using newline counts as wc -l does. No external packages required.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COMPONENTS = [
    ("Framework", ("Word/", "Presentation/", "Circuit/",
                   "Normalization/", "ForStdlib/")),
    ("Symplectic", ("Examples/Groups/Symplectic/",)),
    ("Projective Pauli", ("Examples/Groups/ProjectivePauli/",)),
    ("Projective Clifford", ("Examples/Groups/ProjectiveClifford/",
                            "Examples/Construct/SemiDirectProduct/")),
    ("Exact extension", ("Examples/Groups/Qupit-Clifford/",)),
    ("Figure 1 with scalars", ("Examples/Groups/Clifford+MinusOne/",)),
    ("Supporting examples", ("Examples/Groups/Symmetric/",
                             "Examples/Groups/Cyclic/",
                             "Examples/Groups/Trivial/")),
]


def main():
    sources = {p.relative_to(ROOT).as_posix(): p.read_bytes().count(b"\n")
               for p in ROOT.rglob("*.agda")
               if not any(part.startswith(".") or part == "_build"
                          for part in p.relative_to(ROOT).parts)}
    used = set()
    for name, prefixes in COMPONENTS:
        paths = {p for p in sources if p.startswith(prefixes)}
        assert not paths & used, name
        used |= paths
        print(f"{name:24} {len(paths):4} {sum(sources[p] for p in paths):7}")
    remaining = sources.keys() - used
    print(f"{'Index and notation':24} {len(remaining):4} "
          f"{sum(sources[p] for p in remaining):7}")
    print(f"{'Total':24} {len(sources):4} {sum(sources.values()):7}")
    if remaining != {"MainTheorems.agda", "Notations.agda"}:
        print("Unclassified files:", *sorted(remaining), sep="\n")


if __name__ == "__main__":
    main()
