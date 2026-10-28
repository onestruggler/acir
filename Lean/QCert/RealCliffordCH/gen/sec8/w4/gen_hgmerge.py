"""Generate the four-wire Hadamard merge certificate.

Usage: gen_hgmerge.py OUT.lean
Uses the previously checked A, B1, B2, B3, B4 and Inverse modules.
"""
from pathlib import Path
import sys

import gen_b
import tok


def main():
    project = gen_b.make_project()
    for module in ("B1", "B2", "B3", "B4", "Inverse"):
        for name, (left, right) in gen_b.gen2.read_known(
                Path(gen_b.gen2.LEAN_DIR) / (module + ".lean")).items():
            project.known(name, left, right)
    black = tok.G("hg", [0, 1], [(3, True), (2, True)])
    white = tok.G("hg", [0, 1], [(3, True), (2, False)])
    expanded = project.define(black, "HgDef")
    coloured = project.derive_flip("HgDef", 2, "HgDefWhite")
    pp, box, _ = expanded.R
    _, white_box, _ = coloured.R
    cz = ("p", 2, (("C", 0),), (1, 3))
    target = [tok.G("hg", [0, 1], [(3, True)])]
    project.prove("171a", [[black, white], expanded.R + coloured.R,
                           [pp, box, white_box, pp], [pp, cz, pp], target], budget=60)
    needed = gen_b.used_names(project, ["171a"])
    header = gen_b.HEADER.replace("{title}", "Hadamard merge certificate")
    header = header.replace("{imports}", "import QCert.RealCliffordCH.Sec8.D.W4.Inverse")
    header = header.replace("gen/sec8/w4/gen_b.py", "gen/sec8/w4/gen_hgmerge.py")
    body = "\n".join(gen_b.gen2.lean_run(e, 4, 4) for e in project.out if e.n in needed)
    Path(sys.argv[1]).write_text(header + body +
                                "\nend QCert.RealCliffordCH.Sec8.D.W4\n", encoding="utf-8")


if __name__ == "__main__":
    main()
