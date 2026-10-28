"""Generate (216)--(218) independently by passing a rotation through factors.

Usage: gen_opposite.py D3.json OUT.lean

The partial rotation is CH CZ CH CZ (or its inverse). Opposite-control CH
commutes with the full rotation by (234)/(235); CZ reverses its direction.
Two reversals give the required commutation. Lean checks every certificate.
"""
import json
from pathlib import Path
import sys

import gen_b
import gen2
import proj
import solve2
import sym
import tok


def main():
    source, output = sys.argv[1:]
    data = json.loads(Path(source).read_text(encoding="utf-8"))
    project = proj.Project(4, lambda k, n: n + sym.KIND_AR[k] <= 4, "(havail4b ih)")
    for module in ("A", "B1", "Expansion", "CommuteLate"):
        for name, (left, right) in gen2.read_known(Path(gen2.LEAN_DIR) / (module + ".lean")).items():
            project.known(name, left, right)
    bases = ["234", "235", "CZreverse", "CZreverseBack"]
    for name in bases:
        project.ctx.ensure(name + "f2")
    names = bases + [name + "f2" for name in bases]
    exports = []
    for number in (216, 217, 218):
        left, right, _, _ = gen_b.chain_seq(data, number)
        full, partial = left
        inverse = proj.tinv(full)
        h = tok.P(2, [("K", 0)], [0, 2])
        c = tok.S("C", 0)
        factors = [h, c, h, c] if partial[1] == "zx" else [c, h, c, h]
        solver = project.solver(names)
        solver.start(60)
        expansion = solver.solve([partial], factors)
        steps = solve2.shift(expansion, 1)
        state = full
        for i, factor in enumerate(factors):
            next_state = next(candidate for candidate in (full, inverse)
                              if solver.c.same([state, factor], [factor, candidate]))
            solver.start(100)
            steps += solve2.shift(solver.solve([state, factor], [factor, next_state]), i)
            state = next_state
        assert state == full
        steps += solver.reverse_steps([partial], expansion)
        project.emit(str(number), left, right, steps)
        exports.append((str(number), gen_b.lean_endpoint(project, data, number)))
    needed = gen_b.used_names(project, [name for name, _ in exports])
    header = gen_b.HEADER.replace("{title}", "rotations with opposite controls")
    header = header.replace("{imports}", "import QCert.RealCliffordCH.Sec8.D.W4.CommuteLate")
    header = header.replace("gen/sec8/w4/gen_b.py", "gen/sec8/w4/gen_opposite.py")
    body = "\n".join(gen2.lean_run(e, 4, 4) for e in project.out if e.n in needed)
    body += "\n" + "\n".join(e for _, e in exports)
    Path(output).write_text(header + body + "\nend QCert.RealCliffordCH.Sec8.D.W4\n",
                            encoding="utf-8")


if __name__ == "__main__":
    main()
