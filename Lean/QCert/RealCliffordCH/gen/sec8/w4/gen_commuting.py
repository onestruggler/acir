"""Generate four-wire certificates by expanding commuting gate factors.

Usage: gen_commuting.py D3.json OUT.lean

Numerical comparisons guide the search only. Each output derivation is a
WEng certificate whose steps and table entries must be checked by Lean.
"""
import itertools
import json
from pathlib import Path
import re
import sys

import gen_b
import gen2
import model
import proj
import solve2
import sym
import tok
import letters as LT
from gen_small import dec


def commuting_factors(solver, x, y, depth=0):
    """Commute two gates through factors that separately commute."""
    if depth > 6:
        raise solve2.Fail("factor depth")
    direct = solver.commute(x, y)
    if direct is not None:
        return direct
    if not solver.c.same([x, y], [y, x]):
        raise solve2.Fail("noncommuting factors")
    for side, gate in ((1, y), (0, x)):
        if gate[0] != "g":
            continue
        try:
            expansion, factors = solver.unfold(gate)
            if factors == [gate]:
                continue
            if side == 1:
                steps = solve2.shift(expansion, 1)
                for i, factor in enumerate(factors):
                    steps += solve2.shift(commuting_factors(solver, x, factor, depth + 1), i)
                steps += solver.reverse_steps([gate], expansion)
            else:
                steps = list(expansion)
                for i in range(len(factors) - 1, -1, -1):
                    steps += solve2.shift(commuting_factors(solver, factors[i], y, depth + 1), i)
                steps += solve2.shift(solver.reverse_steps([gate], expansion), 1)
            assert solver.verify([x, y], [y, x], steps)[0]
            return steps
        except solve2.Fail:
            continue
    raise solve2.Fail("no commuting expansion")


def hadamard_reverse(project, left, right):
    """(236): split H into black/white controlled H; use (232)."""
    solver = project.solver([])
    solver.start(100)
    rotation = left[1]
    inverse = right[0]
    control = tok.S("K", 0)
    white = tok.P(2, [("H", 1), ("Z", 1), ("H", 1), ("K", 0),
                      ("H", 1), ("Z", 1), ("H", 1)], [0, 1])
    expansion, factors = solver.unfold(rotation)
    inv_expansion, inv_factors = solver.unfold(inverse)
    assert len(factors) == 4 and factors[0] == factors[2] == control
    assert inv_factors == factors[1:] + [control]
    steps = solve2.shift(expansion, 1)
    steps += [("sem", 0, 2, (), 2), ("sem", 3, 0, (control, control), 2)]
    steps += solver.reverse_steps([inverse], inv_expansion)
    project.emit("CHreverse", [control, rotation], [inverse, control], steps)
    words = [left, [control, white, rotation], [control, rotation, white],
             [inverse, control, white], right]
    project.prove("236", words, budget=60, names=["232", "CHreverse"])


def permuted_commuting(project, left, right):
    """Choose the first control for Definition 2.4 by a wire permutation."""
    solver = project.solver(["154", "155", "156", "159", "160", "163", "164"])
    solver.start(100)
    for swaps in project.ctx.perms.values():
        try:
            front, x, y = solver.wrap(*left, swaps)
            middle = commuting_factors(solver, x, y)
            back, yy, xx = solver.wrap(*right, swaps)
            assert [yy, xx] == [y, x]
            steps = front + solve2.shift(middle, len(swaps)) + solver.reverse_steps(right, back)
            assert solver.verify(left, right, steps)[0]
            return steps
        except solve2.Fail:
            continue
    raise solve2.Fail("no commuting placement")


def pauli_reverse(project, left, right):
    """(237): split Z into black/white CZ; use (231), (212), (213)."""
    rotation, inverse = left[1], right[0]
    control = tok.P(2, [("C", 0)], [0, 3])
    white = tok.P(2, [("H", 1), ("Z", 1), ("H", 1), ("C", 0),
                      ("H", 1), ("Z", 1), ("H", 1)], [0, 3])
    hg = tok.G("hg", [3, 0], [(1, True), (2, True)])
    project.prove("CZreverse", [[control, rotation], [control, control, hg, control, hg],
                               [hg, control, hg], [hg, control, hg, control, control],
                               [inverse, control]], budget=60, names=["212", "213"])
    project.prove("237", [left, [control, white, rotation], [control, rotation, white],
                           [inverse, control, white], right],
                  budget=60, names=["231", "CZreverse"])


def opposite_rotation(project, left, right, name):
    """(239): pass the full rotation through the factors of the partial one."""
    zx = left[0]
    xz = tok.G("xz", [0], [(1, True), (2, True), (3, True)])
    c = tok.P(2, [("C", 0)], [0, 3])
    z = tok.S("Z", 0)
    if "CZreverseBack" not in project.ctx.eqs:
        project.prove("CZreverseBack", [[c, zx], [c, zx, c, c], [c, c, xz, c], [xz, c]],
                      budget=30, names=["CZreverse"])
        project.prove("ZreverseBack", [[z, zx], [z, zx, z, z], [z, z, xz, z], [xz, z]],
                      budget=30, names=["237"])
    solver = project.solver(["232", "233", "CZreverse", "CZreverseBack", "237", "ZreverseBack"])
    solver.start(100)
    white_word = [("H", 1), ("Z", 1), ("H", 1)]
    ch = tok.P(2, white_word + [("K", 0)] + white_word, [0, 2])
    cz = c if dict(left[1][3])[3] else tok.P(2, white_word + [("C", 0)] + white_word, [0, 3])
    factors = [ch, cz, ch, cz] if left[1][1] == "zx" else [cz, ch, cz, ch]
    expansion = solver.solve([left[1]], factors)
    # A white-controlled CZ is Z on the target times the black-controlled CZ.
    i = 0
    while i < len(factors):
        factor = factors[i]
        if factor[0] == "p" and solver.c.same([factor], [c, z]):
            solver.start(30)
            local = solve2.shift(solver.solve([factor], [c, z]), i)
            expansion += local
            factors = solver.run_words(factors, local)
            i += 2
        else:
            i += 1
    steps = solve2.shift(expansion, 1)
    state = zx
    for i, factor in enumerate(factors):
        next_state = next((candidate for candidate in (zx, xz)
                           if solver.c.same([state, factor], [factor, candidate])), None)
        if next_state is None:
            raise solve2.Fail(f"rotation factor {factor}")
        solver.start(60)
        steps += solve2.shift(solver.solve([state, factor], [factor, next_state]), i)
        state = next_state
    assert state == zx
    steps += solver.reverse_steps([left[1]], expansion)
    project.emit(name, left, right, steps)


def main():
    source, output = sys.argv[1:]
    data = json.loads(Path(source).read_text(encoding="utf-8"))
    project = proj.Project(4, lambda kind, count: count + sym.KIND_AR[kind] <= 4,
                           "(havail4b ih)")
    for module in ("A", "B1", "Expansion"):
        for name, (left, right) in gen2.read_known(Path(gen2.LEAN_DIR) / (module + ".lean")).items():
            project.known(name, left, right)
    solver = project.solver([])
    exports = []
    for number in (229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 246):
        statement = data["statements"][str(number)]
        parameters = model.params([dec(g) for d in (statement[0], statement[-1]) for g in d["gates"]])
        for values in itertools.product((False, True), repeat=len(parameters)):
            env = dict(zip(parameters, values))
            suffix = "".join("T" if v else "F" for v in values)
            name = str(number) + suffix
            left, right, _, _ = gen_b.chain_seq(data, number, env)
            if number == 236:
                hadamard_reverse(project, left, right)
            elif number == 237:
                pauli_reverse(project, left, right)
            elif number == 238:
                h, z = tok.S("H", 0), tok.S("Z", 0)
                project.prove(name, [left, [h, z, h, left[1]], [h, z, right[0], h],
                                     [h, left[1], z, h], [right[0], h, z, h], right],
                              budget=60, names=["236", "237"])
            elif number == 239:
                opposite_rotation(project, left, right, name)
            elif number == 246:
                p12 = tok.P(2, LT.PP0, [1, 2])
                p02 = tok.P(2, LT.PP0, [0, 2])
                p13 = tok.P(2, LT.PP0, [1, 3])
                project.prove(name, [left, [left[0], p12, p12, left[1]], [p02, p13], right],
                              budget=60, names=[])
            elif number in (231, 234, 235):
                project.emit(name, left, right, permuted_commuting(project, left, right))
            else:
                assert len(left) == 2 and left == right[::-1]
                solver.start(100)
                project.emit(name, left, right, commuting_factors(solver, *left))
            endpoint = gen_b.lean_endpoint(project, data, number, env, suffix)
            if values:
                arguments = " ".join("true" if v else "false" for v in values)
                for side in "lr":
                    endpoint = re.sub(r"\b" + side + str(number) + r"\b",
                                      f"({side}{number} {arguments})", endpoint)
            exports.append((name, endpoint))
            needed = gen_b.used_names(project, [name for name, _ in exports])
            header = gen_b.HEADER.replace("{title}", "commuting factors")
            header = header.replace("{imports}", "import QCert.RealCliffordCH.Sec8.D.W4.Late")
            header = header.replace("gen/sec8/w4/gen_b.py", "gen/sec8/w4/gen_commuting.py")
            body = "\n".join(gen2.lean_run(e, 4, 4) for e in project.out if e.n in needed)
            body += "\n" + "\n".join(e for _, e in exports)
            Path(output).write_text(header + body +
                                    "\nend QCert.RealCliffordCH.Sec8.D.W4\n", encoding="utf-8")
            print(name, "OK", flush=True)


if __name__ == "__main__":
    main()
