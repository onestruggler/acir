"""Generate fixed-width certificates, including Boolean parameter families.

Usage: gen_families.py D3.json OUT.lean PREVIOUS EQ ...
PREVIOUS is a comma-separated list of checked W4 modules after A.
The output is checkpointed after each successful instance. It must be
checked by Lean before its declarations are used by the interfaces.
"""
import itertools
import json
from pathlib import Path
import re
import sys
import time

import gen_b
import gen2
import model
import numpy as np
import proj
import solve2
from gen_small import dec


def main():
    source, output, previous, *numbers = sys.argv[1:]
    data = json.loads(Path(source).read_text(encoding="utf-8"))
    modules = previous.split(",")
    project = gen_b.make_project()
    if "AvailFull" in modules:
        project.ctx.avail = lambda kind, count: count + gen_b.sym.KIND_AR[kind] <= 4
        project.ctx.havail = "(havail4b ih)"
    for module in modules:
        for name, (left, right) in gen2.read_known(Path(gen2.LEAN_DIR) / (module + ".lean")).items():
            project.known(name, left, right)
    targets, endpoints = [], {}

    def save():
        needed = gen_b.used_names(project, targets)
        entries = [e for e in project.out if e.n in needed]
        header = gen_b.HEADER.replace("{title}", "checked-certificate candidates, Boolean families")
        header = header.replace("{imports}", "import QCert.RealCliffordCH.Sec8.D.W4." + modules[-1])
        body = [gen2.lean_run(e, 4, 4) for e in entries]
        body += [endpoints[n] for n in targets]
        Path(output).write_text(header + "\n".join(body) +
                               "\nend QCert.RealCliffordCH.Sec8.D.W4\n", encoding="utf-8")

    for number in map(int, numbers):
        statement = data["statements"][str(number)]
        parameters = model.params([dec(g) for d in (statement[0], statement[-1]) for g in d["gates"]])
        for values in itertools.product((False, True), repeat=len(parameters)):
            env = dict(zip(parameters, values))
            suffix = "".join("T" if v else "F" for v in values)
            name = str(number) + suffix
            if name in project.ctx.eqs:
                print(f"{name} already available", flush=True)
                continue
            started = time.monotonic()
            try:
                left, right, sequence, middle = gen_b.chain_seq(data, number, env)
                # The endpoints may already follow from a relabelled, inverse,
                # or colour-exchanged earlier result. Try that before following
                # a long diagram chain, whose intermediate forms need not be
                # the easiest route for the token engine.
                try:
                    inverse = next((n for n, (a, b, _) in project.ctx.eqs.items()
                                    if left == proj.winv(b) and right == proj.winv(a)), None)
                    if inverse is not None:
                        project.derive_inv(inverse, name)
                    else:
                        project.prove(name, [left, right], budget=50)
                except solve2.Fail:
                    # Reject a mistranscribed diagram chain before expensive
                    # proof search. This numerical check only rejects input;
                    # every accepted certificate is still checked by Lean.
                    bad = [i for i, (a, b) in enumerate(zip(sequence, sequence[1:]))
                           if not np.allclose(gen_b.tok.wmat(4, a), gen_b.tok.wmat(4, b))]
                    if bad:
                        raise solve2.Fail(f"parsed diagram chain disagrees at steps {bad}")
                    if middle is not None and middle in sequence:
                        project.prove(name + "a", sequence[:sequence.index(middle) + 1], budget=600)
                    project.prove(name, sequence, budget=600)
                endpoint = (gen_b.lean_endpoint(project, data, number, env, suffix)
                            if number in gen_b.EXPORT else "")
                if values:
                    args = " ".join("true" if v else "false" for v in values)
                    for side in "lr":
                        endpoint = re.sub(r"\b" + side + str(number) + r"\b",
                                          f"({side}{number} {args})", endpoint)
                targets.append(name)
                endpoints[name] = endpoint
                save()
                print(f"{name} OK {time.monotonic()-started:.1f}s", flush=True)
            except (solve2.Fail, AssertionError, KeyError) as error:
                print(f"{name} FAILED {time.monotonic()-started:.1f}s: {str(error)[:300]}", flush=True)
    print("Finished:", ", ".join(targets), flush=True)


if __name__ == "__main__":
    main()
