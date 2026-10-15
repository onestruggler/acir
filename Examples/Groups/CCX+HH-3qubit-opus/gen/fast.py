"""Bridge to the C++ bidirectional search (fbfs)."""
import os, subprocess
from model import W, GATES

LETTERS = sorted(GATES) + ['H2']
CODE = {l: i for i, l in enumerate(LETTERS)}


def export(lib):
    rules = []
    for ents in lib.by_first.values():
        for (name, o, p, q) in ents:
            rules.append((p, q, name, o))
    return rules


def fbfs(lib, u, v, maxlen, maxnodes=50_000_000, rules=None):
    u, v = W(u), W(v)
    if rules is None:
        rules = export(lib)
    out = [str(len(rules))]
    for (p, q, _, _) in rules:
        out.append(' '.join([str(len(p))] + [str(CODE[x]) for x in p] + [str(len(q))] + [str(CODE[x]) for x in q]))
    out.append(' '.join([str(len(u))] + [str(CODE[x]) for x in u]))
    out.append(' '.join([str(len(v))] + [str(CODE[x]) for x in v]))
    out.append('%d %d' % (min(maxlen, 25), maxnodes))
    r = subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fbfs')], input='\n'.join(out) + '\n', capture_output=True, text=True)
    lines = r.stdout.split('\n')
    if not lines[0].startswith('FOUND'):
        return None
    steps = []
    for L in lines[1:1 + int(lines[0].split()[1])]:
        pos, rid, d = map(int, L.split())
        p, q, name, o = rules[rid]
        steps.append((pos, name, o if d == 1 else -o))
    return steps
