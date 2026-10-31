"""Python front end to tc.cpp."""
import subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, 'tc_bin')

def build():
    src = os.path.join(HERE, 'tc.cpp')
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(src):
        subprocess.check_call(['g++', '-O2', '-std=c++17', '-o', BIN, src])

def index(letters, relators, subgroup=(), maxcos=20000000):
    """relators: list of (lhs, rhs) words of letter names (rhs may be empty)."""
    build()
    idx = {a: i for i, a in enumerate(letters)}
    def enc(w, invert=False):
        out = [2 * idx[a] for a in w]
        if invert:
            out = [x ^ 1 for x in reversed(out)]
        return out
    rels = [enc(l) + enc(r, True) for l, r in relators]
    rels = [r for r in rels if r]
    subs = [enc(h) for h in subgroup]
    lines = ['%d %d %d %d' % (len(letters), len(rels), len(subs), maxcos)]
    for r in rels + subs:
        lines.append(' '.join(map(str, [len(r)] + r)))
    out = subprocess.run([BIN], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.strip()
    return None if out == 'OVERFLOW' else int(out)
