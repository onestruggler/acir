"""Driver for the C bidirectional search (bfs.c, run in WSL)."""
import subprocess

from paths import bfs_cmd


def rot_parts(rho, rot, cut, rv):
    base = tuple(reversed(rho)) if rv else tuple(rho)
    rr = base[rot:] + base[:rot]
    u = rr[:cut]
    v = tuple(reversed(rr[cut:]))
    return u, v


class Relators:
    """Relators with stable ids; a step is (pos, rid, rot, cut, rv)."""
    def __init__(self):
        self.rels = []
        self.names = []

    def add(self, rho, name):
        self.rels.append(tuple(rho))
        self.names.append(name)
        return len(self.rels) - 1

    def apply(self, w, st):
        i, rid, rot, cut, rv = st
        u, v = rot_parts(self.rels[rid], rot, cut, rv)
        w = tuple(w)
        assert w[i:i + len(u)] == u, (w, st, u)
        return w[:i] + v + w[i + len(u):]

    def inverse(self, st):
        i, rid, rot, cut, rv = st
        rho = self.rels[rid]
        n = len(rho)
        u, v = rot_parts(rho, rot, cut, rv)
        target = v + tuple(reversed(u))
        base2 = tuple(rho) if rv else tuple(reversed(rho))   # reversed of base
        for rot2 in range(n):
            if base2[rot2:] + base2[:rot2] == target:
                return (i, rid, rot2, len(v), not rv)
        raise AssertionError("no inverse")

    def replay(self, w, steps):
        w = tuple(w)
        for st in steps:
            w = self.apply(w, st)
        return w


class CSearch:
    def __init__(self, A, maxlhs, rels: Relators, first=False):
        self.rels = rels
        self.p = subprocess.Popen(bfs_cmd("bfs") + (["--first"] if first else []), stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, bufsize=1)
        out = [f"{A} {maxlhs} {len(rels.rels)}"]
        for r in rels.rels:
            out.append(" ".join(map(str, [len(r)] + list(r))))
        self.p.stdin.write("\n".join(out) + "\n")
        self.p.stdin.flush()

    def query(self, a, b, maxlen, limit, add=False, name=None, grow=100):
        a = tuple(a); b = tuple(b)
        line = f"{1 if add else 0} {maxlen} {limit} {grow} {len(a)} {' '.join(map(str, a))} {len(b)} {' '.join(map(str, b))}\n"
        self.p.stdin.write(line)
        self.p.stdin.flush()
        head = self.p.stdout.readline().split()
        if not head:
            raise RuntimeError("search process died")
        if head[0] == "FAIL":
            self.last_fail = head
            return None
        k = int(head[1])
        steps = []
        for _ in range(k):
            parts = self.p.stdout.readline().split()
            if parts[0] == "I":
                st = tuple(int(x) for x in parts[1:])
                st = (st[0], st[1], st[2], st[3], bool(st[4]))
                steps.append(self.rels.inverse(st))
            else:
                st = tuple(int(x) for x in parts)
                steps.append((st[0], st[1], st[2], st[3], bool(st[4])))
        assert self.rels.replay(a, steps) == b, "replay failed"
        if add:
            self.rels.add(a + tuple(reversed(b)), name or "q")
        return steps

    def close(self):
        self.p.stdin.close()
        self.p.wait()
