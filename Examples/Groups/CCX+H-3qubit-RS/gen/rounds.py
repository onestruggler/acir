"""Derive a pool of lemmas in rounds of growing budget, in whatever order works.

The cached db keeps (u, v, steps); `order` records the order in which
lemmas were added, which is a valid dependency order for Agda.
"""
import json, os, time
from model import W, same
from search import bfs
from fast import fbfs
from closure import RLib, replay

HERE = os.path.dirname(os.path.abspath(__file__))
DB = os.path.join(HERE, 'derivations.json')


def _dec(st):
    i, n, o = st
    return (i, tuple(n) if isinstance(n, list) else n, o)


def load_db():
    if not os.path.exists(DB):
        return {}
    d = json.load(open(DB))
    return {n: (tuple(u), tuple(v), [_dec(s) for s in p]) for n, (u, v, p) in d['lemmas'].items()}


def save_db(db, order):
    enc = lambda st: [st[0], list(st[1]) if isinstance(st[1], tuple) else st[1], st[2]]
    out = {n: [list(db[n][0]), list(db[n][1]), [enc(s) for s in db[n][2]]] for n in order if n in db}
    json.dump({'order': order, 'lemmas': out}, open(DB + '.tmp', 'w'), indent=0)
    os.replace(DB + '.tmp', DB)


def ok_replay(lib, u, p, v):
    try:
        return replay(lib, u, p) == v
    except (AssertionError, KeyError, StopIteration):
        return False


class Pool:
    def __init__(self, axioms, invols):
        self.db = load_db()
        self.known = json.load(open(DB))['order'] if os.path.exists(DB) else []
        self.order = []          # (name, rotated)
        self.lib = RLib(invols)
        for k, (l, r) in axioms.items():
            self.lib.add(k, l, r, rotate=False)
        self.rotating = False
        self.fast = 0

    def save(self):
        pass

    def write(self):
        save_db(self.db, self.order)

    def start_rotating(self):
        if not self.rotating:
            for k in list(self.lib.order):
                self.lib.add_rotations(k)
            self.rotating = True

    def have(self, name):
        return name in self.lib.lemmas

    def try_one(self, name, u, v, slacks, maxnodes, verbose=True):
        u, v = W(u), W(v)
        assert same(u, v), ('unsound', name)
        hit = self.db.get(name)
        if hit is not None and hit[0] == u and hit[1] == v and ok_replay(self.lib, u, hit[2], v):
            p = hit[2]
        else:
            p = None
            t = time.time()
            for s in slacks:
                ml = max(len(u), len(v)) + s
                if self.fast and ml <= 25:
                    p = fbfs(self.lib, u, v, ml, maxnodes * self.fast)
                else:
                    p = bfs(self.lib, u, v, maxlen=ml, maxnodes=maxnodes)
                if p is not None:
                    break
            if verbose:
                print('  ', name, len(u), len(v), None if p is None else len(p),
                      round(time.time() - t, 1), flush=True)
            if p is None:
                return False
            assert replay(self.lib, u, p) == v
            self.db[name] = (u, v, p)
            self.save()
        self.lib.add(name, u, v, check=False, rotate=self.rotating)
        self.order.append(name)
        return True

    def rounds(self, targets, budgets=((2, 4), 50_000), more=(((2, 4, 6), 300_000), ((2, 4, 6, 8), 2_000_000))):
        pending = [t for t in targets if not self.have(t[0])]
        # replay known lemmas in the order in which they were found
        rank = {n: i for i, n in enumerate(self.known)}
        pending.sort(key=lambda t: rank.get(t[0], len(rank)))
        for slacks, maxnodes in (budgets,) + tuple(more):
            progress = True
            while progress and pending:
                progress = False
                rest = []
                for (name, u, v) in pending:
                    if self.try_one(name, u, v, slacks, maxnodes):
                        progress = True
                    else:
                        rest.append((name, u, v))
                pending = rest
            if not pending:
                break
        return pending
