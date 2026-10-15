"""The paper's derivation chains for a fragment, run through the search.

A chain is read from the paper's LaTeX source by paper.py (or from the
cache an earlier reading wrote), its citations renamed by the fragment's
map (rename: a label to an equation, a list of them, or None for a
shortcut's definition, which cites nothing), and derived (frag.derive,
through the spec's D) under the name lname(label).  Where a step is too
long for the search, lines are inserted before a line of the paper's
(fix: (chain, line index) -> [text or (text, labels)], with the line's
own labels or their own); where a step uses more than it cites, labels
are added to it (xl: (chain, line index) -> labels).  after[chain]() is
run once the chain is derived and returns further names its label then
cites; before[chain]() derives lemmas the chain needs, just before it;
and replace[chain](transcribed chain) gives lines to derive in place of
the paper's (keeping its two ends), where a shorter route exists.
correct[(chain, line index)] replaces a line that the paper's figure
draws wrongly.

With $TCKPT a file, the state of frag is pickled there after each
chain, and with $TRESUME set a run starts after the last chain so
checkpointed: for working on a chain without rederiving the ones before
it."""
import os
import pickle

import frag
import paper
from circ import parse, ARITY

STATE = ['LIB', 'OUT', 'MIRROR', 'NATS', 'LABEL', 'CORE', 'SWAPS2', 'SWAPS3', 'NATLABELS']


def width(lines):
    """The number of wires a chain's lines use."""
    top = [w + max(ARITY[k], 1) for t, _ in lines for (k, w) in parse(t) if w is not None]
    return max(top) if top else 1


class Chains:
    def __init__(self, texfile, names, rename, cache, lname,
                 fix=None, xl=None, after=None, before=None, replace=None, correct=None):
        self.texfile, self.names, self.rename, self.cache = texfile, names, rename, cache
        self.lname = lname
        self.fix, self.xl = fix or {}, xl or {}
        self.after, self.before = after or {}, before or {}
        self.replace = replace or {}
        self.correct = correct or {}

    def fixed(self, l, ls):
        out = []
        for i, (t, labs) in enumerate(ls):
            out += [x if isinstance(x, tuple) else (x, labs) for x in self.fix.get((l, i), [])]
            out.append((t, labs if labs is None else labs + self.xl.get((l, i), [])))
        return out

    def save(self, path, last):
        with open(path, 'wb') as f:
            pickle.dump({'last': last, 'rename': self.rename,
                         **{k: getattr(frag, k) for k in STATE}}, f)

    def restore(self, path):
        # The checkpointed state, and what this run derived before the
        # chains that it does not have (lemmas added since).
        with open(path, 'rb') as f:
            st = pickle.load(f)
        for k in STATE:
            x = getattr(frag, k)
            if isinstance(x, dict):
                new = {a: b for a, b in x.items() if a not in st[k]}
                x.clear()
                x.update(st[k])
                x.update(new)
            else:
                new = [a for a in x if a not in st[k]]
                x[:] = st[k] + new
        # (an equation derived twice, by a search started within another)
        seen = set()
        frag.OUT[:] = [d for d in frag.OUT if not (d[0] in seen or seen.add(d[0]))]
        self.rename.clear()
        self.rename.update(st['rename'])
        return self.names.index(st['last']) + 1

    def run(self, D, upto=None):
        ds = paper.transcribed(self.texfile, self.names, self.cache)
        ckpt = os.environ.get('TCKPT')
        start = self.restore(ckpt) if ckpt and os.environ.get('TRESUME') else 0
        for l in self.names[start:]:
            if l in self.before:
                self.before[l]()
            ch = [(self.correct.get((l, i), t), labs) for i, (t, labs) in enumerate(ds[l])]
            ls = (self.replace[l](ch) if l in self.replace
                  else self.fixed(l, paper.lines(ch, self.rename)))
            D(self.lname(l), width(ls), ls)
            self.rename[l] = [self.lname(l)] + (self.after[l]() if l in self.after else [])
            if ckpt:
                self.save(ckpt, l)
            if l == upto:
                break
