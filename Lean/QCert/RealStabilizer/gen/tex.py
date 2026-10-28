"""Read the circuits of Makary, Ross and Selinger's paper off its TeX source.

The figures of arXiv:2109.05655 are TikZ pictures (`qcircuit`
environments) drawn with the macros of `realstab.sty`: wires
(`\\blackgrid`, `\\greengrid` simple type, `\\redgrid` double type), gates
(`\\HGATE`, `\\ZGATE`, `\\XGATE`, `\\CZGATE`, `\\XZCGATE`) and the derived
generators (`\\AONE` ... `\\EONE`, boxes on one or two wires).  A circuit
is read as its gates in the order of their x-coordinates; a wire at height
y is our wire round(y / 1.6), so the bottom wire is wire 0.

The path of `realstab.tex` is the environment variable REALSTAB_TEX, or
`realstab.tex` next to this file.
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
TEX = os.environ.get('REALSTAB_TEX', os.path.join(HERE, 'realstab.tex'))
TEX_SHA256 = None   # filled in by generate.py's check

BOXES = {'AONE': ('A', 1, 1), 'ATWO': ('A', 2, 1), 'ATHREE': ('A', 3, 1),
         'BONE': ('B', 1, 2), 'BTWO': ('B', 2, 2), 'BTHREE': ('B', 3, 2), 'BFOUR': ('B', 4, 2),
         'BFIVE': ('B', 5, 2), 'BSIX': ('B', 6, 2), 'BSEV': ('B', 7, 2), 'BEIG': ('B', 8, 2),
         'CONE': ('C', 1, 1), 'CTWO': ('C', 2, 1),
         'DONE': ('D', 1, 2), 'DTWO': ('D', 2, 2), 'DTHREE': ('D', 3, 2), 'DFOUR': ('D', 4, 2),
         'EONE': ('E', 1, 1), 'ETWO': ('E', 2, 1)}
GATES1 = {'HGATE': 'H', 'ZGATE': 'Z', 'XGATE': 'X'}
GATES2 = {'CZGATE': 'CZ', 'XZCGATE': 'CXZ'}
GRIDS = {'blackgrid': None, 'greengrid': 's', 'redgrid': 'd'}


class OddWire(Exception):
    pass


def wire(y):
    w = round(float(y) / 1.6)
    if abs(float(y) - 1.6 * w) > 1e-6:
        raise OddWire(y)
    return w


def args(s, i, k):
    """k brace groups starting at s[i] (after optional spaces)."""
    out = []
    for _ in range(k):
        while s[i] in ' \t\n':
            i += 1
        assert s[i] == '{', s[i:i + 30]
        depth = 0
        j = i
        while True:
            if s[j] == '{':
                depth += 1
            elif s[j] == '}':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        out.append(s[i + 1:j])
        i = j + 1
    return out, i


class Circuit:
    """Gates ('H'|'Z'|'X', w), ('CZ'|'CXZ', top, bottom), boxes
    ('box', kind, index, wires), in time order; wire types; labels."""

    def __init__(self, body):
        self.items = []       # (x, item)
        self.grids = []       # (type, x0, x1, wire)
        self.labels = []      # (x, wire, text)
        for m in re.finditer(r'\\([A-Za-z]+)', body):
            name = m.group(1)
            i = m.end()
            if name in GRIDS:
                (x0, x1, ys), _ = args(body, i, 3)
                for y in ys.split(','):
                    self.grids.append((GRIDS[name], float(x0), float(x1), wire(y)))
            elif name in GATES1:
                (x, y), _ = args(body, i, 2)
                self.items.append((float(x), (GATES1[name], wire(y))))
            elif name in GATES2:
                (x, y1, y2), _ = args(body, i, 3)
                self.items.append((float(x), (GATES2[name], wire(y1), wire(y2))))
            elif name in BOXES:
                kind, idx, k = BOXES[name]
                if k == 1:
                    (x, y), _ = args(body, i, 2)
                    ws = (wire(y),)
                else:
                    (x, y1, y2), _ = args(body, i, 3)
                    ws = (wire(y2), wire(y1))   # bottom, top
                    assert ws[1] == ws[0] + 1
                self.items.append((float(x), ('box', kind, idx, ws)))
            elif name == 'LABEL':
                (x, y, t), _ = args(body, i, 3)
                self.labels.append((float(x), float(y), t))
        self.items.sort(key=lambda p: p[0])
        self.nw = 1 + max([g[3] for g in self.grids] + [0])

    def gates(self):
        return [it for x, it in self.items]

    def gaps(self):
        """x-coordinates where no wire is drawn (a circuit drawn as l = r)."""
        if not self.grids:
            return []
        lo = min(g[1] for g in self.grids)
        hi = max(g[2] for g in self.grids)
        iv = sorted((g[1], g[2]) for g in self.grids)
        out = []
        reach = iv[0][1]
        for a, b in iv[1:]:
            if a > reach + 1e-9:
                out.append((reach + a) / 2)
            reach = max(reach, b)
        return [x for x in out if lo < x < hi]

    def split_at(self, x0):
        """The parts left and right of x0 (a circuit drawn as 'l = r')."""
        parts = []
        for keep in (lambda x: x < x0, lambda x: x > x0):
            c = Circuit('')
            c.items = [(x, it) for x, it in self.items if keep(x)]
            c.grids = [g for g in self.grids if keep((g[1] + g[2]) / 2)]
            c.labels = [lb for lb in self.labels if keep(lb[0]) and '=' not in lb[2]]
            c.nw = self.nw
            parts.append(c)
        return parts

    def type_at(self, w, x, side):
        """The type of wire w just left (side -1) or right (+1) of x."""
        best = None
        for t, x0, x1, ww in self.grids:
            if ww != w:
                continue
            p = x + side * 0.3
            if x0 - 1e-9 <= p <= x1 + 1e-9:
                if t is not None:
                    best = t
        return best

    def box_types(self):
        """For each box: (kind, index, wires, input types, output types)."""
        out = []
        for x, it in self.items:
            if it[0] == 'box':
                ins = tuple(self.type_at(w, x, -1) for w in it[3])
                outs = tuple(self.type_at(w, x, +1) for w in it[3])
                out.append((it[1], it[2], it[3], ins, outs))
        return out


def blocks(text):
    """The qcircuit environments of text, with the text between them."""
    out = []
    pos = 0
    for m in re.finditer(r'\\begin\{qcircuit\}(\[[^\]]*\])?(.*?)\\end\{qcircuit\}', text, re.S):
        try:
            c = Circuit(m.group(2))
        except OddWire:      # an illustration off the wire grid
            c = Circuit('')
            c.odd = True
        out.append((text[pos:m.start()], c))
        pos = m.end()
    out.append((text[pos:], None))
    return out


def strip_comments(s):
    return re.sub(r'(?<!\\)%.*', '', s)


def equations(text):
    """Chains c0 = c1 = ... of circuits, each with a sign: -1 when the side
    is written '(-1) \\cdot c' or carries a label '\\cdot(-1)'."""
    bl = blocks(strip_comments(text))
    chains = []
    cur = None
    for i, (before, c) in enumerate(bl):
        if c is None:
            break
        eqlab = [lb[0] for lb in c.labels if lb[2].strip() == '$=$'] or c.gaps()
        if eqlab:
            if cur is not None:
                chains.append(cur)
                cur = None
            l, r = c.split_at(eqlab[0])
            chains.append([(l, False), (r, False)])
            continue
        before = re.sub(r'[A-Za-z]+=[0-9.]+[a-z]*', '', before)
        eq = '=' in before
        neg = any('(-1)' in t for _, _, t in c.labels) or             (eq and '(-1)' in before[before.rindex('='):])
        if cur is not None and eq:
            cur.append((c, neg))
        else:
            if cur is not None:
                chains.append(cur)
            cur = [(c, neg)]
    if cur is not None:
        chains.append(cur)
    return chains


def source():
    return open(TEX, encoding='utf-8').read()


def section(src, start, end):
    i = src.index(start)
    j = src.index(end, i)
    return src[i:j]
