"""Read the derivations of the paper's supplement off its vector drawings.

The supplement (the ancillary file `supplement.pdf` of arXiv:2109.05655)
draws every derivation as lines of circuits joined by '=' signs, each
labelled by what justifies the step (R1-R16, the lemmas L1-L19, 'Def' for
the definitions of the derived generators, or a typed relation such as
5.1).  The drawings are vector graphics: a wire is a horizontal line, H a
white box with 'H' inside, Z a black dot, CZ two dots joined by a vertical
line, X a circle with a cross, the derived generators coloured boxes with
their name.  This module turns each derivation into a list of
(label, gates, sign) where gates are in time order, in the format of
`tex.Circuit.gates()`: ('H'|'Z'|'X', w), ('CZ', top, bottom),
('CXZ', xz-wire, control), ('box', kind, index, wires).

The path of the supplement is the environment variable
REALSTAB_SUPPLEMENT, or `supplement.pdf` next to this file.
"""
import os
import re

import pymupdf

HERE = os.path.dirname(os.path.abspath(__file__))
SUPP = os.environ.get('REALSTAB_SUPPLEMENT', os.path.join(HERE, 'supplement.pdf'))


class Page:
    def __init__(self, page):
        self.h = []       # (y, x0, x1)
        self.v = []       # (x, y0, y1)
        self.diag = []    # ((x0, y0), (x1, y1))
        self.dots = []    # (x, y)
        self.rings = []   # (x, y, r)
        self.rects = []   # (x0, y0, x1, y1, fill)
        for d in page.get_drawings():
            items = d['items']
            kinds = set(it[0] for it in items)
            if kinds == {'c'}:
                pts = [p for it in items for p in it[1:]]
                cx = sum(p.x for p in pts) / len(pts)
                cy = sum(p.y for p in pts) / len(pts)
                r = max(abs(p.x - cx) for p in pts)
                if d['type'] == 'f':
                    self.dots.append((cx, cy))
                else:
                    self.rings.append((cx, cy, r))
            elif kinds == {'re'}:
                for it in items:
                    r = it[1]
                    if d.get('color') is not None and d.get('fill') != d.get('color'):
                        self.rects.append((r.x0, r.y0, r.x1, r.y1, d.get('fill')))
            elif kinds == {'l'}:
                for it in items:
                    a, b = it[1], it[2]
                    if abs(a.y - b.y) < 0.05:
                        self.h.append((a.y, min(a.x, b.x), max(a.x, b.x)))
                    elif abs(a.x - b.x) < 0.05:
                        self.v.append((a.x, min(a.y, b.y), max(a.y, b.y)))
                    else:
                        self.diag.append(((a.x, a.y), (b.x, b.y)))
        self.spans = []   # (text, x0, y0, x1, y1, font, size)
        for b in page.get_text('dict')['blocks']:
            for ln in b.get('lines', []):
                for s in ln['spans']:
                    if s['text'].strip():
                        x0, y0, x1, y1 = s['bbox']
                        self.spans.append((s['text'], x0, y0, x1, y1, s['font'], s['size']))


def inside(px, py, r, pad=0.5):
    return r[0] - pad <= px <= r[2] + pad and r[1] - pad <= py <= r[3] + pad


class Circ:
    """A drawn circuit: its wires (y-levels, top first) and x-extent."""

    def __init__(self, ys, x0, x1):
        self.ys = sorted(ys)
        self.x0, self.x1 = x0, x1
        self.items = []
        self.neg = False

    def wire(self, y):
        best = min(range(len(self.ys)), key=lambda i: abs(self.ys[i] - y))
        assert abs(self.ys[best] - y) < 2.5, (y, self.ys)
        return len(self.ys) - 1 - best      # bottom wire is 0

    def contains(self, x, y):
        return self.x0 - 7 <= x <= self.x1 + 7 and self.ys[0] - 6 <= y <= self.ys[-1] + 6

    def gates(self):
        return [it for x, it in sorted(self.items, key=lambda p: p[0])]


def circuits(pg, eqs):
    """The circuits of a page.  Every circuit but the first of a derivation
    starts just right of an '=' sign drawn at the height of its bottom wire,
    and the first ends just left of one: each wire segment is attached to
    the nearest '=' at or below it, on its left or on its right."""
    groups = {}
    for y, x0, x1 in pg.h:
        best = None
        for k, (ex, ey, lab) in enumerate(eqs):
            if ey < y - 7 or ey > y + 40:
                continue
            if ex < x0 + 1 and x0 - ex < 25:
                side = 'R'
            elif ex > x1 - 1 and ex - x1 < 25:
                side = 'L'
            else:
                continue
            if best is None or ey < best[0] - 0.5 or (abs(ey - best[0]) <= 0.5 and side == 'R'):
                best = (ey, k, side)
        if best is None:
            continue
        groups.setdefault((best[1], best[2]), []).append((y, x0, x1))
    out = {}
    for key, segs in groups.items():
        ys = sorted(y for y, _, _ in segs)
        wires = []
        for y in ys:
            if wires and y - wires[-1][-1] < 3.5:   # a double wire
                wires[-1].append(y)
            else:
                wires.append([y])
        c = Circ([sum(w) / len(w) for w in wires], min(a for _, a, _ in segs),
                 max(b for _, _, b in segs))
        out[key] = c
    return out


def letter_box(pg, r):
    """The name of a coloured box: a letter and its index."""
    txt = [s for s in pg.spans if inside((s[1] + s[3]) / 2, (s[2] + s[4]) / 2, r, 1)]
    txt.sort(key=lambda s: s[1])
    t = ''.join(s[0].strip() for s in txt)
    m = re.match(r'^([A-E])(\d)$', t)
    assert m, (t, r)
    return m.group(1), int(m.group(2))


def read_page(pg, eqs):
    cmap = circuits(pg, eqs)
    cs = list(cmap.values())

    def find(x, y, y2=None):
        """The circuit with a wire at y (and at y2) around x."""
        for c in cs:
            if c.x0 - 7 <= x <= c.x1 + 7 and any(abs(w - y) < 2.5 for w in c.ys) and                     (y2 is None or any(abs(w - y2) < 2.5 for w in c.ys)):
                return c
        for c in cs:
            if y2 is None and c.contains(x, y):
                return c
        return None

    used_dots = set()
    # vertical lines: CZ (two dots) or CXZ (dot and ring)
    for x, y0, y1 in pg.v:
        if any(abs(rx - x) < 0.6 and abs(ry - y0) <= rr + 0.3 and abs(ry - y1) <= rr + 0.3
               for rx, ry, rr in pg.rings):
            continue    # the bar of an X gate
        c = find(x, y0, y1)
        if c is None:
            continue
        ends = []
        for y in (y0, y1):
            d = [i for i, (dx, dy) in enumerate(pg.dots) if abs(dx - x) < 0.6 and abs(dy - y) < 0.6]
            rg = [i for i, (rx, ry, rr) in enumerate(pg.rings) if abs(rx - x) < 0.6 and abs(abs(ry - y) - rr) < 0.8 or (abs(rx - x) < 0.6 and abs(ry - y) < 0.6)]
            ends.append(('dot', d[0]) if d else (('ring', rg[0]) if rg else None))
        if None in ends:
            continue    # a line inside a ring, or a box edge
        wt, wb = c.wire(y0), c.wire(y1)    # y0 is above (smaller y): top wire
        for kind, i in ends:
            if kind == 'dot':
                used_dots.add(i)
        if all(k == 'dot' for k, _ in ends):
            c.items.append((x, ('CZ', wt, wb)))
        else:
            ring = [i for k, i in ends if k == 'ring'][0]
            ry = pg.rings[ring][1]
            xzw = c.wire(ry)
            ctl = wb if xzw == wt else wt
            c.items.append((x, ('CXZ', xzw, ctl)))
            pg.rings[ring] = (pg.rings[ring][0], pg.rings[ring][1], -1.0)   # used
    for i, (x, y) in enumerate(pg.dots):
        if i in used_dots:
            continue
        c = find(x, y)
        if c is not None:
            c.items.append((x, ('Z', c.wire(y))))
    for x, y, r in pg.rings:
        if r < 0:
            continue
        c = find(x, y)
        if c is None:
            continue
        inner = [dg for dg in pg.diag if abs((dg[0][0] + dg[1][0]) / 2 - x) < 1 and abs((dg[0][1] + dg[1][1]) / 2 - y) < 1]
        if inner:
            raise ValueError('a single XZ gate at %s' % ((x, y),))
        c.items.append((x, ('X', c.wire(y))))
    for x0, y0, x1, y1, fill in pg.rects:
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        c = find(cx, cy)
        if c is None:
            continue
        if fill == (1.0, 1.0, 1.0):
            txt = ''.join(s[0].strip() for s in pg.spans if inside((s[1] + s[3]) / 2, (s[2] + s[4]) / 2, (x0, y0, x1, y1)))
            if txt == 'H':
                c.items.append((cx, ('H', c.wire(cy))))
            continue
        kind, idx = letter_box(pg, (x0, y0, x1, y1))
        ws = sorted(c.wire(y) for y in c.ys if y0 < y < y1)
        assert len(ws) in (1, 2), (kind, idx, ws)
        c.items.append((cx, ('box', kind, idx, tuple(ws))))
    return cmap


def labels(pg):
    """The '=' signs with the label above them, and headings."""
    eqs = []
    for s in pg.spans:
        if s[0].strip() == '=' and s[5] == 'CMR10':
            cx = (s[1] + s[3]) / 2
            lab = [t for t in pg.spans if t is not s and t[4] <= s[2] + 6.5 and t[4] >= s[2] - 1
                   and t[1] >= s[1] - 4 and t[3] <= s[3] + 12 and t[6] < 9]
            lab.sort(key=lambda t: t[1])
            eqs.append((cx, (s[2] + s[4]) / 2, ''.join(t[0].strip() for t in lab)))
    return eqs


HEAD = re.compile(r'^(L\d+):$')


def headings(pg):
    out = []
    spans = sorted(pg.spans, key=lambda s: (round(s[2]), s[1]))
    i = 0
    while i < len(spans):
        s = spans[i]
        if s[1] < 82 and HEAD.match(s[0].strip()):
            out.append((s[2], HEAD.match(s[0].strip()).group(1)))
        elif s[1] < 82 and re.match(r'^\d+$', s[0].strip()) and s[5].startswith('NimbusRomNo9L-Regu'):
            # "3" "." "1": a typed relation
            row = [t for t in spans if abs(t[2] - s[2]) < 3.5 and t[1] < 100]
            row.sort(key=lambda t: t[1])
            t = ''.join(x[0].strip() for x in row)
            if re.match(r'^\d+\.\d+$', t):
                out.append((s[2], t))
        i += 1
    seen = set()
    res = []
    for y, n in out:
        if (round(y), n) not in seen:
            seen.add((round(y), n))
            res.append((y, n))
    return res


def scalars(pg, cs):
    """'(-1) .' written before a circuit."""
    for s in pg.spans:
        if s[0].strip() == '−':
            for c in cs:
                if c.ys[0] - 8 <= (s[2] + s[4]) / 2 <= c.ys[-1] + 8 and 0 < c.x0 - s[3] < 25:
                    c.neg = True


def derivations():
    """{name: [(label, gates, neg)]} in the supplement's order, the first
    line's label being None, and the list of names."""
    doc = pymupdf.open(SUPP)
    out = {}
    order = []
    cur = None
    for pno in range(3, doc.page_count):
        pg = Page(doc[pno])
        eqs = labels(pg)
        cmap = read_page(pg, eqs)
        scalars(pg, list(cmap.values()))
        events = [(y, 0, n) for y, n in headings(pg)]
        for k, (ex, ey, lab) in enumerate(eqs):
            events.append((ey, 1, k))
        events.sort(key=lambda e: (e[0], e[1]))
        for y, kind, o in events:
            if kind == 0:
                cur = o
                out[cur] = []
                order.append(cur)
                continue
            if cur is None:
                continue
            left = cmap.get((o, 'L'))
            right = cmap.get((o, 'R'))
            if left is not None:
                out[cur].append((None, left.gates(), left.neg))
            if right is not None:
                out[cur].append((eqs[o][2] or '=', right.gates(), right.neg))
    return out, order


def statements():
    """The lemma statements of Lemmas 1.1-1.3 (pages 1-3): {'Lk': (lhs, rhs)}
    as gate lists."""
    doc = pymupdf.open(SUPP)
    out = {}
    for pno in range(0, 3):
        pg = Page(doc[pno])
        eqs = labels(pg)
        tags = [((s[2] + s[4]) / 2, s[0].strip()[1:-1]) for s in pg.spans
                if re.match(r'^\(L\d+\)$', s[0].strip())]
        cmap = {}
        for k, (ex, ey, lab) in enumerate(eqs):
            for side in ('L', 'R'):
                segs = [(y, x0, x1) for y, x0, x1 in pg.h if ey - 40 <= y <= ey + 14 and
                        ((side == 'L' and x1 < ex + 1 and ex - x1 < 25) or
                         (side == 'R' and x0 > ex - 1 and x0 - ex < 25))]
                if not segs:
                    continue
                ys = sorted(set(round(y, 1) for y, _, _ in segs))
                clusters = []
                for y in ys:
                    if clusters and y - clusters[-1][-1] < 12.6:
                        clusters[-1].append(y)
                    else:
                        clusters.append([y])
                best = min(clusters, key=lambda c: min(abs(y - ey) for y in c))
                segs = [s for s in segs if round(s[0], 1) in best]
                wires = []
                for y in sorted(set(round(s[0], 1) for s in segs)):
                    if wires and y - wires[-1][-1] < 3.5:
                        wires[-1].append(y)
                    else:
                        wires.append([y])
                cmap[(k, side)] = Circ([sum(w) / len(w) for w in wires],
                                       min(s[1] for s in segs), max(s[2] for s in segs))
        global circuits
        saved = circuits
        circuits = lambda pg, eqs: cmap
        try:
            cm = read_page(pg, eqs)
        finally:
            circuits = saved
        for k, (ex, ey, lab) in enumerate(eqs):
            l, r = cm.get((k, 'L')), cm.get((k, 'R'))
            if l is None or r is None or not tags:
                continue
            ty, tag = min(tags, key=lambda t: abs(t[0] - ey))
            if abs(ty - ey) < 12:
                out[tag] = (l.gates(), r.gates())
    return out
