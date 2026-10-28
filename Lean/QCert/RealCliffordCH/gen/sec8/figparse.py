"""Parse the circuit diagrams of arXiv:2602.06644 (Clement, Real-Clifford+CH) from the PDF.

The figures are vector graphics: wires are horizontal lines, gates are small filled
circles (black / white dots), stroked circles (the X gate, drawn as a circled plus), white
circles with a label (a control of parametric colour, e.g. beta), white rectangles with a
label (H, ZX, XZ, P, ...), small dashed squares (the box wire of a multi-controlled gate),
pairs of crossing Bezier curves (swaps), solid vertical lines (controls) and dashed
vertical lines (the link of the two halves of P (x) P).

    page_items(page)           -> the primitive items of a page
    rows(page)                 -> the '=' signs with their citations and the diagrams
    parse_page(pdf, pageno)    -> list of Row(y, items) where items are, left to right,
                                  ('diag', Diagram) | ('eq', [citations]) | ('label', 'NNN')

A Diagram has .nw wires (wire 0 = the bottom wire) and .gates in drawn order (left to
right), each a tuple (see `classify`):

    ('Z', w) ('Zw', w) ('H', w) ('X', w)       one-wire gates (a black dot alone is Z, a
                                               white dot alone is X Z X, Figure 3)
    ('SW', a, b)                               the swap of wires a < b
    ('PP', a, b)                               P (x) P on wires a, b (a < b)
    ('CZ', ctrls)                              dots only; ctrls = {wire: colour}
    ('BOX', b, ctrls)                          multi-controlled Z, box wire b
    ('CU', U, t, ctrls)                        multi-controlled U in {H, ZX, XZ, X, ...},
                                               target t (no box wire)
    ('CHB', b, t, ctrls)                       multi-controlled H with box wire b, H on t
    ('?', description)                         anything not understood

a colour is 'b' (black), 'w' (white) or a parameter name (e.g. 'beta').
"""
import re
import sys

import pymupdf

# ----------------------------------------------------------------------------- items

def _black(c): return c is not None and all(v < 0.2 for v in c)
def _white(c): return c is not None and all(v > 0.8 for v in c)


def _dashed(d):
    ds = d.get('dashes') or ''
    return bool(re.search(r'\[\s*[0-9.]+', ds))


def page_items(page):
    """The primitive items of a page.  Coordinates in points, y downwards."""
    H, V, VD, HD, dots, circs, rects, curves = [], [], [], [], [], [], [], []
    for d in page.get_drawings():
        items = d['items']
        r = d['rect']
        kinds = ''.join(it[0] for it in items)
        dashed = _dashed(d)
        if kinds == 'cccc' and r.width < 7 and abs(r.width - r.height) < 0.6:
            cx, cy = (r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2
            if r.width < 3.2:
                col = 'b' if _black(d.get('fill')) else 'w'
                dots.append((cx, cy, col))
            else:
                kind = 'xor' if d.get('fill') is None else 'lab'
                circs.append((cx, cy, r.width / 2, kind))
            continue
        for it in items:
            if it[0] == 'l':
                p, q = it[1], it[2]
                if abs(p.y - q.y) < 0.3 and abs(p.x - q.x) > 0.2:
                    (HD if dashed else H).append((min(p.x, q.x), max(p.x, q.x), (p.y + q.y) / 2))
                elif abs(p.x - q.x) < 0.3 and abs(p.y - q.y) > 0.2:
                    (VD if dashed else V).append(((p.x + q.x) / 2, min(p.y, q.y), max(p.y, q.y)))
            elif it[0] == 're':
                rr = it[1]
                rects.append((rr.x0, rr.y0, rr.x1, rr.y1, dashed))
            elif it[0] == 'c':
                p0, p1, p2, p3 = it[1], it[2], it[3], it[4]
                if max(abs(p.y - p0.y) for p in (p1, p2, p3)) < 0.3 and abs(p3.x - p0.x) > 0.2:
                    # a straight 'curve': a wire drawn as a degenerate Bezier segment
                    (HD if dashed else H).append((min(p0.x, p3.x), max(p0.x, p3.x), (p0.y + p3.y) / 2))
                elif max(abs(p.x - p0.x) for p in (p1, p2, p3)) < 0.3 and abs(p3.y - p0.y) > 0.2:
                    (VD if dashed else V).append(((p0.x + p3.x) / 2, min(p0.y, p3.y), max(p0.y, p3.y)))
                else:
                    curves.append((p0, p1, p2, p3))
    spans = []
    for b in page.get_text('dict')['blocks']:
        for l in b.get('lines', []):
            for s in l['spans']:
                t = s['text'].strip()
                if t:
                    spans.append((t, tuple(s['bbox']), s['size']))
    # the bars of a circled plus are part of the symbol
    def in_circ(x, y):
        return any(abs(x - cx) <= r + 0.3 and abs(y - cy) <= r + 0.3 for cx, cy, r, k in circs if k == 'xor')
    V = [v for v in V if not (in_circ(v[0], v[1]) and in_circ(v[0], v[2]))]
    H = [h for h in H if not (in_circ(h[0], h[2]) and in_circ(h[1], h[2]))]
    # dashed squares drawn as four dashed lines
    dsq = []
    for (x0, x1, y) in HD:
        for (x0b, x1b, yb) in HD:
            if yb > y + 2 and yb - y < 8 and abs(x0b - x0) < 0.3 and abs(x1b - x1) < 0.3 and x1 - x0 < 8:
                dsq.append((x0, y, x1, yb))
    for r in rects:
        if r[4] and r[2] - r[0] < 8:
            dsq.append(r[:4])
    return dict(H=H, V=V, VD=VD, HD=HD, dots=dots, circs=circs,
                rects=[r for r in rects if not r[4]], drects=[r for r in rects if r[4] and r[2] - r[0] >= 8],
                dsq=dsq, curves=curves, spans=spans)


# ----------------------------------------------------------------------------- wires

def _swap_ends(it):
    """Endpoints of the swap curves: (x, y) pairs."""
    pts = []
    for (p0, p1, p2, p3) in it['curves']:
        if abs(p0.y - p3.y) > 2 and abs(p0.x - p3.x) > 4:
            pts.append((p0.x, p0.y)); pts.append((p3.x, p3.y))
    return pts


def wire_runs(it):
    """Horizontal wire lines, joined across the gaps that swaps leave."""
    ends = _swap_ends(it)

    def near_end(x, y):
        return any(abs(ex - x) < 0.6 and abs(ey - y) < 0.6 for ex, ey in ends)

    def circle_gap(x0, x1, y):
        # a labelled circle (a control of parametric colour) drawn over the wire
        return any(abs(cy - y) < 0.6 and abs(cx - (x0 + x1) / 2) < 0.8 and x1 - x0 < 2 * r + 1
                   for cx, cy, r, k in it['circs'])

    segs = sorted(it['H'], key=lambda s: (round(s[2], 1), s[0]))
    out = []
    for s in segs:
        if out and abs(out[-1][2] - s[2]) < 0.3:
            a = out[-1]
            if (s[0] <= a[1] + 0.5 or (near_end(a[1], a[2]) and near_end(s[0], s[2]) and s[0] - a[1] < 40)
                    or circle_gap(a[1], s[0], s[2])):
                out[-1] = (a[0], max(a[1], s[1]), a[2])
                continue
        out.append(s)
    return [w for w in out if w[1] - w[0] > 6]


# ----------------------------------------------------------------------------- '=' signs

def eq_signs(it):
    """The '=' signs (centre x, axis y, bbox) with the citations written above them."""
    res = []
    spans = it['spans']
    for t, b, sz in spans:
        if t in ('=', '≔', ':=') and sz > 8:
            cx = (b[0] + b[2]) / 2
            cy = (b[1] + b[3]) / 2 + 1.1
            cites = []
            for t2, b2, sz2 in spans:
                if sz2 < 8 and b2[3] <= b[1] + 6 and b2[3] > b[1] - 12 and b2[0] < b[2] + 40 and b2[2] > b[0] - 40:
                    cites.append((b2[0], t2))
            txt = ''.join(t2 for _, t2 in sorted(cites))
            res.append(dict(x=cx, y=cy, bbox=b, cite=txt))
    return res


def split_cites(txt):
    """'(81)(5)' -> ['81', '5'];  'Lemma 7.6' -> ['Lemma 7.6']."""
    out = re.findall(r'\(([0-9]+[a-z]?)\)', txt)
    for m in re.finditer(r'(Lemma|Corollary)\s*([A-Z]?[0-9.]+)', txt):
        out.append(m.group(1) + ' ' + m.group(2).rstrip('.'))
    return out


# ----------------------------------------------------------------------------- diagrams

class Diagram:
    def __init__(self, x0, x1, ys):
        self.x0, self.x1 = x0, x1
        self.ys = sorted(ys)          # top first
        self.nw = len(ys)
        self.gates = []
        self.warn = []

    def wire(self, y, tol=3.0):
        best = min(range(self.nw), key=lambda i: abs(self.ys[i] - y))
        if abs(self.ys[best] - y) > tol:
            return None
        return self.nw - 1 - best

    def key(self):
        return (round(self.x0), round(self.x1), round(self.ys[0]))

    def __repr__(self):
        return f"D({self.nw}w @{self.x0:.0f}-{self.x1:.0f},{self.ys[0]:.0f}: {self.gates})"


def _best_block(ys, axis):
    """The largest run of consecutive, equally spaced ys centred near the axis (a diagram is
    drawn centred on the '=' sign, up to about a third of the wire spacing)."""
    best = None
    n = len(ys)
    for i in range(n):
        for j in range(i, n):
            blk = ys[i:j + 1]
            tol = 1.6
            if len(blk) > 1:
                sp = [b - a for a, b in zip(blk, blk[1:])]
                if max(sp) - min(sp) > 0.3 or min(sp) < 8 or max(sp) > 20:
                    continue
                tol = max(tol, 0.45 * sp[0])
            off = abs(sum(blk) / len(blk) - axis)
            if off > tol:
                continue
            if best is None or len(blk) > len(best[0]) or (len(blk) == len(best[0]) and off < best[1]):
                best = (blk, off)
    return best[0] if best else None


GAP = 70


def diagrams(it):
    """The diagrams next to an '=' sign, and the '=' signs."""
    runs = wire_runs(it)
    eqs = eq_signs(it)
    found = {}
    for e in eqs:
        # a diagram does not reach past half-way to the '=' signs above and below it
        col = [f['y'] for f in eqs if f is not e and abs(f['x'] - e['x']) < 12]
        ylo = max([(y + e['y']) / 2 for y in col if y < e['y'] - 3], default=-1e9)
        yhi = min([(y + e['y']) / 2 for y in col if y > e['y'] + 3], default=1e9)
        for side in ('L', 'R'):
            if side == 'L':
                dist = lambda r: e['bbox'][0] - r[1]
            else:
                dist = lambda r: r[0] - e['bbox'][2]
            cand = [r for r in runs if 0.3 < dist(r) < GAP and abs(r[2] - e['y']) < 60]
            groups = {}
            for r in cand:
                groups.setdefault((round(r[0]), round(r[1])), []).append(r)
            # the nearest group of runs of one x-extent that has a block centred on the axis
            best = None
            for (gx0, gx1), rs in groups.items():
                same = sorted(set(round(r[2], 2) for r in runs
                                  if abs(r[0] - rs[0][0]) < 1.2 and abs(r[1] - rs[0][1]) < 1.2
                                  and ylo < r[2] < yhi))
                blk = _best_block(same, e['y'])
                if not blk:
                    continue
                d = dist(rs[0])
                if best is None or d < best[3] - 3 or (abs(d - best[3]) <= 3 and len(blk) > len(best[2])):
                    best = (rs[0][0], rs[0][1], blk, d)
            if best:
                best = best[:3]
            if best:
                D = Diagram(*best)
                k = D.key()
                if k not in found:
                    found[k] = D
                e[side] = found[k]
    return eqs, list(found.values()), runs


# ----------------------------------------------------------------------------- gates

def _inside(D, x, y, pad=2.0, vpad=3.0):
    return D.x0 - pad <= x <= D.x1 + pad and D.ys[0] - vpad <= y <= D.ys[-1] + vpad


def _label_in(it, x0, y0, x1, y1):
    sp = [(b[0], t) for t, b, sz in it['spans']
          if b[0] >= x0 - 1.5 and b[2] <= x1 + 1.5 and b[1] >= y0 - 2.5 and b[3] <= y1 + 2.5]
    return ''.join(t for _, t in sorted(sp))


GREEK = {'𝛼': 'alpha', '𝛽': 'beta', '𝛾': 'gamma', '𝛿': 'delta', '𝜀': 'eps', '𝜆': 'lambda',
         'β': 'beta', 'γ': 'gamma', 'α': 'alpha', 'δ': 'delta'}


def _norm_label(s):
    out = []
    for ch in s:
        o = ord(ch)
        if ch in GREEK:
            out.append(GREEK[ch])
        elif 0x1D434 <= o <= 0x1D44D:      # mathematical italic capitals
            out.append(chr(ord('A') + o - 0x1D434))
        elif 0x1D44E <= o <= 0x1D467:      # mathematical italic small letters
            out.append(chr(ord('a') + o - 0x1D44E))
        elif ch == 'ℎ':
            out.append('h')
        elif ch == '−':
            out.append('-')
        elif ch != ' ':
            out.append(ch)
    return ''.join(out)


def gates(it, D):
    """Extract the gates of diagram D, in drawn order."""
    nodes = []  # dict(kind, x, y0, y1, wire(s), ...)
    for (x, y, col) in it['dots']:
        if _inside(D, x, y):
            w = D.wire(y)
            if w is None:
                D.warn.append(('dot off wire', x, y)); continue
            nodes.append(dict(kind='dot', x=x, y0=y - 1, y1=y + 1, w=w, col=col))
    for (x, y, r, kind) in it['circs']:
        if _inside(D, x, y):
            w = D.wire(y)
            if w is None:
                D.warn.append(('circle off wire', x, y)); continue
            if kind == 'xor':
                nodes.append(dict(kind='xor', x=x, y0=y - r, y1=y + r, w=w))
            else:
                lab = _norm_label(_label_in(it, x - r, y - r, x + r, y + r))
                nodes.append(dict(kind='dot', x=x, y0=y - r, y1=y + r, w=w, col=lab or '?'))
    for (x0, y0, x1, y1, _d) in it["rects"]:
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        if _inside(D, cx, cy):
            ws = [D.nw - 1 - i for i, y in enumerate(D.ys) if y0 - 0.5 <= y <= y1 + 0.5]
            lab = _norm_label(_label_in(it, x0, y0, x1, y1))
            nodes.append(dict(kind='box', x=cx, y0=y0, y1=y1, ws=ws, lab=lab))
    for (x0, y0, x1, y1) in it['dsq']:
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        if _inside(D, cx, cy):
            w = D.wire(cy)
            nodes.append(dict(kind='dsq', x=cx, y0=y0, y1=y1, w=w))
    for (x0, y0, x1, y1, _d) in it["drects"]:
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        if _inside(D, cx, cy):
            D.warn.append(('dashed rect', x0, y0, x1, y1))
    # swaps
    swaps = []
    for (p0, p1, p2, p3) in it['curves']:
        if abs(p0.y - p3.y) > 2 and abs(p0.x - p3.x) > 4 and _inside(D, (p0.x + p3.x) / 2, (p0.y + p3.y) / 2):
            a, b = D.wire(p0.y, 1.0), D.wire(p3.y, 1.0)
            if a is None or b is None:
                D.warn.append(('curve off wire', p0, p3)); continue
            swaps.append((min(p0.x, p3.x), max(p0.x, p3.x), min(a, b), max(a, b)))
    sw = {}
    for s in swaps:
        sw.setdefault((round(s[0], 1), s[2], s[3]), s)
    # union-find over nodes linked by vertical lines
    par = list(range(len(nodes)))

    def find(i):
        while par[i] != i:
            par[i] = par[par[i]]; i = par[i]
        return i

    def link(vl, dashed):
        x, ya, yb = vl
        if not (D.x0 - 1 <= x <= D.x1 + 1 and yb >= D.ys[0] - 9 and ya <= D.ys[-1] + 9):
            return
        hit = [i for i, n in enumerate(nodes)
               if abs(n['x'] - x) < 1.2 and n['y1'] >= ya - 1.6 and n['y0'] <= yb + 1.6]
        for i in hit[1:]:
            par[find(i)] = find(hit[0])
        if len(hit) == 1:
            D.warn.append(('dangling vertical', x, ya, yb))

    for vl in it['V']:
        link(vl, False)
    for vl in it['VD']:
        link(vl, True)
    comps = {}
    for i in range(len(nodes)):
        comps.setdefault(find(i), []).append(nodes[i])
    out = []
    for c in comps.values():
        x = sum(n['x'] for n in c) / len(c)
        out.append((x, classify(c, D)))
    for (x0, x1, a, b) in sw.values():
        out.append(((x0 + x1) / 2, ('SW', a, b)))
    out.sort(key=lambda t: t[0])
    D.gates = [g for _, g in out]
    D.xs = [x for x, _ in out]
    return D


def classify(c, D):
    dots = [n for n in c if n['kind'] == 'dot']
    boxes = [n for n in c if n['kind'] == 'box']
    dsq = [n for n in c if n['kind'] == 'dsq']
    xors = [n for n in c if n['kind'] == 'xor']
    ctr = {n['w']: n['col'] for n in dots}
    if len(c) == 1:
        n = c[0]
        if n['kind'] == 'dot':
            return ('Z', n['w']) if n['col'] == 'b' else ('Zw', n['w']) if n['col'] == 'w' else ('?', 'lone param dot', n)
        if n['kind'] == 'xor':
            return ('X', n['w'])
        if n['kind'] == 'box' and len(n['ws']) == 1:
            if n['lab'] == 'H':
                return ('H', n['ws'][0])
            return ('CU', n['lab'], n['ws'][0], {})
        return ('?', 'lone', n)
    if boxes and all(b['lab'] == 'P' for b in boxes) and len(boxes) == 2 and not dots and not dsq and not xors:
        a, b = sorted(bb['ws'][0] for bb in boxes)
        return ('PP', a, b)
    if not boxes and not dsq and not xors and len(dots) == len(c) and len(dots) >= 2:
        return ('CZ', ctr)
    if dsq and not boxes and not xors and len(dsq) == 1:
        return ('BOX', dsq[0]['w'], ctr)
    if len(boxes) == 1 and len(boxes[0]['ws']) == 1 and not xors:
        b = boxes[0]
        if dsq:
            if len(dsq) == 1 and b['lab'] == 'H':
                return ('CHB', dsq[0]['w'], b['ws'][0], ctr)
            return ('?', 'box+dsq', c)
        return ('CU', b['lab'], b['ws'][0], ctr)
    if len(xors) == 1 and not boxes and not dsq:
        return ('CU', 'X', xors[0]['w'], ctr)
    return ('?', 'unclassified', [(n['kind'], n.get('w', n.get('ws')), n.get('col', n.get('lab'))) for n in c])


# ----------------------------------------------------------------------------- rows

class Row:
    def __init__(self, y):
        self.y = y
        self.items = []

    def __repr__(self):
        return f"Row({self.y:.0f}: {self.items})"


def labels(it):
    """Equation labels '(NNN)' at the right margin: (number, y)."""
    out = []
    for t, b, sz in it['spans']:
        m = re.fullmatch(r'\(([0-9]+)\)', t)
        if m and b[0] > 480 and sz > 8:
            out.append((m.group(1), (b[1] + b[3]) / 2 + 1.1))
    return out


def parse_page(doc, pageno):
    page = doc[pageno - 1]
    it = page_items(page)
    eqs, diags, runs = diagrams(it)
    for D in diags:
        gates(it, D)
    labs = labels(it)
    # rows: cluster '=' signs by axis y
    rows = []
    for e in sorted(eqs, key=lambda e: (round(e['y']), e['x'])):
        if 'L' not in e and 'R' not in e:
            continue
        r = next((r for r in rows if abs(r.y - e['y']) < 2.5), None)
        if r is None:
            r = Row(e['y']); rows.append(r)
        r.items.append(('eq', e))
    out = []
    for r in rows:
        seq = []
        for _, e in sorted(r.items, key=lambda t: t[1]['x']):
            if 'L' in e and (not seq or seq[-1][0] != 'diag' or seq[-1][1] is not e['L']):
                seq.append(('diag', e['L']))
            seq.append(('eq', split_cites(e['cite']), e['cite']))
            if 'R' in e:
                seq.append(('diag', e['R']))
        lab = [n for n, y in labs if abs(y - r.y) < 3]
        if lab:
            seq.append(('label', lab[0]))
        r.items = seq
        out.append(r)
    out.sort(key=lambda r: r.y)
    return out


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    doc = pymupdf.open(sys.argv[1])
    for pg in sys.argv[2:]:
        for r in parse_page(doc, int(pg)):
            print(f'--- p{pg} y={r.y:.1f}')
            for t in r.items:
                if t[0] == 'diag':
                    print('   ', t[1], t[1].warn if t[1].warn else '')
                else:
                    print('   ', t[0], t[1:])
