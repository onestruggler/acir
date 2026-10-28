"""Read a circuit figure (TikZ, compiled to PDF) of Blake's paper into a list of events.

An event is (x, kind, data):
  ('box', (wire, label))        a one-wire gate box
  ('scalar', label)             a rounded box (a scalar)
  ('ctrl', (controls, targets)) dots and ⊕ on one vertical line
  ('perm', perm)                a block of crossing wires: perm[i] = wire at the right of wire i
Wire 0 is the bottom wire.
"""
import pymupdf, sys, json, os

def spans_of(page):
    out = []
    for b in page.get_text('rawdict')['blocks']:
        for l in b.get('lines', []):
            for s in l['spans']:
                for c in s['chars']:
                    x0, y0, x1, y1 = c['bbox']
                    out.append((c['c'], (x0 + x1) / 2, (y0 + y1) / 2, s['size'], s['font']))
    return out

def parse(path):
    d = pymupdf.open(path); p = d[0]
    chars = spans_of(p)
    hlines, vlines, boxes, rboxes, dots, circles, curves, wdots = [], [], [], [], [], [], [], []
    dashed = []
    for dr in p.get_drawings():
        kinds = tuple(it[0] for it in dr['items'])
        typ = dr.get('type'); fill = dr.get('fill')
        if kinds == ('re',) and typ == 'fs':
            r = dr['items'][0][1]; boxes.append((r.x0, r.y0, r.x1, r.y1)); continue
        if typ == 'fs' and fill == (1.0, 1.0, 1.0) and kinds in (('l', 'c', 'c', 'l', 'c', 'c', 'l'), ('l', 'c', 'c', 'c', 'c')):
            r = dr['rect']; rboxes.append((r.x0, r.y0, r.x1, r.y1)); continue
        if kinds == ('c', 'c', 'c', 'c'):
            r = dr['rect']; cx, cy = (r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2
            if typ == 'fs' and fill == (0.0, 0.0, 0.0): dots.append((cx, cy, r.x1 - r.x0))
            elif typ == 'fs' and fill == (1.0, 1.0, 1.0) and r.x1 - r.x0 < 5: wdots.append((cx, cy, r.x1 - r.x0))
            elif typ == 's': circles.append((cx, cy, r.x1 - r.x0))
            else: raise Exception('circle? %s %s' % (path, dr))
            continue
        if all(k == 'l' for k in kinds) and typ == 's':
            for it in dr['items']:
                a, b = it[1], it[2]
                if abs(a.y - b.y) < 0.05: hlines.append((min(a.x, b.x), max(a.x, b.x), a.y))
                elif abs(a.x - b.x) < 0.05:
                    vlines.append((a.x, min(a.y, b.y), max(a.y, b.y)))
                    if (dr.get('dashes') or '[] 0').strip() != '[] 0': dashed.append(a.x)
                else:
                    # a wire crossing drawn straight
                    if a.x > b.x: a, b = b, a
                    curves.append((a.x, a.y, b.x, b.y))
            continue
        if kinds == ('c',) and typ == 's':
            it = dr['items'][0]; a, b = it[1], it[4]
            if a.x > b.x: a, b = b, a
            if abs(a.y - b.y) < 0.05: hlines.append((a.x, b.x, a.y)); continue   # a straight wire drawn as a curve
            curves.append((a.x, a.y, b.x, b.y)); continue
        if all(k == 'c' for k in kinds) and typ == 's':
            # a curve in several pieces
            a = dr['items'][0][1]; b = dr['items'][-1][4]
            if a.x > b.x: a, b = b, a
            curves.append((a.x, a.y, b.x, b.y)); continue
        raise Exception('unknown drawing %s %s %s' % (path, kinds, typ))
    # crosses of ⊕ are short h/v lines inside circles: drop them from wires
    def in_circle(x, y):
        return any(abs(x - cx) < r and abs(y - cy) < r for (cx, cy, r) in circles)
    # wire levels
    ys = []
    for (x0, x1, y) in hlines:
        if not in_circle((x0 + x1) / 2, y): ys.append(y)
    for (x0, y0, x1, y1) in boxes: ys.append((y0 + y1) / 2)
    for (cx, cy, r) in dots + circles + wdots: ys.append(cy)
    for (x0, y0, x1, y1) in curves: ys += [y0, y1]
    ys.sort()
    levels = []
    for y in ys:
        if levels and abs(y - levels[-1][-1]) < 2.0: levels[-1].append(y)
        else: levels.append([y])
    levels = [sum(l) / len(l) for l in levels]
    levels.sort(reverse=True)            # wire 0 = bottom = largest y
    def wire(y, tol=3.0):
        best = min(range(len(levels)), key=lambda i: abs(levels[i] - y))
        if abs(levels[best] - y) > tol: raise Exception('off-wire y=%.1f in %s (levels %s)' % (y, path, levels))
        return best
    events = []
    used = set()
    def text_in(x0, y0, x1, y1):
        cs = [c for c in chars if x0 - 0.5 <= c[1] <= x1 + 0.5 and y0 - 0.5 <= c[2] <= y1 + 0.5]
        for c in cs: used.add(id(c))
        return cs
    for (x0, y0, x1, y1) in boxes:
        cs = text_in(x0, y0, x1, y1)
        lab = label(cs)
        if not cs and y1 - y0 < 10: continue      # the empty diagram
        h = y1 - y0
        events.append(((x0 + x1) / 2, 'box', (wire((y0 + y1) / 2), lab, round(h, 1))))
    for (x0, y0, x1, y1) in rboxes:
        cs = text_in(x0, y0, x1, y1)
        events.append(((x0 + x1) / 2, 'scalar', label(cs)))
    # vertical structures
    cols = {}
    for (cx, cy, r) in dots: cols.setdefault(round(cx, 0), []).append(('c', wire(cy)))
    for (cx, cy, r) in circles: cols.setdefault(round(cx, 0), []).append(('t', wire(cy)))
    for (cx, cy, r) in wdots: cols.setdefault(round(cx, 0), []).append(('w', wire(cy)))
    for x, items in cols.items():
        cs = sorted(w for k, w in items if k == 'c'); ts = sorted(w for k, w in items if k == 't')
        ws = sorted(w for k, w in items if k == 'w')
        if not ts:
            # a controlled box: the box in this column
            bx = [e for e in events if e[1] == 'box' and abs(e[0] - x) < 1.5]
            # the box is controlled only if the vertical line reaches it from the dots
            ydots = [levels[w] for w in cs + ws]
            def joined(e):
                yb = levels[e[2][0]]
                near = min(ydots, key=lambda y: abs(y - yb))
                edge = yb - e[2][2] / 2 if near < yb else yb + e[2][2] / 2
                mid = (near + edge) / 2
                return any(abs(vx - x) < 1.5 and vy0 <= mid <= vy1 for (vx, vy0, vy1) in vlines)
            bx = [e for e in bx if joined(e)]
            if not bx:
                kind = 'csd' if any(abs(dx - x) < 1.5 for dx in dashed) else 'cz'
                events.append((x, kind, (cs, ws))); continue
            if len(bx) != 1: raise Exception('controlled box? %s %s %s' % (path, x, items))
            events.remove(bx[0])
            events.append((x, 'cbox', (cs, ws, bx[0][2][0], bx[0][2][1])))
        elif ws: events.append((x, 'ctrl', (cs, ts, ws)))
        else: events.append((x, 'ctrl', (cs, ts)))
    # curves: crossing blocks
    cvs = sorted(curves)
    blocks = []
    for c in cvs:
        if blocks and c[0] < blocks[-1][-1][2] - 0.5: blocks[-1].append(c)
        else: blocks.append([c])
    for bl in blocks:
        perm = {}
        for (x0, y0, x1, y1) in bl:
            a, b = (wire(y0), wire(y1)) if x0 < x1 else (wire(y1), wire(y0))
            perm[a] = b
        if sorted(perm) != sorted(perm.values()): raise Exception('bad perm %s %s' % (path, perm))
        if all(a == b for a, b in perm.items()): continue
        events.append(((bl[0][0] + bl[0][2]) / 2, 'perm', perm))
    left = [c for c in chars if id(c) not in used and c[0].strip()]
    if left: raise Exception('loose text %s %s' % (path, [c[0] for c in left]))
    events.sort(key=lambda e: e[0])
    return len(levels), events

def label(cs):
    cs = sorted(cs, key=lambda c: c[1])
    main = ''.join(c[0] for c in cs if c[3] > 7).strip()
    sub = ''.join(c[0] for c in cs if c[3] <= 7 and c[2] > max([cc[2] for cc in cs if cc[3] > 7] or [0]))
    sup = ''.join(c[0] for c in cs if c[3] <= 7 and c[2] <= max([cc[2] for cc in cs if cc[3] > 7] or [0]))
    return (main, sub, sup)

if __name__ == '__main__':
    for f in sys.argv[1:]:
        try:
            n, ev = parse(f)
            print(os.path.basename(f), n, [(e[1], e[2]) for e in ev])
        except Exception as e:
            print('ERR', f, e)
