"""Parse the circuit diagrams of arXiv:2602.06644 from the PDF vector graphics.

parse_page(pdf, pageno) -> list of rows; each row is a list of items in reading order:
  ('diag', Diagram) | ('eq', citations:list[str]) | ('label', 'NNN')
A Diagram has .nw wires (wire 0 = bottom) and .gates in drawn order:
  ('Z', w) | ('H', w) | ('X', w) | ('SW', w1, w2)      single gates / swap of two wires
  ('CTRL', target_kind, targets, ctrls)  target_kind in {'Z','H','ZX','XZ','BOX','P','HBOX'...}
"""
import sys, re, math
import pymupdf

TOL = 1.2

def is_black(c): return c is not None and all(v < 0.2 for v in c)
def is_white(c): return c is not None and all(v > 0.8 for v in c)

class Diagram:
    def __init__(self, ys, x0, x1):
        self.ys = sorted(ys)  # top first
        self.nw = len(ys)
        self.x0, self.x1 = x0, x1
        self.gates = []
    def wire(self, y):
        best = min(range(self.nw), key=lambda i: abs(self.ys[i] - y))
        if abs(self.ys[best] - y) > 3.0: return None
        return self.nw - 1 - best
    def __repr__(self):
        return f"D({self.nw}w: {self.gates})"

def page_items(page):
    dr = page.get_drawings()
    H, V, dots, wdots, rects, drects, curves, dotted = [], [], [], [], [], [], [], []
    for d in dr:
        items = d['items']; r = d['rect']
        dashes = d.get('dashes') or ''
        dashed = bool(re.search(r'\[\s*[0-9.]+', dashes or '')) and not re.match(r'^\[\s*\]', dashes or '')
        kinds = ''.join(it[0] for it in items)
        if kinds and set(kinds) == {'c'} and r.width < 6 and r.height < 6 and abs(r.width - r.height) < 1:
            cx, cy = (r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2
            if is_black(d.get('fill')): dots.append((cx, cy, r.width))
            elif is_white(d.get('fill')) or d.get('fill') is None: wdots.append((cx, cy, r.width))
            continue
        for it in items:
            if it[0] == 'l':
                p, q = it[1], it[2]
                if abs(p.y - q.y) < 0.3 and abs(p.x - q.x) > 0.5:
                    (dotted if dashed else H).append((min(p.x, q.x), max(p.x, q.x), p.y))
                elif abs(p.x - q.x) < 0.3 and abs(p.y - q.y) > 0.3:
                    (dotted if dashed else V).append(('v', p.x, min(p.y, q.y), max(p.y, q.y), dashed))
                    if dashed: pass
            elif it[0] == 're':
                rr = it[1]
                (drects if dashed else rects).append((rr.x0, rr.y0, rr.x1, rr.y1))
            elif it[0] == 'c':
                curves.append((it[1], it[2], it[3], it[4]))
    spans = []
    for b in page.get_text('dict')['blocks']:
        for l in b.get('lines', []):
            for s in l['spans']:
                t = s['text'].strip()
                if t: spans.append((t, s['bbox']))
    return dict(H=H, V=V, dots=dots, wdots=wdots, rects=rects, drects=drects, curves=curves,
                dotted=dotted, spans=spans)

def find_diagrams(it, minlen=8):
    """Group horizontal wire segments into diagrams."""
    segs = [s for s in it['H'] if s[1] - s[0] > minlen]
    # merge collinear segments (wires broken by boxes)
    segs.sort(key=lambda s: (round(s[2], 1), s[0]))
    lines = []
    for s in segs:
        if lines and abs(lines[-1][2] - s[2]) < 0.3 and s[0] <= lines[-1][1] + 14:
            lines[-1] = (lines[-1][0], max(lines[-1][1], s[1]), lines[-1][2])
        else:
            lines.append(s)
    # cluster lines that overlap in x and are vertically close (spacing <= 14)
    used = [False] * len(lines); diags = []
    lines.sort(key=lambda s: s[2])
    for i, l in enumerate(lines):
        if used[i]: continue
        group = [l]; used[i] = True
        changed = True
        while changed:
            changed = False
            for j, m in enumerate(lines):
                if used[j]: continue
                for g in group:
                    if abs(g[2] - m[2]) < 14.5 and min(g[1], m[1]) - max(g[0], m[0]) > 4:
                        group.append(m); used[j] = True; changed = True; break
        x0 = min(g[0] for g in group); x1 = max(g[1] for g in group)
        ys = sorted(set(round(g[2], 1) for g in group))
        diags.append((x0, x1, ys))
    return diags

def merge_wires(it):
    segs = sorted([s for s in it['H'] if s[1] - s[0] > 1.5], key=lambda s: (round(s[2], 1), s[0]))
    eqs = eq_signs(it)
    def eq_between(a, b, y):
        return any(a - 1 < ex < b + 1 and abs(ey - y) < 45 for ex, ey in eqs)
    out = []
    for s in segs:
        if out and abs(out[-1][2] - s[2]) < 0.3 and s[0] <= out[-1][1] + 24 and not eq_between(out[-1][1], s[0], s[2]):
            out[-1] = (out[-1][0], max(out[-1][1], s[1]), out[-1][2])
        else:
            out.append(s)
    return [w for w in out if w[1] - w[0] > 8]

def eq_signs(it):
    return [((b[0] + b[2]) / 2, (b[1] + b[3]) / 2) for t, b in it['spans'] if t == '=' or t == '≔' or t == ':=']

def diagrams(it):
    wires = merge_wires(it)
    eqs = eq_signs(it)
    groups = {}
    for (x0, x1, y) in wires:
        cands = [(abs(ey - y), i, side) for i, (ex, ey) in enumerate(eqs)
                 for side, d in (('L', ex - x1), ('R', x0 - ex)) if -2 < d < 30 and abs(ey - y) < 60]
        if not cands: continue
        _, i, side = min(cands)
        groups.setdefault((i, side), []).append((x0, x1, y))
    # a diagram right of one '=' and left of the next is the same diagram
    diags = []
    seen = {}
    for key, ws in groups.items():
        k = (round(min(w[0] for w in ws)), round(max(w[1] for w in ws)), round(min(w[2] for w in ws)))
        if k in seen: continue
        seen[k] = True
        diags.append((key, sorted(ws, key=lambda w: w[2])))
    return eqs, diags
