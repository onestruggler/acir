"""Read a circuit figure of Blake's paper (a PDF from the figures/
directory of its arXiv source) into the transcription notation of
circ.gparse, left to right.

The figures are TikZ drawings, so their primitives are exact: wires
are horizontal strokes, gates white boxes with a label, a control a
small filled circle (white for a negative control), a target ⊕ a larger
unfilled circle, the wire between a control and its target a vertical
stroke, a swap two curves crossing between two wires, and a scalar a
white rounded box off the wires.  Wires are numbered from the bottom,
as in the formalisation (the paper's top wire is the highest).

    python figparse.py FIG.pdf ...     prints each figure's transcription

Needs PyMuPDF (import pymupdf)."""
import re
import sys
import pymupdf

TOL = 1.2


def _labels(page):
    """Text spans as (x0, y0, x1, y1, text), a dagger glyph appended as
    '†' to the span before it."""
    out = []
    for b in page.get_text('rawdict')['blocks']:
        for l in b.get('lines', []):
            for s in l['spans']:
                txt = ''.join(c['c'] for c in s['chars']).strip()
                if not txt:
                    continue
                font = s['font']
                x0, y0, x1, y1 = s['bbox']
                if font.startswith('CMSY') and len(txt) == 1 and ord(txt) not in (0x2212,):
                    txt = '†' if txt not in '−-' else '-'
                out.append([x0, y0, x1, y1, txt])
    # glue a dagger onto the label it follows
    glued = []
    for sp in out:
        if sp[4] == '†' and glued and abs(glued[-1][2] - sp[0]) < 2.5:
            glued[-1][4] += '†'
            glued[-1][2] = sp[2]
        else:
            glued.append(sp)
    return glued


def _inside(sp, r):
    cx, cy = (sp[0] + sp[2]) / 2, (sp[1] + sp[3]) / 2
    return r.x0 - 1 <= cx <= r.x1 + 1 and r.y0 - 1 <= cy <= r.y1 + 1


def parse(path):
    page = pymupdf.open(path)[0]
    draws = page.get_drawings()
    spans = _labels(page)

    # Wires: horizontal strokes, clustered by height.
    ys = []
    for d in draws:
        r = d['rect']
        if d.get('fill') is None and r.height < 0.3 and r.width > 2:
            ys.append(r.y0)
    wy = []
    for y in sorted(ys):
        if not wy or y - wy[-1] > TOL:
            wy.append(y)
    nw = len(wy)

    def wire(y):
        k = min(range(nw), key=lambda i: abs(wy[i] - y))
        return nw - 1 - k            # numbered from the bottom

    def wires_in(y0, y1):
        return sorted(nw - 1 - i for i in range(nw) if y0 - 0.5 <= wy[i] <= y1 + 0.5)

    parts = []                       # (x, kind, wires, label)
    vlines = []                      # (x, y0, y1)
    for d in draws:
        r = d['rect']
        kinds = [it[0] for it in d['items']]
        fill = d.get('fill')
        cx, cy = (r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2
        if fill is None and r.width < 0.3 and r.height > 0.5:
            vlines.append((r.x0, r.y0, r.y1))
        elif 're' in kinds and fill == (1.0, 1.0, 1.0):
            lab = ''.join(sp[4] for sp in spans if _inside(sp, r))
            ws = wires_in(r.y0, r.y1)
            if ws:
                parts.append((cx, 'box', ws, lab))
            else:
                parts.append((cx, 'scalar', [], lab))
        elif fill == (0.0, 0.0, 0.0) and r.width < 5 and r.height < 5:
            parts.append((cx, 'dot', [wire(cy)], ''))
        elif fill == (1.0, 1.0, 1.0) and r.width < 5 and r.height < 5:
            parts.append((cx, 'hollow', [wire(cy)], ''))
        elif fill is None and kinds == ['c', 'c', 'c', 'c'] and 6 < r.width < 11:
            parts.append((cx, 'target', [wire(cy)], ''))
        elif fill is None and kinds == ['c'] and r.height > 3 and r.width > 3:
            parts.append((cx, 'swapcurve', wires_in(r.y0, r.y1), ''))
        elif fill == (1.0, 1.0, 1.0) and 'c' in kinds:
            parts.append((cx, 'scalar', [], scalar_label([sp for sp in spans if _inside(sp, r)])))

    # Columns: parts at one abscissa joined by a vertical stroke make one
    # gate; parts at one abscissa without one are separate gates.
    parts.sort(key=lambda p: p[0])
    gates = []
    used = [False] * len(parts)
    for i, p in enumerate(parts):
        if used[i]:
            continue
        if p[1] == 'swapcurve':
            # its partner: the other curve over the same span
            for j in range(i + 1, len(parts)):
                if not used[j] and parts[j][1] == 'swapcurve' and abs(parts[j][0] - p[0]) < TOL:
                    used[j] = True
                    break
            used[i] = True
            a, b = p[2][0], p[2][-1]
            gates.append((p[0], 'SW%d%d' % (min(a, b), max(a, b))))
            continue
        col = [j for j in range(i, len(parts))
               if not used[j] and abs(parts[j][0] - p[0]) < TOL and parts[j][1] != 'swapcurve']
        joined = any(abs(v[0] - p[0]) < TOL for v in vlines)
        if not joined or len(col) == 1:
            used[i] = True
            gates.append((p[0], single(p)))
            continue
        for j in col:
            used[j] = True
        gates.append((p[0], multi([parts[j] for j in col])))
    gates.sort(key=lambda g: g[0])
    return ' '.join(t for _, t in gates if t)


NAMES = {'H': 'H', 'T': 'T', 'T†': 'Td', 'S': 'S', 'S†': 'Sd', 'Z': 'Z', 'X': 'X',
         'K': 'K'}


def single(p):
    x, kind, ws, lab = p
    if kind == 'scalar':
        return scalar(lab)
    if kind == 'box':
        if len(ws) != 1:
            return 'BOX[%s]%s' % (lab, ''.join(map(str, ws)))
        m = re.fullmatch(r'([A-Za-z]†?)(\d+)', lab)       # a power, as H²
        if m and m.group(1) in NAMES:
            return ' '.join([NAMES[m.group(1)] + str(ws[0])] * int(m.group(2)))
        return NAMES.get(lab, 'BOX[%s]' % lab) + str(ws[0])
    raise ValueError('lone %s in %s' % (kind, p))


def scalar_label(sps):
    """A scalar's text: a sign, ω, a superscript exponent; the subscript
    (the order of the root) is dropped.  As 'ω', 'ω^k', '-ω^k', or the
    plain text otherwise."""
    base = [sp for sp in sps if sp[4] in ('ω', 'ω†')]
    if not base:
        return ''.join(sp[4] for sp in sps)
    b = base[0]
    if b[4] == 'ω†':
        return 'ω†'
    mid = (b[1] + b[3]) / 2
    sign = ''.join(sp[4] for sp in sps if sp[2] <= b[0] + 0.5 and sp[4] in '−-')
    exp = ''.join(sp[4] for sp in sps
                  if sp[0] >= b[2] - 0.5 and (sp[1] + sp[3]) / 2 < mid - 0.5 and sp[4].isdigit())
    return ('-' if sign else '') + 'ω' + ('^' + exp if exp else '')


def scalar(lab):
    if lab == 'ω':
        return 'w'
    if lab == 'ω†':
        return 'wd'
    if lab.startswith('ω^') and lab[2:].isdigit():
        return 'w' + lab[2:]
    return 'SCALAR[%s]' % lab


def multi(ps):
    dots = [p[2][0] for p in ps if p[1] == 'dot']
    holl = [p[2][0] for p in ps if p[1] == 'hollow']
    targ = [p[2][0] for p in ps if p[1] == 'target']
    boxes = [p for p in ps if p[1] == 'box']
    if targ and len(targ) == 1 and len(dots) + len(holl) == 1 and not boxes:
        c = (dots + holl)[0]
        return ('CX%d%d' if dots else 'CXo%d%d') % (c, targ[0])
    if len(dots) == 2 and not holl and not targ and not boxes:
        return 'CZ%d%d' % (max(dots), min(dots))
    if len(boxes) == 1 and len(dots) + len(holl) == 1 and not targ:
        c = (dots + holl)[0]
        lab, t = boxes[0][3], boxes[0][2]
        if len(t) == 1:
            return 'C%s%s%d%d' % (NAMES.get(lab, '[%s]' % lab), '' if dots else 'o', c, t[0])
    return 'MULTI[%s]' % ';'.join('%s%s%s' % (p[1], p[2], p[3]) for p in ps)


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    for f in sys.argv[1:]:
        print(f.rsplit('/', 1)[-1].rsplit('\\', 1)[-1], ':', parse(f))
