"""The statements and derivation chains of the paper's appendices, as parsed diagrams.

    python chains.py PAPER.pdf FIRST LAST [OUT.json]

reads the pages FIRST..LAST, and collects
  * statements: every row ending with an equation label (NNN): the list of its diagrams;
  * proofs: for each 'Proof of Equation (N)' heading, the chains below it: a chain is a
    row starting with a diagram, continued by the rows starting with an '=' sign; each
    step carries the citations written over its '=' sign.
Each step is checked numerically (model.equal), and each chain against the statement
of its equation (its two ends against the two sides, in either order).  Rows that
fail are reported; the JSON output keeps everything for the generators.
"""
import json
import re
import sys

import pymupdf

import figparse
import model

sys.stdout.reconfigure(encoding='utf-8')


def headings(page, pno):
    out = []
    for b in page.get_text('dict')['blocks']:
        for l in b.get('lines', []):
            txt = ''.join(s['text'] for s in l['spans'])
            m = re.match(r'\s*Proof of Equations? \(([0-9]+)\)', txt)
            if m:
                out.append((pno, l['bbox'][1], int(m.group(1))))
    return out


def gates_json(D):
    def enc(g):
        return [dict((str(k), v) for k, v in p.items()) if isinstance(p, dict) else p for p in g]
    return dict(nw=D.nw, gates=[enc(g) for g in D.gates], page=D.page, y=round(D.ys[0], 1))


def collect(doc, first, last):
    statements = {}
    events = []  # (page, y, kind, payload)
    for pno in range(first, last + 1):
        for (p, y, n) in headings(doc[pno - 1], pno):
            events.append((p, y, 'head', n))
        for r in figparse.parse_page(doc, pno):
            for t in r.items:
                if t[0] == 'diag':
                    t[1].page = pno
            lab = [t[1] for t in r.items if t[0] == 'label']
            if lab:
                statements[int(lab[0])] = [t[1] for t in r.items if t[0] == 'diag']
                continue
            events.append((pno, r.y, 'row', r.items))
    events.sort(key=lambda e: (e[0], e[1]))
    proofs = {}
    cur = None
    chain = None
    for (p, y, kind, payload) in events:
        if kind == 'head':
            cur = payload
            proofs.setdefault(cur, [])
            chain = None
            continue
        if cur is None:
            continue
        items = payload
        if items[0][0] == 'diag' or chain is None:
            chain = dict(diags=[], cites=[], pages=[p])
            proofs[cur].append(chain)
            if items[0][0] == 'eq':
                chain['broken_start'] = True
        for t in items:
            if t[0] == 'diag':
                if chain['diags'] and len(chain['diags']) == len(chain['cites']) + 1:
                    # two diagrams in a row: should not happen
                    chain.setdefault('warn', []).append('two diagrams without =')
                chain['diags'].append(t[1])
            elif t[0] == 'eq':
                chain['cites'].append(t[1])
        if p not in chain['pages']:
            chain['pages'].append(p)
    return statements, proofs


def safe_equal(N, a, b):
    try:
        return model.equal(N, a, b)
    except Exception as ex:  # a gate the model does not know
        return False, str(ex)


def check(statements, proofs, verbose=False):
    bad = []
    for n, ds in sorted(statements.items()):
        for a, b in zip(ds, ds[1:]):
            ok, env = safe_equal(a.nw, a.gates, b.gates)
            if not ok:
                bad.append((n, 'statement', env))
    for n, chains in sorted(proofs.items()):
        for ci, ch in enumerate(chains):
            ds = ch['diags']
            ch['ok'] = []
            for i, (a, b) in enumerate(zip(ds, ds[1:])):
                if a.nw != b.nw:
                    ch['ok'].append(False); bad.append((n, ci, i, 'width')); continue
                ok, env = safe_equal(a.nw, a.gates, b.gates)
                ch['ok'].append(ok)
                if not ok:
                    bad.append((n, ci, i, 'step', ch['cites'][i] if i < len(ch['cites']) else None))
            if n in statements and ds:
                st = statements[n]
                l, r = st[0], st[-1]
                ends = (ds[0], ds[-1])
                ch['matches'] = None
                for name, (x, y) in (('fwd', (l, r)), ('bwd', (r, l))):
                    if ends[0].nw == x.nw and ends[1].nw == y.nw:
                        if safe_equal(x.nw, x.gates, ends[0].gates)[0] and safe_equal(y.nw, y.gates, ends[1].gates)[0]:
                            ch['matches'] = name
                            if ends[0].gates == x.gates and ends[1].gates == y.gates:
                                ch['matches'] += '='
                            break
    return bad


def dump(statements, proofs, path):
    out = dict(statements={str(n): [gates_json(D) for D in ds] for n, ds in statements.items()},
               proofs={str(n): [dict(diags=[gates_json(D) for D in ch['diags']], cites=ch['cites'],
                                     ok=ch.get('ok'), matches=ch.get('matches'))
                                for ch in chains] for n, chains in proofs.items()})
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(out, f, indent=1, ensure_ascii=False)


if __name__ == '__main__':
    doc = pymupdf.open(sys.argv[1])
    first, last = int(sys.argv[2]), int(sys.argv[3])
    st, pr = collect(doc, first, last)
    bad = check(st, pr)
    for n in sorted(pr):
        for ci, ch in enumerate(pr[n]):
            steps = len(ch['diags']) - 1
            print(f"({n}) chain {ci}: {steps} steps, pages {ch['pages']}, ends {ch.get('matches')}, "
                  f"{'ALL OK' if all(ch['ok']) else 'FAILS at ' + str([i for i, o in enumerate(ch['ok']) if not o])}"
                  f"{' WARN ' + str(ch.get('warn')) if ch.get('warn') else ''}")
    print('statements:', sorted(st))
    print('bad:', bad)
    if len(sys.argv) > 4:
        dump(st, pr, sys.argv[4])
