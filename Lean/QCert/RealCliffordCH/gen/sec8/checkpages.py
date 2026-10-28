"""Check every row of the given pages: consecutive diagrams denote the same operator.

    python checkpages.py PAPER.pdf PAGE [PAGE ...]
"""
import sys

import pymupdf

import figparse
import model

sys.stdout.reconfigure(encoding='utf-8')


def check_rows(doc, pages, verbose=False):
    bad = 0
    for pg in pages:
        for r in figparse.parse_page(doc, pg):
            ds = [t[1] for t in r.items if t[0] == 'diag']
            lab = [t[1] for t in r.items if t[0] == 'label']
            tag = f'p{pg} y={r.y:.0f} {lab[0] if lab else ""}'
            unk = [g for D in ds for g in D.gates if g[0] == '?']
            if unk or any(D.warn for D in ds):
                print(tag, 'PARSE', unk, [D.warn for D in ds if D.warn]); bad += 1
                continue
            for a, b in zip(ds, ds[1:]):
                if a.nw != b.nw:
                    print(tag, 'WIDTH', a.nw, b.nw); bad += 1; continue
                try:
                    ok, env = model.equal(a.nw, a.gates, b.gates)
                except Exception as ex:
                    print(tag, 'MODEL', ex); bad += 1; continue
                if not ok:
                    print(tag, 'FAIL', env, '\n   ', a, '\n   ', b); bad += 1
                elif verbose:
                    print(tag, 'ok')
    return bad


if __name__ == '__main__':
    doc = pymupdf.open(sys.argv[1])
    pages = [int(p) for p in sys.argv[2:]]
    print('bad rows:', check_rows(doc, pages, verbose=True))
