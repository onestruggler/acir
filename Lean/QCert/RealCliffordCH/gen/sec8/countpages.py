"""Compare the number of '=' signs on a page with the number the parser places in rows."""
import sys
import pymupdf
import figparse
sys.stdout.reconfigure(encoding='utf-8')
doc = pymupdf.open(sys.argv[1])
for pg in map(int, sys.argv[2:]):
    it = figparse.page_items(doc[pg - 1])
    eqs, _, _ = figparse.diagrams(it)
    rows = figparse.parse_page(doc, pg)
    used = sum(1 for r in rows for t in r.items if t[0] == 'eq')
    lone = [(round(e['x']), round(e['y'])) for e in eqs if 'L' not in e and 'R' not in e]
    half = [(round(e['x']), round(e['y'])) for e in eqs if ('L' in e) != ('R' in e)]
    print(pg, 'eq signs', len(eqs), 'in rows', used, 'without diagrams', lone, 'one-sided', half)
