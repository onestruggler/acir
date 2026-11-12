"""Module-level delta of the shared framework between two git revisions.

Usage: python delta.py OLD NEW   (run from the repository root)
The framework is the shared library of pldi/compare/loc.py.
"""
import re
import subprocess
import sys
from collections import defaultdict

PREFIXES = ['Word/', 'Presentation/', 'Circuit/', 'Normalization/', 'Examples/Construct/',
            'Examples/Groups/Symmetric/', 'Examples/Groups/Cyclic/', 'Examples/Groups/Trivial',
            'Examples/Groups/Pauli/', 'Notations.agda']


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, text=True, encoding='utf-8',
                          check=True).stdout


def modules(rev):
    out = {}
    for line in git('ls-tree', '-r', rev).splitlines():
        meta, path = line.split('\t', 1)
        if path.endswith('.agda') and any(path.startswith(p) for p in PREFIXES):
            out[path] = meta.split()[2]
    return out


def code_lines(blob):
    text = git('cat-file', '-p', blob)
    text = re.sub(r'\{-.*?-\}', '', text, flags=re.S)
    n = 0
    for l in text.splitlines():
        s = l.strip()
        if s and not s.startswith('--'):
            n += 1
    return n


old, new = modules(sys.argv[1]), modules(sys.argv[2])
loc_old = sum(code_lines(b) for b in old.values())
loc_new = sum(code_lines(b) for b in new.values())
same = [p for p in new if p in old and new[p] == old[p]]
changed = [p for p in new if p in old and new[p] != old[p]]
added = [p for p in new if p not in old]
removed = [p for p in old if p not in new]
print(f'old: {len(old)} modules, {loc_old} code lines')
print(f'new: {len(new)} modules, {loc_new} code lines')
print(f'kept {len(same) + len(changed)} (unchanged {len(same)}, changed {len(changed)}), '
      f'added {len(added)}, removed {len(removed)}')
print(f'added code lines: {sum(code_lines(new[p]) for p in added)}')


def show(title, paths, rev):
    print(f'\n== {title}')
    groups = defaultdict(list)
    for p in sorted(paths):
        d = p.rsplit('/', 1)[0] if '/' in p else '.'
        groups[d].append((p.rsplit('/', 1)[-1], code_lines(rev[p])))
    for d, items in groups.items():
        print(f'  {d} ({len(items)}, {sum(n for _, n in items)} lines): ' +
              ', '.join(f'{m[:-5]} {n}' for m, n in items))


def norm(blob):
    text = git('cat-file', '-p', blob).replace('\r\n', '\n')
    text = re.sub(r'\{-.*?-\}', '', text, flags=re.S)
    return [l.rstrip() for l in text.splitlines()
            if l.strip() and not l.strip().startswith('--')]


code_same = [p for p in changed if norm(new[p]) == norm(old[p])]
print(f'\nchanged only in comments, blank lines or line ends: {len(code_same)}: '
      + ', '.join(code_same))
show('unchanged', same, new)
show('changed', changed, new)
show('added', added, new)
show('removed', removed, old)
