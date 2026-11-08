"""Shared helpers of the Lean generators of QCert/ToffoliHadamardTietze.

The generators are ports of the Agda development's (`tools/` of
Examples/Groups/CCX+H-3qubit-Tietze), writing Lean instead of Agda.  They
read the same inputs, from the Agda folder: the authors' TIETZE2 files
(`*.rels`, `*.derivs`), the saved search results (`kb-certificates.json`,
`permutation-certificates.json`) and the relations and matrices of the
Agda's `generate.py`, which is imported for its data (it writes nothing
when imported).  Like the Agda's, they are untrusted: Lean checks what they
write.

Generated certificates are grouped into the same chunk modules (B000, ...)
as the Agda's `bundle.py` wrote, read from the Agda chunks, so that the two
developments correspond file for file.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent                      # Lean/QCert/ToffoliHadamardTietze
REPO = LEAN.parents[2]                  # the repository root
AGDA = REPO / 'Examples' / 'Groups' / 'CCX+H-3qubit-Tietze'
TOOLS = AGDA / 'tools'
NS = 'QCert.ToffoliHadamardTietze'

sys.path.insert(0, str(TOOLS))
import generate as ag  # noqa: E402  (the Agda generator, for its data)

GATES = ag.GATES
DEFS = ag.DEFS
RELATIONS = ag.RELATIONS


def word(xs):
    """A word of letters (a string or a list) as a Lean term."""
    if isinstance(xs, str):
        xs = xs.split()
    return ' * '.join(xs) if xs else '1'


def pword(xs):
    """A word, parenthesised unless it is one letter or ε."""
    s = word(xs)
    return s if ' ' not in s else f'({s})'


def header(doc, imports, opens=''):
    s = '/-\nCopyright (c) 2026 QCert contributors. All rights reserved.\n\n' + doc.strip() + '\n-/\n'
    s += ''.join(f'import {NS}.{m}\n' if not m.startswith(('QCert', 'Mathlib')) else f'import {m}\n'
                  for m in imports)
    s += f'\nnamespace {NS}\n'
    if opens:
        s += opens + '\n'
    return s + '\n'


def write(rel, text):
    path = LEAN / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8', newline='\n')


def agda_chunks(folder):
    """The Agda's chunk modules of a folder: [(chunk, [nested module, ...])],
    in order."""
    out = []
    for path in sorted((AGDA / folder).glob('B*.agda')):
        names = re.findall(r'^module (\S+) where$', path.read_text(encoding='utf-8'), re.M)
        out.append((path.stem, [n for n in names if '.' not in n]))
    return out
