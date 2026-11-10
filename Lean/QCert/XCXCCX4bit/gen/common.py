"""Shared helpers of the Lean generators of QCert/XCXCCX4bit.

The generators are ports of the Agda development's (Examples/Groups/
XCXCCX-4bit/gen), writing Lean instead of Agda.  They read the same inputs,
from the Agda folder: the searches of `derive.py`/`appA.py`/`width2.py`
(imported and run, as the Agda's generators run them) and the saved search
results (`width3_lemmas.json`).  Those produce each derivation as Agda text
(`name = derive (lhs) (rhs) (steps) refl`, Kit's engine); `lemma` parses such
a block and writes it as the Lean `Eqn.pad n <| derive [lhs] [rhs] [steps]
(by decide +kernel)` of `QCert.XCXCCX4bit.Kit`, step for step.  Like the
Agda's generators, they are untrusted: Lean checks what they write.

Run them with WSL's python3 from this folder, e.g.
`python3 mk_involutions.py`.
"""
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent                       # Lean/QCert/XCXCCX4bit
REPO = LEAN.parents[2]                   # the repository root
AGDA = REPO / 'Examples' / 'Groups' / 'XCXCCX-4bit'
AGEN = AGDA / 'gen'

sys.path.insert(0, str(AGEN))

COPYRIGHT = '/-\nCopyright (c) 2026 QCert contributors. All rights reserved.\n\n'

# --------------------------------------------------------------------- names


def lean_name(a):
    """An Agda lemma name `xaxa⁼`, `CX²⁼`, `em=me⁼`, `cjX0-01⁼` as a Lean name
    `xaxaE`, `CXsqE`, `em_eq_meE`, `cjX0_01E`."""
    assert a.endswith('⁼'), a
    b = a[:-1].replace('²', 'sq').replace('=', '_eq_').replace('-', '_')
    assert re.fullmatch(r'[A-Za-z0-9_σ]+', b), a
    return b + 'E'


LETTERS = {'Xₗ': 'Xₗ', 'CXₗ': 'CXₗ', 'CCXₗ': 'CCXₗ', 'σₗ': 'σₗ'}

# ---------------------------------------------------------------- the parser

TOKEN = re.compile(r'\(|\)|∷|\[\]|[^\s()]+')


def tokens(s):
    return TOKEN.findall(s)


class Parser:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def next(self):
        x = self.t[self.i]
        self.i += 1
        return x

    def expect(self, x):
        y = self.next()
        assert y == x, (x, y, self.t[max(0, self.i - 8):self.i + 3])

    # a list `[]` or `(a ∷ b ∷ … ∷ [])`, of items read by `item`
    def lst(self, item):
        if self.peek() == '[]':
            self.next()
            return []
        self.expect('(')
        out = []
        while True:
            if self.peek() == '[]':
                self.next()
                break
            out.append(item())
            self.expect('∷')
        self.expect(')')
        return out

    def letter(self):
        x = self.next()
        assert x in LETTERS, x
        s = LETTERS[x]
        while self.peek() == '↥':
            self.next()
            s += '.up'
        return s

    def letters(self):
        return self.lst(self.letter)

    # an equation term
    def eqn(self):
        x = self.next()
        if x == '(':
            e = self.eqn_app()
            self.expect(')')
            return e
        return lean_name(x)

    def eqn_app(self):
        x = self.peek()
        if x == 'sym⁼':
            self.next()
            return 'symE %s' % paren(self.eqn())
        if x == 'lift⁼':
            self.next()
            return 'liftE %s' % paren(self.eqn())
        if x == 'by2':
            self.next()
            l = self.letters()
            r = self.letters()
            self.expect('refl')
            return 'by2 %s %s (by decide +kernel)' % (llist(l), llist(r))
        return self.eqn()

    def step(self):
        x = self.next()
        if x == '(':
            s = self.step_body()
            self.expect(')')
            return s
        raise AssertionError(x)

    def step_body(self):
        x = self.next()
        if x == 'perm':
            return 'perm %s' % llist(self.letters())
        if x == 'rw':
            i = int(self.next())
            return 'rw %d %s' % (i, paren(self.eqn()))
        raise AssertionError(x)


def paren(e):
    return e if re.fullmatch(r'[A-Za-z0-9_σₗ.]+', e) else '(%s)' % e


def llist(xs):
    return '[' + ', '.join(xs) + ']'


WIDTH = {'(₁₊ n)': 1, '(₂₊ n)': 2, '(₃₊ n)': 3, '(₄₊ n)': 4}


def parse_lemma(text):
    """An Agda derivation block: (doc lines, name, width, lhs, rhs, steps)."""
    lines = text.rstrip('\n').split('\n')
    docs = []
    while lines[0].startswith('--'):
        docs.append(lines.pop(0)[2:].strip())
    head = lines.pop(0)
    m = re.fullmatch(r'(\S+) : Eqn (\(.*\))', head)
    assert m, head
    name, width = m.group(1), WIDTH[m.group(2)]
    body = ' '.join(lines)
    toks = tokens(body)
    p = Parser(toks)
    p.expect(name)
    p.expect('=')
    p.expect('derive')
    lhs = p.letters()
    rhs = p.letters()
    # the steps: `(s ∷ s ∷ … ∷ [])`, each s `perm (…)` or `rw i e`, not
    # parenthesised individually
    steps = []
    if p.peek() == '[]':
        p.next()
    else:
        p.expect('(')
        while True:
            if p.peek() == '[]':
                p.next()
                break
            x = p.next()
            if x == 'perm':
                steps.append('perm %s' % llist(p.letters()))
            elif x == 'rw':
                i = int(p.next())
                steps.append('rw %d %s' % (i, paren(p.eqn())))
            else:
                raise AssertionError((name, x))
            p.expect('∷')
        p.expect(')')
    p.expect('refl')
    assert p.peek() is None, (name, p.t[p.i:])
    return docs, name, width, lhs, rhs, steps


def lemma(text, indent='  '):
    """The Lean text of an Agda derivation block."""
    docs, name, width, lhs, rhs, steps = parse_lemma(text)
    out = []
    if docs:
        out.append('/-- %s -/' % ' '.join(docs))
    out.append('def %s : Eqn (n + %d) := Eqn.pad n <| derive' % (lean_name(name), width))
    out.append(indent + llist(lhs))
    out.append(indent + llist(rhs))
    if steps:
        out.append(indent + '[' + (',\n' + indent + ' ').join(steps) + ']')
    else:
        out.append(indent + '[]')
    out.append(indent + '(by decide +kernel)')
    return '\n'.join(out) + '\n'


def agda_blocks(txt):
    """The derivation blocks (with their comment lines) of Agda text, in
    order."""
    blocks = []
    lines = txt.split('\n')
    i = 0
    while i < len(lines):
        m = re.fullmatch(r'(\S+⁼) : Eqn \(.*\)', lines[i])
        if m:
            j = i
            while j > 0 and lines[j - 1].startswith('-- ') and not lines[j - 1].startswith('-----'):
                j -= 1
            k = i + 1
            while k < len(lines) and lines[k].strip() != 'refl':
                k += 1
            blocks.append('\n'.join(lines[j:k + 1]) + '\n')
            i = k + 1
        else:
            i += 1
    return blocks


def write(rel, text):
    path = LEAN / rel
    path.write_text(text, encoding='utf-8', newline='\n')
    print('wrote', path, text.count('\n'), 'lines')
