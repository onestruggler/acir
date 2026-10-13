"""The box relations of Appendix C as typed rewriting tables.

Imports boxrel.py with X, Z and the boxes made symbolic, splits every
right-hand side into its new boxes and its residual dirty gates, types the
residual by the wire labels of Definition 4.1, re-checks the typed form
against the matrices, and can emit the tables for Tables.agda.
"""
import qt
from qt import eq
import boxes as _boxes

REAL = {'X': qt.X, 'Z': qt.Z}
REALBOX = {k: getattr(_boxes, k) for k in 'ABCDEF'}

qt.X = lambda w=0: [('X', w)]
qt.Z = lambda w=0: [('Z', w)]
for k in 'ABD':
    setattr(_boxes, k, (lambda k: lambda a, b, w=0: [('box', k, a % 3, b % 3, w)])(k))
for k in 'CEF':
    setattr(_boxes, k, (lambda k: lambda b, w=0: [('box', k, b % 3, w)])(k))

import boxrel
R = boxrel.R


def expand(toks):
    out = []
    for t in toks:
        if t[0] in ('X', 'Z'):
            out += REAL[t[0]](t[1])
        elif t[0] == 'box':
            k, args, w = t[1], t[2:-1], t[-1]
            out += expand(REALBOX[k](*args, w=w))
        else:
            out.append(t)
    return out


def split(rhs):
    boxes_ = [t for t in rhs if t[0] == 'box']
    rest = [t for t in rhs if t[0] != 'box']
    nb = 0
    while nb < len(rhs) and rhs[nb][0] == 'box':
        nb += 1
    assert boxes_ == rhs[:nb], rhs
    return boxes_, rest

# ---------------------------------------------------------------- typing
# A residual token in time order on given wires -> typed constructor names.
# Expand X and Z into letters where the label is 1 (H, S allowed).
def letters(tok):
    """X or Z on a wire, as H/S letters (time order)."""
    return REAL[tok[0]](tok[1])

def nus(k):
    return k

class Bad(Exception):
    pass

def type_W0(res):        # one wire, label 2
    out = []
    for t in res:
        if t == ('nu',): out.append('iν')
        elif t == ('S', 0): out.append('iS')
        elif t == ('X', 0): out.append('iX')
        elif t == ('Z', 0): out.append('iZ')
        else: raise Bad(t)
    return out

def type_CO(res):        # one wire, label 3
    out = []
    for t in res:
        if t == ('nu',): out.append('coν')
        elif t == ('S', 0): out.append('coS')
        elif t == ('Z', 0): out.append('coZ')
        else: raise Bad(t)
    return out

def type_Post(res):      # wire 1 label 2 (into the ladder), wire 0 label 1
    out = []
    for t in res:
        if t == ('nu',): out.append('pν')
        elif t[0] in ('S', 'X', 'Z') and t[1] == 1:
            out.append('(pin i%s)' % t[0])
        elif t == ('CZ', 0): out.append('pstr')
        elif t == ('H', 0): out.append('pH')
        elif t == ('S', 0): out.append('pS')
        elif t[0] in ('X', 'Z') and t[1] == 0:
            out += type_Post(letters(t))
        else: raise Bad(t)
    return out

def type_SCO(res):       # CZ below a C: wire 0 label 1
    out = []
    for t in res:
        if t == ('nu',): out.append('scν')
        elif t == ('CZ', 0): out.append('scC')
        elif t == ('H', 0): out.append('scH')
        elif t == ('S', 0): out.append('scS')
        elif t[0] in ('X', 'Z') and t[1] == 0: out += type_SCO(letters(t))
        else: raise Bad(t)
    return out

Q01 = {('H', 0): 'qh₀', ('S', 0): 'qs₀', ('H', 1): 'qh₁', ('S', 1): 'qs₁', ('CZ', 0): 'qc₀'}
def type_Post2(res):     # wire 2 label 2, wires 0, 1 label 1
    out = []
    for t in res:
        if t == ('nu',): out.append('qν')
        elif t[0] in ('S', 'X', 'Z') and t[1] == 2: out.append('(qin i%s)' % t[0])
        elif t == ('CZ', 1): out.append('qstr')
        elif t in Q01: out.append('(qd %s)' % Q01[t])
        elif t[0] in ('X', 'Z') and t[1] in (0, 1): out += type_Post2(letters(t))
        else: raise Bad(t)
    return out

def type_O2(res):        # wire 1 label 1, wire 0 label 4
    out = []
    for t in res:
        if t == ('nu',): out.append('oν')
        elif t == ('H', 1): out.append('oh₁')
        elif t == ('S', 1): out.append('os₁')
        elif t[0] in ('X', 'Z') and t[1] == 1: out += type_O2(letters(t))
        elif t == ('S', 0): out.append('oS₀')
        elif t == ('Z', 0): out.append('oZ₀')
        else: raise Bad(t)
    return out

O3 = {('H', 1): 'o3h₁', ('S', 1): 'o3s₁', ('H', 2): 'o3h₂', ('S', 2): 'o3s₂', ('CZ', 1): 'o3c₁',
      ('S', 0): 'o3S₀', ('Z', 0): 'o3Z₀', ('nu',): 'o3ν'}
def type_O3(res):        # wires 1, 2 label 1, wire 0 label 4
    out = []
    for t in res:
        if t in O3: out.append(O3[t])
        elif t[0] in ('X', 'Z') and t[1] in (1, 2): out += type_O3(letters(t))
        else: raise Bad(t)
    return out

# Typed tokens back to time-order letters (for the self-check).
def untype(frame, names):
    toks = []
    for nm in names:
        nm = nm.strip('()')
        if nm in ('iν', 'coν', 'pν', 'scν', 'qν', 'oν', 'o3ν'):
            toks.append(('nu',)); continue
        if frame == 'W0':
            toks += expand([{'iS': ('S', 0), 'iX': ('X', 0), 'iZ': ('Z', 0)}[nm]])
        elif frame == 'CO':
            toks += expand([{'coS': ('S', 0), 'coZ': ('Z', 0)}[nm]])
        elif frame == 'Post':
            if nm.startswith('pin '): toks += expand([(nm[-1], 1)])
            else: toks.append({'pstr': ('CZ', 0), 'pH': ('H', 0), 'pS': ('S', 0)}[nm])
        elif frame == 'SCO':
            toks.append({'scC': ('CZ', 0), 'scH': ('H', 0), 'scS': ('S', 0)}[nm])
        elif frame == 'Post2':
            if nm.startswith('qin '): toks += expand([(nm[-1], 2)])
            elif nm == 'qstr': toks.append(('CZ', 1))
            else: toks.append({v: k for k, v in Q01.items()}[nm[3:]])
        elif frame == 'O2':
            toks += expand([{'oh₁': ('H', 1), 'os₁': ('S', 1), 'oS₀': ('S', 0), 'oZ₀': ('Z', 0)}[nm]])
        elif frame == 'O3':
            toks += expand([{v: k for k, v in O3.items()}[nm]])
    return toks

# ---------------------------------------------------------------- tables
SUB = '₀₁₂'
def bname(t):
    return t[1] + ''.join(SUB[i] for i in t[2:-1])

ENTRIES = {}   # family -> list of (key, value-string, check-info)

def add(fam, key, val):
    ENTRIES.setdefault(fam, []).append((key, val))

def oplist(names):
    """typed names in time order -> Agda list in operator order"""
    names = list(reversed(names))
    if not names:
        return '[]'
    return ' ∷ '.join(names) + ' ∷ []'

def selfcheck(n, lhs, newboxes, frame, typed, rhs_time):
    rhs2 = expand(newboxes) + untype(frame, typed)
    assert eq(expand(lhs), rhs2, n), (lhs, typed)

def build():
    for fig, name, n, lhs, rhs in R:
        nb, res = split(rhs)
        fam = name.split('.')[0]
        try:
            if name.startswith(('H.A', 'S.A')):
                g = 'gH' if name[0] == 'H' else 'gS'
                ty = type_W0(res); frame = 'W0'
                add('ruleA', f'{bname(lhs[1])} {g}', f'{bname(nb[0])} , {oplist(ty)}')
            elif name.startswith(('S.C', 'Z.C', 'X.C')):
                ty = type_CO(res); frame = 'CO'
                add('ruleC', f'{bname(lhs[1])} i{name[0]}', f'{bname(nb[0])} , {oplist(ty)}')
            elif name.startswith('S.E'):
                ty = []; frame = 'W0'
                add('ruleE', f'{bname(lhs[1])}', f'{bname(nb[0])}')
            elif name.startswith('Z.E'):
                ty = []; frame = 'W0'
                assert nb == [lhs[1]] and res == [('Z', 0)]
                continue
            elif name.startswith('Z.F'):
                ty = []; frame = 'W0'
                add('ruleF', f'{bname(lhs[1])}', f'{bname(nb[0])}')
            elif fig == 23:
                ty = type_Post(res); frame = 'Post'
                a = bname(lhs[1])
                if len(nb) == 1:
                    add('ruleAup', a, f'inj₁ ({bname(nb[0])} , {oplist(ty)})')
                else:
                    add('ruleAup', a, f'inj₂ ({bname(nb[0])} , {bname(nb[1])} , {oplist(ty)})')
            elif fig in (24, 25, 26, 27):
                ty = type_Post(res); frame = 'Post'
                a, b = bname(lhs[1]), bname(lhs[2])
                if len(nb) == 2:
                    add('ruleAB', f'{a} {b}', f'inj₁ ({bname(nb[0])} , {bname(nb[1])} , {oplist(ty)})')
                else:
                    assert nb[0][-1] == 1
                    add('ruleAB', f'{a} {b}', f'inj₂ ({bname(nb[0])} , {oplist(ty)})')
            elif fig in (28, 29, 30, 31, 32):
                ty = type_Post(res); frame = 'Post'
                inp = {28: '(w1 gH)', 29: '(w1 gS)', 30: '(w0 iS)', 31: '(w0 iX)', 32: '(w0 iZ)'}[fig]
                add('ruleB', f'{bname(lhs[-1])} {inp}', f'{bname(nb[0])} , {oplist(ty)}')
            elif fig == 33:
                ty = type_SCO(res); frame = 'SCO'
                add('ruleSC', bname(lhs[1]), f'{bname(nb[0])} , {oplist(ty)}')
            elif fig in (34, 35):
                ty = type_O2(res); frame = 'O2'
                g = 'gH' if fig == 34 else 'gS'
                add('ruleD', f'{bname(lhs[-1])} {g}', f'{bname(nb[0])} , {oplist(ty)}')
            elif fig == 36:
                ty = type_O2(res); frame = 'O2'
                continue      # stated uniformly in Tables
            elif fig == 37:
                ty = type_O2(res); frame = 'O2'
                add('ruleCD', bname(lhs[1]), f'{bname(nb[0])} , {oplist(ty)}')
            elif fig in (38, 39, 40, 41, 42):
                ty = type_Post2(res); frame = 'Post2'
                b0, b1 = bname(lhs[1]), bname(lhs[2])
                add('ruleBB', f'{b0} {b1}', f'{bname(nb[0])} , {bname(nb[1])} , {oplist(ty)}')
            elif fig == 43:
                ty = type_Post2(res); frame = 'Post2'
                add('ruleS', bname(lhs[1]), f'{bname(nb[0])} , {oplist(ty)}')
            elif fig == 44:
                ty = type_O3(res); frame = 'O3'
                d1, d0 = bname(lhs[1]), bname(lhs[2])
                add('ruleDD', f'{d1} {d0}', f'{bname(nb[0])} , {bname(nb[1])} , {oplist(ty)}')
            else:
                raise Bad(('unknown', fig, name))
        except Bad as e:
            print('UNTYPABLE', fig, name, e)
            raise
        selfcheck(n, lhs, nb, frame, ty, rhs)

if __name__ == '__main__':
    build()
    for fam, es in ENTRIES.items():
        print(fam, len(es))
