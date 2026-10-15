# Agda names and expressions of the five-wire macro letters (prim5's
# normalised joint letters): constructor names of Five.Letters.Mac, the
# expressions of their spellings (a box by the name of its definition),
# and the shifted spellings that the window tables and the structural
# commutations need.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mac5
import prim5
from prim5 import tree, is_box, is_scalar, norm1
import derivn

def lit_expr(name, s):
    base = mac5.LITERAL[name][1]
    if s == 0: return base
    if ' ' in base: base = '(' + base + ')'
    return base + ' ↑' * s

def tree_expr(t, boxname=None):
    """the Agda expression of a spelling tree; a box (a 'cat' tree) by the
    name of its definition when boxname is given, else inline."""
    if t[0] == 'lit': return lit_expr(t[1], t[2])
    if t[0] == 'conj':
        _, k, inner = t
        swp = 'Swap' + ' ↑' * k
        ie = tree_expr(inner, boxname)
        if ' ' in ie: ie = f'({ie})'
        return f'{swp} • {ie} • {swp}'
    raise ValueError(t)

def paren(e): return f'({e})' if ' ' in e else e

def letter_expr(g, boxes=True):
    """the expression of ⟪ g ⟫: a box by its definition's name (boxes=True)
    or its unfolding inline."""
    if is_box(g):
        if boxes: return box_def_name(g)
        us = [norm1(h) for h in derivn.unfold1(g)]
        return cat_expr([letter_expr(h, False) for h in us])
    return tree_expr(tree(g))

def cat_expr(es):
    """right-nested concatenation, as ⟪_⟫ʷ nests a list."""
    if not es: return 'ε'
    if len(es) == 1: return es[0]
    return ' • '.join(paren(e) for e in es)

def word_expr(letters, boxes=True):
    return cat_expr([letter_expr(g, boxes) for g in letters])

# ------------------------------------------------------------ names
def wires(ws): return ''.join(str(w) for w in ws)

def mname(g):
    k = g[0]
    if k == 'iI': return 'ι' + (str(g[1]) if g[1] else '')
    if k == 'iIi': return 'ι' + (str(g[1]) if g[1] else '') + '⁻'
    if k in ('Sd', 'Kd', 'CSd', 'CKd'): return k[:-1] + wires(g[1:]) + '⁻'
    if k == 'SWAP': return 'Sw' + wires(g[1:])
    if k == 'TOFF': return 'Toff' + wires(g[1:])
    if k in ('BOX', 'BOXd'):
        return ('Bx' if k == 'BOX' else 'Bx⁻') + str(g[1]) + '-' + wires(g[2:])
    if k in ('SBOX', 'SBOXd', 'KBOX', 'KBOXd'):
        pre = {'SBOX': 'Sb', 'SBOXd': 'Sb⁻', 'KBOX': 'Kb', 'KBOXd': 'Kb⁻'}[k]
        return f'{pre}{g[1]}-{g[2]}-{wires(g[3])}-{g[4]}'
    return k + wires(g[1:])

def box_def_name(g): return 'b-' + mname(g)

# ------------------------------------------------------------ shifted spellings
def shift_down(g, m):
    """the letter with wire m deleted (wires above m down one)."""
    if is_scalar(g):
        s = g[1]; assert s != m; return (g[0], s - 1 if s > m else s)
    return norm1(derivn.relabel_word([g], {w: (w - 1 if w > m else w) for w in range(5)})[0])

def downk(g, i):
    if is_scalar(g): return (g[0], g[1] - i)
    return norm1(derivn.relabel_word([g], {w: w - i for w in range(5)})[0])

if __name__ == '__main__':
    AX = ([('CS', 0, 1), ('TOFF', 1, 3, 4), ('CS', 1, 2), ('TOFF', 1, 3, 4), ('CSd', 1, 2)],
          [('TOFF', 1, 3, 4), ('CS', 1, 2), ('TOFF', 1, 3, 4), ('CSd', 1, 2), ('CS', 0, 1)])
    for side in AX: print(word_expr(side))
