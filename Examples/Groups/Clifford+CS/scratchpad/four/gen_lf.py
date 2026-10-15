# The fourth four-wire rule, Barenco's decomposition of the hybrid gadget
# (t_lf.LF), as Agda text for Syntactics: shortcuts whose bodies are the
# macro letters' spellings (mac.agda_of) letter for letter, so that a
# rule step of the emitted derivations is `ax lf` up to by-assoc.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
os.environ.setdefault('DERIV_QUIET', '1')
from mac import mac_tree, agda_of
from deriv import norm, show
from dec import barenco, G_ki, inverse
from t_lf import SQRT_V, SQRT_VI, L2, LF, HD

REN = {'CK₁₀': 'CK′', 'Toffᵗ': 'Toff₃'}

def sp(g):
    s = agda_of(mac_tree(g))
    for a, b in REN.items(): s = s.replace(a, b)
    return s

def body(word):
    return ' • '.join(sp(g) if ' • ' not in sp(g) else f'({sp(g)})' for g in word)

def cs_count(word):
    from mac import word_of
    return sum(1 for g in word for b in word_of(mac_tree(g)) if b[0] == 'CS')

if __name__ == '__main__':
    bar = norm(barenco('SSKS', 1, 2, 0)); nb = len(bar)
    hd = norm(HD)
    assert hd[:nb] == bar and hd[nb] == ('CK', 3, 0)
    bari = hd[nb + 1:-2]; cki = hd[-2:]
    pieces = [L2(1, 2, 0, -1), [('TOFF', 3, 1, 2)], L2(1, 3, 0, 1), [('TOFF', 3, 1, 2)], L2(1, 3, 0, -1)]
    assert norm([g for p in pieces for g in p]) == norm(LF(1, 2, 3, 0))
    out = {}
    out['Bar₁₂'] = body(bar); out['Bar₁₂⁻¹'] = body(bari)
    out['CK₃₀'] = body([('CK', 3, 0)]); out['CK₃₀⁻¹'] = body(cki)
    out['L₁₂W⁻¹'] = body(pieces[0]); out['L₁₃W'] = body(pieces[2]); out['L₁₃W⁻¹'] = body(pieces[4])
    for k, v in out.items(): print(f'{k} = {v}\n')
    print('CS count: lhs', cs_count(hd), 'rhs', cs_count(norm(LF(1, 2, 3, 0))))

NAME = {('CS', 0, 1): 'CS', ('CS', 0, 2): 'CS₀₂', ('CS', 0, 3): 'CS₀₃',
        ('CK', 1, 0): 'CK₁₀′', ('CK', 2, 0): 'CK₂₀′', ('CK', 3, 0): 'CK₃₀′',
        ('CX', 1, 2): 'CX₁₂', ('CX', 1, 3): 'CX₁₃',
        ('S', 1): 'S ↑', ('S', 2): 'S ↑ ↑', ('S', 3): 'S ↑ ↑ ↑', ('TOFF', 3, 1, 2): 'Toff₃₁₂'}

def named(word): return ' • '.join(NAME[g] for g in word)

def agda_block():
    bar = norm(barenco('SSKS', 1, 2, 0)); nb = len(bar)
    hd = norm(HD); bari = hd[nb + 1:-2]; cki = hd[-2:]
    pieces = [L2(1, 2, 0, -1), L2(1, 3, 0, 1), L2(1, 3, 0, -1)]
    def wrap(name, ty, word, width=70):
        toks = [NAME[g] for g in word]
        lines = []; cur = f'{name} = '
        ind = ' ' * len(cur)
        for i, t in enumerate(toks):
            piece = t + (' •' if i < len(toks) - 1 else '')
            if len(cur) + len(piece) + 1 > width and cur.strip():
                lines.append(cur.rstrip()); cur = ind
            cur += piece + ' '
        lines.append(cur.rstrip())
        return '\n'.join(lines)
    out = []
    out.append(wrap('Bar₁₂', '', bar))
    out.append(wrap('Bar₁₂⁻¹', '', bari))
    out.append(wrap('L₁₂W⁻¹', '', pieces[0]))
    out.append(wrap('L₁₃W', '', pieces[1]))
    out.append(wrap('L₁₃W⁻¹', '', pieces[2]))
    out.append('CK₃₀⁻¹′ = ' + named(cki))
    return '\n\n'.join(out)

if __name__ == '__main__' and 'agda' in sys.argv:
    print(agda_block())

LET = {'CS': '𝕤', 'CK': '𝕜', 'S': '𝕚'}
def ctl_of(g):
    """(control, letter) of a controlled one-wire letter onto wire 0."""
    if g[0] == 'S': return g[1], '𝕚'
    c = [w for w in g[1:] if w != 0][0]
    return c, LET[g[0]]

def bar_expr(word):
    """a Barenco-shaped macro word as C_c segments and CX letters."""
    out = []; seg = []; c0 = None
    def flush():
        if seg: out.append(f'C{SUB[c0]} ({" ∷ ".join(seg)} ∷ [])')
    for g in word:
        if g[0] == 'CX':
            flush(); seg.clear(); out.append({(1, 2): 'CX₁₂', (1, 3): 'CX₁₃'}[g[1:]])
            continue
        c, l = ctl_of(g)
        if c0 is not None and c != c0 and seg: flush(); seg.clear()
        c0 = c; seg.append(l)
    flush()
    return ' • '.join(out)
SUB = {1: '₁', 2: '₂', 3: '₃'}

if __name__ == '__main__' and 'bar' in sys.argv:
    bar = norm(barenco('SSKS', 1, 2, 0)); nb = len(bar)
    hd = norm(HD); bari = hd[nb + 1:-2]
    for name, w in [('Bar₁₂', bar), ('Bar₁₂⁻¹', bari), ('L₁₂W⁻¹', L2(1, 2, 0, -1)), ('L₁₃W', L2(1, 3, 0, 1)), ('L₁₃W⁻¹', L2(1, 3, 0, -1))]:
        print(name, '=', bar_expr(w)); print()
