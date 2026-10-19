"""Write Natural/ThreeWire/Circuit/TopCosets.agda: each coset of the top
table as a ThreeQubit coset (`τ`) with a label in the nine letters,
rep c = label · rep_TQ (τ c) as matrices.

    python3 -B emit_separate.py
"""
import sys
sys.path.insert(0, '..')
import pipe as Pp
import top as TP
from emit_circuit import glist, fin9, HEADER, MOD, ROOT

def apply(word, v):
    for g in reversed(word):
        v = TP.gs.actions[g](v)
    return v

def monomial(word):
    """The signed permutation of a word, or None."""
    out = []
    for i in range(8):
        v = tuple(4 if k == i else 0 for k in range(8))
        u = apply(word, v)
        nz = [(k, x) for k, x in enumerate(u) if x]
        if len(nz) != 1 or abs(nz[0][1]) != 4:
            return None
        out.append((nz[0][0], 1 if nz[0][1] > 0 else -1))
    return tuple(out)

def main():
    rels, levels, tc, live, table, _ = TP.build()
    d8 = levels[-1]
    tq = TP.tq_reps()                     # matrix-order gate lists, coset order
    taus, labels = [], []
    for c in live:
        r = tc.rep[c]
        hit = None
        for t, rt in enumerate(tq):
            g = monomial(tuple(r) + tuple(reversed(rt)))   # r · rt⁻¹
            if g is not None:
                hit = (t, g)
                break
        assert hit, c
        t, g = hit
        lab = d8.canon(g)
        assert Pp.sp(lab) == g
        taus.append(t)
        labels.append(lab)
    assert sorted(taus) == list(range(135))
    L = [HEADER.format(title='The cosets of the top table as ThreeQubit cosets.'),
         f'module {MOD}.TopCosets where\n',
         'open import Data.Bool.Base using (true ; false ; _∧_)',
         'open import Data.Fin.Base using (Fin)',
         'open import Data.Fin using (#_)',
         'open import Data.List.Base using (List ; [] ; _∷_)',
         'open import Data.Vec.Base using (Vec ; [] ; _∷_)',
         'open import Relation.Binary.PropositionalEquality using (refl)',
         'open import Examples.Groups.CCX+HH.ThreeQubit.Cosets',
         '']
    L.append('τT : Vec Coset 135')
    L.append('τT = ' + ' ∷ '.join(f'c{t:03d}' for t in taus) + ' ∷ []')
    L.append('')
    L.append('τinv : Coset → Fin 135')
    for k, t in enumerate(taus):
        L.append(f'τinv c{t:03d} = # {k}')
    L.append('')
    L.append('λT : Vec (List (Fin 9)) 135')
    L.append('λT =')
    for lab in labels:
        L.append(f'  ({fin9(lab)}) ∷')
    L.append('  []')
    open(f'{ROOT}/TopCosets.agda', 'w', encoding='utf-8').write('\n'.join(L) + '\n')
    print('written; labels max', max(map(len, labels)))

if __name__ == '__main__':
    main()
