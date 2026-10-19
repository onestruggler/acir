"""Write CCX+H/NaturalP/ThreeWire/RecInst.agda: each circuit generator
against the decoding of its encoding, as a loop."""
import os
from decoder import AUX, REL
from emit_family import Names, elements, chain_src, INST_HEADER, MODP, TW
from syn import M
from deriv import mm

HH02 = ('CX1', 'HH1', 'CX1', 'HH1', 'CX1', 'HH0', 'CX1', 'HH1', 'CX1', 'HH1', 'CX1')
assert M(HH02) == M(('H0', 'H2'))
LX = {0: [('T', ('X0',))], 1: [('T', ('X1',))], 2: [('T', ('X2',))],
      3: [('T', ('CX0',))], 4: [('T', ('CX1',))], 5: [('T', ('CCX0',))],
      6: ['H'], 7: ['H', ('T', ('HH0',))], 8: ['H', ('T', HH02)]}
# check against the matrices of the generators
TOK = {0: ('X0',), 1: ('X1',), 2: ('X2',), 3: ('CX0',), 4: ('CX1',), 5: ('CCX0',), 6: ('H0',), 7: ('H1',), 8: ('H2',)}
for g, els in LX.items():
    w = ()
    for e in els:
        w += ('H0',) if e == 'H' else e[1]
    assert M(w) == M(TOK[g]), g

names = Names()
priv, pub = [], []
for r in REL['relations']:
    if r['source'] != 'roundtrip':
        continue
    g = r['generator']
    lel = LX[g]
    rel = elements([AUX[i] for i in r['auxiliary_encoding']])
    L, Lp, body, c = chain_src(names, lel, rel)
    priv.append(f'  L{g} L{g}′ : List El\n  L{g} = {L}\n  L{g}′ = {Lp}')
    pub.append(f'i{g} : 3 ⊢ ⦅ map ⟦_⟧ₑ (L{g} ++ invL L{g}′) ⦆ ≈ ε\n'
               f'i{g} = run {{map ⟦_⟧ₑ (L{g} ++ invL L{g}′)}}\n    ( {body} )\n')
    print(g, dict(c))
text = INST_HEADER.format(fam='the recovery of the generators', lo=0, hi=8, modp=MODP, mod='Recovery')
text += 'private\n' + '\n'.join(names.defs) + '\n\n'
text += 'private\n' + '\n'.join(priv) + '\n\n' + '\n'.join(pub)
open(os.path.join(TW, 'Inst', 'Recovery.agda'), 'w', encoding='utf-8').write(text)
print('wrote recovery')
