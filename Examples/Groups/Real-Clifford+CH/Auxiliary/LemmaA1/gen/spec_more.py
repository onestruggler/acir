import sys
sys.path.insert(0, '.')
from gen_chain import Line, W

out = []

L = Line(W('Hab Zb'), ['ab'], 'd2†')
L.ins(2, 'Hab').ins(3, 'Xab').d2r(2).cn(1).cn(0).expect('Xab Hab')
out.append('-- (d2†): a sign on the second index of a Hadamard, moved before it.\n' +
           L.agda('d2†', '∀ {a b : Fin N} → a ≢ b → H a b • −1 b ≈ X a b • H a b', '{a} {b} ab'))

L = Line(W('Za Zb Hab'), ['ab'], 'd1')
(L.d2(1).rule(2, 'Xab', 'Xba', 'e1 ab')
  .rule(1, 'Hab Xba', 'Xba Hba', 'axiom (e2* (sy ab))')
  .ins(1, 'Hba').rule(0, 'Za Hba', 'Hba Xba', 'axiom (d2 (sy ab))')
  .d2r(2).cn(3)
  .rule(1, 'Xba', 'Xab', 'e1 (sy ab)')
  .rule(0, 'Hba Xab', 'Xab Hab', 'axiom (e2* ab)')
  .ins(0, 'Hab').d2r(1).cn(2).sw(1)
  .expect('Hab Za Zb'))
out.append('-- (d1): the two signs of a Hadamard pass it.\n' +
           L.agda('d1', '∀ {a b : Fin N} → a ≢ b → −1 a • −1 b • H a b ≈ H a b • −1 a • −1 b', '{a} {b} ab'))
print('\n'.join(out))
