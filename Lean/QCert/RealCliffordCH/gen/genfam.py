import sys
from fig6 import instances
import itertools
INST = {(f, idx) for f, idx, _, _ in instances()}
def Z(v): return 'HadamardPi.Gen.Z %s' % v
def X(a, b, h): return 'HadamardPi.Gen.X %s %s %s' % (a, b, h)
def H(a, b, h): return 'HadamardPi.Gen.H %s %s %s' % (a, b, h)
def GL(xs): return '([%s] : List G4)' % ', '.join(xs)
# family: (vars, binder string, hyps names, lhs list, rhs list)
FAM = {
 'b1': (['a','b'], '(hab : a ≠ b)', ['hab'], [Z('a'), Z('b')], [Z('b'), Z('a')]),
 'b2': (['a','b','c'], '(hbc : b < c) (hab : a ≠ b) (hac : a ≠ c)', ['hbc','hab','hac'],
        [Z('a'), X('b','c','hbc')], [X('b','c','hbc'), Z('a')]),
 'b3': (['a','b','c','d'], '(hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)',
        ['hab','hcd','hac','had','hbc','hbd'], [X('a','b','hab'), X('c','d','hcd')], [X('c','d','hcd'), X('a','b','hab')]),
 'b4': (['a','b','c'], '(hbc : b < c) (hab : a ≠ b) (hac : a ≠ c)', ['hbc','hab','hac'],
        [Z('a'), H('b','c','hbc')], [H('b','c','hbc'), Z('a')]),
 'b5': (['a','b','c','d'], '(hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)',
        ['hab','hcd','hac','had','hbc','hbd'], [X('a','b','hab'), H('c','d','hcd')], [H('c','d','hcd'), X('a','b','hab')]),
 'b6': (['a','b','c','d'], '(hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)',
        ['hab','hcd','hac','had','hbc','hbd'], [H('a','b','hab'), H('c','d','hcd')], [H('c','d','hcd'), H('a','b','hab')]),
 'c1': (['a','b'], '(hab : a < b)', ['hab'], [Z('a'), X('a','b','hab')], [X('a','b','hab'), Z('b')]),
 'c2': (['a','b','c'], '(hab : a < b) (hbc : b < c)', ['hab','hbc'],
        [X('b','c','hbc'), X('a','b','hab')], [X('a','b','hab'), X('a','c','(hab.trans hbc)')]),
 'c3': (['a','b','c'], '(hab : a < b) (hbc : b < c)', ['hab','hbc'],
        [X('a','c','(hab.trans hbc)'), X('b','c','hbc')], [X('b','c','hbc'), X('a','b','hab')]),
 'c4': (['a','b','c'], '(hab : a < b) (hbc : b < c)', ['hab','hbc'],
        [H('b','c','hbc'), X('a','b','hab')], [X('a','b','hab'), H('a','c','(hab.trans hbc)')]),
 'c5': (['a','b','c'], '(hab : a < b) (hbc : b < c)', ['hab','hbc'],
        [H('a','c','(hab.trans hbc)'), X('b','c','hbc')], [X('b','c','hbc'), H('a','b','hab')]),
 'd1': (['a','b'], '(hab : a < b)', ['hab'], [Z('a'), Z('b'), H('a','b','hab')], [H('a','b','hab'), Z('a'), Z('b')]),
 'd2': (['a','b'], '(hab : a < b)', ['hab'], [Z('b'), H('a','b','hab')], [H('a','b','hab'), X('a','b','hab')]),
 'd3': (['a','b','c','d'], '(hab : a < b) (hcd : c < d) (hac : a < c) (hbd : b < d) (hbc : b ≠ c)',
        ['hab','hcd','hac','hbd','hbc'],
        [H('c','d','hcd'), H('a','c','hac'), H('b','d','hbd')] * 4, [H('a','b','hab'), H('c','d','hcd')]),
}
out = ['''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma 7.5, by equation of Figure 6

Generated: each equation (b1)–(d3) of Figure 6 at every admissible choice of
indices in `0, …, 3`, dispatched to the decoded instances of `Lemma75`.
-/
import QCert.RealCliffordCH.Lemma75

namespace QCert.RealCliffordCH.Two

''']
for f, (vs, binders, hyps, l, r) in FAM.items():
    out.append('/-- Decoding Equation (%s). -/' % f)
    out.append('theorem fam_%s (%s : Fin 4) %s :\n    EG %s %s := by' % (f, ' '.join(vs), binders, GL(l), GL(r)))
    out.append('  ' + ' <;> '.join('fin_cases %s' % v for v in vs))
    for idx in itertools.product(range(4), repeat=len(vs)):
        if (f, idx) in INST:
            out.append('  · exact dI_%s_%s' % (f, '_'.join(map(str, idx))))
        else:
            out.append('  · exfalso; revert %s; decide' % ' '.join(hyps))
    out.append('')
out.append('end QCert.RealCliffordCH.Two\n')
open(sys.argv[1],'w',encoding='utf-8',newline='\n').write('\n'.join(out))
print('ok')
