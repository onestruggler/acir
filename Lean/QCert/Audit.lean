/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Axiom audit of Table 1

Run `./check.sh QCert/Audit.lean`. Each result should depend
only on Lean's standard axioms (propext, Classical.choice, Quot.sound).
`sorryAx` marks an unfinished proof, including any inherited dependency.
Keep the individual statements here: a single conjunction would hide
which row is still incomplete.
-/
import QCert.Table1
import QCert.RealCliffordCH.Sec8.D.N13.E336x
import QCert.RealCliffordCH.Sec8.D.W4.ConjCommBase

#print axioms QCert.Greylyn.presentation
#print axioms QCert.BianSelingerUn.presentation
#print axioms QCert.LiRossSelinger.presentation
#print axioms QCert.LiRossSelinger.presentationL
#print axioms QCert.HadamardPi.theorem_4_14
#print axioms QCert.Clement2019.theorem_4_1
#print axioms QCert.SelingerClifford.presentation
#print axioms QCert.QuditClifford.theorem_4_10
#print axioms QCert.RealStabilizer.presentation
#print axioms QCert.CNOTDihedral.presentation
#print axioms QCert.PhaseAffine.theorem1ℂ
#print axioms QCert.PhaseAffine.theorem2_linℂ
#print axioms QCert.PhaseAffine.theorem2_quadℂ
#print axioms QCert.PhaseAffine.theorem2_cubeℂ
#print axioms QCert.CliffordT2.theorem_2_1_U
#print axioms QCert.CliffordCS3.theorem_3_1_U
#print axioms QCert.CliffordCS3.rsData
#print axioms QCert.CliffordCS3.Cosets.hyp_a
#print axioms QCert.CliffordCS3.Cosets.hyp_b
#print axioms QCert.CliffordCS3.Two.Fast.derivable_of_check
#print axioms QCert.runWideChunks_sound
#print axioms QCert.RealCliffordCH.presentation
#print axioms QCert.ToffoliHadamard.theorem_5_2
#print axioms QCert.ToffoliHadamard.rK_independent
#print axioms QCert.ToffoliHadamard.theorem_6_3
#print axioms QCert.QutritClifford.presentation
#print axioms QCert.QutritClifford.card_cliffordGroup

#print axioms QCert.Minimality.clifford_complete
#print axioms QCert.Minimality.realClifford_complete
#print axioms QCert.Minimality.qutritClifford_complete
#print axioms QCert.Minimality.cliffordT_complete
#print axioms QCert.Minimality.cliffordCS_complete
#print axioms QCert.Minimality.cliffordCS_complete_of_source
#print axioms QCert.Minimality.CliffordCS.complete₂
#print axioms QCert.Minimality.cnotDihedral_complete
#print axioms QCert.Minimality.clifford_minimal
#print axioms QCert.Minimality.realClifford_minimal
#print axioms QCert.Minimality.qutritClifford_minimalUpTo_two
#print axioms QCert.Minimality.cliffordT_minimalUpTo_one
#print axioms QCert.Minimality.cliffordCS_minimalUpTo_two
#print axioms QCert.Minimality.cnotDihedral_minimal
#print axioms QCert.Minimality.cliffordT_independent_two
#print axioms QCert.Minimality.cliffordCS_independent_I

-- Auxiliary results, audited separately from the main theorems.
#print axioms QCert.RealCliffordCH.Sec8.item_a
#print axioms QCert.RealCliffordCH.Sec8.D.d139
#print axioms QCert.RealCliffordCH.Sec8.D.d140
#print axioms QCert.RealCliffordCH.Sec8.D.d145
#print axioms QCert.RealCliffordCH.Sec8.D.d146
#print axioms QCert.RealCliffordCH.Sec8.D.d147
#print axioms QCert.RealCliffordCH.Sec8.D.d141
#print axioms QCert.RealCliffordCH.Sec8.D.d142
#print axioms QCert.RealCliffordCH.Sec8.D.d143
#print axioms QCert.RealCliffordCH.Sec8.D.d144
#print axioms QCert.RealCliffordCH.Sec8.D.d148a
#print axioms QCert.RealCliffordCH.Sec8.D.d214
#print axioms QCert.RealCliffordCH.Sec8.D.d215
#print axioms QCert.RealCliffordCH.Sec8.D.d216
#print axioms QCert.RealCliffordCH.Sec8.D.d217
#print axioms QCert.RealCliffordCH.Sec8.D.d218
#print axioms QCert.RealCliffordCH.Sec8.D.d219
#print axioms QCert.RealCliffordCH.Sec8.D.d220
#print axioms QCert.RealCliffordCH.Sec8.D.d221
#print axioms QCert.RealCliffordCH.Sec8.D.d222
#print axioms QCert.RealCliffordCH.Sec8.D.d223
#print axioms QCert.RealCliffordCH.Sec8.D.d224
#print axioms QCert.RealCliffordCH.Sec8.D.d225
#print axioms QCert.RealCliffordCH.Sec8.D.d226
#print axioms QCert.RealCliffordCH.Sec8.D.d227
#print axioms QCert.RealCliffordCH.Sec8.D.d228
#print axioms QCert.RealCliffordCH.Sec8.D.d229
#print axioms QCert.RealCliffordCH.Sec8.D.d230
#print axioms QCert.RealCliffordCH.Sec8.D.d231
#print axioms QCert.RealCliffordCH.Sec8.D.d232
#print axioms QCert.RealCliffordCH.Sec8.D.d233
#print axioms QCert.RealCliffordCH.Sec8.D.d234
#print axioms QCert.RealCliffordCH.Sec8.D.d235
#print axioms QCert.RealCliffordCH.Sec8.D.d236
#print axioms QCert.RealCliffordCH.Sec8.D.d237
#print axioms QCert.RealCliffordCH.Sec8.D.d238
#print axioms QCert.RealCliffordCH.Sec8.D.d239
#print axioms QCert.RealCliffordCH.Sec8.D.d240
#print axioms QCert.RealCliffordCH.Sec8.D.d241
#print axioms QCert.RealCliffordCH.Sec8.D.d242
#print axioms QCert.RealCliffordCH.Sec8.D.d243
#print axioms QCert.RealCliffordCH.Sec8.D.d244
#print axioms QCert.RealCliffordCH.Sec8.D.d245
#print axioms QCert.RealCliffordCH.Sec8.D.d246
#print axioms QCert.RealCliffordCH.Sec8.D.d247
#print axioms QCert.RealCliffordCH.Sec8.D.d248
#print axioms QCert.RealCliffordCH.Sec8.D.N13.comm335_ge5
#print axioms QCert.RealCliffordCH.Sec8.D.N13.comm336_ge5
#print axioms QCert.RealCliffordCH.Sec8.D.N13.comm340_ge5
#print axioms QCert.RealCliffordCH.Sec8.D.eq335
#print axioms QCert.RealCliffordCH.Sec8.D.eq336
#print axioms QCert.RealCliffordCH.Sec8.D.eq337
#print axioms QCert.RealCliffordCH.Sec8.D.eq340
#print axioms QCert.RealCliffordCH.Sec8.D.eq345
#print axioms QCert.RealCliffordCH.Sec8.D.d267
#print axioms QCert.RealCliffordCH.Sec8.D.d268

#print axioms QCert.RealCliffordCH.Sec8.D.W4.t242Case0
#print axioms QCert.RealCliffordCH.Sec8.D.W4.t242Case1
#print axioms QCert.RealCliffordCH.Sec8.D.W4.t243Case0
#print axioms QCert.RealCliffordCH.Sec8.D.W4.t243Case1
#print axioms QCert.RealCliffordCH.Sec8.D.W4.t244Case0
#print axioms QCert.RealCliffordCH.Sec8.D.W4.t245Case0
