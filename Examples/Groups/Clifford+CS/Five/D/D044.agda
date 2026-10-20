{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D044 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0433 ; wl0452 ; wl0508 ; wl0763 ; wl0765 ; wl0831 ; wl1321 ; wl1328 ; wl1329 ; wl1333 ; wl1334 ; wl1335 ; wp0090 ; wp0161 ; wp0272 ; wp0501 ; wp0687 ; wp0774 ; wp1056 ; wp1071 ; wp1143 ; wp1152 ; wp1171 ; wp1173 ; wp1174 ; wp1182 ; wp1183 ; wp1184 ; wp1185 ; wp1186 ; wp1187 ; wp1188 ; wp1189 ; wl0332 ; wl0451 ; wl0560 ; wl0760 ; wl0762 ; wl0898 ; wl1342 ; wl1343 ; wl1344 ; wl1345 ; wl1346 ; wl1347 ; wl1353 ; wl1354 ; wp0048 ; wp0301 ; wp0302 ; wp0543 ; wp0550 ; wp0686 ; wp0776 ; wp0923 ; wp1194 ; wp1195)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02142041 ; lem-box-tQ-at0314203241)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-box-cP-at0213243041 ; lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at02132031 ; lem-box-perm-2314-at0213243041)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at02142041 ; lem-box-perm-2314-at0312243041 ; lem-box-perm-3124-at02142041 ; lem-box-perm-3124-at0314203241 ; lem-box-perm-4123-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-box-1-at0213243041 ; lem-box-perm-1243-at03102132 ; lem-box-perm-1243-at0310213442 ; lem-box-perm-2341-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX30-TOFF214 ; lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX31-TOFF204)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Toff234 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) (wp1182 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ123 ∷ CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ []) (wl1333 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (Toff234 ∷ CCZ123 ∷ Toff234 ∷ []) (wl1334 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1056 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ014 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS34 ∷ Toff204 ∷ []) (Toff204 ∷ CS34 ∷ []) (wp0501 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CX31 ∷ Toff204 ∷ []) (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS14⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS14⁻ ∷ []) (wp1183 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS14 ∷ Toff204 ∷ []) (Toff204 ∷ CS14 ∷ []) (wp1152 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ123 ∷ []) (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl1335 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ []) (wl1321 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff204 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ []) (wp1184 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0181 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx2-4031 ∷ []) (Bx2-4301 ∷ []) (lem-box-perm-1324-at02142041 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx2-4301 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ234 ∷ []) (wp1071 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (Toff304 ∷ []) (wp1185 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Toff201 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (K • iI))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS03 ∷ Toff201 ∷ []) (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff201 ∷ CX34 ∷ []) (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS04⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS04 ∷ Toff201 ∷ []) (Toff201 ∷ CS04 ∷ []) (wp1187 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff201 ∷ K3 ∷ []) (K3 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (K))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) (wl0452 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ234 ∷ CX40 ∷ []) (CX40 ∷ CCZ234 ∷ []) (wp1171 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff304 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff304 ∷ []) (wp1188 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ014 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0161 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx2-4031 ∷ []) (Bx2-3401 ∷ []) (lem-box-perm-3124-at02142041 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx3-4021 ∷ []) (Bx3-2401 ∷ []) (lem-box-perm-3124-at0314203241 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-box-box-1-at0213243041 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx3-2401 ∷ []) (Bx3-4021 ∷ []) (lem-box-perm-2314-at0312243041 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-3401 ∷ []) (Bx2-4031 ∷ []) (lem-box-perm-2314-at0213243041 c4)

-- Tu-box @0314203241: 83 steps
lem-Tu-box-at0314203241 : Ws → ⟪ (Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Bx2-4031 ∷ []) ⟫ʷ
lem-Tu-box-at0314203241 c4 = derive (Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ []) (Bx3-4021 ∷ Bx2-4031 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 0 (q24 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 2 (q31 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q26 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 0 (q23 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 2 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 7 (q16 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 0 (q44 c4) ∷
   rw 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0142 ∷ []) (lem-box-perm-1243-at03102132 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx2-3014 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ234 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl1342 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ023 ∷ CS34 ∷ []) (CS34 ∷ CCZ023 ∷ []) (wp0543 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ []) (wl1343 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ234 ∷ []) (wl1344 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ023 ∷ []) (wl1345 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ012 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1194 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (Toff301 ∷ []) (wl1346 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CS13 ∷ Toff214 ∷ []) (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CX30 ∷ Toff214 ∷ []) (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS01⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CS01 ∷ Toff214 ∷ []) (Toff214 ∷ CS01 ∷ []) (wp0923 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) (wp0048 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ []) (wl0560 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Toff301 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff301 ∷ []) (wl1347 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ []) (wp0302 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ234 ∷ []) (wl0451 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0124 ∷ []) (lem-box-perm-1243-at0310213442 c4)

-- box-box-3 @03102132: 105 steps
lem-box-box-3-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-3-at03102132 c4 = derive (Bx3-0124 ∷ Bx2-3014 ∷ []) (Bx2-3014 ∷ Bx3-0124 ∷ [])
  (rw 0 (q47 c4) ∷
   rw 0 (q48 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw⁻ 8 (q53 c4) ∷
   rw 7 (q54 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 5 (q55 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 4 (q58 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw 7 (q62 c4) ∷
   rw 6 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw 4 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q59 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 10 (q67 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 6 (q55 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   rw 5 (q70 c4) ∷
   rw 6 (q71 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 11 (q60 c4) ∷
   rw 10 (q61 c4) ∷
   rw 9 (q62 c4) ∷
   rw 8 (q63 c4) ∷
   rw 7 (q62 c4) ∷
   rw 6 (q64 c4) ∷
   rw 5 (q65 c4) ∷
   rw 6 (q59 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 2 (q49 c4) ∷
   rw⁻ 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 3 (q55 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 1 (q49 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 0 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw 6 (q61 c4) ∷
   rw 5 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q59 c4) ∷
   rw 4 (q66 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 5 (q68 c4) ∷
   rw 4 (q55 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw 7 (q62 c4) ∷
   rw 6 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw 4 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 2 (q66 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 3 (q75 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 1 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Bx3-2401 ∷ []) (Bx3-4012 ∷ []) (lem-box-perm-2341-at0312243041 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Bx2-3401 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ234 ∷ CS13 ∷ []) (CS13 ∷ CCZ234 ∷ []) (wl0433 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ234 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ []) (wp0776 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ []) (wl1354 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Bx3-4012 ∷ []) (Bx3-2401 ∷ []) (lem-box-perm-4123-at0314203142 c4)

-- box-box-1 @0312243041: 105 steps
lem-box-box-1-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-box-box-1-at0312243041 c4 = derive (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  (rw 0 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw 6 (q82 c4) ∷
   rw⁻ 10 (q83 c4) ∷
   rw⁻ 9 (q84 c4) ∷
   rw 8 (q35 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q82 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q85 c4) ∷
   rw⁻ 3 (q79 c4) ∷
   rw 3 (q79 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw 8 (q35 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 5 (q37 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 5 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 6 (q31 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 2 (q79 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   rw⁻ 8 (q83 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 5 (q82 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q85 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw 1 (q79 c4) ∷
   rw⁻ 0 (q24 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 2 (q31 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q26 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 0 (q79 c4) ∷
   rw 2 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw 1 (q86 c4) ∷ []) Eq.refl
