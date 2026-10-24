{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD044 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D044 (Sᴰ : SD044) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS14-CCZ023 : Ws → St 219
  lem-comm-CS14-CCZ023 = pickᴰ 0 Sᴰ
  lem-comm-CSd14-CCZ023 : Ws → St 224
  lem-comm-CSd14-CCZ023 = pickᴰ 1 Sᴰ
  lem-comm-CX30-TOFF214 : Ws → St 1026
  lem-comm-CX30-TOFF214 = pickᴰ 2 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 3 Sᴰ
  lem-comm-CX31-TOFF204 : Ws → St 1552
  lem-comm-CX31-TOFF204 = pickᴰ 4 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 149
  lem-box-tQ-at0310213442 = pickᴰ 5 Sᴰ
  lem-box-tQ-at0314203142 : Ws → St 310
  lem-box-tQ-at0314203142 = pickᴰ 6 Sᴰ
  lem-box-tQ-at02142041 : Ws → St 349
  lem-box-tQ-at02142041 = pickᴰ 7 Sᴰ
  lem-box-tQ-at0314203241 : Ws → St 400
  lem-box-tQ-at0314203241 = pickᴰ 8 Sᴰ
  lem-box-cP-at0213243041 : Ws → St 889
  lem-box-cP-at0213243041 = pickᴰ 9 Sᴰ
  lem-box-cP-at0214233041 : Ws → St 890
  lem-box-cP-at0214233041 = pickᴰ 10 Sᴰ
  lem-box-cP-at02132031 : Ws → St 1212
  lem-box-cP-at02132031 = pickᴰ 11 Sᴰ
  lem-box-perm-2314-at0213243041 : Ws → St 1553
  lem-box-perm-2314-at0213243041 = pickᴰ 12 Sᴰ
  lem-box-perm-1324-at02142041 : Ws → St 1554
  lem-box-perm-1324-at02142041 = pickᴰ 13 Sᴰ
  lem-box-perm-2314-at0312243041 : Ws → St 1555
  lem-box-perm-2314-at0312243041 = pickᴰ 14 Sᴰ
  lem-box-perm-3124-at02142041 : Ws → St 1556
  lem-box-perm-3124-at02142041 = pickᴰ 15 Sᴰ
  lem-box-perm-3124-at0314203241 : Ws → St 1557
  lem-box-perm-3124-at0314203241 = pickᴰ 16 Sᴰ
  lem-box-perm-4123-at0314203142 : Ws → St 1558
  lem-box-perm-4123-at0314203142 = pickᴰ 17 Sᴰ
  lem-box-box-1-at0213243041 : Ws → St 1559
  lem-box-box-1-at0213243041 = pickᴰ 18 Sᴰ
  lem-box-perm-1243-at03102132 : Ws → St 1560
  lem-box-perm-1243-at03102132 = pickᴰ 19 Sᴰ
  lem-box-perm-1243-at0310213442 : Ws → St 1561
  lem-box-perm-1243-at0310213442 = pickᴰ 20 Sᴰ
  lem-box-perm-2341-at0312243041 : Ws → St 1562
  lem-box-perm-2341-at0312243041 = pickᴰ 21 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 400 (lem-box-tQ-at0314203241 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1182 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 1333 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1334 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 1056 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 1174 c4
  q7 : Ws → Eqn
  q7 c4 = wlE 831 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 501 c4
  q9 : Ws → Eqn
  q9 c4 = sE 1552 (lem-comm-CX31-TOFF204 c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 1183 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 1152 c4
  q12 : Ws → Eqn
  q12 c4 = wpE 272 c4
  q13 : Ws → Eqn
  q13 c4 = wlE 1335 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 1143 c4
  q15 : Ws → Eqn
  q15 c4 = wlE 765 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 1321 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wlE 763 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = wpE 1184 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 181 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = sE 349 (lem-box-tQ-at02142041 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1554 (lem-box-perm-1324-at02142041 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 890 (lem-box-cP-at0214233041 c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 1071 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 774 c4
  q26 : Ws → Eqn
  q26 c4 = wpE 1185 c4
  q27 : Ws → Eqn
  q27 c4 = eqn (ℓ "亏丟") (ℓ "丟亏") (c₃ (Toffᵗ) (K • iI))
  q28 : Ws → Eqn
  q28 c4 = wlE 1329 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (ℓ "亏乽") (ℓ "乽亏") (c₃ (Toffᵗ) (CX₀₁))
  q30 : Ws → Eqn
  q30 c4 = wpE 1186 c4
  q31 : Ws → Eqn
  q31 c4 = wpE 1187 c4
  q32 : Ws → Eqn
  q32 c4 = eqn (ℓ "亏丞") (ℓ "丞亏") (c₃ (Toffᵗ) (K))
  q33 : Ws → Eqn
  q33 c4 = wlE 452 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 1171 c4
  q35 : Ws → Eqn
  q35 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))
  q36 : Ws → Eqn
  q36 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))
  q37 : Ws → Eqn
  q37 c4 = wpE 90 c4
  q38 : Ws → Eqn
  q38 c4 = wpE 1188 c4
  q39 : Ws → Eqn
  q39 c4 = wpE 1189 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 687 c4
  q41 : Ws → Eqn
  q41 c4 = wpE 161 c4
  q42 : Ws → Eqn
  q42 c4 = sE 1556 (lem-box-perm-3124-at02142041 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1557 (lem-box-perm-3124-at0314203241 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1559 (lem-box-box-1-at0213243041 c4)
  q45 : Ws → Eqn
  q45 c4 = sE 1555 (lem-box-perm-2314-at0312243041 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1553 (lem-box-perm-2314-at0213243041 c4)

-- Tu-box @0314203241: 83 steps
lem-Tu-box-at0314203241 : Ws → ⟪ (ℓ "亱佾亱") ⟫ʷ ≈ ⟪ (ℓ "佾余") ⟫ʷ
lem-Tu-box-at0314203241 c4 = derive (ℓ "亱佾亱") (ℓ "佾余")
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
  q47 c4 = sE 1560 (lem-box-perm-1243-at03102132 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 149 (lem-box-tQ-at0310213442 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 1212 (lem-box-cP-at02132031 c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 550 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 1342 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 543 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 1343 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = sE 224 (lem-comm-CSd14-CCZ023 c4)
  q55 : Ws → Eqn
  q55 c4 = sE 219 (lem-comm-CS14-CCZ023 c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 1344 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 1345 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 1194 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 1346 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 760 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wlE 898 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = sE 1026 (lem-comm-CX30-TOFF214 c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 1195 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 923 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 762 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 301 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 48 c4
  q68 : Ws → Eqn
  q68 c4 = wlE 560 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 332 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 1347 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 686 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 302 c4
  q73 : Ws → Eqn
  q73 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))
  q74 : Ws → Eqn
  q74 c4 = wlE 451 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 1173 c4
  q76 : Ws → Eqn
  q76 c4 = sE 1561 (lem-box-perm-1243-at0310213442 c4)

-- box-box-3 @03102132: 105 steps
lem-box-box-3-at03102132 : Ws → ⟪ (ℓ "佤似") ⟫ʷ ≈ ⟪ (ℓ "似佤") ⟫ʷ
lem-box-box-3-at03102132 c4 = derive (ℓ "佤似") (ℓ "似佤")
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
  q77 c4 = sE 1562 (lem-box-perm-2341-at0312243041 c4)
  q78 : Ws → Eqn
  q78 c4 = sE 310 (lem-box-tQ-at0314203142 c4)
  q79 : Ws → Eqn
  q79 c4 = sE 889 (lem-box-cP-at0213243041 c4)
  q80 : Ws → Eqn
  q80 c4 = wlE 508 (lit c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 1328 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wlE 1353 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 433 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wpE 776 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 1354 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = sE 1558 (lem-box-perm-4123-at0314203142 c4)

-- box-box-1 @0312243041: 105 steps
lem-box-box-1-at0312243041 : Ws → ⟪ (ℓ "佴佋") ⟫ʷ ≈ ⟪ (ℓ "佋佴") ⟫ʷ
lem-box-box-1-at0312243041 c4 = derive (ℓ "佴佋") (ℓ "佋佴")
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
