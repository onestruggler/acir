{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD036 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D036 (Sᴰ : SD036) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ124-CK03)

-- The lemmas of other derivation modules (DSig).
private
  lem-sym-ab-at022330 : Ws → St 756
  lem-sym-ab-at022330 = pickᴰ 0 Sᴰ
  lem-sym-ab-at03122130 : Ws → St 910
  lem-sym-ab-at03122130 = pickᴰ 1 Sᴰ
  lem-sym-ab-at0314213240 : Ws → St 912
  lem-sym-ab-at0314213240 = pickᴰ 2 Sᴰ
  lem-sym-ab-at03243240 : Ws → St 914
  lem-sym-ab-at03243240 = pickᴰ 3 Sᴰ
  lem-sym-ab-at0330 : Ws → St 757
  lem-sym-ab-at0330 = pickᴰ 4 Sᴰ
  lem-sym-ab-at02132130 : Ws → St 917
  lem-sym-ab-at02132130 = pickᴰ 5 Sᴰ
  lem-sym-ab-at02142140 : Ws → St 1209
  lem-sym-ab-at02142140 = pickᴰ 6 Sᴰ
  lem-sym-ab-at022440 : Ws → St 1210
  lem-sym-ab-at022440 = pickᴰ 7 Sᴰ
  lem-sym-ab-at0410233241 : Ws → St 1251
  lem-sym-ab-at0410233241 = pickᴰ 8 Sᴰ
  lem-sym-ab-at04122041 : Ws → St 1212
  lem-sym-ab-at04122041 = pickᴰ 9 Sᴰ
  lem-sym-ab-at04122140 : Ws → St 1028
  lem-sym-ab-at04122140 = pickᴰ 10 Sᴰ
  lem-sym-ab-at04133140 : Ws → St 1252
  lem-sym-ab-at04133140 = pickᴰ 11 Sᴰ
  lem-sym-ab-at04233240 : Ws → St 1217
  lem-sym-ab-at04233240 = pickᴰ 12 Sᴰ
  lem-CSdu-box-2-at0214203143 : Ws → St 1253
  lem-CSdu-box-2-at0214203143 = pickᴰ 13 Sᴰ
  lem-box-cP-at0214233041 : Ws → St 751
  lem-box-cP-at0214233041 = pickᴰ 14 Sᴰ
  lem-box-cP-at0214213043 : Ws → St 843
  lem-box-cP-at0214213043 = pickᴰ 15 Sᴰ
  lem-sym-bc-at02132031 : Ws → St 1169
  lem-sym-bc-at02132031 = pickᴰ 16 Sᴰ
  lem-sym-bc-at02132130 : Ws → St 1170
  lem-sym-bc-at02132130 = pickᴰ 17 Sᴰ
  lem-sym-bc-at03122031 : Ws → St 1171
  lem-sym-bc-at03122031 = pickᴰ 18 Sᴰ
  lem-sym-bc-at03122130 : Ws → St 1172
  lem-sym-bc-at03122130 = pickᴰ 19 Sᴰ
  lem-sym-bc-at041041 : Ws → St 1223
  lem-sym-bc-at041041 = pickᴰ 20 Sᴰ
  lem-sym-bc-at0413213240 : Ws → St 1254
  lem-sym-bc-at0413213240 = pickᴰ 21 Sᴰ
  lem-sym-bc-at0440 : Ws → St 1228
  lem-sym-bc-at0440 = pickᴰ 22 Sᴰ
  lem-pairs-at03243240 : Ws → St 1164
  lem-pairs-at03243240 = pickᴰ 23 Sᴰ
  lem-Kdu-box-at0214203143 : Ws → St 1232
  lem-Kdu-box-at0214203143 = pickᴰ 24 Sᴰ
  lem-Ku-box-at0214203143 : Ws → St 1233
  lem-Ku-box-at0214203143 = pickᴰ 25 Sᴰ
  lem-box-perm-1423-at0214203143 : Ws → St 1205
  lem-box-perm-1423-at0214203143 = pickᴰ 26 Sᴰ
  lem-pairs-at0413213240 : Ws → St 1243
  lem-pairs-at0413213240 = pickᴰ 27 Sᴰ
  lem-box-perm-1324-at0214203143 : Ws → St 1246
  lem-box-perm-1324-at0214203143 = pickᴰ 28 Sᴰ
  lem-pairs-at02132031 : Ws → St 1255
  lem-pairs-at02132031 = pickᴰ 29 Sᴰ
  lem-pairs-at022440 : Ws → St 1256
  lem-pairs-at022440 = pickᴰ 30 Sᴰ
  lem-pairs-at03122031 : Ws → St 1257
  lem-pairs-at03122031 = pickᴰ 31 Sᴰ
  lem-pairs-at0412233140 : Ws → St 1248
  lem-pairs-at0412233140 = pickᴰ 32 Sᴰ
  lem-pairs-at0413203241 : Ws → St 1258
  lem-pairs-at0413203241 = pickᴰ 33 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ []) (wl 1441 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wp 1294 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx2-4301 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (Toff201 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wl 1442 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q7 : Ws → Eqn
  q7 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q8 : Ws → Eqn
  q8 c4 = eqn (S0 ∷ CCZ234 ∷ []) (CCZ234 ∷ S0 ∷ []) (c₁ (S) (CCZ ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK01 ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wl 1443 (lit c4))

-- F4-CS0-K1 @0440: 21 steps
lem-F4-CS0-K1-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K1-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx4-2031 ∷ []) (Bx4-0231 ∷ []) (lem-sym-ab-at04122041 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx4-0231 ∷ []) (Bx4-0321 ∷ []) (lem-sym-bc-at041041 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx4-0321 ∷ []) (Bx4-3021 ∷ []) (lem-sym-ab-at0410233241 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx4-3021 ∷ []) (Bx4-2130 ∷ []) (lem-pairs-at0413203241 c4)

-- box-perm-1432 @04122041: 4 steps
lem-box-perm-1432-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-box-perm-1432-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-2130 ∷ [])
  (rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-4130 ∷ []) (Bx2-1430 ∷ []) (lem-sym-ab-at02142140 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx2-1430 ∷ []) (Bx2-3014 ∷ []) (lem-pairs-at022440 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx2-3014 ∷ []) (Bx2-3104 ∷ []) (lem-sym-bc-at02132031 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx2-3104 ∷ []) (Bx2-1304 ∷ []) (lem-sym-ab-at02132130 c4)

-- box-perm-2341 @02142140: 4 steps
lem-box-perm-2341-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-box-perm-2341-at02142140 c4 = derive (Bx2-4130 ∷ []) (Bx2-1304 ∷ [])
  (rw 0 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw 0 (q17 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx2-1304 ∷ []) (Bx2-3104 ∷ []) (lem-sym-ab-at022330 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-3104 ∷ []) (Bx2-3014 ∷ []) (lem-sym-bc-at02132130 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx2-3014 ∷ []) (Bx2-1430 ∷ []) (lem-pairs-at02132031 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx2-1430 ∷ []) (Bx2-4130 ∷ []) (lem-sym-ab-at022440 c4)

-- box-perm-4123 @022330: 4 steps
lem-box-perm-4123-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-box-perm-4123-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-4130 ∷ [])
  (rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx4-2130 ∷ []) (Bx4-1230 ∷ []) (lem-sym-ab-at04122140 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx4-1230 ∷ []) (Bx4-1320 ∷ []) (lem-sym-bc-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx4-1320 ∷ []) (Bx4-3120 ∷ []) (lem-sym-ab-at04233240 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx4-3120 ∷ []) (Bx4-2031 ∷ []) (lem-pairs-at0413213240 c4)

-- box-perm-1432 @04122140: 4 steps
lem-box-perm-1432-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-1432-at04122140 c4 = derive (Bx4-2130 ∷ []) (Bx4-2031 ∷ [])
  (rw 0 (q22 c4) ∷
   rw 0 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (CK02 ∷ []) (CS02⁻ ∷ K2⁻ ∷ CS02⁻ ∷ K2 ∷ CS02⁻ ∷ []) (wl 1723 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS02⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K2 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (K2⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0214203143 c4)

-- CKu-box-2 @0214203143: 7 steps
lem-CKu-box-2-at0214203143 : Ws → ⟪ (CK02 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CK02 ∷ []) ⟫ʷ
lem-CKu-box-2-at0214203143 c4 = derive (CK02 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CK02 ∷ [])
  (rw 0 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q28 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q26 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx3-4120 ∷ []) (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx3-1420 ∷ []) (Bx3-2014 ∷ []) (lem-pairs-at03243240 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx3-2014 ∷ []) (Bx3-2104 ∷ []) (lem-sym-bc-at03122031 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx3-2104 ∷ []) (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4)

-- box-perm-2341 @0314213240: 4 steps
lem-box-perm-2341-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2341-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-1204 ∷ [])
  (rw 0 (q30 c4) ∷
   rw 0 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx3-1204 ∷ []) (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx3-2104 ∷ []) (Bx3-2014 ∷ []) (lem-sym-bc-at03122130 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx3-2014 ∷ []) (Bx3-1420 ∷ []) (lem-pairs-at03122031 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx3-1420 ∷ []) (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4)

-- box-perm-4123 @0330: 4 steps
lem-box-perm-4123-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-4123-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-4120 ∷ [])
  (rw 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 0 (q36 c4) ∷
   rw 0 (q37 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx4-3120 ∷ []) (Bx4-3210 ∷ []) (lem-sym-bc-at0413213240 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx4-3210 ∷ []) (Bx4-2310 ∷ []) (lem-sym-ab-at04133140 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx4-2310 ∷ []) (Bx4-1023 ∷ []) (lem-pairs-at0412233140 c4)

-- box-perm-2431 @0413213240: 3 steps
lem-box-perm-2431-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-2431-at0413213240 c4 = derive (Bx4-3120 ∷ []) (Bx4-1023 ∷ [])
  (rw 0 (q38 c4) ∷
   rw 0 (q39 c4) ∷
   rw 0 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ []) (wl 1574 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wp 1519 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-box-perm-1324-at0214203143 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-4103 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (Toff203 ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wl 1739 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ124 ∷ K3 ∷ []) (K3 ∷ CCZ124 ∷ []) (wl 1576 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CK03 ∷ []) (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (S0 ∷ CCZ124 ∷ []) (CCZ124 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q49 : Ws → Eqn
  q49 c4 = eqn (CK03 ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wl 1577 (lit c4))

-- F4-CS0-K3 @0440: 21 steps
lem-F4-CS0-K3-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K3-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q41 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q49 c4) ∷ []) Eq.refl
