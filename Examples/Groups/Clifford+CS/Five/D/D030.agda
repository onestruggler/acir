{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D030 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0415 ; wl0452 ; wl0508 ; wl0763 ; wl0765 ; wl1258 ; wl1260 ; wl1266 ; wl1273 ; wl1321 ; wl1330 ; wl1331 ; wp0129 ; wp0161 ; wp0366 ; wp0377 ; wp0897 ; wp1143 ; wp1166 ; wp1169 ; wp1170 ; wp1171 ; wp1172 ; wp1173 ; wp1174 ; wp1189 ; wl0271 ; wl0451 ; wl0560 ; wp0048 ; wp0301 ; wp0302 ; wp0550 ; wl0671 ; wl0674 ; wl0982 ; wl1360 ; wl1361 ; wl1362 ; wl1363 ; wl1364 ; wl1365 ; wl1366 ; wp0029 ; wp0513 ; wp0698 ; wp0997 ; wp1203)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at02102441 ; lem-sym-ab-at02142041 ; lem-sym-ab-at0310243241 ; lem-sym-ab-at0312243041 ; lem-sym-ab-at0314203241 ; lem-sym-ab-at03143041)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-sym-bc-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at03122031 ; lem-box-cP-at0312243041 ; lem-pairs-at03102132 ; lem-pairs-at0310213442 ; lem-sym-bc-at02132031 ; lem-sym-bc-at02132130 ; lem-sym-bc-at03122031 ; lem-sym-bc-at03122130 ; lem-sym-bc-at0314203241)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1243-at021021 ; lem-box-perm-1243-at0210213443 ; lem-box-perm-2341-at0213243041 ; lem-box-perm-4123-at0214203143 ; lem-pairs-at02102441 ; lem-pairs-at02132130 ; lem-pairs-at0310243241 ; lem-pairs-at03122130 ; lem-pairs-at0312243041 ; lem-pairs-at03143041)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX20-TOFF314 ; lem-comm-CX24-TOFF301)

-- box-box-1 @0213243041: 105 steps
lem-box-box-1-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-box-box-1-at0213243041 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-3401 ∷ Bx3-2401 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ234 ∷ CX20 ∷ CS12 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-box-perm-2341-at0213243041 c4) ▸
       at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 4 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1258 (lit c4)) ▸
       at 6 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 10 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ234 ∷ CX20 ∷ CS12 ∷ Toff301 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 6 3 (Toff301 ∷ CCZ123 ∷ []) (wl1330 (lit c4)) ▸
       at 3 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 3 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ Toff301 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ [])
  b2 = at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 4 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp0377 c4) ▸
       at 3 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 9 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸ done

  b3 : Chain (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ Toff301 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff301 ∷ CCZ123 ∷ [])
  b3 = at 4 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 3 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 4 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸ done

  b4 : Chain (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff301 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff301 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 4 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 5 3 (Toff204 ∷ []) (wp1172 c4) ▸
       at 6 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 5 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 11 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸ done

  b5 : Chain (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff301 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Bx3-2401 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 10 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 9 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 5 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 6 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 2 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸ done

  b6 : Chain (Toff204 ∷ CCZ123 ∷ Bx3-2401 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 2 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 1 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1258 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸ done

  b7 : Chain (Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff204 ∷ Toff301 ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 3 (Toff301 ∷ CCZ123 ∷ []) (wl1330 (lit c4)) ▸
       at 1 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 2 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp0377 c4) ▸ done

  b8 : Chain (CCZ234 ∷ Toff204 ∷ Toff301 ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff301 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 1 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 7 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 3 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 1 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸ done

  b9 : Chain (CCZ234 ∷ Toff301 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 2 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ Toff301 ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 3 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 3 3 (Toff204 ∷ []) (wp1172 c4) ▸
       at 4 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 3 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 9 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸ done

  b11 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ Toff301 ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx3-2401 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 6 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 3 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 4 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸ done

  b12 : Chain (Bx3-2401 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx3-2401 ∷ Bx2-4013 ∷ [])
  b12 = at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

  b13 : Chain (Bx3-2401 ∷ Bx2-4013 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b13 = at 1 1 (Bx2-3401 ∷ []) (lem-box-perm-4123-at0214203143 c4) ▸ done

-- box-perm-2431 @0314203241: 3 steps
lem-box-perm-2431-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-2431-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-pairs-at0312243041 c4) ▸ done

-- box-perm-3241 @02142041: 3 steps
lem-box-perm-3241-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-box-perm-3241-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Bx2-0431 ∷ []) (lem-sym-ab-at02142041 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-pairs-at02102441 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym-bc-at02132130 c4) ▸ done

-- box-perm-1243 @03102132: 3 steps
lem-box-perm-1243-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-1243-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Bx3-2401 ∷ []) (lem-pairs-at03102132 c4) ▸
       at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-pairs-at03143041 c4) ▸ done

-- box-perm-1243 @0310213442: 3 steps
lem-box-perm-1243-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1243-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-pairs-at0310213442 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-pairs-at0312243041 c4) ▸ done

-- box-perm-4213 @02132031: 3 steps
lem-box-perm-4213-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-4213-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Bx2-3104 ∷ []) (lem-sym-bc-at02132031 c4) ▸
       at 0 1 (Bx2-0431 ∷ []) (lem-pairs-at02132130 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-sym-ab-at02102441 c4) ▸ done

-- box-perm-2341 @0312243041: 4 steps
lem-box-perm-2341-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-2341-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-pairs-at03143041 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done

-- box-perm-3241 @0314203241: 3 steps
lem-box-perm-3241-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-box-perm-3241-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Bx3-0421 ∷ []) (lem-sym-ab-at0314203241 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-pairs-at0310243241 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym-bc-at03122130 c4) ▸ done

-- box-box-3 @021021: 105 steps
lem-box-box-3-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-3-at021021 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-0134 ∷ Bx3-2014 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CCZ023 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ [])
  b0 = at 0 1 (Bx2-0143 ∷ []) (lem-box-perm-1243-at021021 c4) ▸
       at 0 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 4 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 3 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 4 2 (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl1360 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 5 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CCZ023 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 6 3 (Toff314 ∷ CCZ234 ∷ []) (wl1361 (lit c4)) ▸
       at 3 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸
       at 3 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ Toff314 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ [])
  b2 = at 2 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 4 2 (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4) ▸
       at 3 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 9 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 7 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 5 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸ done

  b3 : Chain (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ Toff314 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff314 ∷ CCZ234 ∷ [])
  b3 = at 4 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 3 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸
       at 4 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 10 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 9 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b4 : Chain (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff314 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff314 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 6 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 5 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 5 3 (Toff201 ∷ []) (wl1366 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CCZ014 ∷ []) (wp0698 c4) ▸
       at 5 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 11 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸ done

  b5 : Chain (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff314 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ Bx3-2014 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 10 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 9 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 7 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 5 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸
       at 6 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 2 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸ done

  b6 : Chain (Toff201 ∷ CCZ234 ∷ Bx3-2014 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CCZ023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b6 = at 2 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 2 2 (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl1360 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 6 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸ done

  b7 : Chain (Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CCZ023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff201 ∷ Toff314 ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b7 = at 4 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 4 3 (Toff314 ∷ CCZ234 ∷ []) (wl1361 (lit c4)) ▸
       at 1 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 0 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4) ▸ done

  b8 : Chain (CCZ023 ∷ Toff201 ∷ Toff314 ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff314 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b8 = at 1 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 7 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 5 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 3 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 2 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 1 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸ done

  b9 : Chain (CCZ023 ∷ Toff314 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ014 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b9 = at 2 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b10 : Chain (CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ014 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ Toff314 ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b10 = at 3 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 3 3 (Toff201 ∷ []) (wl1366 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CCZ014 ∷ []) (wp0698 c4) ▸
       at 3 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 9 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 7 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸ done

  b11 : Chain (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ Toff314 ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx3-2014 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b11 = at 6 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 5 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 3 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸
       at 4 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 6 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸ done

  b12 : Chain (Bx3-2014 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx3-2014 ∷ Bx2-0143 ∷ [])
  b12 = at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done

  b13 : Chain (Bx3-2014 ∷ Bx2-0143 ∷ []) (Bx3-2014 ∷ Bx2-0134 ∷ [])
  b13 = at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-1243-at0210213443 c4) ▸ done

-- box-perm-4213 @03122031: 3 steps
lem-box-perm-4213-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-4213-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Bx3-2104 ∷ []) (lem-sym-bc-at03122031 c4) ▸
       at 0 1 (Bx3-0421 ∷ []) (lem-pairs-at03122130 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-sym-ab-at0310243241 c4) ▸ done
