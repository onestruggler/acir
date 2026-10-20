{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D034 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0204 ; wl1270 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1549 ; wl1705 ; wp0021 ; wp0032 ; wp0039 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp1373 ; wp1374 ; wp1375 ; wp1376 ; wp1377 ; wp1378)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D024 using (lem-box2-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX20-TOFF413)

-- S2-SBOX(0;2;43;1) @0440: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at0440 : Ws → ⟪ (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CCZ024 ∷ CS12⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸ done

  b1 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CCZ024 ∷ CS12⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 7 2 (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 3 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 9 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 4 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 4 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b3 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b4 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff403 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 5 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 8 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 7 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 11 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 10 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4) ▸
       at 8 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸ done

  b5 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff403 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 8 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 6 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸
       at 7 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b6 : Chain (Bx4-2031 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 5 2 (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 1 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 7 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b7 : Chain (Bx4-2031 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 2 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 2 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b8 : Chain (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff413 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 6 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸ done

  b9 : Chain (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff413 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 5 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4) ▸
       at 6 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 5 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 4 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸ done

  b10 : Chain (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ023 ∷ [])
  b10 = at 5 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 1 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 0 2 [] (lem-box2-at04122041 c4) ▸
       at 0 3 (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl1549 (lit c4)) ▸
       at 2 2 [] (wl0204 (lit c4)) ▸
       at 0 8 (CCZ023 ∷ []) (sym (wl1705 (lit c4))) ▸ done
