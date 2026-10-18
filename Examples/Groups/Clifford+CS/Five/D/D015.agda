{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0190 ; wl0191 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0263 ; wl0305 ; wl0747 ; wl1000 ; wl1037 ; wl1112 ; wl1114 ; wl1115 ; wl1116 ; wp0021 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0041 ; wp0044 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0093 ; wp0094 ; wp0095 ; wp0096 ; wp0097 ; wp0161 ; wp0651 ; wp0654 ; wp0805 ; wp0806 ; wp0842 ; wp0843 ; wp0845 ; wp0906 ; wp0907 ; wp0908 ; wp0909 ; wp0910)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box2-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-nf-order-CSat2)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF023-CS14 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF213-CS04)
-- S2-SBOX(0;2;43;1): 86 steps
lem-S2-SBOX⟨0·2·43·1⟩ : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 7 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 8 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 5 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 8 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 11 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 10 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 8 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸ done

  b5 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 8 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 6 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 7 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b6 : Chain (Bx0-2431 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 5 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 1 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b7 : Chain (Bx0-2431 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b8 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 6 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸ done

  b9 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 6 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 5 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸ done

  b10 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ234 ∷ [])
  b10 = at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 2 [] (lem-box2-at122441 c4) ▸
       at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 2 2 [] (wl0305 (lit c4)) ▸
       at 0 8 (CCZ234 ∷ []) (sym (wl1114 (lit c4))) ▸ done


-- F1-order-CS@2: 5 steps
lem-F1-order-CSat2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  b0 = at 0 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 0 2 [] (wl0305 (lit c4)) ▸
       at 0 0 [] (wl1112 (lit c4)) ▸
       at 0 0 [] (sym (lem-nf-order-CSat2 c4)) ▸ done


-- nf-comm-CS-S0@0: 83 steps
lem-nf-comm-CS-S0at0 : Ws → ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS04 ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b1 : Chain (CS04 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b2 : Chain (CS04 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b3 : Chain (CS04 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS04 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b5 : Chain (CS04 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ [])
  b5 = at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b7 : Chain (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b7 = at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸ done

  b8 : Chain (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b8 = at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b9 = at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b10 : Chain (CS04 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  b10 = at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 3 2 [] (wp0161 c4) ▸ done


-- F1-comm-CS-S0@0: 91 steps
lem-F1-comm-CS-S0at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS04 ∷ []) (CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 1 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ [])
  b2 = at 3 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 2 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 3 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 4 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 5 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 6 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 2 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b3 : Chain (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ [])
  b3 = at 1 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 0 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ [])
  b4 = at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 1 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b5 : Chain (CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ [])
  b5 = at 2 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 5 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 8 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 7 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ [])
  b6 = at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 7 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b7 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ [])
  b7 = at 5 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 9 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 4 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸ done

  b8 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ [])
  b8 = at 3 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ [])
  b9 = at 10 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 6 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 5 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b10 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ Bx2-0413 ∷ [])
  b10 = at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 8 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸
       at 7 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 6 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸ done

  b11 : Chain (Toff314 ∷ CS03 ∷ CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ Bx2-0413 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  b11 = at 2 2 [] (wp0161 c4) ▸
       at 0 5 (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0907 c4)) ▸
       at 0 6 (CS04 ∷ Sb2-0-41-3 ∷ []) (sym (lem-nf-comm-CS-S0at0 c4)) ▸ done


-- nf-comm-CS-S0@1: 83 steps
lem-nf-comm-CS-S0at1 : Ws → ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS14 ∷ Sb0-1-42-3 ∷ []) (CS14 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b1 : Chain (CS14 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b2 : Chain (CS14 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b3 : Chain (CS14 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b4 : Chain (CS14 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b5 : Chain (CS14 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b6 : Chain (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b7 : Chain (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸ done

  b8 : Chain (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b9 : Chain (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b9 = at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸ done

  b10 : Chain (CS14 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b10 = at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸ done


-- F1-comm-CS-S0@1: 91 steps
lem-F1-comm-CS-S0at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS14 ∷ []) (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 1 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b2 : Chain (CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ [])
  b2 = at 3 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 2 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 3 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 2 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b3 : Chain (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ [])
  b3 = at 1 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 0 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 2 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 3 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b4 : Chain (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ [])
  b4 = at 6 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 1 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b5 : Chain (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ [])
  b5 = at 2 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 8 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 7 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 8 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b6 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ [])
  b6 = at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 13 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 7 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b7 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ [])
  b7 = at 5 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 4 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸ done

  b8 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ [])
  b8 = at 3 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b9 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS14 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ [])
  b9 = at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸ done

  b10 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ Bx0-1423 ∷ [])
  b10 = at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸
       at 7 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 6 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸ done

  b11 : Chain (Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ Bx0-1423 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  b11 = at 2 2 [] (wl0263 (lit c4)) ▸
       at 0 5 (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1115 (lit c4))) ▸
       at 0 6 (CS14 ∷ Sb0-1-42-3 ∷ []) (sym (lem-nf-comm-CS-S0at1 c4)) ▸ done


-- nf-comm-CS-S0@2: 83 steps
lem-nf-comm-CS-S0at2 : Ws → ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS24 ∷ Sb0-2-43-1 ∷ []) (CS24 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CS24 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CS24 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CS24 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS24 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CS24 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b10 = at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done


-- F1-comm-CS-S0@2: 91 steps
lem-F1-comm-CS-S0at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS24 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ [])
  b2 = at 3 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 2 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 3 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 2 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ [])
  b3 = at 1 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 0 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ [])
  b4 = at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 1 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ [])
  b5 = at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ [])
  b6 = at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ [])
  b7 = at 5 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ [])
  b8 = at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS24 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ [])
  b9 = at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ Bx0-2431 ∷ [])
  b10 = at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸
       at 7 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 6 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸ done

  b11 : Chain (Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ Bx0-2431 ∷ []) (CS24 ∷ Sb0-2-43-1 ∷ [])
  b11 = at 2 2 [] (wl0305 (lit c4)) ▸
       at 0 5 (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1116 (lit c4))) ▸
       at 0 6 (CS24 ∷ Sb0-2-43-1 ∷ []) (sym (lem-nf-comm-CS-S0at2 c4)) ▸ done


-- nf-comm-CS-S1@0: 83 steps
lem-nf-comm-CS-S1at0 : Ws → ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS14 ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b1 : Chain (CS14 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b2 : Chain (CS14 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b3 : Chain (CS14 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS14 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b5 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ [])
  b5 = at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b7 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b7 = at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸ done

  b8 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b8 = at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b9 = at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b10 : Chain (CS14 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  b10 = at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 3 2 [] (wp0161 c4) ▸ done


-- F1-comm-CS-S1@0: 91 steps
lem-F1-comm-CS-S1at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS14 ∷ []) (CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 1 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ [])
  b2 = at 3 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 2 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 3 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 4 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 5 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 6 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 2 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b3 : Chain (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ [])
  b3 = at 1 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 0 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ [])
  b4 = at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 1 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b5 : Chain (CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ [])
  b5 = at 2 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 5 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 8 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 7 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ [])
  b6 = at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 7 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b7 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ [])
  b7 = at 5 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 9 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 4 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸ done

  b8 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ CCZ014 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ [])
  b8 = at 3 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ [])
  b9 = at 10 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 6 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 5 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b10 : Chain (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ Bx2-0413 ∷ [])
  b10 = at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸ done

  b11 : Chain (Toff314 ∷ CS03 ∷ CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ Bx2-0413 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  b11 = at 2 2 [] (wp0161 c4) ▸
       at 0 5 (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0910 c4)) ▸
       at 0 6 (CS14 ∷ Sb2-0-41-3 ∷ []) (sym (lem-nf-comm-CS-S1at0 c4)) ▸ done


-- nf-comm-CS-S1@1: 83 steps
lem-nf-comm-CS-S1at1 : Ws → ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS24 ∷ Sb0-1-42-3 ∷ []) (CS24 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b1 : Chain (CS24 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b2 : Chain (CS24 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b3 : Chain (CS24 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b4 : Chain (CS24 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b5 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b6 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b7 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸ done

  b8 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b9 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b9 = at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸ done

  b10 : Chain (CS24 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b10 = at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸ done

