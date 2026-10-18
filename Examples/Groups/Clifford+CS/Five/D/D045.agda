{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D045 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0187 ; wl0188 ; wl0189 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0198 ; wl0323 ; wl1182 ; wl1411 ; wl1412 ; wp0021 ; wp0029 ; wp0030 ; wp0031 ; wp0032 ; wp0033 ; wp0034 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0041 ; wp0042 ; wp0179 ; wp0746 ; wp1259 ; wp1260 ; wp1261 ; wp1262 ; wp1263)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Xb-box-at0210243143 ; lem-box-cP-at0210243143 ; lem-box2-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-K2-at02132031 ; lem-F4-CS2-S3-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-I-K2-at02132031 ; lem-F4-I-S3-at02132031 ; lem-F4-K2-CS2-at02132031 ; lem-F4-K2-K2-at02132031 ; lem-F4-S3-CS2-at02132031 ; lem-F4-S3-I-at02132031 ; lem-F4-S3-K2-at02132031 ; lem-F4-S3-S3-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX04-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX31-CCZ024)
-- F5-23 @02132031: 112 steps
lem-F5-23-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-23-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 4 2 (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) (wl0188 (lit c4)) ▸
       at 7 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 2 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4)) ▸
       at 4 2 (CX13 ∷ Toff314 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 5 2 (CS01 ∷ Toff314 ∷ []) (sym (wp0029 c4)) ▸
       at 6 2 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (sym (wp0030 c4)) ▸
       at 2 6 (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (sym (wp0031 c4)) ▸
       at 0 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-Xb-box-at0210243143 c4) ▸
       at 9 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 11 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b3 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b5 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 4 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 2 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 2 6 (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) (wp1259 c4) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b7 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ Toff213 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ Toff213 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CCZ024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 3 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 15 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 14 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 13 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 12 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CCZ024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 10 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 4 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b11 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 5 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 5 5 (Toff314 ∷ CS03 ∷ CS01 ∷ []) (wp1260 c4) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 10 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 13 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸ done

  b12 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 11 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 10 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 7 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b13 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CS01 ∷ [])
  b13 = at 4 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 9 4 (CS01 ∷ CCZ014 ∷ []) (sym (wp1261 c4)) ▸
       at 5 3 (Toff314 ∷ []) (wl0198 (lit c4)) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 10 (CS01 ∷ []) (sym (wp1262 c4)) ▸ done


-- deb-P-hi-split-a @02132031: 136 steps
lem-deb-P-hi-split-a-at02132031 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-hi-split-a-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 11 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b1 = at 10 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 9 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b2 = at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 17 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 23 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b3 = at 21 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 27 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b4 = at 24 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 24 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 35 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-K2-K2-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b6 = at 33 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 31 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 40 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 44 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b9 = at 38 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 48 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 47 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b10 = at 46 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ [])
  b11 = at 38 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 52 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 51 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 50 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 49 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ [])
  b12 = at 47 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ [])
  b13 = at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 56 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 53 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 52 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 51 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 50 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

  b14 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ [])
  b14 = at 49 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  b15 = at 60 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 59 4 (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S3-I-at02132031 c4)) ▸
       at 58 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 57 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 56 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 55 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 54 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 53 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  b16 = at 52 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 51 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 50 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 49 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 47 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done


-- deb-P-hi-split-b @02132031: 66 steps
lem-deb-P-hi-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-deb-P-hi-split-b-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 3 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 11 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b1 = at 10 4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-K2-K2-at02132031 c4)) ▸
       at 9 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b2 = at 19 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 17 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 15 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 23 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b3 = at 21 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 20 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 27 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS01 ∷ CS01 ∷ [])
  b4 = at 24 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ CS01 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 40 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at02132031 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

