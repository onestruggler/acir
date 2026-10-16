{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D182 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0227 ; wl0283 ; wl0341 ; wl0402 ; wl0550 ; wl0602 ; wl0661 ; wl0833 ; wl0834 ; wl0844 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0853 ; wl0854 ; wl0855 ; wl0856 ; wl0857 ; wl0858 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wp0142 ; wp0143 ; wp0352 ; wp0411 ; wp0415 ; wp0432 ; wp0440 ; wp0441 ; wp0442 ; wp0443 ; wp0444 ; wp0445 ; wp0446 ; wp0447 ; wp0448)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at12213443 ; lem-sym23-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443 ; lem-beta-T-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F0-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 ; lem-beta-T-at01122440)
-- F4 CS23^0|CS01^1 part0: 500 steps
lem-F4-CS23ᵖ0∣CS01ᵖ1-part0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS01ᵖ1-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0142 c4)) ▸
       at 4 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 5 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 8 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 11 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 14 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 13 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 12 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0853 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 10 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 16 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b3 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 10 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸ done

  b4 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 19 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 16 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 13 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 12 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 4 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b6 : Chain (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 5 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 13 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸ done

  b7 : Chain (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 7 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 4 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b8 : Chain (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 6 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 5 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 0 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b9 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx1-2430 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 4 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b10 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx1-2430 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx1-2430 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 16 1 (CS02⁻ ∷ []) (refl) ▸
       at 9 21 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (sym (wp0442 c4)) ▸
       at 22 1 (Sb1-2-0-3 ∷ []) (refl) ▸
       at 28 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 6 15 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ []) (sym (wp0443 c4)) ▸ done

  b11 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx1-2430 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 4 1 (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (lem-beta-T-at01122440 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸ done

  b12 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 17 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl0856 (lit c4)) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b13 = at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 28 4 (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0857 (lit c4))) ▸
       at 25 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 22 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0446 c4)) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸ done

  b14 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b14 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 18 5 (CCZ013 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b15 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b15 = at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 18 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 20 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 23 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b16 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b16 = at 22 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 21 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 24 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 23 2 (CS02 ∷ CCZ013 ∷ []) (wl0858 (lit c4)) ▸
       at 22 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 25 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 24 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 23 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b17 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b17 = at 9 15 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) (sym (wp0447 c4)) ▸
       at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 6 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 10 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 9 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 8 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b18 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b18 = at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl0856 (lit c4)) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b19 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b19 = at 22 4 (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0857 (lit c4))) ▸
       at 19 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 16 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0446 c4)) ▸
       at 13 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 10 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b20 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 12 5 (CCZ013 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 12 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 11 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 12 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b21 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ X4 ∷ CCZ013 ∷ X4 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CCZ013 ∷ CS02 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b21 = at 13 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 15 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 14 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 15 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸ done

  b22 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CCZ013 ∷ CS02 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b22 = at 17 2 (CS02 ∷ CCZ013 ∷ []) (wl0858 (lit c4)) ▸
       at 16 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 18 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 17 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 3 15 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) (sym (wp0447 c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b23 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b23 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 16 4 (Bx1-2430 ∷ []) (sym (lem-beta-T-at01122440 c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 16 5 (Sb1-2-43-0 ∷ []) (refl) ▸
       at 16 1 (Sb0-2-43-1 ∷ []) (sym (lem-F0-at02132031 c4)) ▸ done

  b24 : Chain (K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ X4 ∷ CCZ123 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b24 = at 2 2 [] (wl0550 (lit c4)) ▸
       at 3 2 [] (wl0550 (lit c4)) ▸
       at 4 2 [] (wl0550 (lit c4)) ▸
       at 5 2 [] (wl0550 (lit c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 0 3 (Toff204 ∷ []) (wp0142 c4) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (wl0661 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 c4) ▸ done

  b25 : Chain (Toff204 ∷ X4 ∷ CCZ123 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b25 = at 1 2 (CCZ123 ∷ X4 ∷ []) (sym (wl0661 (lit c4))) ▸
       at 5 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0142 c4)) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4) ▸
       at 7 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 10 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 13 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 16 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0550 (lit c4))) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b26 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b26 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 15 1 (CS12⁻ ∷ []) (refl) ▸
       at 8 12 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0853 (lit c4))) ▸
       at 12 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b27 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b27 = at 18 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 12 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸ done

  b28 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b28 = at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 21 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸ done

  b29 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b29 = at 18 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 15 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 14 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸ done

  b30 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b30 = at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 8 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 6 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 7 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4)) ▸ done

  b31 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ X4 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b31 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 15 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0432 c4)) ▸
       at 9 4 (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (sym (wl0834 (lit c4))) ▸ done

  b32 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX31 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b32 = at 6 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (CCZ013 ∷ []) (sym (wl0833 (lit c4))) ▸
       at 9 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 8 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸ done

  b33 : Chain (Toff204 ∷ CCZ123 ∷ X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2⁻ ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff024 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b33 = at 7 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 2 6 (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b34 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx1-2430 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b34 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 6 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 6 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b35 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Bx1-2430 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b35 = at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 1 (CS02 ∷ []) (refl) ▸
       at 18 1 (CS02⁻ ∷ []) (refl) ▸
       at 11 21 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (sym (wp0442 c4)) ▸
       at 24 1 (Sb1-2-0-3 ∷ []) (refl) ▸
       at 30 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 8 15 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ []) (sym (wp0443 c4)) ▸
       at 6 1 (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (lem-beta-T-at01122440 c4) ▸ done

  b36 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b36 = at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 15 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸ done

  b37 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ X4 ∷ CCZ013 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b37 = at 17 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 19 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl0856 (lit c4)) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b38 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b38 = at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 29 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 30 4 (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0857 (lit c4))) ▸
       at 27 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 24 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0446 c4)) ▸
       at 21 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 18 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b39 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b39 = at 22 2 [] (wl0283 (lit c4)) ▸
       at 23 2 [] (wl0283 (lit c4)) ▸
       at 24 2 [] (wl0283 (lit c4)) ▸
       at 20 5 (CCZ013 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 21 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 22 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b40 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b40 = at 21 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 20 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 21 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 24 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 23 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 22 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 25 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 24 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸ done

  b41 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ K2 ∷ CCZ013 ∷ X4 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b41 = at 23 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 26 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 25 2 (CS02 ∷ CCZ013 ∷ []) (wl0858 (lit c4)) ▸
       at 24 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 27 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 26 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 25 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 11 15 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) (sym (wp0447 c4)) ▸ done

  b42 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b42 = at 10 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 8 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 9 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 12 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 11 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 10 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸ done

  b43 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ X4 ∷ CCZ013 ∷ K2 ∷ X4 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b43 = at 12 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 13 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl0856 (lit c4)) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 4 (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0857 (lit c4))) ▸ done

  b44 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX30 ∷ X4 ∷ CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b44 = at 21 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 18 4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wp0446 c4)) ▸
       at 15 4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (sym (wp0445 c4)) ▸
       at 12 4 (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b45 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ X4 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b45 = at 14 5 (CCZ013 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 15 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 14 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 13 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 16 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 15 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 14 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 15 4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸ done

  b46 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS02 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b46 = at 18 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 17 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 16 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 19 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 18 2 (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4)) ▸
       at 17 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 20 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 19 2 (CS02 ∷ CCZ013 ∷ []) (wl0858 (lit c4)) ▸ done

  b47 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ X4 ∷ CS02 ∷ CCZ013 ∷ X4 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b47 = at 18 2 (CS02 ∷ X4 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))) ▸
       at 21 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 20 2 (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4)) ▸
       at 19 2 (K2⁻ ∷ X4 ∷ []) (sym (c₃ ((K • iI) ↑ ↑) (X ↑))) ▸
       at 5 15 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) (sym (wp0447 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b48 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb1-2-0-3 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ Sb⁻1-2-0-3 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b48 = at 18 4 (Bx1-2430 ∷ []) (sym (lem-beta-T-at01122440 c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 22 2 [] (wl0283 (lit c4)) ▸
       at 18 5 (Sb1-2-43-0 ∷ []) (refl) ▸
       at 18 1 (Sb0-2-43-1 ∷ []) (sym (lem-F0-at02132031 c4)) ▸
       at 4 2 [] (wl0550 (lit c4)) ▸ done

  b49 : Chain (Toff204 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ123 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b49 = at 5 2 [] (wl0550 (lit c4)) ▸
       at 6 2 [] (wl0550 (lit c4)) ▸
       at 7 2 [] (wl0550 (lit c4)) ▸
       at 3 5 (CCZ024 ∷ []) (sym (wp0143 c4)) ▸
       at 2 3 (Toff204 ∷ []) (wp0142 c4) ▸
       at 5 2 (CCZ123 ∷ X4 ∷ []) (sym (wl0661 (lit c4))) ▸
       at 4 2 (CCZ123 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 c4) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (wl0661 (lit c4))) ▸ done

  b50 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b50 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0402 (lit c4))) ▸
       at 5 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0227 (lit c4)) ▸
       at 6 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 9 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 12 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 15 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0859 (lit c4))) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b51 : Chain (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b51 = at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS12⁻ ∷ []) (refl) ▸
       at 13 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (sym (wl0860 (lit c4))) ▸
       at 17 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸ done

  b52 : Chain (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b52 = at 8 1 (CS12 ∷ []) (refl) ▸
       at 7 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wl0862 (lit c4))) ▸
       at 11 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 2 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 2 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b53 : Chain (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b53 = at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 9 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b54 : Chain (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b54 = at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸
       at 12 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸ done

  b55 : Chain (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b55 = at 20 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b56 : Chain (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b56 = at 13 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 8 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 10 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 11 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 9 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸ done

  b57 : Chain (Bx2-0413 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b57 = at 4 6 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 1 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 4 (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0848 (lit c4))) ▸ done

  b58 : Chain (Bx2-0413 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b58 = at 6 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸
       at 14 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (sym (wl0850 (lit c4))) ▸ done

  b59 : Chain (Bx2-0413 ∷ K3 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ X4 ∷ CX21 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b59 = at 8 4 (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (sym (wl0849 (lit c4))) ▸
       at 5 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wl0851 (lit c4))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0602 (lit c4))) ▸
       at 2 4 (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0852 (lit c4))) ▸ done

  b60 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b60 = at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 4 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸
       at 5 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI)) ▸
       at 3 2 (K3⁻ ∷ X4 ∷ []) (sym (c₄ ((K • iI) ↑ ↑ ↑) (X))) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸ done

  b61 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ X4 ∷ CCZ034 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b61 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 5 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 5 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 5 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b62 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b62 = at 5 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

