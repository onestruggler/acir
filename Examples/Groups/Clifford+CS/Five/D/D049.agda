{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D049 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-cP-at1221 ; lem-sym-ab-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-pairs-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-sym-ab-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D046 using (lem-box-tQ-at022330 ; lem-cQ-at022330 ; lem-sym-ab-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-box-tQ-at0213243140 ; lem-box-tQ-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D048 using (lem-box-perm-2341-at021021 ; lem-box-tQ-at02233440 ; lem-sym-ab-at02233440 ; lem-sym-bc-at0213213440 ; lem-tP-at0213243140)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CZ04-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CSd13-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-TOFF213-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CX21-TOFF034 ; lem-comm-SWAP03-BOX⟨2·14⟩)
-- P-box @0213243140: 8 steps
lem-P-box-at0213243140 : Complete 4 → ⟪ (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-P-box-at0213243140 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243140 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (lw4 c4 (Toff201 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243140 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ01 ∷ []) (lw4 c4 (Toff201 ∷ CCZ012 ∷ Toff201 ∷ []) (CCZ012 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff)) ▸
       at 3 3 (CCZ012 ∷ []) (lw4 c4 (CZ01 ∷ CCZ012 ∷ CZ01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done


-- VPQ @0213243140: 14 steps
lem-VPQ-at0213243140 : Complete 4 → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (lw0 c4 (Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (lw4 c4 (Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ S2⁻ ∷ []) (sym (c₂ (CS • CS • CS) (S • S • S))) ▸
       at 2 2 (CS01⁻ ∷ Toff234 ∷ []) (sym (c₂ (CS • CS • CS) (Toff))) ▸
       at 1 2 (CS01⁻ ∷ S2 ∷ []) (sym (c₂ (CS • CS • CS) (S))) ▸
       at 0 2 (CS01⁻ ∷ CS34⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS34⁻ ∷ []) (sym (c₃ (S ↑ ↑) (CS • CS • CS))) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (S2⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))) ▸
       at 0 4 (Toff201 ∷ CCZ012 ∷ []) (lw4 c4 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff234 ∷ CCZ234 ∷ []) (lw0 c4 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0213243140: 3 steps
lem-QVQ-at0213243140 : Complete 4 → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243140 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (lw4 c4 [] (Toff201 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0213243140 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0213243140: 12 steps
lem-box-cP-at0213243140 : Complete 4 → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3410 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243140 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4) ▸
       at 2 2 [] (lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @0213243140: 4 steps
lem-pairs-at0213243140 : Complete 4 → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-pairs-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (sym (lem-P-box-at0213243140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243140 c4) ▸
       at 4 2 [] (lw4 c4 (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done


-- box-perm-4123 @02233440: 4 steps
lem-box-perm-4123-at02233440 : Complete 4 → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-4123-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-3140 ∷ []) (lem-sym-ab-at02233440 c4) ▸
       at 0 1 (Bx2-3410 ∷ []) (lem-sym-bc-at0213213440 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-pairs-at0213243140 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done


-- box-box-1 @021021: 105 steps
lem-box-box-1-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-1-at021021 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-0134 ∷ Bx0-2134 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ012 ∷ CX23 ∷ CS24 ∷ Toff034 ∷ [])
  b0 = at 0 1 (Bx2-1340 ∷ []) (lem-box-perm-2341-at021021 c4) ▸
       at 0 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ012 ∷ CX23 ∷ CS24 ∷ Toff034 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ Toff034 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (Toff213 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ013 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (lw4 c4 (Toff213 ∷ []) (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸
       at 6 2 (Toff034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸ done

  b3 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ Toff034 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff213 ∷ []) (lw4 c4 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff034 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (Toff213 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (lw4 c4 (Toff213 ∷ []) (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff034 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ Bx0-2134 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸
       at 8 2 (Toff034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸
       at 6 2 (Toff034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff213 ∷ []) (lw4 c4 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸ done

  b6 : Chain (Toff213 ∷ CCZ024 ∷ Bx0-2134 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff034 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff034 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff213 ∷ Toff034 ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 0 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (Toff213 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ013 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ012 ∷ Toff213 ∷ Toff034 ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (lw4 c4 (Toff213 ∷ []) (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸
       at 4 2 (Toff034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸
       at 2 2 (Toff034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (CCZ012 ∷ Toff034 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CCZ012 ∷ CCZ134 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff213 ∷ []) (lw4 c4 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CCZ012 ∷ CCZ134 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff034 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (Toff213 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (lw4 c4 (Toff213 ∷ []) (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸ done

  b11 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff034 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx0-2134 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 c4) ▸
       at 4 2 (Toff034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 4 7 (Toff213 ∷ []) (lw4 c4 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 2 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx0-2134 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx0-2134 ∷ Bx2-1340 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b13 : Chain (Bx0-2134 ∷ Bx2-1340 ∷ []) (Bx0-2134 ∷ Bx2-0134 ∷ [])
  b13 = at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-4123-at02233440 c4) ▸ done


-- box-perm-1432 @1221: 4 steps
lem-box-perm-1432-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1432-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-pairs-at132132 c4) ▸ done


-- CXbc-box @0220: 17 steps
lem-CXbc-box-at0220 : Complete 4 → ⟪ (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX03 ∷ CCZ024 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Toff201 ∷ []) (Toff201 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (pw1 c4 (CX03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Toff201 ∷ []) (Toff201 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX03 ∷ CCZ024 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX03 ∷ []) (Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (pw1 c4 (CX03 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (pw1 c4 (CX03 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX03 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done

  b2 : Chain (Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-1034 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (pw2 c4 (CX03 ∷ CCZ014 ∷ CX03 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0220: 18 steps
lem-CXcb-box-at0220 : Complete 4 → ⟪ (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) (Toff201 ∷ CCZ234 ∷ CX30 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ Toff201 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ234 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ CX30 ∷ Toff213 ∷ []) (lw4 c4 (CX30 ∷ Toff201 ∷ []) (Toff201 ∷ CX30 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) (lw0 c4 (Toff213 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX30 ∷ []) (pw1 c4 (CX30 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff201 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ Toff201 ∷ []) (Toff201 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff201 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff201 ∷ []) (Toff201 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX30 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ Toff201 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ234 ∷ CX30 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff201 ∷ []) (Toff201 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ Toff201 ∷ []) (Toff201 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CX30 ∷ Toff213 ∷ []) (lw4 c4 (CX30 ∷ Toff201 ∷ []) (Toff201 ∷ CX30 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (lw4 c4 (CX30 ∷ Toff213 ∷ Toff213 ∷ []) (CX30 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX30 ∷ []) (pw1 c4 (CX30 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX30 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-1034 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (pw2 c4 (CX30 ∷ CCZ134 ∷ CX30 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0220: 11 steps
lem-SWbc-box-at0220 : Complete 4 → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-SWbc-box-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (CX03 ∷ Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (lw4 c4 (Sw03 ∷ []) (CX03 ∷ CX30 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (lw4 c4 (Sw03 ∷ []) (CX03 ∷ CX30 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-1034 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0220 c4) ▸
       at 4 2 (CX03 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX03 ∷ Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (Bx2-1034 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4) ▸
       at 1 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0220: 23 steps
lem-nat-SWbc-at0220 : Complete 4 → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-nat-SWbc-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ Sw03 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ012 ∷ []) (CCZ123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff201 ∷ []) (Toff213 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ123 ∷ []) (CCZ012 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff123 ∷ []) (Toff102 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸
       at 5 2 (Toff102 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff123 ∷ []) (Toff102 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ Sw03 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ Sw03 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Sw03 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ123 ∷ []) (CCZ012 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸
       at 8 2 (Toff213 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff201 ∷ []) (Toff213 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ012 ∷ []) (CCZ123 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ123 ∷ []) (CCZ012 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff102 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff123 ∷ []) (Toff102 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Sw03 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Sw03 ∷ []) (Bx2-1304 ∷ [])
  b2 = at 13 2 (Toff102 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ Toff123 ∷ []) (Toff102 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ012 ∷ Sw03 ∷ []) (lw4 c4 (Sw03 ∷ CCZ123 ∷ []) (CCZ012 ∷ Sw03 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw03 ∷ Sw03 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-204 ∷ []) (refl) ▸
       at 5 6 (Bx1-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- sym-bc @0220: 2 steps
lem-sym-bc-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-bc-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0220 c4)) ▸
       at 0 3 (Bx2-1304 ∷ []) (lem-nat-SWbc-at0220 c4) ▸ done


-- tP @022330: 7 steps
lem-tP-at022330 : Complete 4 → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at022330 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (lw4 c4 (Toff213 ∷ []) (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (pw1 c4 (Toff204 ∷ []) (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at022330 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff204 ∷ []) (pw1 c4 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff213 ∷ []) (lw4 c4 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @022330: 8 steps
lem-P-box-at022330 : Complete 4 → ⟪ (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-P-box-at022330 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at022330 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (pw1 c4 (Toff204 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at022330 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (pw1 c4 (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) (CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 c4) ▸
       at 3 3 (CCZ024 ∷ []) (pw1 c4 (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done


-- VPQ @022330: 14 steps
lem-VPQ-at022330 : Complete 4 → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (lw4 c4 (Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (pw1 c4 (Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (pw1 c4 (S2⁻ ∷ CS04⁻ ∷ []) (CS04⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 c4) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (pw1 c4 (S2 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 c4) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (pw1 c4 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (lw4 c4 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

