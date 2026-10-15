{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D047 where

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
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-pairs-at13243241)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-sym-ab-at122441 ; lem-sym-bc-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D046 using (lem-pairs-at0210243143 ; lem-sym-ab-at0220 ; lem-sym-bc-at022330)
-- box-perm-1342 @0210243143: 3 steps
lem-box-perm-1342-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-pairs-at0210243143 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done


-- sym-ab @14233241: 18 steps
lem-sym-ab-at14233241 : Complete 4 → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-ab-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-31 ∷ []) (refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ [])
  b1 = at 2 6 (Bx3-021 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (pw3 c4 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸
       at 10 1 (Bx0-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (Bx0-3421 ∷ [])
  b2 = at 5 6 (Bx3-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- box-perm-1432 @122441: 4 steps
lem-box-perm-1432-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-1432-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-bc-at1441 c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-sym-ab-at14233241 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-pairs-at13243241 c4) ▸ done


-- sym-ab @021021: 18 steps
lem-sym-ab-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-ab-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-14 ∷ []) (refl) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ [])
  b1 = at 2 6 (Bx1-234 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸
       at 10 1 (Bx2-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (Bx2-1034 ∷ [])
  b2 = at 5 6 (Bx1-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- cQ @0220: 7 steps
lem-cQ-at0220 : Complete 4 → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0220 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0220: 13 steps
lem-box-tQ-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (lw4 c4 (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0220 c4) ▸
       at 2 4 (Toff201 ∷ []) (lw4 c4 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0220: 7 steps
lem-tP-at0220 : Complete 4 → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0220 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (lw4 c4 (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0220 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff201 ∷ []) (lw4 c4 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @0220: 8 steps
lem-P-box-at0220 : Complete 4 → ⟪ (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-P-box-at0220 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0220 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (lw0 c4 (Toff234 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0220 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ34 ∷ []) (lw0 c4 (Toff234 ∷ CCZ234 ∷ Toff234 ∷ []) (CCZ234 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 3 (CCZ234 ∷ []) (lw0 c4 (CZ34 ∷ CCZ234 ∷ CZ34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done


-- VPQ @0220: 14 steps
lem-VPQ-at0220 : Complete 4 → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (lw4 c4 (Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (lw0 c4 (Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (lw0 c4 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (lw4 c4 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0220: 3 steps
lem-QVQ-at0220 : Complete 4 → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0220 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0220 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0220: 12 steps
lem-box-cP-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0220 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4) ▸
       at 2 2 [] (lw4 c4 (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @0213243140: 7 steps
lem-cQ-at0213243140 : Complete 4 → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS24⁻ ∷ []) (pw3 c4 (CS24⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0213243140: 13 steps
lem-box-tQ-at0213243140 : Complete 4 → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243140 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (lw0 c4 (CCZ234 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243140 c4) ▸
       at 2 4 (Toff234 ∷ []) (lw0 c4 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @0220: 4 steps
lem-pairs-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-pairs-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (sym (lem-P-box-at0220 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0220 c4) ▸
       at 4 2 [] (lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done


-- CXbc-box @0213243140: 17 steps
lem-CXbc-box-at0213243140 : Complete 4 → ⟪ (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX41 ∷ CCZ024 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CCZ012 ∷ CX34 ∷ CS03 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ Toff234 ∷ []) (Toff234 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (pw3 c4 (CX41 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff234 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ Toff234 ∷ []) (Toff234 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX41 ∷ CCZ024 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CCZ012 ∷ CX34 ∷ CS03 ∷ CX41 ∷ []) (Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ034 ∷ []) (pw1 c4 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (pw3 c4 (CX41 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX41 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done

  b2 : Chain (Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-3410 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ CX41 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0213243140: 18 steps
lem-CXcb-box-at0213243140 : Complete 4 → ⟪ (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) (Toff234 ∷ CCZ012 ∷ CX14 ∷ Toff213 ∷ CS01 ∷ CX31 ∷ Toff234 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ012 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ CX14 ∷ Toff213 ∷ []) (lw0 c4 (CX14 ∷ Toff234 ∷ []) (Toff234 ∷ CX14 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (lw4 c4 (Toff213 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX14 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ Toff234 ∷ []) (Toff234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ CX14 ∷ Toff213 ∷ CS01 ∷ CX31 ∷ Toff234 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ012 ∷ CX14 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ Toff234 ∷ []) (Toff234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff)) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff234 ∷ CX14 ∷ Toff213 ∷ []) (lw0 c4 (CX14 ∷ Toff234 ∷ []) (Toff234 ∷ CX14 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX14 ∷ []) (lw0 c4 (CX14 ∷ Toff213 ∷ Toff213 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX14 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-3410 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ CX14 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done

