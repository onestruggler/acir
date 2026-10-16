{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D226 where

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
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-BOXd-BOX-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D224 using (lem-AX-SB-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R043 using (lem-nat-1-BOXd⟨3·0421⟩)
-- AX-SB @12213443: 7 steps
lem-AX-SB-at12213443 : Complete 4 → ⟪ (CS02 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS02 ∷ []) ⟫ʷ
lem-AX-SB-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-SB-at3443 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0310243241: 5 steps
lem-BOXd-BOX-at0310243241 : Complete 4 → ⟪ (Bx⁻3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0421 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·0421⟩ c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-BOXd-BOX-at0310243142 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

