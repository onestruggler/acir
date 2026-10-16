{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R042 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124 ; lem-nat-1-TOFF103 ; lem-nat-2-TOFF304 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-1-TOFF013 ; lem-nat-3-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-CCZ014 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-3-BOXd⟨0·13⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF014 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-SBOX⟨3·0·2·1⟩ ; lem-nat-1-SBOXd⟨3·0·2·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-SBOX⟨3·0·1·2⟩ ; lem-nat-2-SBOXd⟨3·0·1·2⟩ ; lem-nat-2-TOFF124 ; lem-nat-3-SBOX⟨2·0·1·3⟩ ; lem-nat-3-SBOXd⟨2·0·1·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-TOFF403 ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-BOXd⟨4·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOXd⟨4·10⟩ ; lem-nat-1-BOXd⟨4·01⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-SBOX⟨2·0·1·4⟩ ; lem-nat-1-SBOXd⟨2·0·1·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-3-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-nat-1-BOXd⟨4·03⟩)
-- nat 1 BOXd(0;413): 8 steps
lem-nat-1-BOXd⟨0·413⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-413 ∷ []) (Bx⁻0-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-03 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·03⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (Bx⁻4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·03⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-423 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0213): 8 steps
lem-nat-1-BOXd⟨4·0213⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0213 ∷ []) (Bx⁻4-0123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-413 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-413 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·413⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Bx⁻0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·413⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;412): 8 steps
lem-nat-2-BOXd⟨0·412⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-412 ∷ []) (Bx⁻0-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-413 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0312): 8 steps
lem-nat-2-BOXd⟨4·0312⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0312 ∷ []) (Bx⁻4-0213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-412 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-412 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·412⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 3 2 (Bx⁻0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·412⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0213 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;421): 8 steps
lem-nat-1-BOXd⟨0·421⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-421 ∷ []) (Bx⁻0-412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-01 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-412 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0321): 8 steps
lem-nat-1-BOXd⟨4·0321⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0321 ∷ []) (Bx⁻4-0312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-421 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-421 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·421⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 3 2 (Bx⁻0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·421⟩ c4) ▸
       at 4 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0312 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;420): 8 steps
lem-nat-0-BOXd⟨1·420⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-420 ∷ []) (Bx⁻0-421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-10 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-10 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻0-421 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;1320): 8 steps
lem-nat-0-BOXd⟨4·1320⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·1320⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-1320 ∷ []) (Bx⁻4-0321 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-420 ∷ CCZ134 ∷ Toff413 ∷ Bx⁻1-420 ∷ Toff413 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·420⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 3 2 (Bx⁻0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·420⟩ c4) ▸
       at 4 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 5 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 0 6 (Bx⁻4-0321 ∷ []) (refl) ▸ done


-- comm CCZ024 CSd13: 11 steps
lem-comm-CCZ024-CSd13 : Complete 4 → ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF413 CX02: 23 steps
lem-comm-TOFF413-CX02 : Complete 4 → ⟪ (Toff413 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CX02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CX02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (lw0 c4 (Toff413 ∷ Sw12 ∷ []) (Sw12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Toff423 ∷ []) (sym (c₂ (CX₀₁) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (lw0 c4 (Toff423 ∷ Sw12 ∷ []) (Sw12 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX02 ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX42 at 3: 6 steps
lem-resp-CX42-at-3 : Complete 4 → ⟪ (CX42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX42-at-3 c4 = run b0
  where
  b0 : Chain (CX42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX43 ∷ []) (lw0 c4 (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX43 ∷ []) (sym (c₃ (Swap ↑) (CX₁₀))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CX43 ∷ []) (sym (c₂ (Swap) (CX₁₀ ↑))) ▸ done


-- comm TOFF013 CX42: 15 steps
lem-comm-TOFF013-CX42 : Complete 4 → ⟪ (Toff013 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CX42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CX42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CX43 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX42 ∷ []) (CX43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX43 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CX43 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CX42 ∷ Toff013 ∷ [])
  b1 = at 2 2 (CX42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX43 ∷ []) (CX42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(1;34): 2 steps
lem-nat-0-BOXd⟨1·34⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-34 ∷ []) (Bx⁻0-34 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx⁻1-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx⁻0-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(3;124): 8 steps
lem-nat-0-BOXd⟨3·124⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻3-124 ∷ []) (Bx⁻3-024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-34 ∷ CCZ123 ∷ Toff312 ∷ Bx⁻1-34 ∷ Toff312 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·34⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·34⟩ c4) ▸
       at 4 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻3-024 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;3024): 8 steps
lem-nat-0-BOXd⟨1·3024⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-3124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-3024 ∷ []) (Bx⁻0-3124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻3-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻3-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨3·124⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨3·124⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-3124 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;34): 2 steps
lem-nat-1-BOXd⟨2·34⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·34⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-34 ∷ []) (Bx⁻1-34 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx⁻2-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx⁻1-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(3;214): 8 steps
lem-nat-1-BOXd⟨3·214⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻3-214 ∷ []) (Bx⁻3-124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-34 ∷ CCZ123 ∷ Toff312 ∷ Bx⁻2-34 ∷ Toff312 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·34⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·34⟩ c4) ▸
       at 4 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻3-124 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;3014): 8 steps
lem-nat-1-BOXd⟨2·3014⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-3014 ∷ []) (Bx⁻1-3024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻3-214 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻3-214 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·214⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 3 2 (Bx⁻3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·214⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻1-3024 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;43): 3 steps
lem-nat-3-BOXd⟨2·43⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-34 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·43⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-43 ∷ []) (Bx⁻2-34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CZ34 ∷ []) (CZ34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-34 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;213): 8 steps
lem-nat-3-BOXd⟨4·213⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-213 ∷ []) (Bx⁻3-214 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·43⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 2 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 3 2 (Bx⁻2-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·43⟩ c4) ▸
       at 4 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 5 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 0 6 (Bx⁻3-214 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;4013): 8 steps
lem-nat-3-BOXd⟨2·4013⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-3014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-4013 ∷ []) (Bx⁻2-3014 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-214 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·213⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 3 2 (Bx⁻3-214 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·213⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻2-3014 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;34): 3 steps
lem-nat-3-BOXd⟨2·34⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-43 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·34⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-34 ∷ []) (Bx⁻2-43 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CZ34 ∷ []) (CZ34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-43 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;214): 8 steps
lem-nat-3-BOXd⟨3·214⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-214 ∷ []) (Bx⁻4-213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-34 ∷ CCZ123 ∷ Toff312 ∷ Bx⁻2-34 ∷ Toff312 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·34⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 2 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·34⟩ c4) ▸
       at 4 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 5 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 0 6 (Bx⁻4-213 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;3014): 8 steps
lem-nat-3-BOXd⟨2·3014⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-3014 ∷ []) (Bx⁻2-4013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-214 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻3-214 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·214⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 3 2 (Bx⁻4-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·214⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 5 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 0 6 (Bx⁻2-4013 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;34): 2 steps
lem-nat-1-BOXd⟨1·34⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-34 ∷ []) (Bx⁻2-34 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx⁻1-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx⁻2-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(3;124): 8 steps
lem-nat-1-BOXd⟨3·124⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻3-124 ∷ []) (Bx⁻3-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-34 ∷ CCZ123 ∷ Toff312 ∷ Bx⁻1-34 ∷ Toff312 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·34⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·34⟩ c4) ▸
       at 4 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻3-214 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;3024): 8 steps
lem-nat-1-BOXd⟨1·3024⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-3014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-3024 ∷ []) (Bx⁻2-3014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻3-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻3-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·124⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 3 2 (Bx⁻3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·124⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-3014 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;24): 3 steps
lem-nat-2-BOXd⟨1·24⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-24 ∷ []) (Bx⁻1-34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-34 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;134): 8 steps
lem-nat-2-BOXd⟨2·134⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-134 ∷ []) (Bx⁻3-124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-24 ∷ CCZ123 ∷ Toff213 ∷ Bx⁻1-24 ∷ Toff213 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·24⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·24⟩ c4) ▸
       at 4 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻3-124 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;2034): 8 steps
lem-nat-2-BOXd⟨1·2034⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-2034 ∷ []) (Bx⁻1-3024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻2-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·134⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻3-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·134⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-3024 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;34): 3 steps
lem-nat-2-BOXd⟨1·34⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-34 ∷ []) (Bx⁻1-24 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-24 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;124): 8 steps
lem-nat-2-BOXd⟨3·124⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-124 ∷ []) (Bx⁻2-134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-34 ∷ CCZ123 ∷ Toff312 ∷ Bx⁻1-34 ∷ Toff312 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·34⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·34⟩ c4) ▸
       at 4 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-134 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;3024): 8 steps
lem-nat-2-BOXd⟨1·3024⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-3024 ∷ []) (Bx⁻1-2034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻3-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·124⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (Bx⁻2-134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·124⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-2034 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;24): 2 steps
lem-nat-0-BOXd⟨0·24⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-24 ∷ []) (Bx⁻1-24 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx⁻0-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx⁻1-24 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(2;034): 8 steps
lem-nat-0-BOXd⟨2·034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-034 ∷ []) (Bx⁻2-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-24 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-24 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·24⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·24⟩ c4) ▸
       at 4 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-134 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;2134): 8 steps
lem-nat-0-BOXd⟨0·2134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-2134 ∷ []) (Bx⁻1-2034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·034⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-2034 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;24): 2 steps
lem-nat-0-BOXd⟨1·24⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-24 ∷ []) (Bx⁻0-24 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx⁻1-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx⁻0-24 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(2;134): 8 steps
lem-nat-0-BOXd⟨2·134⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-134 ∷ []) (Bx⁻2-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-24 ∷ CCZ123 ∷ Toff213 ∷ Bx⁻1-24 ∷ Toff213 ∷ CCZ123 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·24⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·24⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-034 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;2034): 8 steps
lem-nat-0-BOXd⟨1·2034⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-2034 ∷ []) (Bx⁻0-2134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·134⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-2134 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;14): 3 steps
lem-nat-1-BOXd⟨0·14⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-24 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ14 ∷ []) (CZ24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻0-24 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;034): 8 steps
lem-nat-1-BOXd⟨1·034⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-034 ∷ []) (Bx⁻2-034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-034 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;1234): 8 steps
lem-nat-1-BOXd⟨0·1234⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-2134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·034⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-2134 ∷ []) (refl) ▸ done


-- nat 1 BOXd(3;02): 3 steps
lem-nat-1-BOXd⟨3·02⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻3-02 ∷ []) (Bx⁻3-01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx⁻3-01 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;312): 8 steps
lem-nat-1-BOXd⟨0·312⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·02⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (Bx⁻3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·02⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-321 ∷ []) (refl) ▸ done


-- nat 1 BOXd(3;0412): 8 steps
lem-nat-1-BOXd⟨3·0412⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻3-0412 ∷ []) (Bx⁻3-0421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-321 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·312⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-321 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·312⟩ c4) ▸
       at 4 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻3-0421 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;41;2): 7 steps
lem-nat-1-SBOXd⟨3·0·41·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-42-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻3-0-42-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 0 2 (Sb3-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·2·1⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻3-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨3·0412⟩ c4) ▸
       at 0 5 (Sb⁻3-0-42-1 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;01): 2 steps
lem-nat-2-BOXd⟨3·01⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-01 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-01 ∷ []) (Bx⁻2-01 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx⁻3-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx⁻2-01 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOXd(0;321): 8 steps
lem-nat-2-BOXd⟨0·321⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-321 ∷ []) (Bx⁻0-231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-01 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-01 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·01⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·01⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-231 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;0421): 8 steps
lem-nat-2-BOXd⟨3·0421⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-0421 ∷ []) (Bx⁻2-0431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-321 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-321 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-231 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·321⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-231 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·321⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻2-0431 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;0;42;1): 7 steps
lem-nat-2-SBOXd⟨3·0·42·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-43-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·42·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-42-1 ∷ []) (Sb⁻2-0-43-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ Toff124 ∷ Bx⁻3-0421 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·2⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·2⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (Bx⁻2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0421⟩ c4) ▸
       at 0 5 (Sb⁻2-0-43-1 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;231): 8 steps
lem-nat-3-BOXd⟨0·231⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-241 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-231 ∷ []) (Bx⁻0-241 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-01 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-01 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 3 2 (Bx⁻2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 4 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 5 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-241 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;0431): 8 steps
lem-nat-3-BOXd⟨2·0431⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-0431 ∷ []) (Bx⁻2-0341 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-231 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-231 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-241 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·231⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 3 2 (Bx⁻0-241 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·231⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻2-0341 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;0;43;1): 7 steps
lem-nat-3-SBOXd⟨2·0·43·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-34-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-43-1 ∷ []) (Sb⁻2-0-34-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ Toff134 ∷ Bx⁻2-0431 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·1·3⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-0341 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0431⟩ c4) ▸
       at 0 5 (Sb⁻2-0-34-1 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;01): 3 steps
lem-nat-1-BOXd⟨2·01⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-01 ∷ []) (Bx⁻1-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx⁻1-02 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;241): 8 steps
lem-nat-1-BOXd⟨0·241⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-241 ∷ []) (Bx⁻0-142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-01 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·01⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·01⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-142 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0341): 8 steps
lem-nat-1-BOXd⟨2·0341⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0341 ∷ []) (Bx⁻1-0342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-241 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-241 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-142 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·241⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 3 2 (Bx⁻0-142 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·241⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻1-0342 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;34;1): 7 steps
lem-nat-1-SBOXd⟨2·0·34·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-34-1 ∷ []) (Sb⁻1-0-34-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ Toff134 ∷ Bx⁻2-0341 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0341⟩ c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;03): 3 steps
lem-nat-3-BOXd⟨1·03⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-03 ∷ []) (Bx⁻1-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;143): 8 steps
lem-nat-3-BOXd⟨0·143⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-134 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;0243): 8 steps
lem-nat-3-BOXd⟨1·0243⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-0243 ∷ []) (Bx⁻1-0234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-134 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·143⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 3 2 (Bx⁻0-134 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·143⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻1-0234 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;04): 3 steps
lem-nat-3-BOXd⟨1·04⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-04 ∷ []) (Bx⁻1-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx⁻1-03 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;134): 8 steps
lem-nat-3-BOXd⟨0·134⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-143 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-143 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;0234): 8 steps
lem-nat-3-BOXd⟨1·0234⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0243 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-143 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 3 2 (Bx⁻0-143 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻1-0243 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;043): 8 steps
lem-nat-3-BOXd⟨1·043⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-043 ∷ []) (Bx⁻1-034 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-13 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-13 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·13⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·13⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-034 ∷ []) (refl) ▸ done

