{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R031 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-TOFF413 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF214 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF013 ; lem-nat-2-CZ03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023 ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-CZ02 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-1-CZ02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-1-BOX⟨1·24⟩ ; lem-nat-3-CS13 ; lem-nat-3-CS14)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-BOX⟨4·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-3-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-1-BOX⟨2·401⟩)
-- nat 1 BOX(4;2301): 8 steps
lem-nat-1-BOX⟨4·2301⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-2301 ∷ []) (Bx4-1302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·401⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·401⟩ c4) ▸
       at 0 6 (Bx4-1302 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;20): 3 steps
lem-nat-0-BOX⟨4·20⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·20⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-20 ∷ []) (Bx4-21 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ02 ∷ []) (CZ12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;410): 8 steps
lem-nat-0-BOX⟨2·410⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·410⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-410 ∷ []) (Bx2-401 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx4-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·20⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·20⟩ c4) ▸
       at 0 6 (Bx2-401 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;2310): 8 steps
lem-nat-0-BOX⟨4·2310⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·2310⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-2310 ∷ []) (Bx4-2301 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx2-401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·410⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·410⟩ c4) ▸
       at 0 6 (Bx4-2301 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;14): 3 steps
lem-nat-1-BOX⟨2·14⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·14⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-14 ∷ []) (Bx1-24 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CZ14 ∷ []) (CZ24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-24 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;204): 8 steps
lem-nat-1-BOX⟨1·204⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-204 ∷ []) (Bx2-104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;1304): 8 steps
lem-nat-1-BOX⟨2·1304⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-1304 ∷ []) (Bx1-2304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·204⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·204⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;104): 8 steps
lem-nat-1-BOX⟨2·104⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-104 ∷ []) (Bx1-204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx1-204 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2304): 8 steps
lem-nat-1-BOX⟨1·2304⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2304 ∷ []) (Bx2-1304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;31): 3 steps
lem-nat-1-BOX⟨0·31⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-31 ∷ []) (Bx0-32 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-32 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;041): 8 steps
lem-nat-1-BOX⟨3·041⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-041 ∷ []) (Bx3-042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-042 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3241): 8 steps
lem-nat-1-BOX⟨0·3241⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·041⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·041⟩ c4) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;32): 3 steps
lem-nat-1-BOX⟨0·32⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·32⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-32 ∷ []) (Bx0-31 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;042): 8 steps
lem-nat-1-BOX⟨3·042⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·042⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-042 ∷ []) (Bx3-041 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-041 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3142): 8 steps
lem-nat-1-BOX⟨0·3142⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3142 ∷ []) (Bx0-3241 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·042⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·042⟩ c4) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;413): 8 steps
lem-nat-3-BOX⟨0·413⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-413 ∷ []) (Bx0-314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0213): 8 steps
lem-nat-3-BOX⟨4·0213⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0213 ∷ []) (Bx3-0214 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx0-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;30): 3 steps
lem-nat-0-BOX⟨1·30⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-30 ∷ []) (Bx0-31 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ03 ∷ []) (CZ13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;140): 8 steps
lem-nat-0-BOX⟨3·140⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-140 ∷ []) (Bx3-041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-041 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3240): 8 steps
lem-nat-0-BOX⟨1·3240⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3240 ∷ []) (Bx0-3241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·140⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·140⟩ c4) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;31): 3 steps
lem-nat-0-BOX⟨0·31⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-31 ∷ []) (Bx1-30 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ13 ∷ []) (CZ03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;041): 8 steps
lem-nat-0-BOX⟨3·041⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-041 ∷ []) (Bx3-140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-140 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3241): 8 steps
lem-nat-0-BOX⟨0·3241⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3241 ∷ []) (Bx1-3240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·041⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·041⟩ c4) ▸
       at 0 6 (Bx1-3240 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;20): 3 steps
lem-nat-2-BOX⟨3·20⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-20 ∷ []) (Bx2-30 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;340): 8 steps
lem-nat-2-BOX⟨2·340⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·340⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-340 ∷ []) (Bx3-240 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx3-240 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2140): 8 steps
lem-nat-2-BOX⟨3·2140⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2140⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2140 ∷ []) (Bx2-3140 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·340⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·340⟩ c4) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;30): 3 steps
lem-nat-2-BOX⟨2·30⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-30 ∷ []) (Bx3-20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx3-20 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;240): 8 steps
lem-nat-2-BOX⟨3·240⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·240⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-240 ∷ []) (Bx2-340 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx2-340 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3140): 8 steps
lem-nat-2-BOX⟨2·3140⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3140⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3140 ∷ []) (Bx3-2140 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·240⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·240⟩ c4) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;20): 2 steps
lem-nat-3-BOX⟨4·20⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·20⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-20 ∷ []) (Bx3-20 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx3-20 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;430): 8 steps
lem-nat-3-BOX⟨2·430⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·430⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-430 ∷ []) (Bx2-340 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·20⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·20⟩ c4) ▸
       at 0 6 (Bx2-340 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;2130): 8 steps
lem-nat-3-BOX⟨4·2130⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2130⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-2130 ∷ []) (Bx3-2140 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 2 2 (Bx2-340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·430⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·430⟩ c4) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;20): 2 steps
lem-nat-3-BOX⟨3·20⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-20 ∷ []) (Bx4-20 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx4-20 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;340): 8 steps
lem-nat-3-BOX⟨2·340⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·340⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-340 ∷ []) (Bx2-430 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx2-430 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;2140): 8 steps
lem-nat-3-BOX⟨3·2140⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2140⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-2140 ∷ []) (Bx4-2130 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 2 2 (Bx2-430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·340⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·340⟩ c4) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;10): 3 steps
lem-nat-1-BOX⟨4·10⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·10⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx4-20 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;430): 8 steps
lem-nat-1-BOX⟨1·430⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·10⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·10⟩ c4) ▸
       at 0 6 (Bx2-430 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1230): 8 steps
lem-nat-1-BOX⟨4·1230⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·430⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·430⟩ c4) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;20): 3 steps
lem-nat-1-BOX⟨4·20⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·20⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-20 ∷ []) (Bx4-10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx4-10 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;430): 8 steps
lem-nat-1-BOX⟨2·430⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·430⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-430 ∷ []) (Bx1-430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·20⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·20⟩ c4) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;2130): 8 steps
lem-nat-1-BOX⟨4·2130⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2130⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-2130 ∷ []) (Bx4-1230 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·430⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·430⟩ c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;420): 8 steps
lem-nat-2-BOX⟨1·420⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·420⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-420 ∷ []) (Bx1-430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1320): 8 steps
lem-nat-2-BOX⟨4·1320⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1320⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ []) (Bx4-1230 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx1-430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·420⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·420⟩ c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;430): 8 steps
lem-nat-2-BOX⟨1·430⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-430 ∷ []) (Bx1-420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-420 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1230): 8 steps
lem-nat-2-BOX⟨4·1230⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1230 ∷ []) (Bx4-1320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx1-420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·430⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·430⟩ c4) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;4;1): 3 steps
lem-nat-2-SBOX⟨3·0·4·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-4-1 ∷ []) (Sb2-0-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb2-0-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;0;4;1): 3 steps
lem-nat-2-SBOXd⟨3·0·4·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻2-0-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;21;4): 7 steps
lem-nat-2-SBOX⟨3·0·21·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·21·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-21-4 ∷ []) (Sb2-0-31-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0214 ∷ Toff412 ∷ Sb3-0-4-1 ∷ Toff412 ∷ Sb⁻3-0-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Sb2-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·4·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (Sb⁻2-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·4·1⟩ c4) ▸
       at 0 5 (Sb2-0-31-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;2;1): 3 steps
lem-nat-2-SBOX⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;0;2;1): 3 steps
lem-nat-2-SBOXd⟨4·0·2·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻4-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;31;2): 7 steps
lem-nat-2-SBOX⟨4·0·31·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·31·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·2·1⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 0 5 (Sb4-0-21-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;4;2;0): 2 steps
lem-nat-0-SBOX⟨1·4·2·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-4-2-0 ∷ []) (Sb0-4-2-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;4;2;1): 2 steps
lem-nat-0-SBOX⟨0·4·2·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-4-2-1 ∷ []) (Sb1-4-2-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(1;4;2;0): 3 steps
lem-nat-1-SBOX⟨1·4·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-4-2-0 ∷ []) (Sb2-4-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(4;3;1;0): 3 steps
lem-nat-3-SBOX⟨4·3·1·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb4-3-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(3;4;1;0): 3 steps
lem-nat-3-SBOX⟨3·4·1·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-4-1-0 ∷ []) (Sb4-3-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb4-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;3;2;0): 3 steps
lem-nat-1-SBOX⟨4·3·2·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;3;1;0): 3 steps
lem-nat-1-SBOX⟨4·3·1·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;2;3;0): 3 steps
lem-nat-2-SBOX⟨4·2·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-2-3-0 ∷ []) (Sb4-3-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;3;2;0): 3 steps
lem-nat-2-SBOX⟨4·3·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-3-2-0 ∷ []) (Sb4-2-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;1;3;0): 3 steps
lem-nat-1-SBOX⟨4·1·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-1-3-0 ∷ []) (Sb4-2-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;2;3;0): 3 steps
lem-nat-1-SBOX⟨4·2·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-2-3-0 ∷ []) (Sb4-1-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;3;1): 3 steps
lem-nat-0-SBOX⟨4·0·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-3-1 ∷ []) (Sb4-1-3-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;1;3;0): 3 steps
lem-nat-0-SBOX⟨4·1·3·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-1-3-0 ∷ []) (Sb4-0-3-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done

