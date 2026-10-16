{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R022 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-3-CCZ013 ; lem-nat-3-CZ14)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-2-CZ03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023 ; lem-nat-2-CZ02 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-1-BOXd⟨2·03⟩ ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·03⟩ ; lem-nat-0-BOX⟨2·13⟩ ; lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨2·01⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-1-SBOX⟨2·0·3·4⟩ ; lem-nat-1-SBOXd⟨2·0·3·4⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·132⟩ ; lem-nat-0-TOFF124)
-- nat 0 BOX(1;0432): 8 steps
lem-nat-0-BOX⟨1·0432⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0432 ∷ []) (Bx0-1432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·132⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·132⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;231): 8 steps
lem-nat-1-BOX⟨0·231⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-231 ∷ []) (Bx0-132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0431): 8 steps
lem-nat-1-BOX⟨2·0431⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0431 ∷ []) (Bx1-0432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·231⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·231⟩ c4) ▸
       at 0 6 (Bx1-0432 ∷ []) (refl) ▸ done


-- comm CX41 TOFF203: 7 steps
lem-comm-CX41-TOFF203 : Complete 4 → ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF203 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (lw0 c4 (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (lw0 c4 (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (lw0 c4 (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX41 ∷ []) (lw0 c4 (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd13 at 2: 4 steps
lem-resp-CSd13-at-2 : Complete 4 → ⟪ (CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd13-at-2 c4 = run b0
  where
  b0 : Chain (CS13⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (c₂ (Swap) (CS • CS • CS))) ▸ done


-- resp CX04 at 2: 12 steps
lem-resp-CX04-at-2 : Complete 4 → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX04 ∷ []) (Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CX14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(1;23): 3 steps
lem-nat-1-BOX⟨1·23⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-23 ∷ []) (Bx2-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-13 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;143): 8 steps
lem-nat-1-BOX⟨2·143⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-143 ∷ []) (Bx1-243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx1-243 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2043): 8 steps
lem-nat-1-BOX⟨1·2043⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2043 ∷ []) (Bx2-1043 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx2-1043 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;243): 8 steps
lem-nat-0-BOX⟨1·243⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-243 ∷ []) (Bx0-243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-13 ∷ Toff124 ∷ CCZ124 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx0-243 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1043): 8 steps
lem-nat-0-BOX⟨2·1043⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1043⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1043 ∷ []) (Bx2-0143 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-243 ∷ Toff201 ∷ CCZ012 ∷ Bx1-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·243⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·243⟩ c4) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;243): 8 steps
lem-nat-0-BOX⟨0·243⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-243 ∷ []) (Bx1-243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx1-243 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0143): 8 steps
lem-nat-0-BOX⟨2·0143⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0143 ∷ []) (Bx2-1043 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx2-1043 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;41;3): 7 steps
lem-nat-1-SBOXd⟨2·0·41·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ c4) ▸
       at 0 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;3;2): 3 steps
lem-nat-2-SBOX⟨1·0·3·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;3;2): 3 steps
lem-nat-2-SBOXd⟨1·0·3·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;03): 3 steps
lem-nat-2-BOXd⟨1·03⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-03 ∷ []) (Bx⁻1-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx⁻1-02 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;123): 8 steps
lem-nat-2-BOXd⟨0·123⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻0-132 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0423): 8 steps
lem-nat-2-BOXd⟨1·0423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0423 ∷ []) (Bx⁻1-0432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·123⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·123⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0432 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;42;3): 7 steps
lem-nat-2-SBOXd⟨1·0·42·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-43-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0423⟩ c4) ▸
       at 0 5 (Sb⁻1-0-43-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;2;3): 2 steps
lem-nat-3-SBOX⟨1·0·2·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb1-0-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;0;2;3): 2 steps
lem-nat-3-SBOXd⟨1·0·2·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻1-0-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOXd(0;132): 8 steps
lem-nat-3-BOXd⟨0·132⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-142 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-142 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;0432): 8 steps
lem-nat-3-BOXd⟨1·0432⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0342 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·132⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·132⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0342 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;0;43;2): 7 steps
lem-nat-3-SBOXd⟨1·0·43·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0342 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0432⟩ c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;2;4): 3 steps
lem-nat-2-SBOX⟨1·0·2·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-3-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;2;4): 3 steps
lem-nat-2-SBOXd⟨1·0·2·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;02): 3 steps
lem-nat-2-BOXd⟨1·02⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-02 ∷ []) (Bx⁻1-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx⁻1-03 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;142): 8 steps
lem-nat-2-BOXd⟨0·142⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-143 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0342): 8 steps
lem-nat-2-BOXd⟨1·0342⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·142⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·142⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-0243 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;34;2): 7 steps
lem-nat-2-SBOXd⟨1·0·34·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-24-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0342⟩ c4) ▸
       at 0 5 (Sb⁻1-0-24-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;3;4): 3 steps
lem-nat-1-SBOX⟨1·0·3·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-3-4 ∷ []) (Sb2-0-3-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-0-3-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;3;4): 3 steps
lem-nat-1-SBOXd⟨1·0·3·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻2-0-3-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;03): 3 steps
lem-nat-1-BOXd⟨1·03⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-03 ∷ []) (Bx⁻2-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;143): 8 steps
lem-nat-1-BOXd⟨0·143⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-243 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0243): 8 steps
lem-nat-1-BOXd⟨1·0243⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0243 ∷ []) (Bx⁻2-0143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·143⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·143⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻2-0143 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;24;3): 7 steps
lem-nat-1-SBOXd⟨1·0·24·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·24·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻2-0-14-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ Toff324 ∷ Bx⁻1-0243 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0243⟩ c4) ▸
       at 0 5 (Sb⁻2-0-14-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;123): 8 steps
lem-nat-1-BOXd⟨0·123⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0423): 8 steps
lem-nat-1-BOXd⟨1·0423⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0423 ∷ []) (Bx⁻2-0413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·123⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·123⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;42;3): 7 steps
lem-nat-1-SBOXd⟨1·0·42·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ c4) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;243): 8 steps
lem-nat-1-BOXd⟨0·243⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-143 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0143): 8 steps
lem-nat-1-BOXd⟨2·0143⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx⁻2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0143 ∷ []) (Bx⁻1-0243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-243 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·243⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·243⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻1-0243 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;14;3): 7 steps
lem-nat-1-SBOXd⟨2·0·14·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻1-0-24-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·4⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0143⟩ c4) ▸
       at 0 5 (Sb⁻1-0-24-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;132): 8 steps
lem-nat-2-BOXd⟨0·132⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0432): 8 steps
lem-nat-2-BOXd⟨1·0432⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·132⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·132⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0423 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;43;2): 7 steps
lem-nat-2-SBOXd⟨1·0·43·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-42-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0432⟩ c4) ▸
       at 0 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;143): 8 steps
lem-nat-2-BOXd⟨0·143⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-142 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0243): 8 steps
lem-nat-2-BOXd⟨1·0243⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0243 ∷ []) (Bx⁻1-0342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·143⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·143⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-0342 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;24;3): 7 steps
lem-nat-2-SBOXd⟨1·0·24·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·24·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-34-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ Toff324 ∷ Bx⁻1-0243 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0243⟩ c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;142): 8 steps
lem-nat-3-BOXd⟨0·142⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-132 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 4 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-132 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;0342): 8 steps
lem-nat-3-BOXd⟨1·0342⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0432 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·142⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·142⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-0432 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;0;34;2): 7 steps
lem-nat-3-SBOXd⟨1·0·34·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0342⟩ c4) ▸
       at 0 5 (Sb⁻1-0-43-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;42;3): 7 steps
lem-nat-3-SBOXd⟨0·1·42·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-32-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ c4) ▸
       at 0 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;14): 3 steps
lem-nat-3-BOXd⟨0·14⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx⁻0-13 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;024): 8 steps
lem-nat-3-BOXd⟨1·024⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-023 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-14 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 3 2 (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻1-023 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;1324): 8 steps
lem-nat-3-BOXd⟨0·1324⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-024 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-023 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·024⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-023 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·024⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-1423 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;32;4): 7 steps
lem-nat-3-SBOXd⟨0·1·32·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-42-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ c4) ▸
       at 0 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;42;3): 7 steps
lem-nat-0-SBOXd⟨1·0·42·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻0-1-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ c4) ▸
       at 0 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;13): 3 steps
lem-nat-0-BOXd⟨0·13⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-13 ∷ []) (Bx⁻1-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ13 ∷ []) (CZ03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-03 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;023): 8 steps
lem-nat-0-BOXd⟨1·023⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-023 ∷ []) (Bx⁻0-123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·13⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx⁻0-123 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1423): 8 steps
lem-nat-0-BOXd⟨0·1423⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1423 ∷ []) (Bx⁻1-0423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·023⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (Bx⁻0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·023⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0423 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;42;3): 7 steps
lem-nat-0-SBOXd⟨0·1·42·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ c4) ▸
       at 0 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸ done

