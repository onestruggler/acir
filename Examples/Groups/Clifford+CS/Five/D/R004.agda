{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0025 ; wl0027 ; wl0028 ; wl0030 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0042 ; wl0046 ; wl0047 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0062 ; wl0065 ; wl0067 ; wl0068 ; wl0069 ; wl0073 ; wl0074 ; wl0075 ; wl0078 ; wl0079 ; wl0080 ; wl0082 ; wl0084 ; wl0085 ; wl0086 ; wl0087 ; wl0088 ; wl0089 ; wl0090 ; wl0091 ; wl0092 ; wl0093)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ024 ; lem-nat-2-TOFF012 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-CCZ124 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨4·032⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-1-TOFF104)
-- nat 0 BOX(0;4132): 8 steps
lem-nat-0-BOX⟨0·4132⟩ : WsL → ⟪ (Sw01 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4132 ∷ []) (Bx1-4032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx4-132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·032⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·032⟩ c4) ▸
       at 0 6 (Bx1-4032 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;42): 3 steps
lem-nat-1-BOX⟨1·42⟩ : WsL → ⟪ (Sw12 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-42 ∷ []) (Bx2-41 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;132): 8 steps
lem-nat-1-BOX⟨4·132⟩ : WsL → ⟪ (Sw12 ∷ Bx4-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-132 ∷ []) (Bx4-231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-42 ∷ Toff413 ∷ CCZ134 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 2 2 (Bx2-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx2-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-231 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;4032): 8 steps
lem-nat-1-BOX⟨1·4032⟩ : WsL → ⟪ (Sw12 ∷ Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-4032 ∷ []) (Bx2-4031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-132 ∷ Toff104 ∷ CCZ014 ∷ Bx4-132 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx4-231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·132⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·132⟩ c4) ▸
       at 0 6 (Bx2-4031 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;41): 3 steps
lem-nat-2-BOX⟨2·41⟩ : WsL → ⟪ (Sw23 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-41 ∷ []) (Bx3-41 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Bx3-41 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;231): 8 steps
lem-nat-2-BOX⟨4·231⟩ : WsL → ⟪ (Sw23 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·231⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-231 ∷ []) (Bx4-321 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-321 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4031): 8 steps
lem-nat-2-BOX⟨2·4031⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4031⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4031 ∷ []) (Bx3-4021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx4-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·231⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·231⟩ c4) ▸
       at 0 6 (Bx3-4021 ∷ []) (refl) ▸ done


-- nat 0 CZ14: 5 steps
lem-nat-0-CZ14 : WsL → ⟪ (Sw01 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CZ14 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ14 ∷ []) (CZ04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;41): 3 steps
lem-nat-0-BOX⟨3·41⟩ : WsL → ⟪ (Sw01 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·41⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-41 ∷ []) (Bx3-40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx3-40 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;321): 8 steps
lem-nat-0-BOX⟨4·321⟩ : WsL → ⟪ (Sw01 ∷ Bx4-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·321⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-321 ∷ []) (Bx4-320 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx3-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-320 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4021): 8 steps
lem-nat-0-BOX⟨3·4021⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4021⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4021 ∷ []) (Bx3-4120 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx4-320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·321⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·321⟩ c4) ▸
       at 0 6 (Bx3-4120 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;14): 3 steps
lem-nat-1-BOX⟨0·14⟩ : WsL → ⟪ (Sw12 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-14 ∷ []) (Bx0-24 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0089 c4)) ▸
       at 0 1 (Bx0-24 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;034): 8 steps
lem-nat-1-BOX⟨1·034⟩ : WsL → ⟪ (Sw12 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-034 ∷ []) (Bx2-034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx2-034 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;1234): 8 steps
lem-nat-1-BOX⟨0·1234⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx2-034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx2-034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·034⟩ c4) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;24): 3 steps
lem-nat-2-BOX⟨0·24⟩ : WsL → ⟪ (Sw23 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-24 ∷ []) (Bx0-34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 c4)) ▸
       at 0 1 (Bx0-34 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;034): 8 steps
lem-nat-2-BOX⟨2·034⟩ : WsL → ⟪ (Sw23 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-034 ∷ []) (Bx3-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx3-024 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2134): 8 steps
lem-nat-2-BOX⟨0·2134⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2134 ∷ []) (Bx0-3124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx3-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·034⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·034⟩ c4) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- nat 3 TOFF214: 2 steps
lem-nat-3-TOFF214 : WsL → ⟪ (Sw34 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF214 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 TOFF302: 80 steps
lem-nat-3-TOFF302 : WsL → ⟪ (Sw34 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF302 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw34 ∷ Toff302 ∷ []) (Sw34 ∷ Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw34 ∷ K3 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b2 : Chain (Sw34 ∷ K3 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ Sw12 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 2 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b3 : Chain (Sw34 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ Sw12 ∷ ι ∷ Sw12 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw34 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ [])
  b3 = at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw34 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b4 = at 4 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸ done

  b5 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b6 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b6 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b7 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b8 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b9 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Toff402 ∷ Sw34 ∷ [])
  b9 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;34): 3 steps
lem-nat-3-BOX⟨0·34⟩ : WsL → ⟪ (Sw34 ∷ Bx0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·34⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-34 ∷ []) (Bx0-43 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw34 ∷ []) (sym (wl0069 c4)) ▸
       at 0 1 (Bx0-43 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;024): 8 steps
lem-nat-3-BOX⟨3·024⟩ : WsL → ⟪ (Sw34 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-024 ∷ []) (Bx4-023 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx4-023 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;3124): 8 steps
lem-nat-3-BOX⟨0·3124⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3124 ∷ []) (Bx0-4123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx4-023 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·024⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx4-023 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·024⟩ c4) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- nat 0 TOFF204: 70 steps
lem-nat-0-TOFF204 : WsL → ⟪ (Sw01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF204 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff204 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ K2 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K2 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw01 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw01 ∷ CS04 ∷ K2 ∷ ι ∷ [])
  b5 = at 7 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0060 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0060 c4)) ▸ done

  b6 : Chain (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw01 ∷ CS04 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw34 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Toff214 ∷ Sw01 ∷ [])
  b8 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 TOFF402: 70 steps
lem-nat-0-TOFF402 : WsL → ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF402 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff402 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw01 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw01 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b5 = at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0060 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0060 c4)) ▸ done

  b6 : Chain (K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw01 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw34 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Toff412 ∷ Sw01 ∷ [])
  b8 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4) ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(0;43): 2 steps
lem-nat-0-BOX⟨0·43⟩ : WsL → ⟪ (Sw01 ∷ Bx0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·43⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-43 ∷ []) (Bx1-43 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx1-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;023): 8 steps
lem-nat-0-BOX⟨4·023⟩ : WsL → ⟪ (Sw01 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-023 ∷ []) (Bx4-123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·43⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·43⟩ c4) ▸
       at 0 6 (Bx4-123 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;4123): 8 steps
lem-nat-0-BOX⟨0·4123⟩ : WsL → ⟪ (Sw01 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4123 ∷ []) (Bx1-4023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx4-123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·023⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·023⟩ c4) ▸
       at 0 6 (Bx1-4023 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;43): 2 steps
lem-nat-1-BOX⟨1·43⟩ : WsL → ⟪ (Sw12 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-43 ∷ []) (Bx2-43 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx2-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(4;123): 8 steps
lem-nat-1-BOX⟨4·123⟩ : WsL → ⟪ (Sw12 ∷ Bx4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-123 ∷ []) (Bx4-213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-43 ∷ Toff412 ∷ CCZ124 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Bx2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-213 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;4023): 8 steps
lem-nat-1-BOX⟨1·4023⟩ : WsL → ⟪ (Sw12 ∷ Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4023⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-4023 ∷ []) (Bx2-4013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-123 ∷ Toff104 ∷ CCZ014 ∷ Bx4-123 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx4-213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·123⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·123⟩ c4) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- nat 2 TOFF104: 68 steps
lem-nat-2-TOFF104 : WsL → ⟪ (Sw23 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF104 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw23 ∷ Toff104 ∷ []) (Sw23 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K1 ∷ ι ∷ [])
  b3 = at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw23 ∷ ι ∷ [])
  b4 = at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b5 : Chain (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw23 ∷ ι ∷ []) (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸ done

  b6 : Chain (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff104 ∷ Sw23 ∷ [])
  b8 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF412: 2 steps
lem-nat-2-TOFF412 : WsL → ⟪ (Sw23 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF412 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(2;43): 3 steps
lem-nat-2-BOX⟨2·43⟩ : WsL → ⟪ (Sw23 ∷ Bx2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-43 ∷ []) (Bx3-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 c4)) ▸
       at 0 1 (Bx3-42 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;213): 8 steps
lem-nat-2-BOX⟨4·213⟩ : WsL → ⟪ (Sw23 ∷ Bx4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-213 ∷ []) (Bx4-312 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·43⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·43⟩ c4) ▸
       at 0 6 (Bx4-312 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4013): 8 steps
lem-nat-2-BOX⟨2·4013⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4013 ∷ []) (Bx3-4012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx4-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·213⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·213⟩ c4) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done


-- nat 1 TOFF304: 134 steps
lem-nat-1-TOFF304 : WsL → ⟪ (Sw12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF304 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (Sw12 ∷ Toff304 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸ done

  b8 : Chain (K3 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ Sw12 ∷ ι ∷ [])
  b8 = at 3 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 4 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b9 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ Sw12 ∷ ι ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Toff304 ∷ Sw12 ∷ [])
  b16 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;41): 3 steps
lem-nat-1-BOX⟨3·41⟩ : WsL → ⟪ (Sw12 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·41⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-41 ∷ []) (Bx3-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0089 c4)) ▸
       at 0 1 (Bx3-42 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;321): 8 steps
lem-nat-1-BOX⟨4·321⟩ : WsL → ⟪ (Sw12 ∷ Bx4-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-321 ∷ []) (Bx4-312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-312 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4021): 8 steps
lem-nat-1-BOX⟨3·4021⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4021⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4021 ∷ []) (Bx3-4012 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx4-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·321⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·321⟩ c4) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;42): 3 steps
lem-nat-1-BOX⟨3·42⟩ : WsL → ⟪ (Sw12 ∷ Bx3-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·42⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-42 ∷ []) (Bx3-41 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Bx3-41 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;312): 8 steps
lem-nat-1-BOX⟨4·312⟩ : WsL → ⟪ (Sw12 ∷ Bx4-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-312 ∷ []) (Bx4-321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4) ▸
       at 0 6 (Bx4-321 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4012): 8 steps
lem-nat-1-BOX⟨3·4012⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4012⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4012 ∷ []) (Bx3-4021 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx4-321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·312⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·312⟩ c4) ▸
       at 0 6 (Bx3-4021 ∷ []) (refl) ▸ done


-- nat 0 TOFF214: 70 steps
lem-nat-0-TOFF214 : WsL → ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF214 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff214 ∷ []) (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ []) (K2 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι1 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 8 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b2 : Chain (K2 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K2 ∷ ι1 ∷ [])
  b2 = at 2 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0048 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0048 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K2 ∷ ι1 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 6 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0073 c4) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b4 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸ done

  b5 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw12 ∷ []) (wl0074 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Toff204 ∷ Sw01 ∷ [])
  b8 = at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (sym (wl0080 c4)) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CZ04: 5 steps
lem-nat-0-CZ04 : WsL → ⟪ (Sw01 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CZ04 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;40): 3 steps
lem-nat-0-BOX⟨3·40⟩ : WsL → ⟪ (Sw01 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·40⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-40 ∷ []) (Bx3-41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx3-41 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;320): 8 steps
lem-nat-0-BOX⟨4·320⟩ : WsL → ⟪ (Sw01 ∷ Bx4-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·320⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-320 ∷ []) (Bx4-321 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-321 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4120): 8 steps
lem-nat-0-BOX⟨3·4120⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4120⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4120 ∷ []) (Bx3-4021 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx4-321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·320⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·320⟩ c4) ▸
       at 0 6 (Bx3-4021 ∷ []) (refl) ▸ done


-- nat 0 TOFF413: 100 steps
lem-nat-0-TOFF413 : WsL → ⟪ (Sw01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF413 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff413 ∷ []) (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ []) (Sw01 ∷ K4 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι1 ∷ Sw23 ∷ [])
  b1 = at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸ done

  b2 : Chain (Sw01 ∷ K4 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι1 ∷ Sw23 ∷ []) (Sw01 ∷ K4 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ [])
  b2 = at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸ done

  b3 : Chain (Sw01 ∷ K4 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι1 ∷ [])
  b3 = at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι1 ∷ []) (Sw23 ∷ K4 ∷ Sw23 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0073 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ Sw23 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι1 ∷ Sw01 ∷ [])
  b5 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b6 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b6 = at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K4 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b7 = at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K4 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b8 = at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι1 ∷ Sw12 ∷ []) (wl0074 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b9 = at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 10 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 11 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 4 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (sym (wl0075 c4)) ▸
       at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff403 ∷ Sw01 ∷ [])
  b12 = at 3 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;312): 8 steps
lem-nat-0-BOX⟨4·312⟩ : WsL → ⟪ (Sw01 ∷ Bx4-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·312⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-312 ∷ []) (Bx4-302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 6 (Bx4-302 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4012): 8 steps
lem-nat-0-BOX⟨3·4012⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4012⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4012 ∷ []) (Bx3-4102 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx4-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·312⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·312⟩ c4) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done


-- nat 1 TOFF013: 2 steps
lem-nat-1-TOFF013 : WsL → ⟪ (Sw12 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF013 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(1;024): 8 steps
lem-nat-1-BOX⟨1·024⟩ : WsL → ⟪ (Sw12 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-024 ∷ []) (Bx2-014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx2-014 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;1324): 8 steps
lem-nat-1-BOX⟨0·1324⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx2-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·024⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·024⟩ c4) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;014): 8 steps
lem-nat-2-BOX⟨2·014⟩ : WsL → ⟪ (Sw23 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·014⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-014 ∷ []) (Bx3-014 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx3-014 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2314): 8 steps
lem-nat-2-BOX⟨0·2314⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2314 ∷ []) (Bx0-3214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx3-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·014⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx3-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·014⟩ c4) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- nat 3 TOFF023: 80 steps
lem-nat-3-TOFF023 : WsL → ⟪ (Sw34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF023 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw34 ∷ Toff023 ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b2 : Chain (Sw34 ∷ K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 2 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b3 : Chain (Sw34 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw34 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b3 = at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw34 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b4 = at 4 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸ done

  b5 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b6 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b6 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b7 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b8 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b9 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Toff024 ∷ Sw34 ∷ [])
  b9 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 TOFF301: 2 steps
lem-nat-3-TOFF301 : WsL → ⟪ (Sw34 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF301 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(3;014): 8 steps
lem-nat-3-BOX⟨3·014⟩ : WsL → ⟪ (Sw34 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·014⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-014 ∷ []) (Bx4-013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;3214): 8 steps
lem-nat-3-BOX⟨0·3214⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3214 ∷ []) (Bx0-4213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·014⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·014⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done

