{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R010 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0023 ; wl0030 ; wl0031 ; wl0034 ; wl0035 ; wl0036 ; wl0039 ; wl0040 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0061 ; wl0062 ; wl0063 ; wl0064 ; wl0067 ; wl0068 ; wl0073 ; wl0074 ; wl0082 ; wl0084 ; wl0088 ; wl0092 ; wl0098 ; wl0103 ; wl0104 ; wl0105 ; wl0108 ; wl0110 ; wl0111 ; wl0112 ; wl0121 ; wl0127 ; wl0131 ; wl0134 ; wl0135 ; wl0136 ; wl0138 ; wl0139 ; wl0140 ; wl0144 ; wl0145 ; wl0146)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-TOFF102)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-CZ03 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·12⟩ ; lem-nat-1-BOX⟨0·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·20⟩ ; lem-nat-0-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨3·124⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
-- nat 1 BOX(1;3024): 8 steps
lem-nat-1-BOX⟨1·3024⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3024 ∷ []) (Bx2-3014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-124 ∷ Toff103 ∷ CCZ013 ∷ Bx3-124 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·124⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·124⟩ c4) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;214): 8 steps
lem-nat-0-BOX⟨3·214⟩ : WsL → ⟪ (Sw01 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-214 ∷ []) (Bx3-204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx3-204 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3014): 8 steps
lem-nat-0-BOX⟨2·3014⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3014 ∷ []) (Bx2-3104 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx3-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·214⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx3-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·214⟩ c4) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done


-- resp TOFF403 at 1: 101 steps
lem-resp-TOFF403-at-1 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b6 : Chain (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ Sw01 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 3 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ Sw01 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b9 = at 1 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸ done

  b10 : Chain (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 8 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ Sw34 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸ done

  b12 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ Sw34 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw01 ∷ Toff413 ∷ Sw01 ∷ [])
  b12 = at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4) ▸
       at 3 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(0;21): 3 steps
lem-nat-0-BOX⟨0·21⟩ : WsL → ⟪ (Sw01 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·21⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (sym (wl0105 c4)) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;041): 8 steps
lem-nat-0-BOX⟨2·041⟩ : WsL → ⟪ (Sw01 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-041 ∷ []) (Bx2-140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx2-140 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2341): 8 steps
lem-nat-0-BOX⟨0·2341⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2341 ∷ []) (Bx1-2340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx2-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx1-2340 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;03): 3 steps
lem-nat-2-BOX⟨1·03⟩ : WsL → ⟪ (Sw23 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-03 ∷ []) (Bx1-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx1-02 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;143): 8 steps
lem-nat-2-BOX⟨0·143⟩ : WsL → ⟪ (Sw23 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-143 ∷ []) (Bx0-142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-142 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0243): 8 steps
lem-nat-2-BOX⟨1·0243⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0243 ∷ []) (Bx1-0342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·143⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·143⟩ c4) ▸
       at 0 6 (Bx1-0342 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;3;4): 3 steps
lem-nat-2-SBOX⟨1·0·3·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-2-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb1-0-2-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;3;4): 3 steps
lem-nat-2-SBOXd⟨1·0·3·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻1-0-2-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;24;3): 7 steps
lem-nat-2-SBOX⟨1·0·24·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·24·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-24-3 ∷ []) (Sb1-0-34-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-0243 ∷ Toff324 ∷ Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 0 5 (Sb1-0-34-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;3;4): 3 steps
lem-nat-1-SBOX⟨2·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;3;4): 3 steps
lem-nat-1-SBOXd⟨2·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;14;3): 7 steps
lem-nat-1-SBOX⟨2·0·14·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-24-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-14-3 ∷ []) (Sb1-0-24-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Sb1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 0 5 (Sb1-0-24-3 ∷ []) (refl) ▸ done


-- resp TOFF204 at 3: 239 steps
lem-resp-TOFF204-at-3 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff204 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b4 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b5 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸ done

  b6 : Chain (Sw23 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b8 : Chain (Sw23 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 9 2 [] (wl0006 c4) ▸
       at 8 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 7 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw23 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 5 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 4 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 2 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 1 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw23 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 9 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 11 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 12 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 13 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 8 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 5 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 7 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0001 c4) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 10 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b14 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 11 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 6 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 3 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b18 = at 5 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b19 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b19 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 13 2 [] (wl0006 c4) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b20 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 12 2 [] (wl0007 c4) ▸ done

  b21 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b21 = at 3 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 4 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K3 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b22 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 11 2 [] (wl0001 c4) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸ done

  b23 : Chain (Sw23 ∷ Sw12 ∷ K3 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b23 = at 3 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b24 : Chain (Sw23 ∷ Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b24 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b25 : Chain (Sw23 ∷ Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw01 ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b25 = at 9 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 8 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸ done

  b26 : Chain (Sw23 ∷ Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw01 ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b26 = at 5 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 3 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 2 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b27 = at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b28 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b28 = at 5 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 11 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b29 = at 10 2 [] (wl0007 c4) ▸
       at 11 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 5 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸
       at 5 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(0;1;42;3): 7 steps
lem-nat-2-SBOX⟨0·1·42·3⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;43;2): 7 steps
lem-nat-2-SBOX⟨0·1·43·2⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- nat 3 TOFF124: 2 steps
lem-nat-3-TOFF124 : WsL → ⟪ (Sw34 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF124 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 TOFF213: 2 steps
lem-nat-3-TOFF213 : WsL → ⟪ (Sw34 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF213 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;130): 8 steps
lem-nat-3-BOX⟨2·130⟩ : WsL → ⟪ (Sw34 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·130⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-130 ∷ []) (Bx2-140 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 3 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx1-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 6 (Bx2-140 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2430): 8 steps
lem-nat-3-BOX⟨1·2430⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2430⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2430 ∷ []) (Bx1-2340 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4) ▸
       at 2 2 (Bx2-140 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·130⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-140 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·130⟩ c4) ▸
       at 0 6 (Bx1-2340 ∷ []) (refl) ▸ done


-- nat 3 TOFF034: 144 steps
lem-nat-3-TOFF034 : WsL → ⟪ (Sw34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF034 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (Sw34 ∷ Toff034 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw34 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b8 : Chain (K0 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b8 = at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0040 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b9 : Chain (K0 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b9 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b10 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b10 = at 8 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b14 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b15 = at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b16 = at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff034 ∷ Sw34 ∷ [])
  b17 = at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0145 c4)) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(1;2;0;3): 2 steps
lem-nat-3-SBOX⟨1·2·0·3⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-0-3 ∷ []) (Sb1-2-0-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb1-2-0-3 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb1-2-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;2;0;3): 2 steps
lem-nat-3-SBOXd⟨1·2·0·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻1-2-0-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻1-2-0-3 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻1-2-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(1;2;43;0): 7 steps
lem-nat-3-SBOX⟨1·2·43·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-34-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Sb1-2-0-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·0·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (Sb⁻1-2-0-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·0·3⟩ c4) ▸
       at 0 5 (Sb1-2-34-0 ∷ []) (refl) ▸ done


-- nat 3 TOFF123: 2 steps
lem-nat-3-TOFF123 : WsL → ⟪ (Sw34 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF123 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;140): 8 steps
lem-nat-3-BOX⟨2·140⟩ : WsL → ⟪ (Sw34 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·140⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-140 ∷ []) (Bx2-130 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-20 ∷ Toff214 ∷ CCZ124 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx1-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 6 (Bx2-130 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2340): 8 steps
lem-nat-3-BOX⟨1·2340⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2340 ∷ []) (Bx1-2430 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 2 2 (Bx2-130 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·140⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-130 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·140⟩ c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;2;0;4): 2 steps
lem-nat-3-SBOX⟨1·2·0·4⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-0-4 ∷ []) (Sb1-2-0-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb1-2-0-4 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;2;0;4): 2 steps
lem-nat-3-SBOXd⟨1·2·0·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-2-0-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻1-2-0-4 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(1;2;34;0): 7 steps
lem-nat-3-SBOX⟨1·2·34·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·34·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-43-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-2340 ∷ Toff034 ∷ Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2340⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·0·4⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·0·4⟩ c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;031): 8 steps
lem-nat-0-BOX⟨2·031⟩ : WsL → ⟪ (Sw01 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx2-130 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2431): 8 steps
lem-nat-0-BOX⟨0·2431⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;1;3): 3 steps
lem-nat-0-SBOX⟨0·2·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 c4)) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;2;1;3): 3 steps
lem-nat-0-SBOXd⟨0·2·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0036 c4)) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;43;1): 7 steps
lem-nat-0-SBOX⟨0·2·43·1⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·1·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done


-- nat 0 TOFF124: 70 steps
lem-nat-0-TOFF124 : WsL → ⟪ (Sw01 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF124 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff124 ∷ []) (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ []) (K0 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 c4)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b2 : Chain (K0 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K1 ∷ ι1 ∷ [])
  b2 = at 2 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0048 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0048 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K1 ∷ ι1 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 6 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 c4)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0073 c4) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b4 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b5 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw12 ∷ []) (wl0074 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Toff024 ∷ Sw01 ∷ [])
  b8 = at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0131 c4)) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;130): 8 steps
lem-nat-0-BOX⟨2·130⟩ : WsL → ⟪ (Sw01 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·130⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-130 ∷ []) (Bx2-031 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2430): 8 steps
lem-nat-0-BOX⟨1·2430⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2430 ∷ []) (Bx0-2431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·130⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·130⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;0;3): 3 steps
lem-nat-0-SBOX⟨1·2·0·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-0-3 ∷ []) (Sb0-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 c4)) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;2;0;3): 3 steps
lem-nat-0-SBOXd⟨1·2·0·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 c4)) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;43;0): 7 steps
lem-nat-0-SBOX⟨1·2·43·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Sb0-2-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·0·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (Sb⁻0-2-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·0·3⟩ c4) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;032): 8 steps
lem-nat-1-BOX⟨1·032⟩ : WsL → ⟪ (Sw12 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-032 ∷ []) (Bx2-031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;1432): 8 steps
lem-nat-1-BOX⟨0·1432⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·032⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·032⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;2;3): 3 steps
lem-nat-1-SBOX⟨0·1·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-2-3 ∷ []) (Sb0-2-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0134 c4)) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;1;2;3): 3 steps
lem-nat-1-SBOXd⟨0·1·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0135 c4)) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;43;2): 7 steps
lem-nat-1-SBOX⟨0·1·43·2⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;031): 8 steps
lem-nat-1-BOX⟨2·031⟩ : WsL → ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-031 ∷ []) (Bx1-032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2431): 8 steps
lem-nat-1-BOX⟨0·2431⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;1;3): 3 steps
lem-nat-1-SBOX⟨0·2·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0134 c4)) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;1;3): 3 steps
lem-nat-1-SBOXd⟨0·2·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0135 c4)) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;43;1): 7 steps
lem-nat-1-SBOX⟨0·2·43·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;30): 3 steps
lem-nat-0-BOX⟨2·30⟩ : WsL → ⟪ (Sw01 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-30 ∷ []) (Bx2-31 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;240): 8 steps
lem-nat-0-BOX⟨3·240⟩ : WsL → ⟪ (Sw01 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-240 ∷ []) (Bx3-241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-241 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3140): 8 steps
lem-nat-0-BOX⟨2·3140⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3140 ∷ []) (Bx2-3041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 2 2 (Bx3-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·240⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx3-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·240⟩ c4) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;0;4): 3 steps
lem-nat-0-SBOX⟨2·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-0-4 ∷ []) (Sb2-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Sb2-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;0;4): 3 steps
lem-nat-0-SBOXd⟨2·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻2-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 c4)) ▸
       at 0 1 (Sb⁻2-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;14;0): 7 steps
lem-nat-0-SBOX⟨2·3·14·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·14·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-04-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3140 ∷ Toff014 ∷ Sb2-3-0-4 ∷ Toff014 ∷ Sb⁻2-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Sb2-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·0·4⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (Sb⁻2-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·0·4⟩ c4) ▸
       at 0 5 (Sb2-3-04-1 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;31): 3 steps
lem-nat-0-BOX⟨2·31⟩ : WsL → ⟪ (Sw01 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-31 ∷ []) (Bx2-30 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;241): 8 steps
lem-nat-0-BOX⟨3·241⟩ : WsL → ⟪ (Sw01 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-241 ∷ []) (Bx3-240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-240 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3041): 8 steps
lem-nat-0-BOX⟨2·3041⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3041 ∷ []) (Bx2-3140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx3-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·241⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx3-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·241⟩ c4) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;1;4): 3 steps
lem-nat-0-SBOX⟨2·3·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-1-4 ∷ []) (Sb2-3-0-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 0 1 (Sb2-3-0-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;1;4): 3 steps
lem-nat-0-SBOXd⟨2·3·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 0 1 (Sb⁻2-3-0-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;04;1): 7 steps
lem-nat-0-SBOX⟨2·3·04·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·04·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-14-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Sb2-3-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·1·4⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-3-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·1·4⟩ c4) ▸
       at 0 5 (Sb2-3-14-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;30): 3 steps
lem-nat-1-BOX⟨1·30⟩ : WsL → ⟪ (Sw12 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-30 ∷ []) (Bx2-30 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;140): 8 steps
lem-nat-1-BOX⟨3·140⟩ : WsL → ⟪ (Sw12 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·140⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-140 ∷ []) (Bx3-240 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-240 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3240): 8 steps
lem-nat-1-BOX⟨1·3240⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3240⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3240 ∷ []) (Bx2-3140 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 2 2 (Bx3-240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·140⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx3-240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·140⟩ c4) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;0;4): 3 steps
lem-nat-1-SBOX⟨1·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-0-4 ∷ []) (Sb2-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 0 1 (Sb2-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;3;0;4): 3 steps
lem-nat-1-SBOXd⟨1·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻2-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;24;0): 7 steps
lem-nat-1-SBOX⟨1·3·24·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·24·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-24-0 ∷ []) (Sb2-3-14-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Sb2-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·0·4⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (Sb⁻2-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·0·4⟩ c4) ▸
       at 0 5 (Sb2-3-14-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;30): 3 steps
lem-nat-1-BOX⟨2·30⟩ : WsL → ⟪ (Sw12 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-30 ∷ []) (Bx1-30 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;240): 8 steps
lem-nat-1-BOX⟨3·240⟩ : WsL → ⟪ (Sw12 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·240⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-240 ∷ []) (Bx3-140 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-140 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3140): 8 steps
lem-nat-1-BOX⟨2·3140⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3140⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3140 ∷ []) (Bx1-3240 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx3-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·240⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx3-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·240⟩ c4) ▸
       at 0 6 (Bx1-3240 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;0;4): 3 steps
lem-nat-1-SBOX⟨2·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 0 1 (Sb1-3-0-4 ∷ []) (refl) ▸ done

