{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R013 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0024 ; wl0025 ; wl0026 ; wl0027 ; wl0028 ; wl0029 ; wl0030 ; wl0031 ; wl0032 ; wl0034 ; wl0037 ; wl0038 ; wl0043 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0061 ; wl0063 ; wl0066 ; wl0078 ; wl0084 ; wl0085 ; wl0086 ; wl0088 ; wl0090 ; wl0091 ; wl0092 ; wl0095 ; wl0096 ; wl0097 ; wl0099 ; wl0115 ; wl0121 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0144 ; wl0152 ; wl0153 ; wl0154 ; wl0155)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF301 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ013 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF412 ; lem-nat-1-BOX⟨2·43⟩ ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204 ; lem-nat-2-TOFF413 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF412 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ04 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOXd⟨2·43⟩ ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·4013⟩ ; lem-nat-1-CS04 ; lem-nat-2-TOFF124 ; lem-nat-3-CS23)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-CSd04 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04 ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨2·3401⟩ ; lem-nat-0-BOX⟨2·3410⟩ ; lem-nat-0-SBOX⟨2·1·3·0⟩ ; lem-nat-0-SBOXd⟨2·1·3·0⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-1-BOX⟨3·40⟩ ; lem-nat-1-SBOX⟨1·2·3·0⟩ ; lem-nat-1-SBOXd⟨1·2·3·0⟩ ; lem-nat-2-SBOX⟨1·3·2·0⟩ ; lem-nat-2-SBOX⟨1·4·2·0⟩ ; lem-nat-2-SBOXd⟨1·3·2·0⟩ ; lem-nat-2-SBOXd⟨1·4·2·0⟩)
-- resp TOFF034 at 2: 236 steps
lem-resp-TOFF034-at-2 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b6 : Chain (K0 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸ done

  b8 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 2 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸ done

  b9 : Chain (K0 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Toff034 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 11 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸ done

  b17 : Chain (Sw12 ∷ Toff034 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b24 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 4 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done

  b26 : Chain (Sw12 ∷ K0 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b26 = at 1 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b27 = at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸ done

  b28 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b29 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ [])
  b29 = at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF412 at 3: 7 steps
lem-resp-TOFF412-at-3 : WsL → ⟪ (Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF412-at-3 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0091 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


-- nat 2 BOX(1;43): 3 steps
lem-nat-2-BOX⟨1·43⟩ : WsL → ⟪ (Sw23 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-43 ∷ []) (Bx1-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 c4)) ▸
       at 0 1 (Bx1-42 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;103): 8 steps
lem-nat-2-BOX⟨4·103⟩ : WsL → ⟪ (Sw23 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-103 ∷ []) (Bx4-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-102 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;4203): 8 steps
lem-nat-2-BOX⟨1·4203⟩ : WsL → ⟪ (Sw23 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-4203 ∷ []) (Bx1-4302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·103⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·103⟩ c4) ▸
       at 0 6 (Bx1-4302 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;3;0): 3 steps
lem-nat-2-SBOX⟨1·4·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;3;0): 3 steps
lem-nat-2-SBOXd⟨1·4·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 0 1 (Sb⁻1-4-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;20;3): 7 steps
lem-nat-2-SBOX⟨1·4·20·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-20-3 ∷ []) (Sb1-4-30-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4203⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Sb1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 0 5 (Sb1-4-30-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;203): 8 steps
lem-nat-1-BOX⟨4·203⟩ : WsL → ⟪ (Sw12 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-203 ∷ []) (Bx4-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4103): 8 steps
lem-nat-1-BOX⟨2·4103⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4103 ∷ []) (Bx1-4203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Bx4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·203⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·203⟩ c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;4;3;0): 2 steps
lem-nat-1-SBOX⟨2·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb1-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(2;4;3;0): 2 steps
lem-nat-1-SBOXd⟨2·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(2;4;10;3): 7 steps
lem-nat-1-SBOX⟨2·4·10·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·10·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-10-3 ∷ []) (Sb1-4-20-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4103⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·3·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 0 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;4;3;1): 2 steps
lem-nat-0-SBOX⟨2·4·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-3-1 ∷ []) (Sb2-4-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 0 1 (Sb2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(2;4;3;1): 2 steps
lem-nat-0-SBOXd⟨2·4·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-4-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(2;4;01;3): 7 steps
lem-nat-0-SBOX⟨2·4·01·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·01·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-10-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·1⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·1⟩ c4) ▸
       at 0 5 (Sb2-4-10-3 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;310): 8 steps
lem-nat-1-BOX⟨4·310⟩ : WsL → ⟪ (Sw12 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-320 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·310⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-310 ∷ []) (Bx4-320 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 2 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-320 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4210): 8 steps
lem-nat-1-BOX⟨3·4210⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4210⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4210 ∷ []) (Bx3-4120 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Bx4-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·310⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx4-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·310⟩ c4) ▸
       at 0 6 (Bx3-4120 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;0;1): 3 steps
lem-nat-1-SBOX⟨3·4·0·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-0-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb3-4-0-2 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;0;1): 3 steps
lem-nat-1-SBOXd⟨3·4·0·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-0-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-0-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;21;0): 7 steps
lem-nat-1-SBOX⟨3·4·21·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-12-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·21·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-12-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4210⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Sb3-4-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·0·1⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (Sb⁻3-4-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·0·1⟩ c4) ▸
       at 0 5 (Sb3-4-12-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;40): 3 steps
lem-nat-2-BOX⟨2·40⟩ : WsL → ⟪ (Sw23 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·40⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-40 ∷ []) (Bx3-40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx3-40 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;210): 8 steps
lem-nat-2-BOX⟨4·210⟩ : WsL → ⟪ (Sw23 ∷ Bx4-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·210⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-210 ∷ []) (Bx4-310 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-40 ∷ Toff412 ∷ CCZ124 ∷ Bx2-40 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx3-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·40⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·40⟩ c4) ▸
       at 0 6 (Bx4-310 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4310): 8 steps
lem-nat-2-BOX⟨2·4310⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4310 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4310⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4310 ∷ []) (Bx3-4210 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-210 ∷ Toff234 ∷ CCZ234 ∷ Bx4-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Bx4-310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·210⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx4-310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·210⟩ c4) ▸
       at 0 6 (Bx3-4210 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;0;1): 3 steps
lem-nat-2-SBOX⟨2·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-0-1 ∷ []) (Sb3-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb3-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;4;0;1): 3 steps
lem-nat-2-SBOXd⟨2·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻3-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;31;0): 7 steps
lem-nat-2-SBOX⟨2·4·31·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·31·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-31-0 ∷ []) (Sb3-4-21-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-4310 ∷ Toff013 ∷ Sb2-4-0-1 ∷ Toff013 ∷ Sb⁻2-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4310⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Sb3-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·0·1⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (Sb⁻3-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·4·0·1⟩ c4) ▸
       at 0 5 (Sb3-4-21-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;40): 3 steps
lem-nat-2-BOX⟨3·40⟩ : WsL → ⟪ (Sw23 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·40⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-40 ∷ []) (Bx2-40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx2-40 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;310): 8 steps
lem-nat-2-BOX⟨4·310⟩ : WsL → ⟪ (Sw23 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-210 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·310⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-310 ∷ []) (Bx4-210 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx2-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx2-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-210 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;4210): 8 steps
lem-nat-2-BOX⟨3·4210⟩ : WsL → ⟪ (Sw23 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4310 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4210⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-4210 ∷ []) (Bx2-4310 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx4-210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·310⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx4-210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·310⟩ c4) ▸
       at 0 6 (Bx2-4310 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;0;1): 3 steps
lem-nat-2-SBOX⟨3·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb2-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;4;0;1): 3 steps
lem-nat-2-SBOXd⟨3·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻2-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;21;0): 7 steps
lem-nat-2-SBOX⟨3·4·21·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·21·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-21-0 ∷ []) (Sb2-4-31-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-4310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4210⟩ c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Sb2-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·0·1⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (Sb⁻2-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·4·0·1⟩ c4) ▸
       at 0 5 (Sb2-4-31-0 ∷ []) (refl) ▸ done


-- nat 3 TOFF312: 2 steps
lem-nat-3-TOFF312 : WsL → ⟪ (Sw34 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF312 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff312 ∷ []) (Toff412 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;30): 3 steps
lem-nat-3-BOX⟨2·30⟩ : WsL → ⟪ (Sw34 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-30 ∷ []) (Bx2-40 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx2-40 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;210): 8 steps
lem-nat-3-BOX⟨3·210⟩ : WsL → ⟪ (Sw34 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-210 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·210⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-210 ∷ []) (Bx4-210 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 2 2 (Bx2-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx4-210 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;3410): 8 steps
lem-nat-3-BOX⟨2·3410⟩ : WsL → ⟪ (Sw34 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4310 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·3410⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-3410 ∷ []) (Bx2-4310 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx4-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·210⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx4-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·210⟩ c4) ▸
       at 0 6 (Bx2-4310 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;0;1): 3 steps
lem-nat-3-SBOX⟨2·3·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 0 1 (Sb2-4-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;3;0;1): 3 steps
lem-nat-3-SBOXd⟨2·3·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 0 1 (Sb⁻2-4-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;41;0): 7 steps
lem-nat-3-SBOX⟨2·3·41·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·41·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-41-0 ∷ []) (Sb2-4-31-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-3410 ∷ Toff014 ∷ Sb2-3-0-1 ∷ Toff014 ∷ Sb⁻2-3-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-4310 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3410⟩ c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Sb2-4-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·0·1⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (Sb⁻2-4-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·0·1⟩ c4) ▸
       at 0 5 (Sb2-4-31-0 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;40): 3 steps
lem-nat-3-BOX⟨2·40⟩ : WsL → ⟪ (Sw34 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·40⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-40 ∷ []) (Bx2-30 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;210): 8 steps
lem-nat-3-BOX⟨4·210⟩ : WsL → ⟪ (Sw34 ∷ Bx4-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·210⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-210 ∷ []) (Bx3-210 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-40 ∷ Toff412 ∷ CCZ124 ∷ Bx2-40 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 2 2 (Bx2-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·40⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·40⟩ c4) ▸
       at 0 6 (Bx3-210 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;4310): 8 steps
lem-nat-3-BOX⟨2·4310⟩ : WsL → ⟪ (Sw34 ∷ Bx2-4310 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·4310⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-4310 ∷ []) (Bx2-3410 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-210 ∷ Toff234 ∷ CCZ234 ∷ Bx4-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx3-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·210⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx3-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·210⟩ c4) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;0;1): 3 steps
lem-nat-3-SBOX⟨2·4·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-0-1 ∷ []) (Sb2-3-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 0 1 (Sb2-3-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;4;0;1): 3 steps
lem-nat-3-SBOXd⟨2·4·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻2-3-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 0 1 (Sb⁻2-3-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;31;0): 7 steps
lem-nat-3-SBOX⟨2·4·31·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·31·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-31-0 ∷ []) (Sb2-3-41-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-4310 ∷ Toff013 ∷ Sb2-4-0-1 ∷ Toff013 ∷ Sb⁻2-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-3410 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4310⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Sb2-3-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·0·1⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (Sb⁻2-3-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·0·1⟩ c4) ▸
       at 0 5 (Sb2-3-41-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;1;0): 3 steps
lem-nat-0-SBOX⟨2·3·1·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-1-0 ∷ []) (Sb2-3-0-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 0 1 (Sb2-3-0-1 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;1;0): 3 steps
lem-nat-0-SBOXd⟨2·3·1·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-3-0-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 0 1 (Sb⁻2-3-0-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;40;1): 7 steps
lem-nat-0-SBOX⟨2·3·40·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-41-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Sb2-3-0-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·1·0⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-3-0-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·1·0⟩ c4) ▸
       at 0 5 (Sb2-3-41-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;0;1): 3 steps
lem-nat-0-SBOX⟨2·3·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-0-1 ∷ []) (Sb2-3-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;0;1): 3 steps
lem-nat-0-SBOXd⟨2·3·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-3-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 c4)) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;41;0): 7 steps
lem-nat-0-SBOX⟨2·3·41·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·41·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-40-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3410 ∷ Toff014 ∷ Sb2-3-0-1 ∷ Toff014 ∷ Sb⁻2-3-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3410⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·0·1⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·0·1⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;2;0): 3 steps
lem-nat-1-SBOX⟨1·3·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-2-0 ∷ []) (Sb2-3-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;3;2;0): 3 steps
lem-nat-1-SBOXd⟨1·3·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;40;2): 7 steps
lem-nat-1-SBOX⟨1·3·40·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-40-2 ∷ []) (Sb2-3-40-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-3402 ∷ Toff204 ∷ Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;1;0): 3 steps
lem-nat-1-SBOX⟨2·3·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-1-0 ∷ []) (Sb1-3-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 0 1 (Sb1-3-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;3;1;0): 3 steps
lem-nat-1-SBOXd⟨2·3·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 0 1 (Sb⁻1-3-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;40;1): 7 steps
lem-nat-1-SBOX⟨2·3·40·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-40-1 ∷ []) (Sb1-3-40-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Sb1-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·1·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (Sb⁻1-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·1·0⟩ c4) ▸
       at 0 5 (Sb1-3-40-2 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;23): 3 steps
lem-nat-2-BOX⟨1·23⟩ : WsL → ⟪ (Sw23 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-23 ∷ []) (Bx1-32 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (sym (wl0045 c4)) ▸
       at 0 1 (Bx1-32 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;103): 8 steps
lem-nat-2-BOX⟨2·103⟩ : WsL → ⟪ (Sw23 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-103 ∷ []) (Bx3-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2403): 8 steps
lem-nat-2-BOX⟨1·2403⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2403 ∷ []) (Bx1-3402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;3;0): 3 steps
lem-nat-2-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-3-0 ∷ []) (Sb1-3-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 c4)) ▸
       at 0 1 (Sb1-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;3;0): 3 steps
lem-nat-2-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (sym (wl0153 c4)) ▸
       at 0 1 (Sb⁻1-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;40;3): 7 steps
lem-nat-2-SBOX⟨1·2·40·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-40-3 ∷ []) (Sb1-3-40-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 0 5 (Sb1-3-40-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;3;0): 3 steps
lem-nat-1-SBOX⟨2·1·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-3-0 ∷ []) (Sb1-2-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;3;0): 3 steps
lem-nat-1-SBOXd⟨2·1·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;40;3): 7 steps
lem-nat-1-SBOX⟨2·1·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-40-3 ∷ []) (Sb1-2-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 0 5 (Sb1-2-40-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;0;3;1): 3 steps
lem-nat-0-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-3-1 ∷ []) (Sb2-1-3-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;3;1): 3 steps
lem-nat-0-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-1-3-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 c4)) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;0;41;3): 7 steps
lem-nat-0-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-41-3 ∷ []) (Sb2-1-40-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 0 5 (Sb2-1-40-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;03): 3 steps
lem-nat-0-BOXd⟨2·03⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx⁻2-13 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;213): 8 steps
lem-nat-0-BOXd⟨0·213⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-213 ∷ []) (Bx⁻1-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 3 2 (Bx⁻2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻1-203 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;0413): 8 steps
lem-nat-0-BOXd⟨2·0413⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-0413 ∷ []) (Bx⁻2-1403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·213⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 3 2 (Bx⁻1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·213⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻2-1403 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;41;3): 7 steps
lem-nat-0-SBOXd⟨2·0·41·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 2 (Sb2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (Bx⁻2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·0413⟩ c4) ▸
       at 0 5 (Sb⁻2-1-40-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;13): 3 steps
lem-nat-1-BOXd⟨2·13⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-13 ∷ []) (Bx⁻1-23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 0 1 (Bx⁻1-23 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;203): 8 steps
lem-nat-1-BOXd⟨1·203⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-203 ∷ []) (Bx⁻2-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 3 2 (Bx⁻1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·13⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻2-103 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;1403): 8 steps
lem-nat-1-BOXd⟨2·1403⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-1403 ∷ []) (Bx⁻1-2403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·203⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 2 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 3 2 (Bx⁻2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·203⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 0 6 (Bx⁻1-2403 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;40;3): 7 steps
lem-nat-1-SBOXd⟨2·1·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻1-2-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ Toff304 ∷ Bx⁻2-1403 ∷ []) (refl) ▸
       at 0 2 (Sb1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Bx⁻1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·1403⟩ c4) ▸
       at 0 5 (Sb⁻1-2-40-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;23): 3 steps
lem-nat-2-BOXd⟨1·23⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-23 ∷ []) (Bx⁻1-32 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (sym (wl0045 c4)) ▸
       at 0 1 (Bx⁻1-32 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;103): 8 steps
lem-nat-2-BOXd⟨2·103⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-103 ∷ []) (Bx⁻3-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-23 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻1-23 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·23⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (Bx⁻1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·23⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻3-102 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;2403): 8 steps
lem-nat-2-BOXd⟨1·2403⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-2403 ∷ []) (Bx⁻1-3402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻2-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·103⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 3 2 (Bx⁻3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·103⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 5 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 0 6 (Bx⁻1-3402 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;40;3): 7 steps
lem-nat-2-SBOXd⟨1·2·40·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻1-3-40-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ Toff304 ∷ Bx⁻1-2403 ∷ []) (refl) ▸
       at 0 2 (Sb1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·3·0⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (Bx⁻1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·2403⟩ c4) ▸
       at 0 5 (Sb⁻1-3-40-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;3;2;0): 3 steps
lem-nat-3-SBOX⟨1·3·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-3-2-0 ∷ []) (Sb1-4-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (refl) ▸ done


-- nat 3 CSd23: 2 steps
lem-nat-3-CSd23 : WsL → ⟪ (Sw34 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd23 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;3;2;0): 3 steps
lem-nat-3-SBOXd⟨1·3·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻1-4-2-0 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;32): 3 steps
lem-nat-3-BOXd⟨1·32⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-42 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-42 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx⁻1-42 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;102): 8 steps
lem-nat-3-BOXd⟨3·102⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-102 ∷ []) (Bx⁻4-102 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-32 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻1-32 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-42 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·32⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 3 2 (Bx⁻1-42 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·32⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻4-102 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;3402): 8 steps
lem-nat-3-BOXd⟨1·3402⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4302 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-4302 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻3-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·102⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 c4)) ▸
       at 2 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 3 2 (Bx⁻4-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·102⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 5 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 c4)) ▸
       at 0 6 (Bx⁻1-4302 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;3;40;2): 7 steps
lem-nat-3-SBOXd⟨1·3·40·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ Toff204 ∷ Bx⁻1-3402 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·3·2·0⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Sb⁻1-4-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (Bx⁻1-4302 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·3402⟩ c4) ▸
       at 0 5 (Sb⁻1-4-30-2 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;42): 3 steps
lem-nat-2-BOXd⟨1·42⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 c4)) ▸
       at 0 1 (Bx⁻1-43 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;102): 8 steps
lem-nat-2-BOXd⟨4·102⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-102 ∷ []) (Bx⁻4-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-42 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-42 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·42⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·42⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-103 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;4302): 8 steps
lem-nat-2-BOXd⟨1·4302⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-4203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·102⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 3 2 (Bx⁻4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·102⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 5 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 0 6 (Bx⁻1-4203 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;30;2): 7 steps
lem-nat-2-SBOXd⟨1·4·30·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-4-20-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ Toff203 ∷ Bx⁻1-4302 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·2·0⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (Bx⁻1-4203 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·4302⟩ c4) ▸
       at 0 5 (Sb⁻1-4-20-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;4;3;0): 2 steps
lem-nat-1-SBOX⟨1·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(1;4;3;0): 2 steps
lem-nat-1-SBOXd⟨1·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(1;43): 2 steps
lem-nat-1-BOXd⟨1·43⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-43 ∷ []) (Bx⁻2-43 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx⁻2-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(4;103): 8 steps
lem-nat-1-BOXd⟨4·103⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-43 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-43 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·43⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·43⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-203 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;4203): 8 steps
lem-nat-1-BOXd⟨1·4203⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-4203 ∷ []) (Bx⁻2-4103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·103⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 2 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 3 2 (Bx⁻4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·103⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 0 6 (Bx⁻2-4103 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;4;20;3): 7 steps
lem-nat-1-SBOXd⟨1·4·20·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ Toff302 ∷ Bx⁻1-4203 ∷ []) (refl) ▸
       at 0 2 (Sb2-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·4·3·0⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (Bx⁻2-4103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·4203⟩ c4) ▸
       at 0 5 (Sb⁻2-4-10-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;4;3;0): 2 steps
lem-nat-0-SBOX⟨2·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 0 1 (Sb2-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(2;4;3;0): 2 steps
lem-nat-0-SBOXd⟨2·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻2-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(4;203): 8 steps
lem-nat-0-BOXd⟨4·203⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻2-43 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 4 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-213 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;4103): 8 steps
lem-nat-0-BOXd⟨2·4103⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-4103 ∷ []) (Bx⁻2-4013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻4-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·203⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 3 2 (Bx⁻4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·203⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻2-4013 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;4;10;3): 7 steps
lem-nat-0-SBOXd⟨2·4·10·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·10·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻2-4-01-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ Toff301 ∷ Bx⁻2-4103 ∷ []) (refl) ▸
       at 0 2 (Sb2-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·0⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (Bx⁻2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·4103⟩ c4) ▸
       at 0 5 (Sb⁻2-4-01-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;13): 3 steps
lem-nat-0-BOXd⟨2·13⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-13 ∷ []) (Bx⁻2-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;203): 8 steps
lem-nat-0-BOXd⟨1·203⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-203 ∷ []) (Bx⁻0-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·13⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;1403): 8 steps
lem-nat-0-BOXd⟨2·1403⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-1403 ∷ []) (Bx⁻2-0413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·203⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·203⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;1;40;3): 7 steps
lem-nat-0-SBOXd⟨2·1·40·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ Toff304 ∷ Bx⁻2-1403 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (Bx⁻2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·1403⟩ c4) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;213): 8 steps
lem-nat-0-BOXd⟨4·213⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 3 2 (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 4 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻4-203 ∷ []) (refl) ▸ done


-- nat 0 BOXd(2;4013): 8 steps
lem-nat-0-BOXd⟨2·4013⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻2-4013 ∷ []) (Bx⁻2-4103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·213⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 3 2 (Bx⁻4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·213⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻2-4103 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;4;01;3): 7 steps
lem-nat-0-SBOXd⟨2·4·01·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·01·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) (refl) ▸
       at 0 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·1⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·1⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (Bx⁻2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·4013⟩ c4) ▸
       at 0 5 (Sb⁻2-4-10-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;23): 3 steps
lem-nat-1-BOXd⟨1·23⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-23 ∷ []) (Bx⁻2-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0026 c4)) ▸
       at 0 1 (Bx⁻2-13 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;103): 8 steps
lem-nat-1-BOXd⟨2·103⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-103 ∷ []) (Bx⁻1-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-23 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻1-23 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·23⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 3 2 (Bx⁻2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·23⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻1-203 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;2403): 8 steps
lem-nat-1-BOXd⟨1·2403⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-2403 ∷ []) (Bx⁻2-1403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·103⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 2 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 3 2 (Bx⁻1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·103⟩ c4) ▸
       at 4 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 0 6 (Bx⁻2-1403 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;2;40;3): 7 steps
lem-nat-1-SBOXd⟨1·2·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ Toff304 ∷ Bx⁻1-2403 ∷ []) (refl) ▸
       at 0 2 (Sb2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·3·0⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Bx⁻2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·2403⟩ c4) ▸
       at 0 5 (Sb⁻2-1-40-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;203): 8 steps
lem-nat-1-BOXd⟨4·203⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻2-43 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-103 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;4103): 8 steps
lem-nat-1-BOXd⟨2·4103⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-4103 ∷ []) (Bx⁻1-4203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻4-203 ∷ Toff214 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·203⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 2 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 3 2 (Bx⁻4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·203⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 0 6 (Bx⁻1-4203 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;4;10;3): 7 steps
lem-nat-1-SBOXd⟨2·4·10·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·10·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻1-4-20-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ Toff301 ∷ Bx⁻2-4103 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·3·0⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (Bx⁻1-4203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·4103⟩ c4) ▸
       at 0 5 (Sb⁻1-4-20-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;32): 3 steps
lem-nat-2-BOXd⟨1·32⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (sym (wl0045 c4)) ▸
       at 0 1 (Bx⁻1-23 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;102): 8 steps
lem-nat-2-BOXd⟨3·102⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-102 ∷ []) (Bx⁻2-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-32 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻1-32 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·32⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 3 2 (Bx⁻1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·32⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-103 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;3402): 8 steps
lem-nat-2-BOXd⟨1·3402⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-2403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻3-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·102⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 3 2 (Bx⁻2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·102⟩ c4) ▸
       at 4 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 5 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 0 6 (Bx⁻1-2403 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;40;2): 7 steps
lem-nat-2-SBOXd⟨1·3·40·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-2-40-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ Toff204 ∷ Bx⁻1-3402 ∷ []) (refl) ▸
       at 0 2 (Sb1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·2·0⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (Bx⁻1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·3402⟩ c4) ▸
       at 0 5 (Sb⁻1-2-40-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;43): 3 steps
lem-nat-2-BOXd⟨1·43⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-43 ∷ []) (Bx⁻1-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 c4)) ▸
       at 0 1 (Bx⁻1-42 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;103): 8 steps
lem-nat-2-BOXd⟨4·103⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-43 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-43 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·43⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·43⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-102 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;4203): 8 steps
lem-nat-2-BOXd⟨1·4203⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-4203 ∷ []) (Bx⁻1-4302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-103 ∷ Toff124 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·103⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 3 2 (Bx⁻4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·103⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 5 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 0 6 (Bx⁻1-4302 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;20;3): 7 steps
lem-nat-2-SBOXd⟨1·4·20·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻1-4-30-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ Toff302 ∷ Bx⁻1-4203 ∷ []) (refl) ▸
       at 0 2 (Sb1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·3·0⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (Bx⁻1-4302 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·4203⟩ c4) ▸
       at 0 5 (Sb⁻1-4-30-2 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;42): 3 steps
lem-nat-3-BOXd⟨1·42⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx⁻1-32 ∷ []) (refl) ▸ done

