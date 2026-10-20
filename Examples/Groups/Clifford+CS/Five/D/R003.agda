{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0018 ; wl0020 ; wl0021 ; wl0028 ; wl0029 ; wl0033 ; wl0036 ; wl0037 ; wl0038 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0072 ; wl0075 ; wl0084 ; wl0085 ; wl0086 ; wl0087 ; wl0090 ; wl0091 ; wl0093 ; wl0096 ; wl0098 ; wl0099 ; wl0100 ; wl0015 ; wl0042 ; wl0043 ; wl0049 ; wl0074 ; wl0079 ; wl0081 ; wl0088 ; wl0105 ; wl0106 ; wl0112 ; wl0113 ; wl0114 ; wl0010 ; wl0035 ; wl0053 ; wl0023 ; wl0024 ; wl0076 ; wl0139 ; wl0140 ; wl0034 ; wl0145 ; wl0146 ; wl0147 ; wl0151)
open import Examples.Groups.Clifford+CS.Five.Chain

-- comm CCZ123 CX04: 13 steps
lem-comm-CCZ123-CX04 : WsL → ⟪ (CCZ123 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CX04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CX04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 3 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 4 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ []) (CX04 ∷ CCZ123 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ134 CSd02: 23 steps
lem-comm-CCZ134-CSd02 : WsL → ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CSd02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CS02⁻ ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CS01⁻ ∷ CCZ234 ∷ []) (sym (c₂ (CS • CS • CS) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02⁻ ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CZ02 CCZ134: 23 steps
lem-comm-CZ02-CCZ134 : WsL → ⟪ (CZ02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CZ02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CS14 TOFF302: 7 steps
lem-comm-CS14-TOFF302 : WsL → ⟪ (CS14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF302 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Toff302 ∷ []) (Toff302 ∷ CS14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done

-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK41-at-3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CK41 ∷ []) (wl0099 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CK42 ∷ []) (wl0087 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done

-- comm SWAP14 BOX(3;02): 7 steps
lem-comm-SWAP14-BOX⟨3·02⟩ : WsL → ⟪ (Sw14 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw14 ∷ Bx3-02 ∷ []) (Bx3-02 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 1 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 2 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done

-- resp CK42 at 3: 6 steps
lem-resp-CK42-at-3 : WsL → ⟪ (CK42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK42-at-3 c4 = run b0
  where
  b0 : Chain (CK42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (wl0090 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CK43 ∷ []) (sym (c₂ (Swap) (CK₁₀ ↑))) ▸ done

-- comm TOFF301 CK42: 15 steps
lem-comm-TOFF301-CK42 : WsL → ⟪ (Toff301 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Toff301 ∷ []) ⟫ʷ
lem-comm-TOFF301-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 3 2 (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ Toff301 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : WsL → ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push SWAP04 sw0 L: 5 steps
lem-comm-push-SWAP04-sw0-L : WsL → ⟪ (Sw04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-push-SWAP04-sw0-L c4 = run b0
  where
  b0 : Chain (Sw04 ∷ Sw01 ∷ []) (Sw01 ∷ Sw14 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ Sw13 ∷ []) (sym (wl0098 c4)) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (Sw14 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push CX04 sw2 L: 7 steps
lem-comm-push-CX04-sw2-L : WsL → ⟪ (CX04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw2-L c4 = run b0
  where
  b0 : Chain (CX04 ∷ Sw23 ∷ []) (Sw23 ∷ CX04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm SWAP04 BOX(3;21): 13 steps
lem-comm-SWAP04-BOX⟨3·21⟩ : WsL → ⟪ (Sw04 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw04 ∷ []) ⟫ʷ
lem-comm-SWAP04-BOX⟨3·21⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw04 ∷ Bx3-21 ∷ []) (Sw34 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0036 c4)) ▸
       at 3 2 (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 2 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0033 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Bx3-21 ∷ Sw04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 0 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 1 7 (Sw04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done

-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : WsL → ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX20 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CX20 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX20 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm TOFF312 CK40: 13 steps
lem-comm-TOFF312-CK40 : WsL → ⟪ (Toff312 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CK40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CK40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 2 (CK10 ∷ Toff423 ∷ []) (sym (c₂ (CK₁₀) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CK40 ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ034 CSd12: 15 steps
lem-comm-CCZ034-CSd12 : WsL → ⟪ (CCZ034 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CSd12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ034 ∷ CS12⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CS12⁻ ∷ CCZ034 ∷ [])
  b1 = at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ014 CS23: 9 steps
lem-comm-CCZ014-CS23 : WsL → ⟪ (CCZ014 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CS23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CS23 ∷ []) (CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 2 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ014 CSd23: 9 steps
lem-comm-CCZ014-CSd23 : WsL → ⟪ (CCZ014 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CSd23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 1 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CS23⁻ ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm TOFF314 CX02: 23 steps
lem-comm-TOFF314-CX02 : WsL → ⟪ (Toff314 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CX02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff314 ∷ CX02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 5 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX02 ∷ Toff314 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done

-- resp SWAP02 at 1: 2 steps
lem-resp-SWAP02-at-1 : WsL → ⟪ (Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP02-at-1 c4 = run b0
  where
  b0 : Chain (Sw02 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Sw12 ∷ []) (sym (wl0100 c4)) ▸ done

-- comm SWAP02 BOX(3;41): 11 steps
lem-comm-SWAP02-BOX⟨3·41⟩ : WsL → ⟪ (Sw02 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨3·41⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-41 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Sw03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CZ12 ∷ Sw03 ∷ []) (sym (wl0086 c4)) ▸
       at 3 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ []) (Bx3-41 ∷ Sw02 ∷ [])
  b1 = at 4 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-41 ∷ []) (refl) ▸ done

-- comm CX31 TOFF204: 11 steps
lem-comm-CX31-TOFF204 : WsL → ⟪ (CX31 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX31 ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 3 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸
       at 4 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CX31 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CX24 TOFF301: 5 steps
lem-comm-CX24-TOFF301 : WsL → ⟪ (CX24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-TOFF301 c4 = run b0
  where
  b0 : Chain (CX24 ∷ Toff301 ∷ []) (Toff301 ∷ CX24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 1 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CX21 TOFF304: 15 steps
lem-comm-CX21-TOFF304 : WsL → ⟪ (CX21 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX21 ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 4 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CX21 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CX20 TOFF314: 23 steps
lem-comm-CX20-TOFF314 : WsL → ⟪ (CX20 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 5 2 (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CK40 TOFF312: 13 steps
lem-comm-CK40-TOFF312 : WsL → ⟪ (CK40 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm SWAP13 BOX(2;04): 13 steps
lem-comm-SWAP13-BOX⟨2·04⟩ : WsL → ⟪ (Sw13 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨2·04⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx2-04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw14 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 2 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 3 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw14 ∷ Sw23 ∷ Sw34 ∷ []) (Bx2-04 ∷ Sw13 ∷ [])
  b1 = at 5 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 6 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done

-- comm TOFF214 CX03: 9 steps
lem-comm-TOFF214-CX03 : WsL → ⟪ (Toff214 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CX03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CX03 ∷ []) (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 2 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ []) (CX03 ∷ Toff214 ∷ [])
  b1 = at 0 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CX32 TOFF014: 9 steps
lem-comm-CX32-TOFF014 : WsL → ⟪ (CX32 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX32 ∷ []) ⟫ʷ
lem-comm-CX32-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 2 (Toff012 ∷ CX43 ∷ []) (sym (c₃ (Toff) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 4 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ []) (Toff014 ∷ CX32 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : WsL → ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CS24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 3 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ013 CSd24: 15 steps
lem-comm-CCZ013-CSd24 : WsL → ⟪ (CCZ013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CS24⁻ ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24⁻ ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push SBOXd(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS03⁻ ∷ []) (wl0043 c4) ▸
       at 1 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done

-- comm push SBOX(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb2-0-3-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-3-2 ∷ [])
  b0 = at 0 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS03 ∷ []) (wl0001 c4) ▸
       at 1 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done

-- comm push BOX(2;03) sw1 L: 3 steps
lem-comm-push-BOX⟨2·03⟩-sw1-L : WsL → ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx2-03 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-03 ∷ [])
  b0 = at 0 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CZ03 ∷ []) (wl0079 c4) ▸
       at 1 1 (Bx1-03 ∷ []) (refl) ▸ done

-- comm push SBOXd(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (Sw01 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0042 c4) ▸
       at 1 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

-- comm push SBOX(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb1-0-3-2 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (Sw01 ∷ CS13 ∷ []) (wl0015 c4) ▸
       at 1 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

-- comm push BOX(1;03) sw0 L: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw0-L : WsL → ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx1-03 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-13 ∷ [])
  b0 = at 0 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (Sw01 ∷ CZ13 ∷ []) (wl0049 c4) ▸
       at 1 1 (Bx0-13 ∷ []) (refl) ▸ done

-- comm push CSd14 sw0 L: 5 steps
lem-comm-push-CSd14-sw0-L : WsL → ⟪ (CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd14-sw0-L c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS04⁻ ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CS03⁻ ∷ []) (wl0105 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push CS14 sw0 L: 5 steps
lem-comm-push-CS14-sw0-L : WsL → ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS14-sw0-L c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CS03 ∷ []) (wl0106 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push SBOXd(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

-- comm push SBOX(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done

-- comm push BOX(0;13) sw2 L: 4 steps
lem-comm-push-BOX⟨0·13⟩-sw2-L : WsL → ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-13 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-12 ∷ [])
  b0 = at 0 1 (CZ13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Bx0-12 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS12⁻ ∷ []) (wl0112 c4) ▸
       at 1 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

-- comm push SBOX(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-1-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS12 ∷ []) (wl0113 c4) ▸
       at 1 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

-- comm push BOX(0;12) sw1 L: 3 steps
lem-comm-push-BOX⟨0·12⟩-sw1-L : WsL → ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-12 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-21 ∷ [])
  b0 = at 0 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CZ12 ∷ []) (wl0114 c4) ▸
       at 1 1 (Bx0-21 ∷ []) (refl) ▸ done

-- comm push BOX(0;21) sw1 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0114 c4)) ▸
       at 0 1 (Bx0-12 ∷ []) (refl) ▸ done

-- comm push SBOX(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0113 c4)) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0112 c4)) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

-- comm push BOX(0;12) sw2 R: 4 steps
lem-comm-push-BOX⟨0·12⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done

-- comm push SBOX(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

-- comm push CK41 sw0 R: 5 steps
lem-comm-push-CK41-sw0-R : WsL → ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CK41-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK30 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push CS14 sw0 R: 5 steps
lem-comm-push-CS14-sw0-R : WsL → ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CS14-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0015 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push CSd14 sw0 R: 5 steps
lem-comm-push-CSd14-sw0-R : WsL → ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CSd14-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0042 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push CS04 sw0 R: 5 steps
lem-comm-push-CS04-sw0-R : WsL → ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0106 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push BOX(0;13) sw0 R: 3 steps
lem-comm-push-BOX⟨0·13⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0049 c4)) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done

-- comm push SBOX(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0015 c4)) ▸
       at 0 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done

-- comm push CK40 sw1 R: 5 steps
lem-comm-push-CK40-sw1-R : WsL → ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0088 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push BOX(1;03) sw1 R: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0079 c4)) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done

-- comm push SBOX(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

-- comm push SBOXd(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

-- comm CCZ014 CX32: 9 steps
lem-comm-CCZ014-CX32 : WsL → ⟪ (CCZ014 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX32 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CX32 ∷ []) (CX32 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX43 ∷ Sw23 ∷ []) (sym (wl0059 c4)) ▸
       at 2 2 (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀)) ▸
       at 1 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 1 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CX32 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CX32 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push BOX(4;203) sw1 L: 12 steps
lem-comm-push-BOX⟨4·203⟩-sw1-L : WsL → ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-203 ∷ Sw12 ∷ []) (CCZ024 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Sw12 ∷ Bx2-43 ∷ Toff401 ∷ CCZ014 ∷ Bx2-43 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx2-43 ∷ []) (sym (c₃ (Swap ↑) (CZ))) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 3 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 2 2 (Sw12 ∷ Bx2-43 ∷ []) (sym (c₃ (Swap ↑) (CZ))) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Sw12 ∷ Bx2-43 ∷ Toff401 ∷ CCZ014 ∷ Bx2-43 ∷ []) (Sw12 ∷ Bx4-103 ∷ [])
  b1 = at 3 2 [] (wl0006 c4) ▸
       at 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 1 6 (Bx4-103 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-4-2-1 ∷ [])
  b0 = at 0 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 1 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done

-- comm push SBOX(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-2-1 ∷ [])
  b0 = at 0 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 1 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done

-- comm push BOX(0;43) sw2 L: 3 steps
lem-comm-push-BOX⟨0·43⟩-sw2-L : WsL → ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·43⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-43 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-42 ∷ [])
  b0 = at 0 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 1 1 (Bx0-42 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻0-4-1-2 ∷ [])
  b0 = at 0 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4) ▸
       at 1 1 (Sb⁻0-4-1-2 ∷ []) (refl) ▸ done

-- comm push SBOX(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (Sb0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb0-4-2-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-1-2 ∷ [])
  b0 = at 0 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 1 1 (Sb0-4-1-2 ∷ []) (refl) ▸ done

-- comm push BOX(0;42) sw1 L: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw1-L : WsL → ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-42 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-41 ∷ [])
  b0 = at 0 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CZ14 ∷ []) (wl0053 c4) ▸
       at 1 1 (Bx0-41 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻0-3-1-2 ∷ [])
  b0 = at 0 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 1 (Sb⁻0-3-1-2 ∷ []) (refl) ▸ done

-- comm push SBOX(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Sb0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-1-2 ∷ [])
  b0 = at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 1 (Sb0-3-1-2 ∷ []) (refl) ▸ done

-- comm push BOX(0;41) sw3 L: 4 steps
lem-comm-push-BOX⟨0·41⟩-sw3-L : WsL → ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Bx0-41 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-31 ∷ [])
  b0 = at 0 1 (CZ14 ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ CZ13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 1 (Bx0-31 ∷ []) (refl) ▸ done

-- comm push CX04 sw2 R: 7 steps
lem-comm-push-CX04-sw2-R : WsL → ⟪ (Sw23 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CX04 ∷ []) (CX04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push CX04 sw1 R: 5 steps
lem-comm-push-CX04-sw1-R : WsL → ⟪ (Sw12 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX04 ∷ []) (CX04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push SBOXd(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 0 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

-- comm push SBOX(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-3-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-2-1-3 ∷ [])
  b0 = at 0 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

-- comm push BOX(0;31) sw2 L: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw2-L : WsL → ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-31 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-21 ∷ [])
  b0 = at 0 1 (CZ13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Bx0-21 ∷ []) (refl) ▸ done

-- comm push BOX(0;21) sw2 R: 4 steps
lem-comm-push-BOX⟨0·21⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done

-- comm push SBOX(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-1-3 ∷ []) (Sb0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb0-3-1-2 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻0-3-1-2 ∷ []) (refl) ▸ done

-- comm push BOX(0;31) sw3 R: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-31 ∷ []) (Bx0-41 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done

-- comm push SBOX(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-1-2 ∷ []) (Sb0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb0-4-1-2 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (Sb⁻0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻0-4-1-2 ∷ []) (refl) ▸ done

-- comm push BOX(0;41) sw1 R: 3 steps
lem-comm-push-BOX⟨0·41⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0053 c4)) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done

-- comm push SBOX(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-1-2 ∷ []) (Sb0-4-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) (Sb⁻0-4-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 0 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done

-- comm push BOX(0;42) sw2 R: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0035 c4)) ▸
       at 0 1 (Bx0-43 ∷ []) (refl) ▸ done

-- comm push SBOX(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (refl) ▸ done

-- comm push BOX(4;103) sw1 R: 12 steps
lem-comm-push-BOX⟨4·103⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-103 ∷ []) (CCZ024 ∷ Toff402 ∷ Bx1-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx1-43 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ Bx1-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx1-43 ∷ []) (Bx4-203 ∷ Sw12 ∷ [])
  b1 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx4-203 ∷ []) (refl) ▸ done

-- comm CX40 TOFF213: 13 steps
lem-comm-CX40-TOFF213 : WsL → ⟪ (CX40 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CX40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm TOFF213 CX40: 13 steps
lem-comm-TOFF213-CX40 : WsL → ⟪ (Toff213 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CX40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CX40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 2 (CX10 ∷ Toff324 ∷ []) (sym (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CX40 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push BOX(0;21) sw0 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done

-- comm push SBOX(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (refl) ▸ done

-- comm push SBOXd(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸ done

-- comm push BOX(1;20) sw1 R: 4 steps
lem-comm-push-BOX⟨1·20⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·20⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 0 1 (Bx2-10 ∷ []) (refl) ▸ done

-- comm push SBOX(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-0-3 ∷ []) (Sb2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (refl) ▸ done

-- comm push SBOXd(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (refl) ▸ done

-- comm push BOX(1;230) sw2 R: 8 steps
lem-comm-push-BOX⟨1·230⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·230⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0139 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0139 c4)) ▸
       at 5 2 (Bx2-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-320 ∷ []) (refl) ▸ done

-- comm push BOX(1;320) sw3 R: 12 steps
lem-comm-push-BOX⟨1·320⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·320⟩-sw3-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx1-320 ∷ []) (CCZ124 ∷ Toff124 ∷ Bx3-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx3-10 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff124 ∷ Bx3-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx3-10 ∷ []) (Bx1-420 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 6 (Bx1-420 ∷ []) (refl) ▸ done

-- comm push BOX(1;420) sw2 R: 12 steps
lem-comm-push-BOX⟨1·420⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·420⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx1-420 ∷ []) (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ []) (Bx1-430 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done

-- comm push BOX(4;10) sw1 R: 4 steps
lem-comm-push-BOX⟨4·10⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·10⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-20 ∷ []) (refl) ▸ done

-- comm push SBOX(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-1-0-3 ∷ []) (Sb4-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb4-2-0-3 ∷ []) (refl) ▸ done

-- comm push SBOXd(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻4-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-1-0-3 ∷ []) (Sb⁻4-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻4-2-0-3 ∷ []) (refl) ▸ done

-- comm push BOX(4;20) sw0 R: 3 steps
lem-comm-push-BOX⟨4·20⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·20⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-20 ∷ []) (Bx4-21 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (sym (wl0145 c4)) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done

-- comm push SBOX(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-2-0-3 ∷ []) (Sb4-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0146 c4)) ▸
       at 0 1 (Sb4-2-1-3 ∷ []) (refl) ▸ done

-- comm push SBOXd(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻4-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-2-0-3 ∷ []) (Sb⁻4-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0147 c4)) ▸
       at 0 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸ done

-- comm CSd13 TOFF402: 11 steps
lem-comm-CSd13-TOFF402 : WsL → ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 3 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 4 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CS13 TOFF402: 11 steps
lem-comm-CS13-TOFF402 : WsL → ⟪ (CS13 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 3 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 4 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CS13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm SWAP03 BOX(4;21): 3 steps
lem-comm-SWAP03-BOX⟨4·21⟩ : WsL → ⟪ (Sw03 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw03 ∷ Bx4-21 ∷ []) (Bx4-21 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw03 ∷ []) (sym (wl0086 c4)) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done

-- comm TOFF402 CSd13: 11 steps
lem-comm-TOFF402-CSd13 : WsL → ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-TOFF402-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff402 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ Toff402 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CSd02 TOFF413: 23 steps
lem-comm-CSd02-TOFF413 : WsL → ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CK02 TOFF413: 23 steps
lem-comm-CK02-TOFF413 : WsL → ⟪ (CK02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CK02 ∷ []) ⟫ʷ
lem-comm-CK02-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK02 ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CK02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm push BOX(2;03) sw2 R: 4 steps
lem-comm-push-BOX⟨2·03⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done

-- comm push SBOX(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done

-- comm push SBOXd(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

-- comm push BOX(0;312) sw3 R: 12 steps
lem-comm-push-BOX⟨0·312⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·312⟩-sw3-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-312 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx3-02 ∷ Toff014 ∷ Sw34 ∷ CCZ013 ∷ Bx3-02 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ Bx3-02 ∷ Toff014 ∷ Sw34 ∷ CCZ013 ∷ Bx3-02 ∷ []) (Bx0-412 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done

-- comm push BOX(4;02) sw2 R: 4 steps
lem-comm-push-BOX⟨4·02⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·02⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done

-- comm push SBOX(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done

-- comm push SBOXd(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻4-0-3-1 ∷ []) (refl) ▸ done

-- comm push BOX(4;03) sw1 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0079 c4)) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done

-- comm push SBOX(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sb4-0-3-2 ∷ []) (refl) ▸ done

-- comm push SBOXd(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻4-0-3-2 ∷ []) (refl) ▸ done

-- comm push BOX(4;03) sw0 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0151 c4)) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done

-- comm push SBOX(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-3-2 ∷ []) (Sb4-1-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0106 c4)) ▸
       at 0 1 (Sb4-1-3-2 ∷ []) (refl) ▸ done

-- comm push SBOXd(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) (Sb⁻4-1-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0105 c4)) ▸
       at 0 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

-- comm SWAP12 BOX(4;03): 11 steps
lem-comm-SWAP12-BOX⟨4·03⟩ : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨4·03⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-03 ∷ []) (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Sw13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Sw12 ∷ Sw13 ∷ []) (sym (wl0096 c4)) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  b1 = at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done

-- resp CZ03 at 2: 4 steps
lem-resp-CZ03-at-2 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ03-at-2 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ []) (Sw12 ∷ Sw01 ∷ CZ13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CZ03 ∷ []) (wl0079 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CZ13 ∷ []) (wl0049 c4) ▸ done

-- comm CZ13 TOFF402: 11 steps
lem-comm-CZ13-TOFF402 : WsL → ⟪ (CZ13 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ13 ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 3 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 4 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CZ13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm TOFF413 CSd02: 23 steps
lem-comm-TOFF413-CSd02 : WsL → ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CSd02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CS02⁻ ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 5 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02⁻ ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CCZ134 CK02: 23 steps
lem-comm-CCZ134-CK02 : WsL → ⟪ (CCZ134 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CK02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CK02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CK02 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CX23 TOFF401: 9 steps
lem-comm-CX23-TOFF401 : WsL → ⟪ (CX23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-TOFF401 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff401 ∷ []) (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ []) (Toff401 ∷ CX23 ∷ [])
  b1 = at 0 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CZ23 TOFF401: 9 steps
lem-comm-CZ23-TOFF401 : WsL → ⟪ (CZ23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-TOFF401 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ23 ∷ Toff401 ∷ []) (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ []) (Toff401 ∷ CZ23 ∷ [])
  b1 = at 0 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm CK02 CCZ134: 23 steps
lem-comm-CK02-CCZ134 : WsL → ⟪ (CK02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CK02 ∷ []) ⟫ʷ
lem-comm-CK02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CK02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm TOFF413 CK02: 23 steps
lem-comm-TOFF413-CK02 : WsL → ⟪ (Toff413 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CK02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CK02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 5 2 (CK01 ∷ Toff423 ∷ []) (sym (c₂ (CK₀₁) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CK02 ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done

-- comm TOFF401 CX23: 9 steps
lem-comm-TOFF401-CX23 : WsL → ⟪ (Toff401 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-TOFF401-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ Toff401 ∷ [])
  b1 = at 1 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done
