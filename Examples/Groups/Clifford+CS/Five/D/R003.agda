{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0018 ; wl0020 ; wl0021 ; wl0028 ; wl0029 ; wl0033 ; wl0036 ; wl0037 ; wl0038 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0072 ; wl0075 ; wl0084 ; wl0085 ; wl0086 ; wl0087 ; wl0090 ; wl0091 ; wl0093 ; wl0096 ; wl0098 ; wl0099 ; wl0100 ; wl0015 ; wl0042 ; wl0043 ; wl0049 ; wl0074 ; wl0079 ; wl0081 ; wl0088 ; wl0105 ; wl0106 ; wl0112 ; wl0113 ; wl0114 ; wl0010 ; wl0035 ; wl0053 ; wl0023 ; wl0024 ; wl0076 ; wl0139 ; wl0140 ; wl0034 ; wl0145 ; wl0146 ; wl0147 ; wl0151)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q5 : WsL → Eqn
  q5 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4)

-- comm CCZ123 CX04: 13 steps
lem-comm-CCZ123-CX04 : WsL → ⟪ (CCZ123 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CX04 c4 = derive (CCZ123 ∷ CX04 ∷ []) (CX04 ∷ CCZ123 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ124 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (CCZ134 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   re 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   re 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 0 7 (CX04 ∷ []) ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))

-- comm CCZ134 CSd02: 23 steps
lem-comm-CCZ134-CSd02 : WsL → ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CSd02 c4 = derive (CCZ134 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ134 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q5 c4) ∷
   re 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   re 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 2 7 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (CZ01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ))

-- comm CZ02 CCZ134: 23 steps
lem-comm-CZ02-CCZ134 : WsL → ⟪ (CZ02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-CCZ134 c4 = derive (CZ02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CZ02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CZ03 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CZ04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 3 7 (CZ04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0013 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0011 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS))
  q11 : WsL → Eqn
  q11 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0008 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0005 c4)

-- comm CS14 TOFF302: 7 steps
lem-comm-CS14-TOFF302 : WsL → ⟪ (CS14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF302 c4 = derive (CS14 ∷ Toff302 ∷ []) (Toff302 ∷ CS14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   re 0 5 (Toff302 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl0099 c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0087 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0018 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK41-at-3 c4 = derive (CK41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw12 ∷ Sw24 ∷ []) (Sw14 ∷ Sw12 ∷ []) (wl0072 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (CZ01 ∷ Sw24 ∷ []) (Sw24 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw12 ∷ Sw14 ∷ []) (Sw24 ∷ Sw12 ∷ []) (wl0093 c4)

-- comm SWAP14 BOX(3;02): 7 steps
lem-comm-SWAP14-BOX⟨3·02⟩ : WsL → ⟪ (Sw14 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨3·02⟩ c4 = derive (Sw14 ∷ Bx3-02 ∷ []) (Bx3-02 ∷ Sw14 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   re 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   re 0 3 (CZ02 ∷ []) ∷
   re 0 1 (Bx3-02 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl0090 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ CK43 ∷ []) (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑))

-- resp CK42 at 3: 6 steps
lem-resp-CK42-at-3 : WsL → ⟪ (CK42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK42-at-3 c4 = derive (CK42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q23 c4) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) (wl0091 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Toff201 ∷ CK43 ∷ []) (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀))

-- comm TOFF301 CK42: 15 steps
lem-comm-TOFF301-CK42 : WsL → ⟪ (Toff301 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Toff301 ∷ []) ⟫ʷ
lem-comm-TOFF301-CK42 c4 = derive (Toff301 ∷ CK42 ∷ []) (CK42 ∷ Toff301 ∷ [])
  (re 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff401 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CK42 ∷ []) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 2 5 (Toff401 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   rw 4 (q1 c4) ∷
   re 0 3 (CK42 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))

-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : WsL → ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-CCZ134 c4 = derive (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 3 7 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw01 ∷ Sw13 ∷ []) (Sw03 ∷ Sw01 ∷ []) (wl0098 c4)

-- comm push SWAP04 sw0 L: 5 steps
lem-comm-push-SWAP04-sw0-L : WsL → ⟪ (Sw04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-push-SWAP04-sw0-L c4 = derive (Sw04 ∷ Sw01 ∷ []) (Sw01 ∷ Sw14 ∷ [])
  (re 0 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   re 1 3 (Sw14 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q31 : WsL → Eqn
  q31 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))

-- comm push CX04 sw2 L: 7 steps
lem-comm-push-CX04-sw2-L : WsL → ⟪ (CX04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw2-L c4 = derive (CX04 ∷ Sw23 ∷ []) (Sw23 ∷ CX04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q30 c4) ∷
   rw⁻ 0 (q29 c4) ∷
   re 1 7 (CX04 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (CZ12 ∷ Sw34 ∷ []) (Sw34 ∷ CZ12 ∷ []) (c₃ (CZ ↑) (Swap))
  q33 : WsL → Eqn
  q33 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0036 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))
  q35 : WsL → Eqn
  q35 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl0033 c4)

-- comm SWAP04 BOX(3;21): 13 steps
lem-comm-SWAP04-BOX⟨3·21⟩ : WsL → ⟪ (Sw04 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw04 ∷ []) ⟫ʷ
lem-comm-SWAP04-BOX⟨3·21⟩ c4 = derive (Sw04 ∷ Bx3-21 ∷ []) (Bx3-21 ∷ Sw04 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CZ13 ∷ []) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   re 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 0 (q32 c4) ∷
   re 1 7 (Sw04 ∷ []) ∷
   re 0 1 (Bx3-21 ∷ []) ∷ []) Eq.refl

-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : WsL → ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX20 c4 = derive (CCZ134 ∷ CX20 ∷ []) (CX20 ∷ CCZ134 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CX30 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw 6 (q5 c4) ∷
   re 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   re 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 2 7 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0085 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (CK10 ∷ Toff423 ∷ []) (Toff423 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Toffᵗ))
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0084 c4)

-- comm TOFF312 CK40: 13 steps
lem-comm-TOFF312-CK40 : WsL → ⟪ (Toff312 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CK40 c4 = derive (Toff312 ∷ CK40 ∷ []) (CK40 ∷ Toff312 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff412 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q36 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   re 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   re 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 0 7 (CK40 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q42 : WsL → Eqn
  q42 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4)

-- comm CCZ034 CSd12: 15 steps
lem-comm-CCZ034-CSd12 : WsL → ⟪ (CCZ034 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CSd12 c4 = derive (CCZ034 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))

-- comm CCZ014 CS23: 9 steps
lem-comm-CCZ014-CS23 : WsL → ⟪ (CCZ014 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CS23 c4 = derive (CCZ014 ∷ CS23 ∷ []) (CS23 ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CCZ014 ∷ []) ∷ []) Eq.refl

-- comm CCZ014 CSd23: 9 steps
lem-comm-CCZ014-CSd23 : WsL → ⟪ (CCZ014 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CSd23 c4 = derive (CCZ014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 3 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0038 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0045 c4)

-- comm TOFF314 CX02: 23 steps
lem-comm-TOFF314-CX02 : WsL → ⟪ (Toff314 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CX02 c4 = derive (Toff314 ∷ CX02 ∷ []) (CX02 ∷ Toff314 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (Toff214 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   re 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   re 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 2 7 (CX04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ Sw12 ∷ []) (Sw02 ∷ Sw01 ∷ []) (wl0100 c4)

-- resp SWAP02 at 1: 2 steps
lem-resp-SWAP02-at-1 : WsL → ⟪ (Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP02-at-1 c4 = derive (Sw02 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q16 c4) ∷
   rw⁻ 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw02 ∷ Sw34 ∷ []) (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap))
  q50 : WsL → Eqn
  q50 c4 = eqn (CZ12 ∷ Sw03 ∷ []) (Sw03 ∷ CZ12 ∷ []) (wl0086 c4)

-- comm SWAP02 BOX(3;41): 11 steps
lem-comm-SWAP02-BOX⟨3·41⟩ : WsL → ⟪ (Sw02 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨3·41⟩ c4 = derive (Sw02 ∷ Bx3-41 ∷ []) (Bx3-41 ∷ Sw02 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (Sw03 ∷ []) ∷
   rw⁻ 2 (q50 c4) ∷
   re 3 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw 4 (q49 c4) ∷
   re 0 5 (CZ14 ∷ []) ∷
   re 0 1 (Bx3-41 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wl0057 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) (wl0058 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Toff102 ∷ CX43 ∷ []) (CX43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))
  q54 : WsL → Eqn
  q54 c4 = eqn (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) (wl0059 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wl0060 c4)

-- comm CX31 TOFF204: 11 steps
lem-comm-CX31-TOFF204 : WsL → ⟪ (CX31 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF204 c4 = derive (CX31 ∷ Toff204 ∷ []) (Toff204 ∷ CX31 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CX42 ∷ []) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 6 (q55 c4) ∷
   re 0 7 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl0020 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Toff201 ∷ CX34 ∷ []) (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁))
  q58 : WsL → Eqn
  q58 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl0021 c4)

-- comm CX24 TOFF301: 5 steps
lem-comm-CX24-TOFF301 : WsL → ⟪ (CX24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-TOFF301 c4 = derive (CX24 ∷ Toff301 ∷ []) (Toff301 ∷ CX24 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw⁻ 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   re 0 3 (Toff301 ∷ []) ∷ []) Eq.refl

-- comm CX21 TOFF304: 15 steps
lem-comm-CX21-TOFF304 : WsL → ⟪ (CX21 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF304 c4 = derive (CX21 ∷ Toff304 ∷ []) (Toff304 ∷ CX21 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (CX42 ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q55 c4) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 (q2 c4) ∷
   re 0 9 (Toff304 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (CX10 ∷ Toff324 ∷ []) (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI))

-- comm CX20 TOFF314: 23 steps
lem-comm-CX20-TOFF314 : WsL → ⟪ (CX20 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-TOFF314 c4 = derive (CX20 ∷ Toff314 ∷ []) (Toff314 ∷ CX20 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (Toff214 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (Toff314 ∷ []) ∷
   rw 6 (q47 c4) ∷
   rw 5 (q59 c4) ∷
   rw 4 (q45 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 3 7 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (Toff314 ∷ []) ∷ []) Eq.refl

-- comm CK40 TOFF312: 13 steps
lem-comm-CK40-TOFF312 : WsL → ⟪ (CK40 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-TOFF312 c4 = derive (CK40 ∷ Toff312 ∷ []) (Toff312 ∷ CK40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (Toff412 ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (Toff413 ∷ []) ∷
   rw 4 (q38 c4) ∷
   rw 3 (q37 c4) ∷
   rw 2 (q36 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q2 c4) ∷
   re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 7 (CK40 ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw14 ∷ Sw23 ∷ []) (Sw23 ∷ Sw14 ∷ []) (wl0074 c4)

-- comm SWAP13 BOX(2;04): 13 steps
lem-comm-SWAP13-BOX⟨2·04⟩ : WsL → ⟪ (Sw13 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨2·04⟩ c4 = derive (Sw13 ∷ Bx2-04 ∷ []) (Bx2-04 ∷ Sw13 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Sw14 ∷ []) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q60 c4) ∷
   re 6 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 0 7 (CZ04 ∷ []) ∷
   re 0 1 (Bx2-04 ∷ []) ∷ []) Eq.refl

-- comm TOFF214 CX03: 9 steps
lem-comm-TOFF214-CX03 : WsL → ⟪ (Toff214 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CX03 c4 = derive (Toff214 ∷ CX03 ∷ []) (CX03 ∷ Toff214 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw⁻ 1 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (CX03 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Toff012 ∷ CX43 ∷ []) (CX43 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₁₀))

-- comm CX32 TOFF014: 9 steps
lem-comm-CX32-TOFF014 : WsL → ⟪ (CX32 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX32 ∷ []) ⟫ʷ
lem-comm-CX32-TOFF014 c4 = derive (CX32 ∷ Toff014 ∷ []) (Toff014 ∷ CX32 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX42 ∷ []) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q54 c4) ∷
   re 4 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff014 ∷ []) ∷ []) Eq.refl

-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : WsL → ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS24 c4 = derive (CCZ013 ∷ CS24 ∷ []) (CS24 ∷ CCZ013 ∷ [])
  (re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 3 (q44 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 2 5 (CCZ014 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   rw 4 (q1 c4) ∷
   re 0 3 (CS24 ∷ []) ∷ []) Eq.refl

-- comm CCZ013 CSd24: 15 steps
lem-comm-CCZ013-CSd24 : WsL → ⟪ (CCZ013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd24 c4 = derive (CCZ013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ013 ∷ [])
  (re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 2 5 (CCZ014 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   rw 4 (q1 c4) ∷
   re 0 3 (CS24⁻ ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0043 c4)

-- comm push SBOXd(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L c4 = derive (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻1-0-3-2 ∷ [])
  (re 0 1 (CS03⁻ ∷ []) ∷
   rw 0 (q62 c4) ∷
   re 1 1 (Sb⁻1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0001 c4)

-- comm push SBOX(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L c4 = derive (Sb2-0-3-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-3-2 ∷ [])
  (re 0 1 (CS03 ∷ []) ∷
   rw 0 (q63 c4) ∷
   re 1 1 (Sb1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl0079 c4)

-- comm push BOX(2;03) sw1 L: 3 steps
lem-comm-push-BOX⟨2·03⟩-sw1-L : WsL → ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw1-L c4 = derive (Bx2-03 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-03 ∷ [])
  (re 0 1 (CZ03 ∷ []) ∷
   rw 0 (q64 c4) ∷
   re 1 1 (Bx1-03 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0042 c4)

-- comm push SBOXd(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L c4 = derive (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (Sw01 ∷ Sb⁻0-1-3-2 ∷ [])
  (re 0 1 (CS03⁻ ∷ []) ∷
   rw 0 (q65 c4) ∷
   re 1 1 (Sb⁻0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0015 c4)

-- comm push SBOX(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L c4 = derive (Sb1-0-3-2 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-3-2 ∷ [])
  (re 0 1 (CS03 ∷ []) ∷
   rw 0 (q66 c4) ∷
   re 1 1 (Sb0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0049 c4)

-- comm push BOX(1;03) sw0 L: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw0-L : WsL → ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw0-L c4 = derive (Bx1-03 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-13 ∷ [])
  (re 0 1 (CZ03 ∷ []) ∷
   rw 0 (q67 c4) ∷
   re 1 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0105 c4)

-- comm push CSd14 sw0 L: 5 steps
lem-comm-push-CSd14-sw0-L : WsL → ⟪ (CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd14-sw0-L c4 = derive (CS14⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q68 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   re 1 3 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0106 c4)

-- comm push CS14 sw0 L: 5 steps
lem-comm-push-CS14-sw0-L : WsL → ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS14-sw0-L c4 = derive (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ [])
  (re 0 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   re 1 3 (CS04 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L c4 = derive (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-1-2-3 ∷ [])
  (re 0 1 (CS13⁻ ∷ []) ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 1 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L c4 = derive (Sb0-1-3-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-2-3 ∷ [])
  (re 0 1 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 1 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;13) sw2 L: 4 steps
lem-comm-push-BOX⟨0·13⟩-sw2-L : WsL → ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw2-L c4 = derive (Bx0-13 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-12 ∷ [])
  (re 0 1 (CZ13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 1 1 (Bx0-12 ∷ []) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wl0112 c4)

-- comm push SBOXd(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L c4 = derive (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻0-2-1-3 ∷ [])
  (re 0 1 (CS12⁻ ∷ []) ∷
   rw 0 (q70 c4) ∷
   re 1 1 (Sb⁻0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wl0113 c4)

-- comm push SBOX(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L c4 = derive (Sb0-1-2-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-1-3 ∷ [])
  (re 0 1 (CS12 ∷ []) ∷
   rw 0 (q71 c4) ∷
   re 1 1 (Sb0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ []) (wl0114 c4)

-- comm push BOX(0;12) sw1 L: 3 steps
lem-comm-push-BOX⟨0·12⟩-sw1-L : WsL → ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw1-L c4 = derive (Bx0-12 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-21 ∷ [])
  (re 0 1 (CZ12 ∷ []) ∷
   rw 0 (q72 c4) ∷
   re 1 1 (Bx0-21 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;21) sw1 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw1-R c4 = derive (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   re 0 1 (Bx0-12 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q71 c4) ∷
   re 0 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q70 c4) ∷
   re 0 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;12) sw2 R: 4 steps
lem-comm-push-BOX⟨0·12⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CZ13 ∷ []) ∷
   re 0 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R c4 = derive (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS13 ∷ []) ∷
   re 0 1 (Sb0-1-3-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R c4 = derive (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   re 0 1 (Sb⁻0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) (wl0081 c4)

-- comm push CK41 sw0 R: 5 steps
lem-comm-push-CK41-sw0-R : WsL → ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CK41-sw0-R c4 = derive (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (CK40 ∷ []) ∷ []) Eq.refl

-- comm push CS14 sw0 R: 5 steps
lem-comm-push-CS14-sw0-R : WsL → ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CS14-sw0-R c4 = derive (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (CS04 ∷ []) ∷ []) Eq.refl

-- comm push CSd14 sw0 R: 5 steps
lem-comm-push-CSd14-sw0-R : WsL → ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CSd14-sw0-R c4 = derive (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (CS04⁻ ∷ []) ∷ []) Eq.refl

-- comm push CS04 sw0 R: 5 steps
lem-comm-push-CS04-sw0-R : WsL → ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw0-R c4 = derive (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (CS14 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;13) sw0 R: 3 steps
lem-comm-push-BOX⟨0·13⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw0-R c4 = derive (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q67 c4) ∷
   re 0 1 (Bx1-03 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R c4 = derive (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q66 c4) ∷
   re 0 1 (Sb1-0-3-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R c4 = derive (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   re 0 1 (Sb⁻1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0088 c4)

-- comm push CK40 sw1 R: 5 steps
lem-comm-push-CK40-sw1-R : WsL → ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw1-R c4 = derive (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (CK40 ∷ []) ∷ []) Eq.refl

-- comm push BOX(1;03) sw1 R: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw1-R c4 = derive (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q64 c4) ∷
   re 0 1 (Bx2-03 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R c4 = derive (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q63 c4) ∷
   re 0 1 (Sb2-0-3-1 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R c4 = derive (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   re 0 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))

-- comm CCZ014 CX32: 9 steps
lem-comm-CCZ014-CX32 : WsL → ⟪ (CCZ014 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX32 c4 = derive (CCZ014 ∷ CX32 ∷ []) (CX32 ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX42 ∷ []) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q75 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   re 1 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw12 ∷ Bx2-43 ∷ []) (Bx2-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- comm push BOX(4;203) sw1 L: 12 steps
lem-comm-push-BOX⟨4·203⟩-sw1-L : WsL → ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw1-L c4 = derive (Bx4-203 ∷ Sw12 ∷ []) (Sw12 ∷ Bx4-103 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 5 (q76 c4) ∷
   re 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 6 (q14 c4) ∷
   re 3 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 3 (q14 c4) ∷
   re 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 2 (q14 c4) ∷
   re 1 6 (Bx4-103 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4 = derive (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-4-2-1 ∷ [])
  (re 0 1 (CS34⁻ ∷ []) ∷
   rw 0 (q40 c4) ∷
   re 1 1 (Sb⁻0-4-2-1 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4 = derive (Sb0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-2-1 ∷ [])
  (re 0 1 (CS34 ∷ []) ∷
   rw 0 (q11 c4) ∷
   re 1 1 (Sb0-4-2-1 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0035 c4)

-- comm push BOX(0;43) sw2 L: 3 steps
lem-comm-push-BOX⟨0·43⟩-sw2-L : WsL → ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·43⟩-sw2-L c4 = derive (Bx0-43 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-42 ∷ [])
  (re 0 1 (CZ34 ∷ []) ∷
   rw 0 (q77 c4) ∷
   re 1 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4)

-- comm push SBOXd(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L c4 = derive (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻0-4-1-2 ∷ [])
  (re 0 1 (CS24⁻ ∷ []) ∷
   rw 0 (q78 c4) ∷
   re 1 1 (Sb⁻0-4-1-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (Sb0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L c4 = derive (Sb0-4-2-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-1-2 ∷ [])
  (re 0 1 (CS24 ∷ []) ∷
   rw 0 (q12 c4) ∷
   re 1 1 (Sb0-4-1-2 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl0053 c4)

-- comm push BOX(0;42) sw1 L: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw1-L : WsL → ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw1-L c4 = derive (Bx0-42 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-41 ∷ [])
  (re 0 1 (CZ24 ∷ []) ∷
   rw 0 (q79 c4) ∷
   re 1 1 (Bx0-41 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4 = derive (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻0-3-1-2 ∷ [])
  (re 0 1 (CS14⁻ ∷ []) ∷
   re 0 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 1 1 (Sb⁻0-3-1-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4 = derive (Sb0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-1-2 ∷ [])
  (re 0 1 (CS14 ∷ []) ∷
   re 0 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 1 1 (Sb0-3-1-2 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;41) sw3 L: 4 steps
lem-comm-push-BOX⟨0·41⟩-sw3-L : WsL → ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw3-L c4 = derive (Bx0-41 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-31 ∷ [])
  (re 0 1 (CZ14 ∷ []) ∷
   re 0 1 (Sw34 ∷ CZ13 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 1 1 (Bx0-31 ∷ []) ∷ []) Eq.refl

-- comm push CX04 sw2 R: 7 steps
lem-comm-push-CX04-sw2-R : WsL → ⟪ (Sw23 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw2-R c4 = derive (Sw23 ∷ CX04 ∷ []) (CX04 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   re 0 7 (CX04 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0010 c4)

-- comm push CX04 sw1 R: 5 steps
lem-comm-push-CX04-sw1-R : WsL → ⟪ (Sw12 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw1-R c4 = derive (Sw12 ∷ CX04 ∷ []) (CX04 ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q80 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (CX04 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L c4 = derive (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-2-1-3 ∷ [])
  (re 0 1 (CS13⁻ ∷ []) ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 1 1 (Sb⁻0-2-1-3 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L c4 = derive (Sb0-3-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-2-1-3 ∷ [])
  (re 0 1 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 1 1 (Sb0-2-1-3 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;31) sw2 L: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw2-L : WsL → ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw2-L c4 = derive (Bx0-31 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-21 ∷ [])
  (re 0 1 (CZ13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   re 1 1 (Bx0-21 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;21) sw2 R: 4 steps
lem-comm-push-BOX⟨0·21⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CZ13 ∷ []) ∷
   re 0 1 (Bx0-31 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R c4 = derive (Sw23 ∷ Sb0-2-1-3 ∷ []) (Sb0-3-1-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS13 ∷ []) ∷
   re 0 1 (Sb0-3-1-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R c4 = derive (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-3-1-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   re 0 1 (Sb⁻0-3-1-2 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;31) sw3 R: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw3-R c4 = derive (Sw34 ∷ Bx0-31 ∷ []) (Bx0-41 ∷ Sw34 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (CZ14 ∷ []) ∷
   re 0 1 (Bx0-41 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4 = derive (Sw34 ∷ Sb0-3-1-2 ∷ []) (Sb0-4-1-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (CS14 ∷ []) ∷
   re 0 1 (Sb0-4-1-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4 = derive (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (Sb⁻0-4-1-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (CS14⁻ ∷ []) ∷
   re 0 1 (Sb⁻0-4-1-2 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;41) sw1 R: 3 steps
lem-comm-push-BOX⟨0·41⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw1-R c4 = derive (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q79 c4) ∷
   re 0 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4 = derive (Sw12 ∷ Sb0-4-1-2 ∷ []) (Sb0-4-2-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q12 c4) ∷
   re 0 1 (Sb0-4-2-1 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4 = derive (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) (Sb⁻0-4-2-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q78 c4) ∷
   re 0 1 (Sb⁻0-4-2-1 ∷ []) ∷ []) Eq.refl

-- comm push BOX(0;42) sw2 R: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q77 c4) ∷
   re 0 1 (Bx0-43 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4 = derive (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q11 c4) ∷
   re 0 1 (Sb0-4-3-1 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4 = derive (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw⁻ 0 (q40 c4) ∷
   re 0 1 (Sb⁻0-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Bx1-43 ∷ []) (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- comm push BOX(4;103) sw1 R: 12 steps
lem-comm-push-BOX⟨4·103⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw1-R c4 = derive (Sw12 ∷ Bx4-103 ∷ []) (Bx4-203 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q14 c4) ∷
   re 1 3 (Toff402 ∷ []) ∷
   rw 2 (q81 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 3 3 (Toff402 ∷ []) ∷
   rw⁻ 6 (q14 c4) ∷
   re 4 3 (CCZ024 ∷ []) ∷
   rw 5 (q81 c4) ∷
   re 0 6 (Bx4-203 ∷ []) ∷ []) Eq.refl

-- comm CX40 TOFF213: 13 steps
lem-comm-CX40-TOFF213 : WsL → ⟪ (CX40 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-TOFF213 c4 = derive (CX40 ∷ Toff213 ∷ []) (Toff213 ∷ CX40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (Toff214 ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (Toff314 ∷ []) ∷
   rw 4 (q47 c4) ∷
   rw 3 (q59 c4) ∷
   rw 2 (q45 c4) ∷
   re 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 1 (q2 c4) ∷
   re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 7 (CX40 ∷ []) ∷ []) Eq.refl

-- comm TOFF213 CX40: 13 steps
lem-comm-TOFF213-CX40 : WsL → ⟪ (Toff213 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CX40 c4 = derive (Toff213 ∷ CX40 ∷ []) (CX40 ∷ Toff213 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff214 ∷ []) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q45 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   re 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   re 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 0 7 (CX40 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wl0076 c4)

-- comm push BOX(0;21) sw0 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw0-R c4 = derive (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q82 c4) ∷
   re 0 1 (Bx1-20 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0024 c4)

-- comm push SBOX(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q83 c4) ∷
   re 0 1 (Sb1-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0023 c4)

-- comm push SBOXd(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (Sb⁻1-2-0-3 ∷ []) ∷ []) Eq.refl

-- comm push BOX(1;20) sw1 R: 4 steps
lem-comm-push-BOX⟨1·20⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·20⟩-sw1-R c4 = derive (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   re 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw 0 (q14 c4) ∷
   re 0 1 (Bx2-10 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb1-2-0-3 ∷ []) (Sb2-1-0-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 0 (q14 c4) ∷
   re 0 1 (Sb2-1-0-3 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   re 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 0 (q14 c4) ∷
   re 0 1 (Sb⁻2-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0139 c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0140 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Bx2-10 ∷ Sw23 ∷ []) (Sw23 ∷ Bx2-10 ∷ []) (c₂ (CZ) (Swap))

-- comm push BOX(1;230) sw2 R: 8 steps
lem-comm-push-BOX⟨1·230⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·230⟩-sw2-R c4 = derive (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw⁻ 5 (q87 c4) ∷
   re 0 6 (Bx1-320 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Bx3-10 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-10 ∷ []) (c₂ (CZ) (Swap ↑))

-- comm push BOX(1;320) sw3 R: 12 steps
lem-comm-push-BOX⟨1·320⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·320⟩-sw3-R c4 = derive (Sw34 ∷ Bx1-320 ∷ []) (Bx1-420 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (Toff124 ∷ []) ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (Toff124 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ124 ∷ []) ∷
   rw⁻ 5 (q88 c4) ∷
   re 0 6 (Bx1-420 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Bx4-10 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-10 ∷ []) (c₂ (CZ) (Swap))

-- comm push BOX(1;420) sw2 R: 12 steps
lem-comm-push-BOX⟨1·420⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·420⟩-sw2-R c4 = derive (Sw23 ∷ Bx1-420 ∷ []) (Bx1-430 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (Toff134 ∷ []) ∷
   rw⁻ 2 (q89 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (Toff134 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 5 (q89 c4) ∷
   re 0 6 (Bx1-430 ∷ []) ∷ []) Eq.refl

-- comm push BOX(4;10) sw1 R: 4 steps
lem-comm-push-BOX⟨4·10⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·10⟩-sw1-R c4 = derive (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (CZ02 ∷ []) ∷
   re 0 1 (Bx4-20 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb4-1-0-3 ∷ []) (Sb4-2-0-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (CS02 ∷ []) ∷
   re 0 1 (Sb4-2-0-3 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻4-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb⁻4-1-0-3 ∷ []) (Sb⁻4-2-0-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (CS02⁻ ∷ []) ∷
   re 0 1 (Sb⁻4-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (CZ12 ∷ Sw01 ∷ []) (Sw01 ∷ CZ02 ∷ []) (wl0145 c4)

-- comm push BOX(4;20) sw0 R: 3 steps
lem-comm-push-BOX⟨4·20⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·20⟩-sw0-R c4 = derive (Sw01 ∷ Bx4-20 ∷ []) (Bx4-21 ∷ Sw01 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw⁻ 0 (q90 c4) ∷
   re 0 1 (Bx4-21 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0146 c4)

-- comm push SBOX(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb4-2-0-3 ∷ []) (Sb4-2-1-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   re 0 1 (Sb4-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0147 c4)

-- comm push SBOXd(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻4-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb⁻4-2-0-3 ∷ []) (Sb⁻4-2-1-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   re 0 1 (Sb⁻4-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))

-- comm CSd13 TOFF402: 11 steps
lem-comm-CSd13-TOFF402 : WsL → ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF402 c4 = derive (CS13⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS13⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw 2 (q42 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw 4 (q40 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 6 (q39 c4) ∷
   re 0 7 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0046 c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0047 c4)

-- comm CS13 TOFF402: 11 steps
lem-comm-CS13-TOFF402 : WsL → ⟪ (CS13 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF402 c4 = derive (CS13 ∷ Toff402 ∷ []) (Toff402 ∷ CS13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q94 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 6 (q95 c4) ∷
   re 0 7 (Toff402 ∷ []) ∷ []) Eq.refl

-- comm SWAP03 BOX(4;21): 3 steps
lem-comm-SWAP03-BOX⟨4·21⟩ : WsL → ⟪ (Sw03 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨4·21⟩ c4 = derive (Sw03 ∷ Bx4-21 ∷ []) (Bx4-21 ∷ Sw03 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q50 c4) ∷
   re 0 1 (Bx4-21 ∷ []) ∷ []) Eq.refl

-- comm TOFF402 CSd13: 11 steps
lem-comm-TOFF402-CSd13 : WsL → ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-TOFF402-CSd13 c4 = derive (Toff402 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff402 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   re 1 7 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (CS01⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ))

-- comm CSd02 TOFF413: 23 steps
lem-comm-CSd02-TOFF413 : WsL → ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF413 c4 = derive (CS02⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (Toff412 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (Toff413 ∷ []) ∷
   rw 6 (q38 c4) ∷
   rw 5 (q96 c4) ∷
   rw 4 (q36 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 3 7 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (CK01 ∷ Toff423 ∷ []) (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ))

-- comm CK02 TOFF413: 23 steps
lem-comm-CK02-TOFF413 : WsL → ⟪ (CK02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CK02 ∷ []) ⟫ʷ
lem-comm-CK02-TOFF413 c4 = derive (CK02 ∷ Toff413 ∷ []) (Toff413 ∷ CK02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CK03 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CK04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (Toff412 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (Toff413 ∷ []) ∷
   rw 6 (q38 c4) ∷
   rw 5 (q97 c4) ∷
   rw 4 (q36 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 3 7 (CK04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (Toff413 ∷ []) ∷ []) Eq.refl

-- comm push BOX(2;03) sw2 R: 4 steps
lem-comm-push-BOX⟨2·03⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw2-R c4 = derive (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 0 1 (Bx3-02 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R c4 = derive (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 0 1 (Sb3-0-2-1 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R c4 = derive (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 0 1 (Sb⁻3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Bx3-02 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-02 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- comm push BOX(0;312) sw3 R: 12 steps
lem-comm-push-BOX⟨0·312⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·312⟩-sw3-R c4 = derive (Sw34 ∷ Bx0-312 ∷ []) (Bx0-412 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (CCZ014 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (Toff014 ∷ []) ∷
   rw⁻ 2 (q98 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (Toff014 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ014 ∷ []) ∷
   rw⁻ 5 (q98 c4) ∷
   re 0 6 (Bx0-412 ∷ []) ∷ []) Eq.refl

-- comm push BOX(4;02) sw2 R: 4 steps
lem-comm-push-BOX⟨4·02⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·02⟩-sw2-R c4 = derive (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CZ03 ∷ []) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4 = derive (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS03 ∷ []) ∷
   re 0 1 (Sb4-0-3-1 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4 = derive (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   re 0 1 (Sb⁻4-0-3-1 ∷ []) ∷ []) Eq.refl

-- comm push BOX(4;03) sw1 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw1-R c4 = derive (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q64 c4) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R c4 = derive (Sw12 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q63 c4) ∷
   re 0 1 (Sb4-0-3-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R c4 = derive (Sw12 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   re 0 1 (Sb⁻4-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0151 c4)

-- comm push BOX(4;03) sw0 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw0-R c4 = derive (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q99 c4) ∷
   re 0 1 (Bx4-13 ∷ []) ∷ []) Eq.refl

-- comm push SBOX(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4 = derive (Sw01 ∷ Sb4-0-3-2 ∷ []) (Sb4-1-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q69 c4) ∷
   re 0 1 (Sb4-1-3-2 ∷ []) ∷ []) Eq.refl

-- comm push SBOXd(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4 = derive (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) (Sb⁻4-1-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q68 c4) ∷
   re 0 1 (Sb⁻4-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw12 ∷ Sw23 ∷ []) (Sw13 ∷ Sw12 ∷ []) (wl0075 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap))
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw12 ∷ Sw13 ∷ []) (Sw23 ∷ Sw12 ∷ []) (wl0096 c4)

-- comm SWAP12 BOX(4;03): 11 steps
lem-comm-SWAP12-BOX⟨4·03⟩ : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨4·03⟩ c4 = derive (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (Sw13 ∷ []) ∷
   rw⁻ 1 (q100 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (CZ03 ∷ []) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

-- resp CZ03 at 2: 4 steps
lem-resp-CZ03-at-2 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ03-at-2 c4 = derive (CZ03 ∷ []) (Sw12 ∷ Sw01 ∷ CZ13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q64 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0034 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Toff201 ∷ CZ34 ∷ []) (CZ34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CZ))

-- comm CZ13 TOFF402: 11 steps
lem-comm-CZ13-TOFF402 : WsL → ⟪ (CZ13 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF402 c4 = derive (CZ13 ∷ Toff402 ∷ []) (Toff402 ∷ CZ13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q35 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CZ24 ∷ []) ∷
   rw 2 (q103 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 4 (q77 c4) ∷
   re 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw 6 (q33 c4) ∷
   re 0 7 (Toff402 ∷ []) ∷ []) Eq.refl

-- comm TOFF413 CSd02: 23 steps
lem-comm-TOFF413-CSd02 : WsL → ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CSd02 c4 = derive (Toff413 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff413 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (Toff412 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 5 (q96 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   re 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 2 7 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))

-- comm CCZ134 CK02: 23 steps
lem-comm-CCZ134-CK02 : WsL → ⟪ (CCZ134 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CK02 c4 = derive (CCZ134 ∷ CK02 ∷ []) (CK02 ∷ CCZ134 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CK03 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CK04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 6 (q5 c4) ∷
   re 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   re 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 2 7 (CK04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (CCZ134 ∷ []) ∷ []) Eq.refl

-- comm CX23 TOFF401: 9 steps
lem-comm-CX23-TOFF401 : WsL → ⟪ (CX23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-TOFF401 c4 = derive (CX23 ∷ Toff401 ∷ []) (Toff401 ∷ CX23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX24 ∷ []) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   re 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff401 ∷ []) ∷ []) Eq.refl

-- comm CZ23 TOFF401: 9 steps
lem-comm-CZ23-TOFF401 : WsL → ⟪ (CZ23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-TOFF401 c4 = derive (CZ23 ∷ Toff401 ∷ []) (Toff401 ∷ CZ23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CZ24 ∷ []) ∷
   rw 1 (q103 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw 3 (q77 c4) ∷
   re 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (Toff401 ∷ []) ∷ []) Eq.refl

-- comm CK02 CCZ134: 23 steps
lem-comm-CK02-CCZ134 : WsL → ⟪ (CK02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CK02 ∷ []) ⟫ʷ
lem-comm-CK02-CCZ134 c4 = derive (CK02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CK02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CK03 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CK04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 3 7 (CK04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

-- comm TOFF413 CK02: 23 steps
lem-comm-TOFF413-CK02 : WsL → ⟪ (Toff413 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CK02 c4 = derive (Toff413 ∷ CK02 ∷ []) (CK02 ∷ Toff413 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CK03 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CK04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (Toff412 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   re 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 2 7 (CK04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) ∷
   rw 1 (q1 c4) ∷
   re 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (Toff413 ∷ []) ∷ []) Eq.refl

-- comm TOFF401 CX23: 9 steps
lem-comm-TOFF401-CX23 : WsL → ⟪ (Toff401 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-TOFF401-CX23 c4 = derive (Toff401 ∷ CX23 ∷ []) (CX23 ∷ Toff401 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX24 ∷ []) ∷
   rw⁻ 3 (q58 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   re 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (Toff401 ∷ []) ∷ []) Eq.refl
