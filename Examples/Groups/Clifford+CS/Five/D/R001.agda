{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0025 ; wl0026 ; wl0027 ; wl0028 ; wl0029 ; wl0030 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0038 ; wl0039 ; wl0040 ; wl0041 ; wl0042 ; wl0043 ; wl0044 ; wl0045)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)

-- resp CCZ013 at 2: 5 steps
lem-resp-CCZ013-at-2 : WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ013-at-2 c4 = derive (CCZ013 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0004 c4)

-- resp TOFF103 at 2: 5 steps
lem-resp-TOFF103-at-2 : WsL → ⟪ (Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF103-at-2 c4 = derive (Toff103 ∷ []) (Sw12 ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff203 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 1 (q4 c4) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) (wl0005 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw01 ∷ CZ24 ∷ []) (CZ24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- resp CZ14 at 2: 4 steps
lem-resp-CZ14-at-2 : WsL → ⟪ (CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ14-at-2 c4 = derive (CZ14 ∷ []) (Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 1 (q6 c4) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q11 : WsL → Eqn
  q11 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q14 : WsL → Eqn
  q14 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q19 : WsL → Eqn
  q19 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q22 : WsL → Eqn
  q22 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q27 : WsL → Eqn
  q27 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))

-- resp CCZ034 at 2: 187 steps
lem-resp-CCZ034-at-2 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-2 c4 = derive (CCZ034 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   re 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   re 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   re 4 7 (CS04 ∷ []) ∷
   rw 5 (q7 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 3 (q9 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q7 c4) ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   re 3 3 (CCZ014 ∷ []) ∷
   re 2 3 (CCZ024 ∷ []) ∷
   re 1 3 (CCZ034 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q8 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q28 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   re 2 3 (CCZ134 ∷ []) ∷ []) Eq.refl

-- resp CCZ034 at 1: 79 steps
lem-resp-CCZ034-at-1 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-1 c4 = derive (CCZ034 ∷ []) (Sw01 ∷ CCZ134 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   re 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   re 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   re 4 7 (CS04 ∷ []) ∷
   rw 5 (q7 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 3 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ124 ∷ []) ∷
   re 1 3 (CCZ134 ∷ []) ∷ []) Eq.refl

-- resp CS04 at 1: 6 steps
lem-resp-CS04-at-1 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS04-at-1 c4 = derive (CS04 ∷ []) (Sw01 ∷ CS14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   re 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   re 1 3 (CS14 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- resp CSd04 at 1: 6 steps
lem-resp-CSd04-at-1 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd04-at-1 c4 = derive (CS04⁻ ∷ []) (Sw01 ∷ CS14⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   re 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   re 1 3 (CS14⁻ ∷ []) ∷ []) Eq.refl

-- resp CS03 at 1: 2 steps
lem-resp-CS03-at-1 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS03-at-1 c4 = derive (CS03 ∷ []) (Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q27 c4) ∷ []) Eq.refl

-- resp CS04 at 3: 20 steps
lem-resp-CS04-at-3 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS04-at-3 c4 = derive (CS04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   re 1 7 (CS04 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 2 3 (CS04 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   re 3 3 (CS14 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (CS01⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑))
  q35 : WsL → Eqn
  q35 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)

-- resp CSd04 at 3: 20 steps
lem-resp-CSd04-at-3 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd04-at-3 c4 = derive (CS04⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   re 1 7 (CS04⁻ ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 2 3 (CS04⁻ ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q38 : WsL → Eqn
  q38 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)

-- comm CS12 CCZ034: 15 steps
lem-comm-CS12-CCZ034 : WsL → ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-CCZ034 c4 = derive (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q15 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q38 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl0026 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (CCZ012 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CZ))
  q42 : WsL → Eqn
  q42 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0029 c4)

-- comm CZ12 CCZ034: 15 steps
lem-comm-CZ12-CCZ034 : WsL → ⟪ (CZ12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-CCZ034 c4 = derive (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 1 (q39 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CZ24 ∷ []) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   re 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q43 c4) ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q45 : WsL → Eqn
  q45 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q46 : WsL → Eqn
  q46 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q47 : WsL → Eqn
  q47 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q48 : WsL → Eqn
  q48 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q49 : WsL → Eqn
  q49 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q53 : WsL → Eqn
  q53 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q54 : WsL → Eqn
  q54 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- resp TOFF034 at 1: 101 steps
lem-resp-TOFF034-at-1 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-1 c4 = derive (Toff034 ∷ []) (Sw01 ∷ Toff134 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   re 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q8 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q44 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 9 (q47 c4) ∷
   rw 10 (q9 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q48 c4) ∷
   rw⁻ 8 (q49 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q44 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 6 (q51 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q28 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 8 (q52 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 10 (q47 c4) ∷
   rw 3 (q54 c4) ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff124 ∷ []) ∷
   re 1 3 (Toff134 ∷ []) ∷ []) Eq.refl

-- comm CCZ034 CS12: 15 steps
lem-comm-CCZ034-CS12 : WsL → ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CS12 c4 = derive (CCZ034 ∷ CS12 ∷ []) (CS12 ∷ CCZ034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CS24 ∷ []) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- resp CSd14 at 3: 6 steps
lem-resp-CSd14-at-3 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd14-at-3 c4 = derive (CS14⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q55 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 2 (q56 c4) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- resp CS14 at 3: 6 steps
lem-resp-CS14-at-3 : WsL → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS14-at-3 c4 = derive (CS14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q31 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 2 (q57 c4) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))

-- resp CCZ134 at 2: 4 steps
lem-resp-CCZ134-at-2 : WsL → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ134-at-2 c4 = derive (CCZ134 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q58 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 1 (q59 c4) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 c4)

-- resp CS02 at 1: 2 steps
lem-resp-CS02-at-1 : WsL → ⟪ (CS02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS02-at-1 c4 = derive (CS02 ∷ []) (Sw01 ∷ CS12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 c4)

-- resp CSd02 at 1: 2 steps
lem-resp-CSd02-at-1 : WsL → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd02-at-1 c4 = derive (CS02⁻ ∷ []) (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q61 c4) ∷ []) Eq.refl

-- nat 1 CCZ023: 2 steps
lem-nat-1-CCZ023 : WsL → ⟪ (Sw12 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ023 c4 = derive (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

-- nat 1 TOFF203: 2 steps
lem-nat-1-TOFF203 : WsL → ⟪ (Sw12 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF203 c4 = derive (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

-- nat 1 BOX(0;24): 3 steps
lem-nat-1-BOX⟨0·24⟩ : WsL → ⟪ (Sw12 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·24⟩ c4 = derive (Sw12 ∷ Bx0-24 ∷ []) (Bx0-14 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q5 c4) ∷
   re 0 1 (Bx0-14 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw12 ∷ Bx0-24 ∷ []) (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4)

-- nat 1 BOX(2;034): 8 steps
lem-nat-1-BOX⟨2·034⟩ : WsL → ⟪ (Sw12 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·034⟩ c4 = derive (Sw12 ∷ Bx2-034 ∷ []) (Bx1-034 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q62 c4) ∷
   rw 5 (q64 c4) ∷
   re 0 6 (Bx1-034 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw12 ∷ Bx2-034 ∷ []) (Bx1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·034⟩ c4)

-- nat 1 BOX(0;2134): 8 steps
lem-nat-1-BOX⟨0·2134⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2134⟩ c4 = derive (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q67 c4) ∷
   re 0 6 (Bx0-1234 ∷ []) ∷ []) Eq.refl

-- nat 1 CCZ034: 107 steps
lem-nat-1-CCZ034 : WsL → ⟪ (Sw12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ034 c4 = derive (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q8 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q13 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   re 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q7 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 0 3 (CCZ034 ∷ []) ∷ []) Eq.refl

-- nat 3 CCZ014: 2 steps
lem-nat-3-CCZ014 : WsL → ⟪ (Sw34 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ014 c4 = derive (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷ []) Eq.refl

-- nat 3 TOFF104: 2 steps
lem-nat-3-TOFF104 : WsL → ⟪ (Sw34 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF104 c4 = derive (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷ []) Eq.refl

-- nat 3 CZ13: 2 steps
lem-nat-3-CZ13 : WsL → ⟪ (Sw34 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ13 c4 = derive (Sw34 ∷ CZ13 ∷ []) (CZ14 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q9 c4) ∷
   re 0 3 (CZ14 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw34 ∷ CZ13 ∷ []) (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4)

-- nat 3 BOX(0;13): 3 steps
lem-nat-3-BOX⟨0·13⟩ : WsL → ⟪ (Sw34 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·13⟩ c4 = derive (Sw34 ∷ Bx0-13 ∷ []) (Bx0-14 ∷ Sw34 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q68 c4) ∷
   re 0 1 (Bx0-14 ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw34 ∷ Bx0-13 ∷ []) (Bx0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·13⟩ c4)

-- nat 3 BOX(1;043): 8 steps
lem-nat-3-BOX⟨1·043⟩ : WsL → ⟪ (Sw34 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·043⟩ c4 = derive (Sw34 ∷ Bx1-043 ∷ []) (Bx1-034 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q69 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx1-034 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q73 : WsL → Eqn
  q73 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw34 ∷ Bx1-043 ∷ []) (Bx1-034 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·043⟩ c4)

-- nat 3 BOX(0;1243): 8 steps
lem-nat-3-BOX⟨0·1243⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1243⟩ c4 = derive (Sw34 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw⁻ 3 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   re 0 6 (Bx0-1234 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0040 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q78 : WsL → Eqn
  q78 c4 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0041 c4)

-- nat 3 CCZ034: 117 steps
lem-nat-3-CCZ034 : WsL → ⟪ (Sw34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ034 c4 = derive (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q8 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q10 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   re 1 3 (CX04 ∷ []) ∷
   rw⁻ 2 (q76 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (CX04 ∷ []) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 2 (q17 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   re 2 7 (CX04 ∷ []) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   re 4 7 (CX04 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   re 4 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q13 c4) ∷
   re 3 3 (CX04 ∷ []) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CX04 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q9 c4) ∷
   re 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q9 c4) ∷
   re 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q7 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 0 3 (CCZ034 ∷ []) ∷ []) Eq.refl

-- nat 2 CCZ013: 2 steps
lem-nat-2-CCZ013 : WsL → ⟪ (Sw23 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ013 c4 = derive (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

-- nat 2 TOFF013: 2 steps
lem-nat-2-TOFF013 : WsL → ⟪ (Sw23 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF013 c4 = derive (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

-- nat 2 CCZ012: 2 steps
lem-nat-2-CCZ012 : WsL → ⟪ (Sw23 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ012 c4 = derive (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF102: 2 steps
lem-nat-2-TOFF102 : WsL → ⟪ (Sw23 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF102 c4 = derive (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (Toff103 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) (wl0042 c4)

-- nat 2 BOX(0;14): 3 steps
lem-nat-2-BOX⟨0·14⟩ : WsL → ⟪ (Sw23 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·14⟩ c4 = derive (Sw23 ∷ Bx0-14 ∷ []) (Bx0-14 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q79 c4) ∷
   re 0 1 (Bx0-14 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw23 ∷ Bx0-14 ∷ []) (Bx0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·14⟩ c4)

-- nat 2 BOX(1;024): 8 steps
lem-nat-2-BOX⟨1·024⟩ : WsL → ⟪ (Sw23 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·024⟩ c4 = derive (Sw23 ∷ Bx1-024 ∷ []) (Bx1-034 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   re 0 6 (Bx1-034 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw23 ∷ Bx1-024 ∷ []) (Bx1-034 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·024⟩ c4)

-- nat 2 BOX(0;1324): 8 steps
lem-nat-2-BOX⟨0·1324⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1324⟩ c4 = derive (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (Bx0-1234 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF012: 2 steps
lem-nat-2-TOFF012 : WsL → ⟪ (Sw23 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF012 c4 = derive (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

-- nat 2 CCZ034: 2 steps
lem-nat-2-CCZ034 : WsL → ⟪ (Sw23 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ034 c4 = derive (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

-- nat 3 TOFF014: 2 steps
lem-nat-3-TOFF014 : WsL → ⟪ (Sw34 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF014 c4 = derive (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Toff102 ∷ Sw34 ∷ []) (Sw34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))

-- nat 3 BOX(1;023): 8 steps
lem-nat-3-BOX⟨1·023⟩ : WsL → ⟪ (Sw34 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·023⟩ c4 = derive (Sw34 ∷ Bx1-023 ∷ []) (Bx1-024 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q86 c4) ∷
   rw 2 (q71 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx1-024 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw34 ∷ Bx1-023 ∷ []) (Bx1-024 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·023⟩ c4)

-- nat 3 BOX(0;1423): 8 steps
lem-nat-3-BOX⟨0·1423⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1423⟩ c4 = derive (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q69 c4) ∷
   rw 5 (q88 c4) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF013: 2 steps
lem-nat-3-TOFF013 : WsL → ⟪ (Sw34 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF013 c4 = derive (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q9 c4) ∷
   re 0 3 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q90 : WsL → Eqn
  q90 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)

-- nat 3 CCZ024: 62 steps
lem-nat-3-CCZ024 : WsL → ⟪ (Sw34 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ024 c4 = derive (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 3 (q90 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷ []) Eq.refl

-- nat 1 CCZ024: 2 steps
lem-nat-1-CCZ024 : WsL → ⟪ (Sw12 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ024 c4 = derive (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

-- nat 1 TOFF024: 2 steps
lem-nat-1-TOFF024 : WsL → ⟪ (Sw12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF024 c4 = derive (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

-- nat 1 BOX(0;23): 3 steps
lem-nat-1-BOX⟨0·23⟩ : WsL → ⟪ (Sw12 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·23⟩ c4 = derive (Sw12 ∷ Bx0-23 ∷ []) (Bx0-13 ∷ Sw12 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q39 c4) ∷
   re 0 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw12 ∷ Bx0-23 ∷ []) (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4)

-- nat 1 BOX(2;013): 8 steps
lem-nat-1-BOX⟨2·013⟩ : WsL → ⟪ (Sw12 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·013⟩ c4 = derive (Sw12 ∷ Bx2-013 ∷ []) (Bx1-023 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q91 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q92 c4) ∷
   re 0 6 (Bx1-023 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw12 ∷ Bx2-013 ∷ []) (Bx1-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·013⟩ c4)

-- nat 1 BOX(0;2413): 8 steps
lem-nat-1-BOX⟨0·2413⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2413⟩ c4 = derive (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   rw 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q95 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q93 c4) ∷
   rw 5 (q95 c4) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF014: 2 steps
lem-nat-1-TOFF014 : WsL → ⟪ (Sw12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF014 c4 = derive (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 0 3 (Toff024 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF034: 2 steps
lem-nat-2-TOFF034 : WsL → ⟪ (Sw23 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF034 c4 = derive (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

-- nat 2 TOFF301: 2 steps
lem-nat-2-TOFF301 : WsL → ⟪ (Sw23 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF301 c4 = derive (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (CZ23 ∷ Sw23 ∷ []) (Sw23 ∷ CZ23 ∷ []) (wl0045 c4)

-- nat 2 BOX(0;32): 3 steps
lem-nat-2-BOX⟨0·32⟩ : WsL → ⟪ (Sw23 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·32⟩ c4 = derive (Sw23 ∷ Bx0-32 ∷ []) (Bx0-23 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q96 c4) ∷
   re 0 1 (Bx0-23 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw23 ∷ Bx0-32 ∷ []) (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4)

-- nat 2 BOX(3;012): 8 steps
lem-nat-2-BOX⟨3·012⟩ : WsL → ⟪ (Sw23 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·012⟩ c4 = derive (Sw23 ∷ Bx3-012 ∷ []) (Bx2-013 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q97 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx2-013 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw23 ∷ Bx3-012 ∷ []) (Bx2-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·012⟩ c4)

-- nat 2 BOX(0;3412): 8 steps
lem-nat-2-BOX⟨0·3412⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3412⟩ c4 = derive (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q99 c4) ∷
   rw 5 (q101 c4) ∷
   re 0 6 (Bx0-2413 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF024: 2 steps
lem-nat-2-TOFF024 : WsL → ⟪ (Sw23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF024 c4 = derive (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

-- nat 2 CCZ024: 2 steps
lem-nat-2-CCZ024 : WsL → ⟪ (Sw23 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ024 c4 = derive (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (CCZ034 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF103: 2 steps
lem-nat-2-TOFF103 : WsL → ⟪ (Sw23 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF103 c4 = derive (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)

-- nat 2 BOX(1;034): 8 steps
lem-nat-2-BOX⟨1·034⟩ : WsL → ⟪ (Sw23 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·034⟩ c4 = derive (Sw23 ∷ Bx1-034 ∷ []) (Bx1-024 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q102 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q82 c4) ∷
   re 0 6 (Bx1-024 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw23 ∷ Bx1-034 ∷ []) (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ c4)

-- nat 2 BOX(0;1234): 8 steps
lem-nat-2-BOX⟨0·1234⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1234⟩ c4 = derive (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q80 c4) ∷
   rw 5 (q104 c4) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷ []) Eq.refl
