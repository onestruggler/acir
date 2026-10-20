{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q2 : WsL → Eqn
  q2 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl 1 c4)

-- comm push CS04 sw1 R: 5 steps
lem-comm-push-CS04-sw1-R : WsL → ⟪ (Sw12 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw1-R c4 = derive (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 2 (q1 c4) ∷
   re 0 3 (CS04 ∷ []) ∷ []) Eq.refl

private
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl 2 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))

-- comm push CS04 sw2 R: 7 steps
lem-comm-push-CS04-sw2-R : WsL → ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw2-R c4 = derive (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 0 7 (CS04 ∷ []) ∷ []) Eq.refl

-- comm push CS04 sw1 L: 5 steps
lem-comm-push-CS04-sw1-L : WsL → ⟪ (CS04 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw1-L c4 = derive (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ [])
  (re 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS04 ∷ []) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q6 : WsL → Eqn
  q6 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl 15 c4)

-- comm push CS04 sw0 L: 5 steps
lem-comm-push-CS04-sw0-L : WsL → ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw0-L c4 = derive (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ [])
  (re 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CS14 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wl 19 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl 20 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q12 : WsL → Eqn
  q12 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl 21 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wl 22 c4)

-- comm CX12 CCZ034: 15 steps
lem-comm-CX12-CCZ034 : WsL → ⟪ (CX12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-CCZ034 c4 = derive (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CX13 ∷ []) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CX24 ∷ []) ∷
   rw 3 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 5 (q12 c4) ∷
   re 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q13 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl 23 c4)

-- resp CSd02 at 1: 2 steps
lem-resp-CSd02-at-1 : WsL → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd02-at-1 c4 = derive (CS02⁻ ∷ []) (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q15 c4) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl 24 c4)

-- resp CS02 at 1: 2 steps
lem-resp-CS02-at-1 : WsL → ⟪ (CS02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS02-at-1 c4 = derive (CS02 ∷ []) (Sw01 ∷ CS12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl 28 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl 12 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q20 : WsL → Eqn
  q20 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl 9 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl 29 c4)

-- comm CSd12 TOFF034: 15 steps
lem-comm-CSd12-TOFF034 : WsL → ⟪ (CS12⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-TOFF034 c4 = derive (CS12⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl 30 c4)

-- resp CCZ013 at 2: 5 steps
lem-resp-CCZ013-at-2 : WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ013-at-2 c4 = derive (CCZ013 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl 31 c4)

-- resp TOFF103 at 2: 5 steps
lem-resp-TOFF103-at-2 : WsL → ⟪ (Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF103-at-2 c4 = derive (Toff103 ∷ []) (Sw12 ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (Toff203 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q24 c4) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) (wl 32 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw01 ∷ CZ24 ∷ []) (CZ24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- resp CZ14 at 2: 4 steps
lem-resp-CZ14-at-2 : WsL → ⟪ (CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ14-at-2 c4 = derive (CZ14 ∷ []) (Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q26 c4) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl 33 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl 34 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (CCZ012 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CZ))
  q30 : WsL → Eqn
  q30 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl 35 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl 36 c4)

-- comm CZ12 CCZ034: 15 steps
lem-comm-CZ12-CCZ034 : WsL → ⟪ (CZ12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-CCZ034 c4 = derive (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CZ24 ∷ []) ∷
   rw 3 (q28 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 5 (q30 c4) ∷
   re 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q31 c4) ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Toff012 ∷ CZ34 ∷ []) (CZ34 ∷ Toff012 ∷ []) (c₃ (Toff) (CZ))

-- comm CZ12 TOFF034: 15 steps
lem-comm-CZ12-TOFF034 : WsL → ⟪ (CZ12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF034 c4 = derive (CZ12 ∷ Toff034 ∷ []) (Toff034 ∷ CZ12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CZ24 ∷ []) ∷
   rw 3 (q28 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q30 c4) ∷
   re 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q31 c4) ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl 37 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))

-- resp CCZ134 at 2: 4 steps
lem-resp-CCZ134-at-2 : WsL → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ134-at-2 c4 = derive (CCZ134 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q34 c4) ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- resp CS14 at 3: 6 steps
lem-resp-CS14-at-3 : WsL → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS14-at-3 c4 = derive (CS14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q35 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q37 c4) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl 38 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))

-- resp TOFF314 at 2: 4 steps
lem-resp-TOFF314-at-2 : WsL → ⟪ (Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF314-at-2 c4 = derive (Toff314 ∷ []) (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q39 c4) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₀₁))

-- resp CX13 at 2: 4 steps
lem-resp-CX13-at-2 : WsL → ⟪ (CX13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX13-at-2 c4 = derive (CX13 ∷ []) (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q8 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q40 c4) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl 42 c4)

-- comm push CSd04 sw0 L: 5 steps
lem-comm-push-CSd04-sw0-L : WsL → ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd04-sw0-L c4 = derive (CS04⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS14⁻ ∷ [])
  (re 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (Toff102 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))

-- comm TOFF204 CSd13: 11 steps
lem-comm-TOFF204-CSd13 : WsL → ⟪ (Toff204 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff204 ∷ []) ⟫ʷ
lem-comm-TOFF204-CSd13 c4 = derive (Toff204 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff204 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q42 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   re 1 7 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl 43 c4)

-- comm push CSd04 sw1 L: 5 steps
lem-comm-push-CSd04-sw1-L : WsL → ⟪ (CS04⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd04-sw1-L c4 = derive (CS04⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q43 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS))

-- resp CSd13 at 2: 4 steps
lem-resp-CSd13-at-2 : WsL → ⟪ (CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd13-at-2 c4 = derive (CS13⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q44 c4) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl 16 c4)

-- comm push CX04 sw0 L: 5 steps
lem-comm-push-CX04-sw0-L : WsL → ⟪ (CX04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw0-L c4 = derive (CX04 ∷ Sw01 ∷ []) (Sw01 ∷ CX14 ∷ [])
  (re 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q45 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CX14 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl 44 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))

-- comm CX04 CCZ123: 13 steps
lem-comm-CX04-CCZ123 : WsL → ⟪ (CX04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-CCZ123 c4 = derive (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 7 (CX04 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl 45 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))

-- comm CSd04 TOFF213: 13 steps
lem-comm-CSd04-TOFF213 : WsL → ⟪ (CS04⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-TOFF213 c4 = derive (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (Toff214 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (Toff314 ∷ []) ∷
   rw 4 (q48 c4) ∷
   rw 3 (q49 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

-- resp CS03 at 1: 2 steps
lem-resp-CS03-at-1 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS03-at-1 c4 = derive (CS03 ∷ []) (Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))

-- comm CSd13 CCZ024: 11 steps
lem-comm-CSd13-CCZ024 : WsL → ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-CCZ024 c4 = derive (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw 4 (q20 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q21 c4) ∷
   re 0 7 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q54 : WsL → Eqn
  q54 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 c4)

-- comm CS13 CCZ024: 11 steps
lem-comm-CS13-CCZ024 : WsL → ⟪ (CS13 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-CCZ024 c4 = derive (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q55 c4) ∷
   re 0 7 (CCZ024 ∷ []) ∷ []) Eq.refl

-- resp CSd03 at 1: 2 steps
lem-resp-CSd03-at-1 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd03-at-1 c4 = derive (CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q41 c4) ∷ []) Eq.refl

-- comm CX13 CCZ024: 11 steps
lem-comm-CX13-CCZ024 : WsL → ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ
lem-comm-CX13-CCZ024 c4 = derive (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q8 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CX24 ∷ []) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   re 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q13 c4) ∷
   re 0 7 (CCZ024 ∷ []) ∷ []) Eq.refl

-- comm push CS04 sw2 L: 7 steps
lem-comm-push-CS04-sw2-L : WsL → ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw2-L c4 = derive (CS04 ∷ Sw23 ∷ []) (Sw23 ∷ CS04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q4 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (CS04 ∷ []) ∷ []) Eq.refl

-- resp CS03 at 2: 4 steps
lem-resp-CS03-at-2 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS03-at-2 c4 = derive (CS03 ∷ []) (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

-- resp CS14 at 2: 4 steps
lem-resp-CS14-at-2 : WsL → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS14-at-2 c4 = derive (CS14 ∷ []) (Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q36 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q37 c4) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl 10 c4)

-- comm push CX04 sw1 L: 5 steps
lem-comm-push-CX04-sw1-L : WsL → ⟪ (CX04 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw1-L c4 = derive (CX04 ∷ Sw12 ∷ []) (Sw12 ∷ CX04 ∷ [])
  (re 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX04 ∷ []) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl 14 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- resp CSd14 at 2: 4 steps
lem-resp-CSd14-at-2 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd14-at-2 c4 = derive (CS14⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q58 c4) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))

-- comm CX04 TOFF213: 13 steps
lem-comm-CX04-TOFF213 : WsL → ⟪ (CX04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-TOFF213 c4 = derive (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (Toff214 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (Toff314 ∷ []) ∷
   rw 4 (q48 c4) ∷
   rw 3 (q59 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 7 (CX04 ∷ []) ∷ []) Eq.refl

-- resp TOFF214 at 3: 7 steps
lem-resp-TOFF214-at-3 : WsL → ⟪ (Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF214-at-3 c4 = derive (Toff214 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q39 c4) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl 49 c4)

-- comm push CZ04 sw0 L: 5 steps
lem-comm-push-CZ04-sw0-L : WsL → ⟪ (CZ04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-push-CZ04-sw0-L c4 = derive (CZ04 ∷ Sw01 ∷ []) (Sw01 ∷ CZ14 ∷ [])
  (re 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CZ14 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (CZ01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ))

-- comm CZ04 CCZ123: 13 steps
lem-comm-CZ04-CCZ123 : WsL → ⟪ (CZ04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-CZ04-CCZ123 c4 = derive (CZ04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 7 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (CZ01 ∷ Toff324 ∷ []) (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))

-- comm CZ04 TOFF213: 13 steps
lem-comm-CZ04-TOFF213 : WsL → ⟪ (CZ04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-CZ04-TOFF213 c4 = derive (CZ04 ∷ Toff213 ∷ []) (Toff213 ∷ CZ04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (Toff214 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (Toff314 ∷ []) ∷
   rw 4 (q48 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 7 (CZ04 ∷ []) ∷ []) Eq.refl

-- resp CSd03 at 2: 4 steps
lem-resp-CSd03-at-2 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd03-at-2 c4 = derive (CS03⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q43 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q41 c4) ∷ []) Eq.refl

-- comm TOFF014 CSd23: 9 steps
lem-comm-TOFF014-CSd23 : WsL → ⟪ (Toff014 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-TOFF014-CSd23 c4 = derive (Toff014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 3 (q20 c4) ∷
   rw 2 (q19 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 5 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ []) (wl 50 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ CX24 ∷ []) (CX24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))

-- resp CX14 at 2: 4 steps
lem-resp-CX14-at-2 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX14-at-2 c4 = derive (CX14 ∷ []) (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q63 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q64 c4) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (CX24 ∷ Sw12 ∷ []) (Sw12 ∷ CX14 ∷ []) (wl 51 c4)

-- comm CX14 CCZ023: 7 steps
lem-comm-CX14-CCZ023 : WsL → ⟪ (CX14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-CCZ023 c4 = derive (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q65 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

-- resp CCZ023 at 1: 2 steps
lem-resp-CCZ023-at-1 : WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ023-at-1 c4 = derive (CCZ023 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl 7 c4)

-- comm CSd14 TOFF023: 7 steps
lem-comm-CSd14-TOFF023 : WsL → ⟪ (CS14⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF023 c4 = derive (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q66 c4) ∷
   re 0 5 (Toff023 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))

-- resp CS13 at 2: 4 steps
lem-resp-CS13-at-2 : WsL → ⟪ (CS13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS13-at-2 c4 = derive (CS13 ∷ []) (Sw12 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q51 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q67 c4) ∷ []) Eq.refl

-- comm CSd23 CCZ014: 9 steps
lem-comm-CSd23-CCZ014 : WsL → ⟪ (CS23⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-comm-CSd23-CCZ014 c4 = derive (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CS24⁻ ∷ []) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 3 (q20 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (CCZ014 ∷ []) ∷ []) Eq.refl

-- comm CS23 CCZ014: 9 steps
lem-comm-CS23-CCZ014 : WsL → ⟪ (CS23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-CCZ014 c4 = derive (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))

-- resp CS24 at 3: 6 steps
lem-resp-CS24-at-3 : WsL → ⟪ (CS24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS24-at-3 c4 = derive (CS24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q69 c4) ∷ []) Eq.refl

-- comm CX23 CCZ014: 9 steps
lem-comm-CX23-CCZ014 : WsL → ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-CCZ014 c4 = derive (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CX24 ∷ []) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   re 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (CCZ014 ∷ []) ∷ []) Eq.refl

-- resp CCZ124 at 3: 7 steps
lem-resp-CCZ124-at-3 : WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ124-at-3 c4 = derive (CCZ124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CCZ134 ∷ []) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q34 c4) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl 52 c4)

-- resp TOFF023 at 1: 2 steps
lem-resp-TOFF023-at-1 : WsL → ⟪ (Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF023-at-1 c4 = derive (Toff023 ∷ []) (Sw01 ∷ Toff123 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (Toff012 ∷ CX34 ∷ []) (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁))

-- comm CX14 TOFF023: 7 steps
lem-comm-CX14-TOFF023 : WsL → ⟪ (CX14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-TOFF023 c4 = derive (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q65 c4) ∷
   re 0 5 (Toff023 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl 53 c4)

-- comm CZ14 CCZ023: 7 steps
lem-comm-CZ14-CCZ023 : WsL → ⟪ (CZ14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-CCZ023 c4 = derive (CZ14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q72 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

-- comm CZ14 TOFF023: 7 steps
lem-comm-CZ14-TOFF023 : WsL → ⟪ (CZ14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF023 c4 = derive (CZ14 ∷ Toff023 ∷ []) (Toff023 ∷ CZ14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q72 c4) ∷
   re 0 5 (Toff023 ∷ []) ∷ []) Eq.refl

-- comm TOFF024 CSd13: 11 steps
lem-comm-TOFF024-CSd13 : WsL → ⟪ (Toff024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-TOFF024-CSd13 c4 = derive (Toff024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   re 1 7 (Toff024 ∷ []) ∷ []) Eq.refl

-- comm CX24 CCZ013: 5 steps
lem-comm-CX24-CCZ013 : WsL → ⟪ (CX24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-CCZ013 c4 = derive (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- comm CSd24 TOFF013: 5 steps
lem-comm-CSd24-TOFF013 : WsL → ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-TOFF013 c4 = derive (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl 54 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))

-- resp TOFF134 at 2: 4 steps
lem-resp-TOFF134-at-2 : WsL → ⟪ (Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF134-at-2 c4 = derive (Toff134 ∷ []) (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q73 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q74 c4) ∷ []) Eq.refl

-- resp TOFF013 at 2: 5 steps
lem-resp-TOFF013-at-2 : WsL → ⟪ (Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF013-at-2 c4 = derive (Toff013 ∷ []) (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q70 c4) ∷ []) Eq.refl

-- comm CX24 TOFF013: 5 steps
lem-comm-CX24-TOFF013 : WsL → ⟪ (CX24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-TOFF013 c4 = derive (CX24 ∷ Toff013 ∷ []) (Toff013 ∷ CX24 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q12 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

-- comm CZ24 CCZ013: 5 steps
lem-comm-CZ24-CCZ013 : WsL → ⟪ (CZ24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-CCZ013 c4 = derive (CZ24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ24 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- comm CZ24 TOFF013: 5 steps
lem-comm-CZ24-TOFF013 : WsL → ⟪ (CZ24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-TOFF013 c4 = derive (CZ24 ∷ Toff013 ∷ []) (Toff013 ∷ CZ24 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw23 ∷ Sw34 ∷ []) (Sw24 ∷ Sw23 ∷ []) (wl 55 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (CZ12 ∷ Sw34 ∷ []) (Sw34 ∷ CZ12 ∷ []) (c₃ (CZ ↑) (Swap))
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw23 ∷ Sw24 ∷ []) (Sw34 ∷ Sw23 ∷ []) (wl 56 c4)

-- comm SWAP23 BOX(0;14): 11 steps
lem-comm-SWAP23-BOX⟨0·14⟩ : WsL → ⟪ (Sw23 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-SWAP23-BOX⟨0·14⟩ c4 = derive (Sw23 ∷ Bx0-14 ∷ []) (Bx0-14 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Sw24 ∷ []) ∷
   rw⁻ 1 (q75 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   re 4 1 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (CZ14 ∷ []) ∷
   re 0 1 (Bx0-14 ∷ []) ∷ []) Eq.refl

-- resp TOFF203 at 1: 2 steps
lem-resp-TOFF203-at-1 : WsL → ⟪ (Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF203-at-1 c4 = derive (Toff203 ∷ []) (Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q24 c4) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (CS01⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑))

-- comm push CSd04 sw2 L: 7 steps
lem-comm-push-CSd04-sw2-L : WsL → ⟪ (CS04⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd04-sw2-L c4 = derive (CS04⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q78 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wl 57 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) (wl 58 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))
  q82 : WsL → Eqn
  q82 c4 = eqn (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) (wl 59 c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wl 60 c4)

-- comm CX21 CCZ034: 15 steps
lem-comm-CX21-CCZ034 : WsL → ⟪ (CX21 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-CCZ034 c4 = derive (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 1 (q79 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CX42 ∷ []) ∷
   rw 3 (q80 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw 5 (q82 c4) ∷
   re 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q83 c4) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₁₀))

-- resp CX31 at 2: 4 steps
lem-resp-CX31-at-2 : WsL → ⟪ (CX31 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX31-at-2 c4 = derive (CX31 ∷ []) (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q79 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q84 c4) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (CZ23 ∷ Sw14 ∷ []) (Sw14 ∷ CZ23 ∷ []) (wl 61 c4)

-- comm SWAP13 BOX(0;24): 9 steps
lem-comm-SWAP13-BOX⟨0·24⟩ : WsL → ⟪ (Sw13 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨0·24⟩ c4 = derive (Sw13 ∷ Bx0-24 ∷ []) (Bx0-24 ∷ Sw13 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   re 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Sw14 ∷ []) ∷
   rw⁻ 1 (q85 c4) ∷
   re 2 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   re 0 3 (CZ24 ∷ []) ∷
   re 0 1 (Bx0-24 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) (wl 62 c4)

-- resp CZ14 at 3: 6 steps
lem-resp-CZ14-at-3 : WsL → ⟪ (CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ14-at-3 c4 = derive (CZ14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q26 c4) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl 63 c4)

-- resp TOFF302 at 1: 2 steps
lem-resp-TOFF302-at-1 : WsL → ⟪ (Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF302-at-1 c4 = derive (Toff302 ∷ []) (Sw01 ∷ Toff312 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q87 c4) ∷ []) Eq.refl

-- comm CZ13 CCZ024: 11 steps
lem-comm-CZ13-CCZ024 : WsL → ⟪ (CZ13 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-CCZ024 c4 = derive (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CZ24 ∷ []) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   re 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q31 c4) ∷
   re 0 7 (CCZ024 ∷ []) ∷ []) Eq.refl

-- comm TOFF013 CSd24: 15 steps
lem-comm-TOFF013-CSd24 : WsL → ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CSd24 c4 = derive (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ [])
  (re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q9 c4) ∷
   re 2 5 (Toff014 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   re 0 3 (CS24⁻ ∷ []) ∷ []) Eq.refl

-- comm CSd13 TOFF024: 11 steps
lem-comm-CSd13-TOFF024 : WsL → ⟪ (CS13⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF024 c4 = derive (CS13⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS13⁻ ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q21 c4) ∷
   re 0 7 (Toff024 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw12 ∷ CZ34 ∷ []) (CZ34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw01 ∷ CZ34 ∷ []) (CZ34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- resp CZ24 at 3: 6 steps
lem-resp-CZ24-at-3 : WsL → ⟪ (CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ24-at-3 c4 = derive (CZ24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q88 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q89 c4) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) (wl 69 c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw01 ∷ CX42 ∷ []) (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))

-- resp CX41 at 2: 4 steps
lem-resp-CX41-at-2 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX41-at-2 c4 = derive (CX41 ∷ []) (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q90 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q91 c4) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (CX41 ∷ Sw23 ∷ []) (Sw23 ∷ CX41 ∷ []) (wl 70 c4)

-- resp CX41 at 3: 6 steps
lem-resp-CX41-at-3 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX41-at-3 c4 = derive (CX41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q92 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q91 c4) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- resp CSd24 at 3: 6 steps
lem-resp-CSd24-at-3 : WsL → ⟪ (CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd24-at-3 c4 = derive (CS24⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q94 c4) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (CX14 ∷ Sw23 ∷ []) (Sw23 ∷ CX14 ∷ []) (wl 71 c4)

-- resp CX14 at 3: 6 steps
lem-resp-CX14-at-3 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX14-at-3 c4 = derive (CX14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q95 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q63 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q64 c4) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))

-- comm CS12 TOFF034: 15 steps
lem-comm-CS12-TOFF034 : WsL → ⟪ (CS12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF034 c4 = derive (CS12 ∷ Toff034 ∷ []) (Toff034 ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q55 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw12 ∷ Sw24 ∷ []) (Sw14 ∷ Sw12 ∷ []) (wl 72 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw01 ∷ Sw24 ∷ []) (Sw24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • Swap • Swap ↑))

-- resp SWAP14 at 2: 4 steps
lem-resp-SWAP14-at-2 : WsL → ⟪ (Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-SWAP14-at-2 c4 = derive (Sw14 ∷ []) (Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q97 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q98 c4) ∷ []) Eq.refl

-- resp TOFF301 at 2: 5 steps
lem-resp-TOFF301-at-2 : WsL → ⟪ (Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF301-at-2 c4 = derive (Toff301 ∷ []) (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (Toff302 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

-- comm SWAP14 BOX(0;32): 3 steps
lem-comm-SWAP14-BOX⟨0·32⟩ : WsL → ⟪ (Sw14 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨0·32⟩ c4 = derive (Sw14 ∷ Bx0-32 ∷ []) (Bx0-32 ∷ Sw14 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q85 c4) ∷
   re 0 1 (Bx0-32 ∷ []) ∷ []) Eq.refl

-- comm CZ23 CCZ014: 9 steps
lem-comm-CZ23-CCZ014 : WsL → ⟪ (CZ23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-CCZ014 c4 = derive (CZ23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CZ24 ∷ []) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q30 c4) ∷
   re 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (CCZ014 ∷ []) ∷ []) Eq.refl

-- comm CSd23 TOFF014: 9 steps
lem-comm-CSd23-TOFF014 : WsL → ⟪ (CS23⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-comm-CSd23-TOFF014 c4 = derive (CS23⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS23⁻ ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CS24⁻ ∷ []) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw12 ∷ CX43 ∷ []) (CX43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CX₁₀))
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw01 ∷ CX43 ∷ []) (CX43 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₁₀ ↑))

-- resp CX42 at 3: 6 steps
lem-resp-CX42-at-3 : WsL → ⟪ (CX42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX42-at-3 c4 = derive (CX42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q99 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q100 c4) ∷ []) Eq.refl

private
  q101 : WsL → Eqn
  q101 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl 48 c4)

-- resp CSd14 at 3: 6 steps
lem-resp-CSd14-at-3 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd14-at-3 c4 = derive (CS14⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q58 c4) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw12 ∷ CX34 ∷ []) (CX34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CX₀₁))
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw01 ∷ CX34 ∷ []) (CX34 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₀₁ ↑))

-- resp CX24 at 3: 6 steps
lem-resp-CX24-at-3 : WsL → ⟪ (CX24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX24-at-3 c4 = derive (CX24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q102 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q103 c4) ∷ []) Eq.refl

-- comm SWAP24 BOX(0;31): 7 steps
lem-comm-SWAP24-BOX⟨0·31⟩ : WsL → ⟪ (Sw24 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw24 ∷ []) ⟫ʷ
lem-comm-SWAP24-BOX⟨0·31⟩ c4 = derive (Sw24 ∷ Bx0-31 ∷ []) (Bx0-31 ∷ Sw24 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q75 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   re 0 3 (CZ13 ∷ []) ∷
   re 0 1 (Bx0-31 ∷ []) ∷ []) Eq.refl

-- comm CX31 CCZ024: 11 steps
lem-comm-CX31-CCZ024 : WsL → ⟪ (CX31 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-CCZ024 c4 = derive (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CX42 ∷ []) ∷
   rw 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   re 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q83 c4) ∷
   re 0 7 (CCZ024 ∷ []) ∷ []) Eq.refl

-- comm CS13 TOFF024: 11 steps
lem-comm-CS13-TOFF024 : WsL → ⟪ (CS13 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF024 c4 = derive (CS13 ∷ Toff024 ∷ []) (Toff024 ∷ CS13 ∷ [])
  (re 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q55 c4) ∷
   re 0 7 (Toff024 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw14 ∷ Sw23 ∷ []) (Sw23 ∷ Sw14 ∷ []) (wl 74 c4)

-- resp SWAP14 at 3: 6 steps
lem-resp-SWAP14-at-3 : WsL → ⟪ (Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-SWAP14-at-3 c4 = derive (Sw14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q104 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q97 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q98 c4) ∷ []) Eq.refl

-- comm SWAP14 BOX(0;23): 3 steps
lem-comm-SWAP14-BOX⟨0·23⟩ : WsL → ⟪ (Sw14 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨0·23⟩ c4 = derive (Sw14 ∷ Bx0-23 ∷ []) (Bx0-23 ∷ Sw14 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q85 c4) ∷
   re 0 1 (Bx0-23 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw12 ∷ Sw23 ∷ []) (Sw13 ∷ Sw12 ∷ []) (wl 75 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap))

-- resp SWAP13 at 2: 4 steps
lem-resp-SWAP13-at-2 : WsL → ⟪ (Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-SWAP13-at-2 c4 = derive (Sw13 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q105 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q106 c4) ∷ []) Eq.refl

-- comm SWAP13 BOX(0;42): 9 steps
lem-comm-SWAP13-BOX⟨0·42⟩ : WsL → ⟪ (Sw13 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨0·42⟩ c4 = derive (Sw13 ∷ Bx0-42 ∷ []) (Bx0-42 ∷ Sw13 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   re 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Sw14 ∷ []) ∷
   rw⁻ 1 (q85 c4) ∷
   re 2 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   re 0 3 (CZ24 ∷ []) ∷
   re 0 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

-- comm TOFF034 CSd12: 15 steps
lem-comm-TOFF034-CSd12 : WsL → ⟪ (Toff034 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-TOFF034-CSd12 c4 = derive (Toff034 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff034 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q21 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 9 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- resp CZ13 at 2: 4 steps
lem-resp-CZ13-at-2 : WsL → ⟪ (CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ13-at-2 c4 = derive (CZ13 ∷ []) (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q107 c4) ∷ []) Eq.refl

-- comm CX42 CCZ013: 5 steps
lem-comm-CX42-CCZ013 : WsL → ⟪ (CX42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CX42 ∷ []) ⟫ʷ
lem-comm-CX42-CCZ013 c4 = derive (CX42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX42 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- comm CX32 CCZ014: 9 steps
lem-comm-CX32-CCZ014 : WsL → ⟪ (CX32 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CX32 ∷ []) ⟫ʷ
lem-comm-CX32-CCZ014 c4 = derive (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CX42 ∷ []) ∷
   rw 1 (q80 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q82 c4) ∷
   re 4 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 0 5 (CCZ014 ∷ []) ∷ []) Eq.refl

-- comm CSd12 CCZ034: 15 steps
lem-comm-CSd12-CCZ034 : WsL → ⟪ (CS12⁻ ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-CCZ034 c4 = derive (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

-- comm CS12 CCZ034: 15 steps
lem-comm-CS12-CCZ034 : WsL → ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-CCZ034 c4 = derive (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q55 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wl 76 c4)

-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : WsL → ⟪ (CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ02-at-1 c4 = derive (CZ02 ∷ []) (Sw01 ∷ CZ12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wl 77 c4)

-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : WsL → ⟪ (CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX20-at-1 c4 = derive (CX20 ∷ []) (Sw01 ∷ CX21 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q109 c4) ∷ []) Eq.refl

-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX03-at-1 c4 = derive (CX03 ∷ []) (Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q45 c4) ∷ []) Eq.refl

-- resp CZ03 at 1: 2 steps
lem-resp-CZ03-at-1 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ03-at-1 c4 = derive (CZ03 ∷ []) (Sw01 ∷ CZ13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q60 c4) ∷ []) Eq.refl

-- comm CX12 TOFF034: 15 steps
lem-comm-CX12-TOFF034 : WsL → ⟪ (CX12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-TOFF034 c4 = derive (CX12 ∷ Toff034 ∷ []) (Toff034 ∷ CX12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CX13 ∷ []) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CX24 ∷ []) ∷
   rw 3 (q10 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 5 (q12 c4) ∷
   re 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q13 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = eqn (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) (wl 78 c4)

-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX30-at-1 c4 = derive (CX30 ∷ []) (Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q110 c4) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (CZ01 ∷ Sw34 ∷ []) (Sw34 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap ↑))

-- comm push CZ04 sw2 L: 7 steps
lem-comm-push-CZ04-sw2-L : WsL → ⟪ (CZ04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-push-CZ04-sw2-L c4 = derive (CZ04 ∷ Sw23 ∷ []) (Sw23 ∷ CZ04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q111 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl 79 c4)

-- comm push CZ04 sw1 L: 5 steps
lem-comm-push-CZ04-sw1-L : WsL → ⟪ (CZ04 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-push-CZ04-sw1-L c4 = derive (CZ04 ∷ Sw12 ∷ []) (Sw12 ∷ CZ04 ∷ [])
  (re 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))

-- comm push CX40 sw2 L: 7 steps
lem-comm-push-CX40-sw2-L : WsL → ⟪ (CX40 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-push-CX40-sw2-L c4 = derive (CX40 ∷ Sw23 ∷ []) (Sw23 ∷ CX40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q113 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (CX40 ∷ []) ∷ []) Eq.refl

private
  q114 : WsL → Eqn
  q114 c4 = eqn (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) (wl 80 c4)

-- comm push CX40 sw1 L: 5 steps
lem-comm-push-CX40-sw1-L : WsL → ⟪ (CX40 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-push-CX40-sw1-L c4 = derive (CX40 ∷ Sw12 ∷ []) (Sw12 ∷ CX40 ∷ [])
  (re 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX40 ∷ []) ∷ []) Eq.refl

-- comm push CX40 sw0 L: 5 steps
lem-comm-push-CX40-sw0-L : WsL → ⟪ (CX40 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-push-CX40-sw0-L c4 = derive (CX40 ∷ Sw01 ∷ []) (Sw01 ∷ CX41 ∷ [])
  (re 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q110 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CX41 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) (wl 81 c4)

-- comm push CK40 sw0 L: 5 steps
lem-comm-push-CK40-sw0-L : WsL → ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw0-L c4 = derive (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ [])
  (re 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q115 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CK41 ∷ []) ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = eqn (CK30⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK31⁻ ∷ []) (wl 82 c4)

-- comm push CKd40 sw0 L: 5 steps
lem-comm-push-CKd40-sw0-L : WsL → ⟪ (CK40⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ []) ⟫ʷ
lem-comm-push-CKd40-sw0-L c4 = derive (CK40⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK41⁻ ∷ [])
  (re 0 1 (Sw34 ∷ CK30⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q116 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (CK41⁻ ∷ []) ∷ []) Eq.refl

-- comm CX02 CCZ134: 23 steps
lem-comm-CX02-CCZ134 : WsL → ⟪ (CX02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX02 ∷ []) ⟫ʷ
lem-comm-CX02-CCZ134 c4 = derive (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q9 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q7 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 7 (CX04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q9 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl 83 c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (CS01⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff))

-- comm CSd02 TOFF134: 23 steps
lem-comm-CSd02-TOFF134 : WsL → ⟪ (CS02⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF134 c4 = derive (CS02⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS02⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q9 c4) ∷
   re 8 3 (Toff124 ∷ []) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (Toff134 ∷ []) ∷
   rw 6 (q117 c4) ∷
   rw 5 (q118 c4) ∷
   rw 4 (q73 c4) ∷
   re 4 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) ∷
   rw 3 (q7 c4) ∷
   re 3 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 7 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q9 c4) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 0 5 (Toff134 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (CX01 ∷ Toff234 ∷ []) (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff))

-- comm CX02 TOFF134: 23 steps
lem-comm-CX02-TOFF134 : WsL → ⟪ (CX02 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CX02 ∷ []) ⟫ʷ
lem-comm-CX02-TOFF134 c4 = derive (CX02 ∷ Toff134 ∷ []) (Toff134 ∷ CX02 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q9 c4) ∷
   re 8 3 (Toff124 ∷ []) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (Toff134 ∷ []) ∷
   rw 6 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   rw 4 (q73 c4) ∷
   re 4 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) ∷
   rw 3 (q7 c4) ∷
   re 3 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 7 (CX04 ∷ []) ∷
   re 3 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q9 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 0 5 (Toff134 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl 5 c4)

-- comm CS14 TOFF023: 7 steps
lem-comm-CS14-TOFF023 : WsL → ⟪ (CS14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF023 c4 = derive (CS14 ∷ Toff023 ∷ []) (Toff023 ∷ CS14 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q36 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 3 (q54 c4) ∷
   rw 4 (q120 c4) ∷
   re 0 5 (Toff023 ∷ []) ∷ []) Eq.refl

-- comm CS24 TOFF013: 5 steps
lem-comm-CS24-TOFF013 : WsL → ⟪ (CS24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-TOFF013 c4 = derive (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q96 c4) ∷
   rw 2 (q54 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))

-- comm TOFF301 CSd24: 15 steps
lem-comm-TOFF301-CSd24 : WsL → ⟪ (Toff301 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff301 ∷ []) ⟫ʷ
lem-comm-TOFF301-CSd24 c4 = derive (Toff301 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff301 ∷ [])
  (re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Toff401 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q121 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q9 c4) ∷
   re 2 5 (Toff401 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   rw 4 (q9 c4) ∷
   re 0 3 (CS24⁻ ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl 39 c4)

-- resp CX02 at 1: 2 steps
lem-resp-CX02-at-1 : WsL → ⟪ (CX02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX02-at-1 c4 = derive (CX02 ∷ []) (Sw01 ∷ CX12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q122 c4) ∷ []) Eq.refl

-- comm CSd24 CCZ013: 5 steps
lem-comm-CSd24-CCZ013 : WsL → ⟪ (CS24⁻ ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-CCZ013 c4 = derive (CS24⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q50 c4) ∷
   rw 2 (q20 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- comm CS24 CCZ013: 5 steps
lem-comm-CS24-CCZ013 : WsL → ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-CCZ013 c4 = derive (CS24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

-- comm TOFF401 CSd23: 9 steps
lem-comm-TOFF401-CSd23 : WsL → ⟪ (Toff401 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-TOFF401-CSd23 c4 = derive (Toff401 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff401 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 3 (q20 c4) ∷
   rw 2 (q121 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 5 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl 84 c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (CS01 ∷ Toff423 ∷ []) (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ))
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl 85 c4)

-- comm CS03 TOFF412: 9 steps
lem-comm-CS03-TOFF412 : WsL → ⟪ (CS03 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-TOFF412 c4 = derive (CS03 ∷ Toff412 ∷ []) (Toff412 ∷ CS03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   re 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 5 (CS03 ∷ []) ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (CS01⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ))

-- comm TOFF412 CSd03: 9 steps
lem-comm-TOFF412-CSd03 : WsL → ⟪ (Toff412 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff412 ∷ []) ⟫ʷ
lem-comm-TOFF412-CSd03 c4 = derive (Toff412 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff412 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (Toff413 ∷ []) ∷
   rw⁻ 1 (q125 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 0 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

-- comm CSd12 TOFF403: 15 steps
lem-comm-CSd12-TOFF403 : WsL → ⟪ (CS12⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-TOFF403 c4 = derive (CS12⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 0 9 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))

-- comm CSd03 CCZ124: 9 steps
lem-comm-CSd03-CCZ124 : WsL → ⟪ (CS03⁻ ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-CCZ124 c4 = derive (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q127 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))

-- comm CS03 CCZ124: 9 steps
lem-comm-CS03-CCZ124 : WsL → ⟪ (CS03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-CCZ124 c4 = derive (CS03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q128 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 5 (CS03 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))

-- resp TOFF412 at 3: 7 steps
lem-resp-TOFF412-at-3 : WsL → ⟪ (Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF412-at-3 c4 = derive (Toff412 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q125 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q129 c4) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (CZ01 ∷ Toff423 ∷ []) (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ))

-- comm CZ03 TOFF412: 9 steps
lem-comm-CZ03-TOFF412 : WsL → ⟪ (CZ03 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-TOFF412 c4 = derive (CZ03 ∷ Toff412 ∷ []) (Toff412 ∷ CZ03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q130 c4) ∷
   rw 1 (q125 c4) ∷
   re 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 5 (CZ03 ∷ []) ∷ []) Eq.refl

-- comm CSd03 TOFF412: 9 steps
lem-comm-CSd03-TOFF412 : WsL → ⟪ (CS03⁻ ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-TOFF412 c4 = derive (CS03⁻ ∷ Toff412 ∷ []) (Toff412 ∷ CS03⁻ ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (Toff413 ∷ []) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q125 c4) ∷
   re 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 0 (q7 c4) ∷
   re 1 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

-- resp TOFF124 at 3: 7 steps
lem-resp-TOFF124-at-3 : WsL → ⟪ (Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF124-at-3 c4 = derive (Toff124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (Toff134 ∷ []) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q74 c4) ∷ []) Eq.refl

private
  q131 : WsL → Eqn
  q131 c4 = eqn (CZ12 ∷ Sw03 ∷ []) (Sw03 ∷ CZ12 ∷ []) (wl 86 c4)

-- comm SWAP02 BOX(4;13): 9 steps
lem-comm-SWAP02-BOX⟨4·13⟩ : WsL → ⟪ (Sw02 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨4·13⟩ c4 = derive (Sw02 ∷ Bx4-13 ∷ []) (Bx4-13 ∷ Sw02 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (Sw03 ∷ []) ∷
   rw⁻ 1 (q131 c4) ∷
   re 2 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) ∷
   rw 4 (q7 c4) ∷
   re 0 3 (CZ13 ∷ []) ∷
   re 0 1 (Bx4-13 ∷ []) ∷ []) Eq.refl

-- comm CZ04 TOFF312: 13 steps
lem-comm-CZ04-TOFF312 : WsL → ⟪ (CZ04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-CZ04-TOFF312 c4 = derive (CZ04 ∷ Toff312 ∷ []) (Toff312 ∷ CZ04 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (Toff412 ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (Toff413 ∷ []) ∷
   rw 4 (q123 c4) ∷
   rw 3 (q130 c4) ∷
   rw 2 (q125 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 1 7 (CZ04 ∷ []) ∷ []) Eq.refl

-- comm TOFF312 CSd04: 13 steps
lem-comm-TOFF312-CSd04 : WsL → ⟪ (Toff312 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CSd04 c4 = derive (Toff312 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff312 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Toff412 ∷ []) ∷
   rw⁻ 1 (q7 c4) ∷
   re 2 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q125 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   re 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 7 (q7 c4) ∷
   re 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 8 (q9 c4) ∷
   re 0 7 (CS04⁻ ∷ []) ∷ []) Eq.refl
