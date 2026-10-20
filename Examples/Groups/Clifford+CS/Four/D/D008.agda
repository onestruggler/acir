{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D008 (W : Ws) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : Eqn
  q1 = eqn [] (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (wn 148 W)
  q2 : Eqn
  q2 = eqn (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ []) (wn 149 W)
  q3 : Eqn
  q3 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q4 : Eqn
  q4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q9 : Eqn
  q9 = eqn (K0⁻ ∷ S0 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK20 ∷ CX20 ∷ S2 ∷ []) (wn 150 W)
  q10 : Eqn
  q10 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q11 : Eqn
  q11 = eqn (K0⁻ ∷ S0 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) (wn 152 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q13 : Eqn
  q13 = eqn (Toff012 ∷ S3 ∷ []) (S3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (S))
  q14 : Eqn
  q14 = eqn (S3 ∷ S3⁻ ∷ []) [] (wn 154 W)
  q15 : Eqn
  q15 = eqn (Toff012 ∷ []) (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) (wn 155 W)
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q17 : Eqn
  q17 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q18 : Eqn
  q18 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q19 : Eqn
  q19 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q22 : Eqn
  q22 = eqn (CX31 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ []) (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) (wn 156 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q28 : Eqn
  q28 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q29 : Eqn
  q29 = eqn (CX10 ∷ CX23 ∷ []) (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁))
  q30 : Eqn
  q30 = eqn (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) (wn 158 W)
  q31 : Eqn
  q31 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q32 : Eqn
  q32 = eqn (CX31 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ []) (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) (wn 159 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q34 : Eqn
  q34 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q35 : Eqn
  q35 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q36 : Eqn
  q36 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q37 : Eqn
  q37 = eqn (CX20 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) (wn 160 W)
  q38 : Eqn
  q38 = eqn (CX20 ∷ CX20 ∷ []) [] (wn 161 W)
  q39 : Eqn
  q39 = eqn (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) (Toff012 ∷ []) (wn 162 W)

-- PU: 117 steps
lem-PU : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-PU = derive (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ [])
  (rw 6 q1 ∷
   rw 5 q1 ∷
   rw 4 q1 ∷
   rw 0 q2 ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q4 ∷
   rw 2 q8 ∷
   rw 1 q6 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 4 q3 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q7 ∷
   rw 4 q2 ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q4 ∷
   rw 6 q8 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   rw 5 q12 ∷
   rw 8 q3 ∷
   re 6 3 (CX30 ∷ []) ∷
   rw 9 q3 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 3 q13 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 6 q16 ∷
   rw 5 q17 ∷
   rw 4 q18 ∷
   rw 3 q19 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q20 ∷
   rw 3 q21 ∷
   rw⁻ 2 q20 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 3 q22 ∷
   rw 2 q23 ∷
   rw 3 q24 ∷
   rw 4 q25 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q26 ∷
   rw 7 q20 ∷
   re 5 3 (CX30 ∷ []) ∷
   rw 6 q27 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 8 q28 ∷
   rw 7 q29 ∷
   rw 6 q30 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   re 6 5 (CX30 ∷ []) ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   rw 8 q31 ∷
   rw 7 q19 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q20 ∷
   rw 7 q21 ∷
   rw⁻ 6 q20 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 7 q32 ∷
   rw 6 q23 ∷
   rw 7 q33 ∷
   rw 8 q25 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q26 ∷
   rw 11 q20 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q27 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 13 3 (CX13 ∷ []) ∷
   rw 12 q28 ∷
   rw 11 q29 ∷
   rw 10 q30 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   re 10 5 (CX30 ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q34 ∷
   rw 12 q35 ∷
   rw 11 q36 ∷
   re 10 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 11 q37 ∷
   rw⁻ 10 q36 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q34 ∷
   rw 15 q3 ∷
   re 13 3 (CX30 ∷ []) ∷
   rw 14 q7 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   rw 14 q38 ∷
   rw 13 q7 ∷
   rw 2 q39 ∷ []) Eq.refl

-- PUinv: 117 steps
lem-PUinv : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-PUinv = derive (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ [])
  (rw 6 q1 ∷
   rw 5 q1 ∷
   rw 4 q1 ∷
   rw 7 q3 ∷
   rw 6 q4 ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q4 ∷
   rw 1 q8 ∷
   rw 0 q6 ∷
   rw 1 q9 ∷
   rw 2 q3 ∷
   re 0 3 (CK30 ∷ []) ∷
   rw 3 q3 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 2 q10 ∷
   rw 3 q7 ∷
   rw 3 q2 ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q4 ∷
   rw 5 q8 ∷
   rw 4 q6 ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   rw 7 q3 ∷
   re 5 3 (CX30 ∷ []) ∷
   rw 8 q3 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q7 ∷
   rw 7 q2 ∷
   rw⁻ 2 q13 ∷
   rw 3 q14 ∷
   rw 2 q15 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q25 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q20 ∷
   rw 5 q26 ∷
   rw 6 q20 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q27 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   re 8 3 (CX13 ∷ []) ∷
   rw 7 q28 ∷
   rw 6 q29 ∷
   rw 5 q30 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   re 5 5 (CX30 ∷ []) ∷
   rw 9 q16 ∷
   rw 8 q17 ∷
   rw 7 q31 ∷
   rw 6 q19 ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw 6 q21 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (CX31 ∷ []) ∷
   rw 6 q32 ∷
   rw 5 q23 ∷
   rw 6 q33 ∷
   rw 7 q25 ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q20 ∷
   rw 9 q26 ∷
   rw 10 q20 ∷
   re 8 3 (CX30 ∷ []) ∷
   rw 9 q27 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 11 q28 ∷
   rw 10 q29 ∷
   rw 9 q30 ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   re 9 5 (CX30 ∷ []) ∷
   rw 13 q3 ∷
   rw 12 q34 ∷
   rw 11 q35 ∷
   rw 10 q36 ∷
   re 9 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 10 q37 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q34 ∷
   rw 14 q3 ∷
   re 12 3 (CX30 ∷ []) ∷
   rw 13 q7 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   re 12 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 13 q38 ∷
   rw 12 q7 ∷
   rw 1 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q43 : Eqn
  q43 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q44 : Eqn
  q44 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q45 : Eqn
  q45 = eqn (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wn 163 W)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q47 : Eqn
  q47 = eqn (CZ01 ∷ CS02 ∷ []) (CS02 ∷ CZ01 ∷ []) (wn 164 W)
  q48 : Eqn
  q48 = eqn (CZ01 ∷ CX32 ∷ []) (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀))
  q49 : Eqn
  q49 = eqn (CZ01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CZ01 ∷ []) (wn 165 W)
  q50 : Eqn
  q50 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap))
  q51 : Eqn
  q51 = eqn (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) (wn 166 W)
  q52 : Eqn
  q52 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q53 : Eqn
  q53 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)

-- comm CZ01 CCZ023: 83 steps
lem-comm-CZ01-CCZ023 : ⟪ (CZ01 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ01 ∷ []) ⟫ʷ
lem-comm-CZ01-CCZ023 = derive (CZ01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ01 ∷ [])
  (rw 2 q16 ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q40 ∷
   rw 2 q41 ∷
   rw 3 q42 ∷
   rw 4 q41 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q24 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q27 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw 6 q18 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q43 ∷
   rw⁻ 3 q42 ∷
   rw 2 q43 ∷
   rw⁻ 1 q40 ∷
   rw 2 q44 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 2 q45 ∷
   rw 1 q24 ∷
   rw 2 q46 ∷
   rw 3 q33 ∷
   rw 4 q46 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q24 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q27 ∷
   rw 0 q47 ∷
   rw 1 q48 ∷
   rw 2 q49 ∷
   rw 3 q48 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 4 q50 ∷
   rw 5 q47 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw⁻ 5 q50 ∷
   rw 6 q7 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q20 ∷
   rw 5 q18 ∷
   rw⁻ 4 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 3 q46 ∷
   rw 2 q31 ∷
   rw⁻ 1 q46 ∷
   rw 0 q18 ∷
   rw 1 q51 ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q40 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 3 q41 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q20 ∷
   rw 5 q24 ∷
   rw 6 q20 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q16 ∷
   rw 1 q40 ∷
   rw 2 q52 ∷
   rw 3 q42 ∷
   rw 4 q52 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q53 ∷
   rw 7 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q44 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   rw 1 q27 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (CZ01 ∷ CS12 ∷ []) (CS12 ∷ CZ01 ∷ []) (wn 167 W)
  q55 : Eqn
  q55 = eqn (CZ01 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CZ01 ∷ []) (wn 168 W)

-- comm CZ01 CCZ123: 15 steps
lem-comm-CZ01-CCZ123 : ⟪ (CZ01 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ01 ∷ []) ⟫ʷ
lem-comm-CZ01-CCZ123 = derive (CZ01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ01 ∷ [])
  (rw 1 q45 ∷
   rw 0 q54 ∷
   rw 1 q48 ∷
   rw 2 q55 ∷
   rw 3 q48 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 4 q50 ∷
   rw 5 q54 ∷
   rw 6 q3 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q50 ∷
   rw 6 q7 ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (CS12 ∷ CK10⁻ ∷ []) (CK10⁻ ∷ CS12 ∷ []) (wn 169 W)
  q57 : Eqn
  q57 = eqn (CK10⁻ ∷ CX32 ∷ []) (CX32 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q58 : Eqn
  q58 = eqn (CS12⁻ ∷ CK10⁻ ∷ []) (CK10⁻ ∷ CS12⁻ ∷ []) (wn 170 W)

-- CCZ123 passes CKd10: 15 steps
lem-CCZ123-passes-CKd10 : ⟪ (CCZ123 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ123-passes-CKd10 = derive (CCZ123 ∷ CK10⁻ ∷ []) (CK10⁻ ∷ CCZ123 ∷ [])
  (rw 0 q45 ∷
   rw 6 q3 ∷
   rw 5 q36 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q56 ∷
   rw⁻ 4 q36 ∷
   rw 7 q3 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 3 q57 ∷
   rw 2 q58 ∷
   rw⁻ 1 q57 ∷
   rw 0 q56 ∷
   rw 1 q51 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q60 : Eqn
  q60 = eqn (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) (Toff012 ∷ []) (wn 171 W)
  q61 : Eqn
  q61 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q62 : Eqn
  q62 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q63 : Eqn
  q63 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q64 : Eqn
  q64 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))

-- SW12-PP: 17 steps
lem-SW12-PP : ⟪ (Sw12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-SW12-PP = derive (Sw12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 4 q59 ∷
   rw 3 q59 ∷
   rw 2 q59 ∷
   rw 0 q60 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q61 ∷
   rw⁻ 3 q35 ∷
   rw 4 q62 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q63 ∷
   rw 2 q60 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q61 ∷
   rw⁻ 5 q64 ∷
   rw 6 q62 ∷
   re 3 5 (CS03⁻ ∷ []) ∷
   rw 4 q63 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ []) (wn 172 W)

-- pass [CCZ012] [CZ01]: 1 steps
lem-pass-CCZ012-vs-CZ01 : ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ01 = derive (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ [])
  (rw 0 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q67 : Eqn
  q67 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q68 : Eqn
  q68 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q69 : Eqn
  q69 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q70 : Eqn
  q70 = eqn (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) (wn 174 W)
  q71 : Eqn
  q71 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)

-- pass [CS03] [X3 TOFF013 X3]: 65 steps
lem-pass-CS03-vs-X3-TOFF013-X3 : ⟪ (CS03 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-TOFF013-X3 = derive (CS03 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ [])
  (rw 4 q3 ∷
   rw 3 q66 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q67 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 10 q7 ∷
   rw 9 q68 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q67 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 4 q67 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q4 ∷
   rw 3 q69 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q66 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q70 ∷
   rw 0 q71 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q67 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q68 ∷
   rw 1 q3 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw⁻ 4 q67 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw⁻ 6 q67 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 2 q69 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q71 ∷
   rw 5 q3 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) (wn 176 W)

-- pass [CSd03] [X3 TOFF013 X3]: 65 steps
lem-pass-CSd03-vs-X3-TOFF013-X3 : ⟪ (CS03⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-X3-TOFF013-X3 = derive (CS03⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 4 q3 ∷
   rw 3 q66 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q67 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 10 q7 ∷
   rw 9 q68 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q67 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 4 q67 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q4 ∷
   rw 3 q69 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q66 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q72 ∷
   rw 0 q71 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q67 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q68 ∷
   rw 1 q3 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw⁻ 4 q67 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw⁻ 6 q67 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 2 q69 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q71 ∷
   rw 5 q3 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q74 : Eqn
  q74 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q75 : Eqn
  q75 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)

-- pass [CS12] [CS03]: 9 steps
lem-pass-CS12-vs-CS03 : ⟪ (CS12 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CS03 = derive (CS12 ∷ CS03 ∷ []) (CS03 ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q73 ∷
   rw⁻ 2 q74 ∷
   rw 3 q75 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 0 5 (CS03 ∷ []) ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ []) (wn 93 W)

-- pass [CS02] [CS03]: 15 steps
lem-pass-CS02-vs-CS03 : ⟪ (CS02 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CS03 = derive (CS02 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ [])
  (rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q18 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 0 q18 ∷
   rw 1 q76 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q20 ∷
   rw 1 q24 ∷
   rw 2 q20 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q24 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) (wn 177 W)

-- pass [CCZ012] [CS12]: 1 steps
lem-pass-CCZ012-vs-CS12 : ⟪ (CCZ012 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS12 = derive (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ [])
  (rw 0 q77 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = eqn (CCZ012 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ012 ∷ []) (wn 178 W)

-- pass [CCZ012] [CZ12]: 1 steps
lem-pass-CCZ012-vs-CZ12 : ⟪ (CCZ012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ12 = derive (CCZ012 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ012 ∷ [])
  (rw 0 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = eqn (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ []) (wn 86 W)

-- pass [CS02] [CSd03]: 15 steps
lem-pass-CS02-vs-CSd03 : ⟪ (CS02 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CSd03 = derive (CS02 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS02 ∷ [])
  (rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q31 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 0 q18 ∷
   rw 1 q79 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q20 ∷
   rw 1 q33 ∷
   rw 2 q20 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q24 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wn 84 W)
  q81 : Eqn
  q81 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q82 : Eqn
  q82 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)

-- pass [CSd12] [CS03]: 9 steps
lem-pass-CSd12-vs-CS03 : ⟪ (CS12⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CS03 = derive (CS12⁻ ∷ CS03 ∷ []) (CS03 ∷ CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q3 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 q80 ∷
   rw⁻ 2 q81 ∷
   rw 3 q82 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 0 5 (CS03 ∷ []) ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = eqn (CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ CS12⁻ ∷ []) (wn 179 W)

-- pass [CSd02] [CS03]: 15 steps
lem-pass-CSd02-vs-CS03 : ⟪ (CS02⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CS03 = derive (CS02⁻ ∷ CS03 ∷ []) (CS03 ∷ CS02⁻ ∷ [])
  (rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q18 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 0 q31 ∷
   rw 1 q83 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q20 ∷
   rw 1 q24 ∷
   rw 2 q20 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q33 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ []) (wn 180 W)

-- pass [CCZ012] [CSd12]: 1 steps
lem-pass-CCZ012-vs-CSd12 : ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd12 = derive (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ [])
  (rw 0 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = eqn (CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12⁻ ∷ []) (wn 181 W)

-- pass [CSd02] [CSd03]: 15 steps
lem-pass-CSd02-vs-CSd03 : ⟪ (CS02⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CSd03 = derive (CS02⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS02⁻ ∷ [])
  (rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q31 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 0 q31 ∷
   rw 1 q85 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q20 ∷
   rw 1 q33 ∷
   rw 2 q20 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q33 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) (wn 182 W)

-- pass [TOFF012] [X2 TOFF012 X2]: 1 steps
lem-pass-TOFF012-vs-X2-TOFF012-X2 : ⟪ (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF012-X2 = derive (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ [])
  (rw 0 q86 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)

-- pass [CCZ013] [CZ01]: 47 steps
lem-pass-CCZ013-vs-CZ01 : ⟪ (CCZ013 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ01 = derive (CCZ013 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ013 ∷ [])
  (rw 2 q3 ∷
   rw 1 q50 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q3 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q67 ∷
   rw 4 q3 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q67 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q67 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q87 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q65 ∷
   rw⁻ 0 q50 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q67 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw⁻ 3 q67 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q67 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 2 q87 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

-- pass [CS02] [X2 TOFF012 X2]: 1 steps
lem-pass-CS02-vs-X2-TOFF012-X2 : ⟪ (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-X2-TOFF012-X2 = derive (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ [])
  (rw 0 q70 ∷ []) Eq.refl

-- pass [CSd02] [X2 TOFF012 X2]: 1 steps
lem-pass-CSd02-vs-X2-TOFF012-X2 : ⟪ (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-X2-TOFF012-X2 = derive (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ [])
  (rw 0 q72 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (S0 ∷ CS02 ∷ []) (CS02 ∷ S0 ∷ []) (wn 183 W)

-- pass [S0] [CS03]: 9 steps
lem-pass-S0-vs-CS03 : ⟪ (S0 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS03 = derive (S0 ∷ CS03 ∷ []) (CS03 ∷ S0 ∷ [])
  (rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q8 ∷
   rw 1 q88 ∷
   rw 2 q3 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q8 ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0 ∷ []) (wn 184 W)

-- pass [S0] [CSd03]: 9 steps
lem-pass-S0-vs-CSd03 : ⟪ (S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd03 = derive (S0 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0 ∷ [])
  (rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q8 ∷
   rw 1 q89 ∷
   rw 2 q3 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 q8 ∷
   rw 2 q7 ∷ []) Eq.refl

-- pass [CSd13] [CS02]: 5 steps
lem-pass-CSd13-vs-CS02 : ⟪ (CS13⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CS02 = derive (CS13⁻ ∷ CS02 ∷ []) (CS02 ∷ CS13⁻ ∷ [])
  (re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 0 q80 ∷
   rw⁻ 1 q81 ∷
   rw 2 q82 ∷
   re 0 3 (CS02 ∷ []) ∷ []) Eq.refl

-- pass [CCZ013] [CSd13]: 49 steps
lem-pass-CCZ013-vs-CSd13 : ⟪ (CCZ013 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd13 = derive (CCZ013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ013 ∷ [])
  (rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q3 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q67 ∷
   rw 4 q3 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q67 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q67 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q87 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q84 ∷
   rw 2 q3 ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q67 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw⁻ 3 q67 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q67 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 2 q87 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

-- pass [CCZ013] [CZ13]: 49 steps
lem-pass-CCZ013-vs-CZ13 : ⟪ (CCZ013 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ13 = derive (CCZ013 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ013 ∷ [])
  (rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q3 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q67 ∷
   rw 4 q3 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q67 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q67 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q87 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q78 ∷
   rw 2 q3 ∷
   re 0 3 (CZ13 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q67 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw⁻ 3 q67 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q67 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 2 q87 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (S0⁻ ∷ CS02 ∷ []) (CS02 ∷ S0⁻ ∷ []) (wn 185 W)

-- pass [Sd0] [CS03]: 9 steps
lem-pass-Sd0-vs-CS03 : ⟪ (S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CS03 = derive (S0⁻ ∷ CS03 ∷ []) (CS03 ∷ S0⁻ ∷ [])
  (rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q5 ∷
   rw 1 q90 ∷
   rw 2 q3 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q5 ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (S0⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0⁻ ∷ []) (wn 186 W)

-- pass [Sd0] [CSd03]: 9 steps
lem-pass-Sd0-vs-CSd03 : ⟪ (S0⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CSd03 = derive (S0⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0⁻ ∷ [])
  (rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q5 ∷
   rw 1 q91 ∷
   rw 2 q3 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 q5 ∷
   rw 2 q7 ∷ []) Eq.refl
