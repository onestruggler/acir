{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0024 ; wl0025 ; wl0027 ; wl0029 ; wl0030 ; wl0034 ; wl0037 ; wl0043 ; wl0045 ; wl0046 ; wl0047 ; wl0048 ; wl0049 ; wl0050 ; wl0051 ; wl0052 ; wl0053 ; wl0054 ; wl0055 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0062 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0069)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-TOFF014 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q3 : WsL → Eqn
  q3 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q9 : WsL → Eqn
  q9 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q12 : WsL → Eqn
  q12 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))

-- nat 3 CCZ023: 62 steps
lem-nat-3-CCZ023 : WsL → ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ023 c4 = derive (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   re 0 3 (CS24 ∷ []) ∷
   rw⁻ 1 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw⁻ 3 (q8 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 7 (q11 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 1 (q7 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 0 3 (CCZ024 ∷ []) ∷ []) Eq.refl

-- nat 3 CCZ013: 2 steps
lem-nat-3-CCZ013 : WsL → ⟪ (Sw34 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ013 c4 = derive (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (CCZ014 ∷ []) ∷ []) Eq.refl

-- nat 3 CZ14: 2 steps
lem-nat-3-CZ14 : WsL → ⟪ (Sw34 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ14 c4 = derive (Sw34 ∷ CZ14 ∷ []) (CZ13 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CZ13 ∷ Sw34 ∷ []) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw34 ∷ CZ14 ∷ []) (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4)

-- nat 3 BOX(0;14): 3 steps
lem-nat-3-BOX⟨0·14⟩ : WsL → ⟪ (Sw34 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·14⟩ c4 = derive (Sw34 ∷ Bx0-14 ∷ []) (Bx0-13 ∷ Sw34 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q13 c4) ∷
   re 0 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q15 : WsL → Eqn
  q15 c4 = eqn (Toff102 ∷ Sw34 ∷ []) (Sw34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw34 ∷ Bx0-14 ∷ []) (Bx0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·14⟩ c4)

-- nat 3 BOX(1;024): 8 steps
lem-nat-3-BOX⟨1·024⟩ : WsL → ⟪ (Sw34 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·024⟩ c4 = derive (Sw34 ∷ Bx1-024 ∷ []) (Bx1-023 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q16 c4) ∷
   re 0 6 (Bx1-023 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw34 ∷ Bx1-024 ∷ []) (Bx1-023 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·024⟩ c4)

-- nat 3 BOX(0;1324): 8 steps
lem-nat-3-BOX⟨0·1324⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1324⟩ c4 = derive (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q19 c4) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

-- nat 1 CCZ013: 2 steps
lem-nat-1-CCZ013 : WsL → ⟪ (Sw12 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ013 c4 = derive (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q4 c4) ∷
   re 0 3 (CCZ023 ∷ []) ∷ []) Eq.refl

-- nat 1 CCZ014: 2 steps
lem-nat-1-CCZ014 : WsL → ⟪ (Sw12 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CCZ014 c4 = derive (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q4 c4) ∷
   re 0 3 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0029 c4)

-- nat 1 BOX(0;13): 3 steps
lem-nat-1-BOX⟨0·13⟩ : WsL → ⟪ (Sw12 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·13⟩ c4 = derive (Sw12 ∷ Bx0-13 ∷ []) (Bx0-23 ∷ Sw12 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q20 c4) ∷
   re 0 1 (Bx0-23 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw12 ∷ Bx0-13 ∷ []) (Bx0-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·13⟩ c4)

-- nat 1 BOX(1;023): 8 steps
lem-nat-1-BOX⟨1·023⟩ : WsL → ⟪ (Sw12 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·023⟩ c4 = derive (Sw12 ∷ Bx1-023 ∷ []) (Bx2-013 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx2-013 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw12 ∷ Bx1-023 ∷ []) (Bx2-013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·023⟩ c4)

-- nat 1 BOX(0;1423): 8 steps
lem-nat-1-BOX⟨0·1423⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1423⟩ c4 = derive (Sw12 ∷ Bx0-1423 ∷ []) (Bx0-2413 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (Bx0-2413 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF201: 2 steps
lem-nat-2-TOFF201 : WsL → ⟪ (Sw23 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF201 c4 = derive (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 0 3 (Toff301 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (CZ23 ∷ Sw23 ∷ []) (Sw23 ∷ CZ23 ∷ []) (wl0045 c4)

-- nat 2 BOX(0;23): 3 steps
lem-nat-2-BOX⟨0·23⟩ : WsL → ⟪ (Sw23 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·23⟩ c4 = derive (Sw23 ∷ Bx0-23 ∷ []) (Bx0-32 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q27 c4) ∷
   re 0 1 (Bx0-32 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ Bx0-23 ∷ []) (Bx0-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·23⟩ c4)

-- nat 2 BOX(2;013): 8 steps
lem-nat-2-BOX⟨2·013⟩ : WsL → ⟪ (Sw23 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·013⟩ c4 = derive (Sw23 ∷ Bx2-013 ∷ []) (Bx3-012 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx3-012 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw23 ∷ Bx2-013 ∷ []) (Bx3-012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·013⟩ c4)

-- nat 2 BOX(0;2413): 8 steps
lem-nat-2-BOX⟨0·2413⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2413⟩ c4 = derive (Sw23 ∷ Bx0-2413 ∷ []) (Bx0-3412 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   rw 0 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx0-3412 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q38 : WsL → Eqn
  q38 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q42 : WsL → Eqn
  q42 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))

-- resp CCZ024 at 1: 55 steps
lem-resp-CCZ024-at-1 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-1 c4 = derive (CCZ024 ∷ []) (Sw01 ∷ CCZ124 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q34 c4) ∷
   re 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 1 3 (CX02 ∷ []) ∷
   rw⁻ 2 (q36 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q11 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw 5 (q4 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 3 (q39 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 1 (q39 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q7 c4) ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ124 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q47 : WsL → Eqn
  q47 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q50 : WsL → Eqn
  q50 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q55 : WsL → Eqn
  q55 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)

-- resp CCZ024 at 3: 190 steps
lem-resp-CCZ024-at-3 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-3 c4 = derive (CCZ024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ034 ∷ []) ∷
   rw⁻ 2 (q4 c4) ∷
   re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 8 (q11 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q45 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 9 (q11 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q11 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 1 (q49 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 7 (q45 c4) ∷
   rw⁻ 9 (q11 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 12 (q45 c4) ∷
   re 7 7 (CS04 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q4 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q11 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 10 (q11 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   re 4 3 (CCZ014 ∷ []) ∷
   re 3 3 (CCZ024 ∷ []) ∷
   re 2 3 (CCZ034 ∷ []) ∷
   rw⁻ 3 (q34 c4) ∷
   re 2 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 3 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 4 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q36 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 9 (q11 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q4 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q45 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 11 (q45 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q37 c4) ∷
   rw 7 (q38 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q52 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q51 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   re 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   re 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 9 (q7 c4) ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ124 ∷ []) ∷
   re 3 3 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))

-- resp CCZ124 at 3: 7 steps
lem-resp-CCZ124-at-3 : WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ124-at-3 c4 = derive (CCZ124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ134 ∷ []) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 2 (q57 c4) ∷ []) Eq.refl

-- resp CS14 at 2: 4 steps
lem-resp-CS14-at-2 : WsL → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS14-at-2 c4 = derive (CS14 ∷ []) (Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q4 c4) ∷
   rw 0 (q9 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 1 (q41 c4) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wl0049 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl0050 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q61 : WsL → Eqn
  q61 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl0051 c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wl0052 c4)

-- comm CX12 CCZ034: 15 steps
lem-comm-CX12-CCZ034 : WsL → ⟪ (CX12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-CCZ034 c4 = derive (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CX13 ∷ []) ∷
   rw 1 (q58 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   re 3 3 (CX24 ∷ []) ∷
   rw 3 (q59 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 5 (q61 c4) ∷
   re 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 8 (q7 c4) ∷
   rw 7 (q62 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   re 0 9 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))

-- resp CS13 at 2: 4 steps
lem-resp-CS13-at-2 : WsL → ⟪ (CS13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS13-at-2 c4 = derive (CS13 ∷ []) (Sw12 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q4 c4) ∷
   rw 0 (q63 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 1 (q64 c4) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)

-- resp TOFF013 at 2: 5 steps
lem-resp-TOFF013-at-2 : WsL → ⟪ (Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF013-at-2 c4 = derive (Toff013 ∷ []) (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q4 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 1 (q65 c4) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw12 ∷ CX34 ∷ []) (CX34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CX₀₁))
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ CX34 ∷ []) (CX34 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₀₁ ↑))

-- resp CX24 at 3: 6 steps
lem-resp-CX24-at-3 : WsL → ⟪ (CX24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX24-at-3 c4 = derive (CX24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q59 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 2 (q67 c4) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (CX14 ∷ Sw23 ∷ []) (Sw23 ∷ CX14 ∷ []) (wl0054 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ []) (wl0055 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ CX24 ∷ []) (CX24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))

-- resp CX14 at 3: 6 steps
lem-resp-CX14-at-3 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX14-at-3 c4 = derive (CX14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q68 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 2 (q70 c4) ∷ []) Eq.refl

-- resp CX04 at 1: 6 steps
lem-resp-CX04-at-1 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX04-at-1 c4 = derive (CX04 ∷ []) (Sw01 ∷ CX14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q34 c4) ∷
   re 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 0 (q37 c4) ∷
   re 1 3 (CX14 ∷ []) ∷ []) Eq.refl

-- resp CX04 at 3: 20 steps
lem-resp-CX04-at-3 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX04-at-3 c4 = derive (CX04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q45 c4) ∷
   rw 4 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   re 1 7 (CX04 ∷ []) ∷
   rw⁻ 2 (q4 c4) ∷
   re 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw⁻ 3 (q34 c4) ∷
   re 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   re 3 3 (CX14 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q72 : WsL → Eqn
  q72 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q73 : WsL → Eqn
  q73 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q74 : WsL → Eqn
  q74 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q75 : WsL → Eqn
  q75 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q77 : WsL → Eqn
  q77 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑))
  q80 : WsL → Eqn
  q80 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q82 : WsL → Eqn
  q82 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- resp TOFF304 at 1: 101 steps
lem-resp-TOFF304-at-1 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff314 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-1 c4 = derive (Toff304 ∷ []) (Sw01 ∷ Toff314 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q34 c4) ∷
   re 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q71 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 8 (q11 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 0 (q77 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q45 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 9 (q11 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 7 (q72 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 6 (q79 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 6 (q38 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 0 (q79 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw⁻ 9 (q72 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 7 (q42 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 9 (q81 c4) ∷
   rw⁻ 10 (q74 c4) ∷
   rw 3 (q82 c4) ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff214 ∷ []) ∷
   re 1 3 (Toff314 ∷ []) ∷ []) Eq.refl

-- nat 2 CCZ124: 2 steps
lem-nat-2-CCZ124 : WsL → ⟪ (Sw23 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ124 c4 = derive (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 0 3 (CCZ134 ∷ []) ∷ []) Eq.refl

-- nat 2 CCZ134: 2 steps
lem-nat-2-CCZ134 : WsL → ⟪ (Sw23 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ134 c4 = derive (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

-- nat 1 TOFF302: 2 steps
lem-nat-1-TOFF302 : WsL → ⟪ (Sw12 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF302 c4 = derive (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

-- nat 1 TOFF301: 2 steps
lem-nat-1-TOFF301 : WsL → ⟪ (Sw12 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF301 c4 = derive (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q4 c4) ∷
   re 0 3 (Toff302 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wl0060 c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)

-- nat 0 CCZ024: 54 steps
lem-nat-0-CCZ024 : WsL → ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ024 c4 = derive (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q36 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 7 (q11 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q4 c4) ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   rw 6 (q37 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ124 ∷ []) ∷ []) Eq.refl

-- nat 0 CCZ124: 54 steps
lem-nat-0-CCZ124 : WsL → ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ124 c4 = derive (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q42 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 6 (q37 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 7 (q11 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 1 (q7 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 0 3 (CCZ024 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF204: 2 steps
lem-nat-2-TOFF204 : WsL → ⟪ (Sw23 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF204 c4 = derive (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 0 3 (Toff304 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF304: 2 steps
lem-nat-2-TOFF304 : WsL → ⟪ (Sw23 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF304 c4 = derive (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 c4)

-- nat 3 TOFF203: 80 steps
lem-nat-3-TOFF203 : WsL → ⟪ (Sw34 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF203 c4 = derive (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 (q71 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 9 (q72 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q8 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q81 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q85 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 8 (q11 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q85 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 10 (q72 c4) ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   re 1 3 (Toff104 ∷ []) ∷
   re 0 3 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)

-- nat 3 TOFF204: 80 steps
lem-nat-3-TOFF204 : WsL → ⟪ (Sw34 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF204 c4 = derive (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q71 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 8 (q11 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q85 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 9 (q72 c4) ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF103: 2 steps
lem-nat-1-TOFF103 : WsL → ⟪ (Sw12 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF103 c4 = derive (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q4 c4) ∷
   re 0 3 (Toff203 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)

-- comm TOFF214 CSd03: 9 steps
lem-comm-TOFF214-CSd03 : WsL → ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CSd03 c4 = derive (Toff214 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff214 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw⁻ 1 (q87 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   re 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 0 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))

-- comm TOFF314 CS02: 23 steps
lem-comm-TOFF314-CS02 : WsL → ⟪ (Toff314 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CS02 c4 = derive (Toff314 ∷ CS02 ∷ []) (CS02 ∷ Toff314 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS03 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS04 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   re 3 3 (Toff214 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   rw⁻ 6 (q89 c4) ∷
   re 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 2 7 (CS04 ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (Toff314 ∷ []) ∷ []) Eq.refl

-- comm CS03 TOFF214: 9 steps
lem-comm-CS03-TOFF214 : WsL → ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-TOFF214 c4 = derive (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ CS03 ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw 3 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   rw 1 (q87 c4) ∷
   re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (CS03 ∷ []) ∷ []) Eq.refl

-- comm TOFF314 CSd02: 23 steps
lem-comm-TOFF314-CSd02 : WsL → ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CSd02 c4 = derive (Toff314 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff314 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   re 3 3 (Toff214 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff314 ∷ []) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 5 (q88 c4) ∷
   rw⁻ 6 (q89 c4) ∷
   re 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 10 (q7 c4) ∷
   re 2 7 (CS04⁻ ∷ []) ∷
   re 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q7 c4) ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 1 5 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)

-- nat 2 BOX(0;34): 3 steps
lem-nat-2-BOX⟨0·34⟩ : WsL → ⟪ (Sw23 ∷ Bx0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·34⟩ c4 = derive (Sw23 ∷ Bx0-34 ∷ []) (Bx0-24 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   re 0 1 (Bx0-24 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw23 ∷ Bx0-34 ∷ []) (Bx0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·34⟩ c4)

-- nat 2 BOX(3;024): 8 steps
lem-nat-2-BOX⟨3·024⟩ : WsL → ⟪ (Sw23 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·024⟩ c4 = derive (Sw23 ∷ Bx3-024 ∷ []) (Bx2-034 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 5 (q94 c4) ∷
   re 0 6 (Bx2-034 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw23 ∷ Bx3-024 ∷ []) (Bx2-034 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·024⟩ c4)

-- nat 2 BOX(0;3124): 8 steps
lem-nat-2-BOX⟨0·3124⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3124⟩ c4 = derive (Sw23 ∷ Bx0-3124 ∷ []) (Bx0-2134 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q96 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q97 c4) ∷
   re 0 6 (Bx0-2134 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q100 : WsL → Eqn
  q100 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))

-- nat 3 TOFF402: 80 steps
lem-nat-3-TOFF402 : WsL → ⟪ (Sw34 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF402 c4 = derive (Sw34 ∷ Toff402 ∷ []) (Toff302 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 3 (q77 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q77 c4) ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q98 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 10 (q7 c4) ∷
   rw 1 (q99 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 8 (q11 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q99 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q100 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q101 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 7 (q101 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw⁻ 9 (q72 c4) ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   re 0 3 (Toff302 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (CZ34 ∷ Sw34 ∷ []) (Sw34 ∷ CZ34 ∷ []) (wl0069 c4)

-- nat 3 BOX(0;43): 3 steps
lem-nat-3-BOX⟨0·43⟩ : WsL → ⟪ (Sw34 ∷ Bx0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-34 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·43⟩ c4 = derive (Sw34 ∷ Bx0-43 ∷ []) (Bx0-34 ∷ Sw34 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q102 c4) ∷
   re 0 1 (Bx0-34 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw34 ∷ Toff402 ∷ []) (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw34 ∷ Bx0-43 ∷ []) (Bx0-34 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·43⟩ c4)

-- nat 3 BOX(4;023): 8 steps
lem-nat-3-BOX⟨4·023⟩ : WsL → ⟪ (Sw34 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·023⟩ c4 = derive (Sw34 ∷ Bx4-023 ∷ []) (Bx3-024 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q104 c4) ∷
   rw 4 (q103 c4) ∷
   rw 5 (q105 c4) ∷
   re 0 6 (Bx3-024 ∷ []) ∷ []) Eq.refl
