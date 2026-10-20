{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0025 ; wl0027 ; wl0028 ; wl0030 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0042 ; wl0046 ; wl0047 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0062 ; wl0065 ; wl0067 ; wl0068 ; wl0069 ; wl0073 ; wl0074 ; wl0075 ; wl0078 ; wl0079 ; wl0080 ; wl0082 ; wl0084 ; wl0085 ; wl0086 ; wl0087 ; wl0088 ; wl0089 ; wl0090 ; wl0091 ; wl0092 ; wl0093)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ024 ; lem-nat-2-TOFF012 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-CCZ124 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨4·032⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-1-TOFF104)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw01 ∷ Bx4-032 ∷ []) (Bx4-132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·032⟩ c4)

-- nat 0 BOX(0;4132): 8 steps
lem-nat-0-BOX⟨0·4132⟩ : WsL → ⟪ (Sw01 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4132⟩ c4 = derive (Sw01 ∷ Bx0-4132 ∷ []) (Bx1-4032 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx1-4032 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) (wl0005 c4)

-- nat 1 BOX(1;42): 3 steps
lem-nat-1-BOX⟨1·42⟩ : WsL → ⟪ (Sw12 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·42⟩ c4 = derive (Sw12 ∷ Bx1-42 ∷ []) (Bx2-41 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   re 0 1 (Bx2-41 ∷ []) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw12 ∷ Bx1-42 ∷ []) (Bx2-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·42⟩ c4)

-- nat 1 BOX(4;132): 8 steps
lem-nat-1-BOX⟨4·132⟩ : WsL → ⟪ (Sw12 ∷ Bx4-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·132⟩ c4 = derive (Sw12 ∷ Bx4-132 ∷ []) (Bx4-231 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-42 ∷ Toff413 ∷ CCZ134 ∷ Bx1-42 ∷ []) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q7 c4) ∷
   re 0 6 (Bx4-231 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw12 ∷ Bx4-132 ∷ []) (Bx4-231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·132⟩ c4)

-- nat 1 BOX(1;4032): 8 steps
lem-nat-1-BOX⟨1·4032⟩ : WsL → ⟪ (Sw12 ∷ Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4032⟩ c4 = derive (Sw12 ∷ Bx1-4032 ∷ []) (Bx2-4031 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-132 ∷ Toff104 ∷ CCZ014 ∷ Bx4-132 ∷ []) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q10 c4) ∷
   re 0 6 (Bx2-4031 ∷ []) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = eqn (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) (wl0042 c4)

-- nat 2 BOX(2;41): 3 steps
lem-nat-2-BOX⟨2·41⟩ : WsL → ⟪ (Sw23 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·41⟩ c4 = derive (Sw23 ∷ Bx2-41 ∷ []) (Bx3-41 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q11 c4) ∷
   re 0 1 (Bx3-41 ∷ []) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) (wl0087 c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw23 ∷ Bx2-41 ∷ []) (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4)

-- nat 2 BOX(4;231): 8 steps
lem-nat-2-BOX⟨4·231⟩ : WsL → ⟪ (Sw23 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·231⟩ c4 = derive (Sw23 ∷ Bx4-231 ∷ []) (Bx4-321 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   rw⁻ 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 5 (q14 c4) ∷
   re 0 6 (Bx4-321 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ Bx4-231 ∷ []) (Bx4-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·231⟩ c4)

-- nat 2 BOX(2;4031): 8 steps
lem-nat-2-BOX⟨2·4031⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4031⟩ c4 = derive (Sw23 ∷ Bx2-4031 ∷ []) (Bx3-4021 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q15 c4) ∷
   rw 5 (q17 c4) ∷
   re 0 6 (Bx3-4021 ∷ []) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q19 : WsL → Eqn
  q19 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 CZ14: 5 steps
lem-nat-0-CZ14 : WsL → ⟪ (Sw01 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CZ14 c4 = derive (Sw01 ∷ CZ14 ∷ []) (CZ04 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CZ13 ∷ Sw34 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 2 (q18 c4) ∷
   re 0 3 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw01 ∷ CZ14 ∷ []) (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4)

-- nat 0 BOX(3;41): 3 steps
lem-nat-0-BOX⟨3·41⟩ : WsL → ⟪ (Sw01 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·41⟩ c4 = derive (Sw01 ∷ Bx3-41 ∷ []) (Bx3-40 ∷ Sw01 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q20 c4) ∷
   re 0 1 (Bx3-40 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ Bx3-41 ∷ []) (Bx3-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·41⟩ c4)

-- nat 0 BOX(4;321): 8 steps
lem-nat-0-BOX⟨4·321⟩ : WsL → ⟪ (Sw01 ∷ Bx4-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·321⟩ c4 = derive (Sw01 ∷ Bx4-321 ∷ []) (Bx4-320 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx4-320 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw01 ∷ Bx4-321 ∷ []) (Bx4-320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·321⟩ c4)

-- nat 0 BOX(3;4021): 8 steps
lem-nat-0-BOX⟨3·4021⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4021⟩ c4 = derive (Sw01 ∷ Bx3-4021 ∷ []) (Bx3-4120 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (Bx3-4120 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl0089 c4)

-- nat 1 BOX(0;14): 3 steps
lem-nat-1-BOX⟨0·14⟩ : WsL → ⟪ (Sw12 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·14⟩ c4 = derive (Sw12 ∷ Bx0-14 ∷ []) (Bx0-24 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q27 c4) ∷
   re 0 1 (Bx0-24 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw12 ∷ Bx0-14 ∷ []) (Bx0-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·14⟩ c4)

-- nat 1 BOX(1;034): 8 steps
lem-nat-1-BOX⟨1·034⟩ : WsL → ⟪ (Sw12 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·034⟩ c4 = derive (Sw12 ∷ Bx1-034 ∷ []) (Bx2-034 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx2-034 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw12 ∷ Bx1-034 ∷ []) (Bx2-034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·034⟩ c4)

-- nat 1 BOX(0;1234): 8 steps
lem-nat-1-BOX⟨0·1234⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1234⟩ c4 = derive (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw⁻ 0 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx0-2134 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 c4)

-- nat 2 BOX(0;24): 3 steps
lem-nat-2-BOX⟨0·24⟩ : WsL → ⟪ (Sw23 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·24⟩ c4 = derive (Sw23 ∷ Bx0-24 ∷ []) (Bx0-34 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q34 c4) ∷
   re 0 1 (Bx0-34 ∷ []) ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw23 ∷ Bx0-24 ∷ []) (Bx0-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·24⟩ c4)

-- nat 2 BOX(2;034): 8 steps
lem-nat-2-BOX⟨2·034⟩ : WsL → ⟪ (Sw23 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·034⟩ c4 = derive (Sw23 ∷ Bx2-034 ∷ []) (Bx3-024 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 0 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 5 (q37 c4) ∷
   re 0 6 (Bx3-024 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw23 ∷ Bx2-034 ∷ []) (Bx3-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·034⟩ c4)

-- nat 2 BOX(0;2134): 8 steps
lem-nat-2-BOX⟨0·2134⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2134⟩ c4 = derive (Sw23 ∷ Bx0-2134 ∷ []) (Bx0-3124 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q40 c4) ∷
   re 0 6 (Bx0-3124 ∷ []) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)

-- nat 3 TOFF214: 2 steps
lem-nat-3-TOFF214 : WsL → ⟪ (Sw34 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF214 c4 = derive (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   rw 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q45 : WsL → Eqn
  q45 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))
  q47 : WsL → Eqn
  q47 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q52 : WsL → Eqn
  q52 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q54 : WsL → Eqn
  q54 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q56 : WsL → Eqn
  q56 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q59 : WsL → Eqn
  q59 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q61 : WsL → Eqn
  q61 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)

-- nat 3 TOFF302: 80 steps
lem-nat-3-TOFF302 : WsL → ⟪ (Sw34 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF302 c4 = derive (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 2 (q42 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   rw 10 (q43 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q49 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw⁻ 6 (q50 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 0 (q52 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q52 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw 1 (q55 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q48 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 8 (q58 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q55 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 8 (q59 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw⁻ 3 (q61 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q44 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q43 c4) ∷
   rw⁻ 9 (q61 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff401 ∷ []) ∷
   re 0 3 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (CZ34 ∷ Sw34 ∷ []) (Sw34 ∷ CZ34 ∷ []) (wl0069 c4)

-- nat 3 BOX(0;34): 3 steps
lem-nat-3-BOX⟨0·34⟩ : WsL → ⟪ (Sw34 ∷ Bx0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·34⟩ c4 = derive (Sw34 ∷ Bx0-34 ∷ []) (Bx0-43 ∷ Sw34 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   re 0 1 (Bx0-43 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw34 ∷ Bx0-34 ∷ []) (Bx0-43 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·34⟩ c4)

-- nat 3 BOX(3;024): 8 steps
lem-nat-3-BOX⟨3·024⟩ : WsL → ⟪ (Sw34 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·024⟩ c4 = derive (Sw34 ∷ Bx3-024 ∷ []) (Bx4-023 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q65 c4) ∷
   re 0 6 (Bx4-023 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw34 ∷ Bx3-024 ∷ []) (Bx4-023 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·024⟩ c4)

-- nat 3 BOX(0;3124): 8 steps
lem-nat-3-BOX⟨0·3124⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3124⟩ c4 = derive (Sw34 ∷ Bx0-3124 ∷ []) (Bx0-4123 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q66 c4) ∷
   rw 5 (q68 c4) ∷
   re 0 6 (Bx0-4123 ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q70 : WsL → Eqn
  q70 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q71 : WsL → Eqn
  q71 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q72 : WsL → Eqn
  q72 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K))
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q76 : WsL → Eqn
  q76 c4 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wl0060 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q78 : WsL → Eqn
  q78 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q81 : WsL → Eqn
  q81 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q82 : WsL → Eqn
  q82 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- nat 0 TOFF204: 70 steps
lem-nat-0-TOFF204 : WsL → ⟪ (Sw01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF204 c4 = derive (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ [])
  (re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q43 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q44 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 11 (q43 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q70 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw 10 (q41 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 8 (q58 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q71 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw 9 (q48 c4) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q18 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q74 c4) ∷
   rw 7 (q79 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw⁻ 1 (q80 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 7 (q80 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 1 (q82 c4) ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff214 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q84 : WsL → Eqn
  q84 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4)

-- nat 0 TOFF402: 70 steps
lem-nat-0-TOFF402 : WsL → ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF402 c4 = derive (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ [])
  (re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 6 (q43 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q44 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 11 (q43 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q52 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw 10 (q41 c4) ∷
   rw 1 (q55 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 8 (q58 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q55 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw 9 (q48 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q18 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q83 c4) ∷
   rw 7 (q79 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 1 (q84 c4) ∷
   re 1 8 (Toff312 ∷ []) ∷
   re 0 3 (Toff412 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw01 ∷ Bx0-43 ∷ []) (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(0;43): 2 steps
lem-nat-0-BOX⟨0·43⟩ : WsL → ⟪ (Sw01 ∷ Bx0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·43⟩ c4 = derive (Sw01 ∷ Bx0-43 ∷ []) (Bx1-43 ∷ Sw01 ∷ [])
  (rw 0 (q85 c4) ∷
   re 0 1 (Bx1-43 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw01 ∷ Bx0-43 ∷ []) (Bx1-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·43⟩ c4)

-- nat 0 BOX(4;023): 8 steps
lem-nat-0-BOX⟨4·023⟩ : WsL → ⟪ (Sw01 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·023⟩ c4 = derive (Sw01 ∷ Bx4-023 ∷ []) (Bx4-123 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q86 c4) ∷
   rw 5 (q88 c4) ∷
   re 0 6 (Bx4-123 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw01 ∷ Bx4-023 ∷ []) (Bx4-123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·023⟩ c4)

-- nat 0 BOX(0;4123): 8 steps
lem-nat-0-BOX⟨0·4123⟩ : WsL → ⟪ (Sw01 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4123⟩ c4 = derive (Sw01 ∷ Bx0-4123 ∷ []) (Bx1-4023 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q89 c4) ∷
   re 0 6 (Bx1-4023 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw12 ∷ Bx1-43 ∷ []) (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(1;43): 2 steps
lem-nat-1-BOX⟨1·43⟩ : WsL → ⟪ (Sw12 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·43⟩ c4 = derive (Sw12 ∷ Bx1-43 ∷ []) (Bx2-43 ∷ Sw12 ∷ [])
  (rw 0 (q90 c4) ∷
   re 0 1 (Bx2-43 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl0079 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw12 ∷ Bx1-43 ∷ []) (Bx2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·43⟩ c4)

-- nat 1 BOX(4;123): 8 steps
lem-nat-1-BOX⟨4·123⟩ : WsL → ⟪ (Sw12 ∷ Bx4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·123⟩ c4 = derive (Sw12 ∷ Bx4-123 ∷ []) (Bx4-213 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-43 ∷ Toff412 ∷ CCZ124 ∷ Bx1-43 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx4-213 ∷ []) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw12 ∷ Bx4-123 ∷ []) (Bx4-213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·123⟩ c4)

-- nat 1 BOX(1;4023): 8 steps
lem-nat-1-BOX⟨1·4023⟩ : WsL → ⟪ (Sw12 ∷ Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4023⟩ c4 = derive (Sw12 ∷ Bx1-4023 ∷ []) (Bx2-4013 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-123 ∷ Toff104 ∷ CCZ014 ∷ Bx4-123 ∷ []) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q94 c4) ∷
   re 0 6 (Bx2-4013 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))

-- nat 2 TOFF104: 68 steps
lem-nat-2-TOFF104 : WsL → ⟪ (Sw23 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF104 c4 = derive (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q69 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   rw 10 (q43 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q60 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q95 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q97 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw⁻ 8 (q98 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw⁻ 10 (q97 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 6 (q69 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q43 c4) ∷
   rw⁻ 8 (q69 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   re 0 3 (Toff104 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF412: 2 steps
lem-nat-2-TOFF412 : WsL → ⟪ (Sw23 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF412 c4 = derive (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q43 c4) ∷
   re 0 3 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)

-- nat 2 BOX(2;43): 3 steps
lem-nat-2-BOX⟨2·43⟩ : WsL → ⟪ (Sw23 ∷ Bx2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·43⟩ c4 = derive (Sw23 ∷ Bx2-43 ∷ []) (Bx3-42 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q99 c4) ∷
   re 0 1 (Bx3-42 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4)
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw23 ∷ Bx2-43 ∷ []) (Bx3-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·43⟩ c4)

-- nat 2 BOX(4;213): 8 steps
lem-nat-2-BOX⟨4·213⟩ : WsL → ⟪ (Sw23 ∷ Bx4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·213⟩ c4 = derive (Sw23 ∷ Bx4-213 ∷ []) (Bx4-312 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 3 (q101 c4) ∷
   rw 4 (q100 c4) ∷
   rw 5 (q102 c4) ∷
   re 0 6 (Bx4-312 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw23 ∷ Bx4-213 ∷ []) (Bx4-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·213⟩ c4)

-- nat 2 BOX(2;4013): 8 steps
lem-nat-2-BOX⟨2·4013⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4013⟩ c4 = derive (Sw23 ∷ Bx2-4013 ∷ []) (Bx3-4012 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q15 c4) ∷
   rw 5 (q103 c4) ∷
   re 0 6 (Bx3-4012 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q107 : WsL → Eqn
  q107 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q109 : WsL → Eqn
  q109 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 c4)

-- nat 1 TOFF304: 134 steps
lem-nat-1-TOFF304 : WsL → ⟪ (Sw12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF304 c4 = derive (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ [])
  (re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q69 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q44 c4) ∷
   rw⁻ 11 (q43 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q69 c4) ∷
   rw⁻ 11 (q45 c4) ∷
   rw 12 (q43 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q60 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q60 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q70 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw 11 (q41 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 8 (q48 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q58 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 9 (q58 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 10 (q48 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q97 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw⁻ 9 (q98 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw⁻ 11 (q97 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 9 (q43 c4) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q106 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 3 (q108 c4) ∷
   rw⁻ 4 (q107 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q58 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   rw 7 (q58 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q46 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q43 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q97 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw⁻ 9 (q98 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw⁻ 11 (q97 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q61 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw⁻ 2 (q111 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q48 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q58 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 9 (q58 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q111 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q41 c4) ∷
   rw⁻ 9 (q70 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q43 c4) ∷
   rw⁻ 8 (q44 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q43 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw⁻ 11 (q45 c4) ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   re 2 3 (Toff104 ∷ []) ∷
   re 1 3 (Toff204 ∷ []) ∷
   re 0 3 (Toff304 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(3;41): 3 steps
lem-nat-1-BOX⟨3·41⟩ : WsL → ⟪ (Sw12 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·41⟩ c4 = derive (Sw12 ∷ Bx3-41 ∷ []) (Bx3-42 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q27 c4) ∷
   re 0 1 (Bx3-42 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw12 ∷ Bx3-41 ∷ []) (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4)

-- nat 1 BOX(4;321): 8 steps
lem-nat-1-BOX⟨4·321⟩ : WsL → ⟪ (Sw12 ∷ Bx4-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·321⟩ c4 = derive (Sw12 ∷ Bx4-321 ∷ []) (Bx4-312 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   rw⁻ 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q113 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 5 (q114 c4) ∷
   re 0 6 (Bx4-312 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4)
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw12 ∷ Bx4-321 ∷ []) (Bx4-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·321⟩ c4)

-- nat 1 BOX(3;4021): 8 steps
lem-nat-1-BOX⟨3·4021⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4021⟩ c4 = derive (Sw12 ∷ Bx3-4021 ∷ []) (Bx3-4012 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q115 c4) ∷
   rw 5 (q117 c4) ∷
   re 0 6 (Bx3-4012 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(3;42): 3 steps
lem-nat-1-BOX⟨3·42⟩ : WsL → ⟪ (Sw12 ∷ Bx3-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·42⟩ c4 = derive (Sw12 ∷ Bx3-42 ∷ []) (Bx3-41 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   re 0 1 (Bx3-41 ∷ []) ∷ []) Eq.refl

private
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw12 ∷ Bx3-42 ∷ []) (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4)

-- nat 1 BOX(4;312): 8 steps
lem-nat-1-BOX⟨4·312⟩ : WsL → ⟪ (Sw12 ∷ Bx4-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·312⟩ c4 = derive (Sw12 ∷ Bx4-312 ∷ []) (Bx4-321 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q118 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q118 c4) ∷
   re 0 6 (Bx4-321 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw12 ∷ Bx4-312 ∷ []) (Bx4-321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·312⟩ c4)

-- nat 1 BOX(3;4012): 8 steps
lem-nat-1-BOX⟨3·4012⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4012⟩ c4 = derive (Sw12 ∷ Bx3-4012 ∷ []) (Bx3-4021 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q115 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (Bx3-4021 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (ι1 ∷ Sw34 ∷ []) (Sw34 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap ↑))
  q121 : WsL → Eqn
  q121 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) (wl0073 c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) (wl0074 c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q126 : WsL → Eqn
  q126 c4 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι1 ∷ []) (wl0080 c4)

-- nat 0 TOFF214: 70 steps
lem-nat-0-TOFF214 : WsL → ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF214 c4 = derive (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw⁻ 1 (q80 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q81 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw⁻ 7 (q80 c4) ∷
   rw⁻ 8 (q120 c4) ∷
   rw 9 (q41 c4) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q121 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q122 c4) ∷
   rw 7 (q18 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q74 c4) ∷
   rw 7 (q123 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q111 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q48 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 8 (q58 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q111 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 8 (q70 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw⁻ 3 (q69 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q44 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q43 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 10 (q125 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   re 1 3 (Toff104 ∷ []) ∷
   re 0 3 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 CZ04: 5 steps
lem-nat-0-CZ04 : WsL → ⟪ (Sw01 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CZ04 c4 = derive (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q127 c4) ∷
   rw 2 (q18 c4) ∷
   re 0 3 (CZ14 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4)

-- nat 0 BOX(3;40): 3 steps
lem-nat-0-BOX⟨3·40⟩ : WsL → ⟪ (Sw01 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·40⟩ c4 = derive (Sw01 ∷ Bx3-40 ∷ []) (Bx3-41 ∷ Sw01 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q128 c4) ∷
   re 0 1 (Bx3-41 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw01 ∷ Bx3-40 ∷ []) (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4)

-- nat 0 BOX(4;320): 8 steps
lem-nat-0-BOX⟨4·320⟩ : WsL → ⟪ (Sw01 ∷ Bx4-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·320⟩ c4 = derive (Sw01 ∷ Bx4-320 ∷ []) (Bx4-321 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q129 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q129 c4) ∷
   re 0 6 (Bx4-321 ∷ []) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4)
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw01 ∷ Bx4-320 ∷ []) (Bx4-321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·320⟩ c4)

-- nat 0 BOX(3;4120): 8 steps
lem-nat-0-BOX⟨3·4120⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4120⟩ c4 = derive (Sw01 ∷ Bx3-4120 ∷ []) (Bx3-4021 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 3 (q131 c4) ∷
   rw 4 (q130 c4) ∷
   rw 5 (q132 c4) ∷
   re 0 6 (Bx3-4021 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q135 : WsL → Eqn
  q135 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q137 : WsL → Eqn
  q137 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ []) (wl0075 c4)

-- nat 0 TOFF413: 100 steps
lem-nat-0-TOFF413 : WsL → ⟪ (Sw01 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF413 c4 = derive (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   re 3 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw⁻ 2 (q52 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q81 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 6 (q81 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw⁻ 8 (q52 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 10 (q41 c4) ∷
   rw 1 (q133 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 3 3 (CX13 ∷ []) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   re 5 3 (CX13 ∷ []) ∷
   rw⁻ 6 (q95 c4) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 8 (q125 c4) ∷
   rw 9 (q43 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q134 c4) ∷
   rw⁻ 2 (q135 c4) ∷
   rw 3 (q136 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q122 c4) ∷
   rw 7 (q18 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q83 c4) ∷
   rw 7 (q123 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw 1 (q133 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q43 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q97 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw⁻ 9 (q98 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw⁻ 11 (q97 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 8 (q125 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 2 (q55 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q48 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q58 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 9 (q58 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q55 c4) ∷
   rw 9 (q124 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q41 c4) ∷
   rw⁻ 9 (q59 c4) ∷
   rw⁻ 10 (q120 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q43 c4) ∷
   rw⁻ 8 (q44 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q43 c4) ∷
   rw⁻ 10 (q61 c4) ∷
   rw⁻ 11 (q125 c4) ∷
   rw⁻ 4 (q137 c4) ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   re 2 3 (Toff401 ∷ []) ∷
   re 1 3 (Toff402 ∷ []) ∷
   re 0 3 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4)
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw01 ∷ Bx3-42 ∷ []) (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(4;312): 8 steps
lem-nat-0-BOX⟨4·312⟩ : WsL → ⟪ (Sw01 ∷ Bx4-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·312⟩ c4 = derive (Sw01 ∷ Bx4-312 ∷ []) (Bx4-302 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q138 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q138 c4) ∷
   rw 4 (q130 c4) ∷
   rw 5 (q139 c4) ∷
   re 0 6 (Bx4-302 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw01 ∷ Bx4-312 ∷ []) (Bx4-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·312⟩ c4)

-- nat 0 BOX(3;4012): 8 steps
lem-nat-0-BOX⟨3·4012⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4012⟩ c4 = derive (Sw01 ∷ Bx3-4012 ∷ []) (Bx3-4102 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q140 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q140 c4) ∷
   re 0 6 (Bx3-4102 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF013: 2 steps
lem-nat-1-TOFF013 : WsL → ⟪ (Sw12 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF013 c4 = derive (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q48 c4) ∷
   re 0 3 (Toff023 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)

-- nat 1 BOX(1;024): 8 steps
lem-nat-1-BOX⟨1·024⟩ : WsL → ⟪ (Sw12 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·024⟩ c4 = derive (Sw12 ∷ Bx1-024 ∷ []) (Bx2-014 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 0 (q31 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q141 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx2-014 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw12 ∷ Bx1-024 ∷ []) (Bx2-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·024⟩ c4)

-- nat 1 BOX(0;1324): 8 steps
lem-nat-1-BOX⟨0·1324⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1324⟩ c4 = derive (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q143 c4) ∷
   re 0 6 (Bx0-2314 ∷ []) ∷ []) Eq.refl

private
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)

-- nat 2 BOX(2;014): 8 steps
lem-nat-2-BOX⟨2·014⟩ : WsL → ⟪ (Sw23 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·014⟩ c4 = derive (Sw23 ∷ Bx2-014 ∷ []) (Bx3-014 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q144 c4) ∷
   rw 2 (q37 c4) ∷
   rw 3 (q144 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q37 c4) ∷
   re 0 6 (Bx3-014 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw23 ∷ Bx2-014 ∷ []) (Bx3-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·014⟩ c4)

-- nat 2 BOX(0;2314): 8 steps
lem-nat-2-BOX⟨0·2314⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2314⟩ c4 = derive (Sw23 ∷ Bx0-2314 ∷ []) (Bx0-3214 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   rw⁻ 0 (q35 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q145 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 5 (q146 c4) ∷
   re 0 6 (Bx0-3214 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q148 : WsL → Eqn
  q148 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q149 : WsL → Eqn
  q149 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))

-- nat 3 TOFF023: 80 steps
lem-nat-3-TOFF023 : WsL → ⟪ (Sw34 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF023 c4 = derive (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q147 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q147 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   rw 10 (q43 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q49 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw⁻ 6 (q50 c4) ∷
   rw⁻ 7 (q148 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q149 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q48 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 8 (q58 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q148 c4) ∷
   rw⁻ 8 (q51 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 8 (q149 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q44 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q43 c4) ∷
   rw⁻ 9 (q147 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 0 3 (Toff024 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF301: 2 steps
lem-nat-3-TOFF301 : WsL → ⟪ (Sw34 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF301 c4 = derive (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q41 c4) ∷
   re 0 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4)

-- nat 3 BOX(3;014): 8 steps
lem-nat-3-BOX⟨3·014⟩ : WsL → ⟪ (Sw34 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·014⟩ c4 = derive (Sw34 ∷ Bx3-014 ∷ []) (Bx4-013 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q65 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 0 6 (Bx4-013 ∷ []) ∷ []) Eq.refl

private
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw34 ∷ Bx3-014 ∷ []) (Bx4-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·014⟩ c4)

-- nat 3 BOX(0;3214): 8 steps
lem-nat-3-BOX⟨0·3214⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3214⟩ c4 = derive (Sw34 ∷ Bx0-3214 ∷ []) (Bx0-4213 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx0-4213 ∷ []) ∷ []) Eq.refl
