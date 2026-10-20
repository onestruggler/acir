{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) (wp 8 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) (wp 111 c4)

-- sym-ab: 18 steps
lem-sym-ab : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-ab c4 = derive (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (Bx0-24 ∷ []) ∷
   re 7 1 (Bx0-24 ∷ []) ∷
   re 2 6 (Bx2-034 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Bx0-24 ∷ []) ∷
   re 10 1 (Bx0-24 ∷ []) ∷
   re 5 6 (Bx2-034 ∷ []) ∷
   re 0 6 (Bx0-2134 ∷ []) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp 115 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) (wl 268 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) (wp 116 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) (wp 117 c4)

-- cQ @13243142: 7 steps
lem-cQ-at13243142 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243142 c4 = derive (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  (rw 0 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q3 c4) ∷ []) Eq.refl

-- cQ @13243241: 7 steps
lem-cQ-at13243241 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243241 c4 = derive (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  (rw 0 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q3 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) (wp 130 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) (wp 131 c4)

-- sym-ab @2332: 18 steps
lem-sym-ab-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-ab-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-3124 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Bx0-34 ∷ []) ∷
   re 7 1 (Bx0-34 ∷ []) ∷
   re 2 6 (Bx3-024 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 7 1 (Bx0-34 ∷ []) ∷
   re 10 1 (Bx0-34 ∷ []) ∷
   re 5 6 (Bx3-024 ∷ []) ∷
   re 0 6 (Bx0-3124 ∷ []) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ012 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (wl 269 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (wp 136 c4)

-- sym-ab @13243142: 18 steps
lem-sym-ab-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-ab-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-4312 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   re 4 1 (Bx0-42 ∷ []) ∷
   re 7 1 (Bx0-42 ∷ []) ∷
   re 2 6 (Bx4-012 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   re 7 1 (Bx0-42 ∷ []) ∷
   re 10 1 (Bx0-42 ∷ []) ∷
   re 5 6 (Bx4-012 ∷ []) ∷
   re 0 6 (Bx0-4312 ∷ []) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) (wp 153 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) (wp 154 c4)

-- sym-ab @122331: 18 steps
lem-sym-ab-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-ab-at122331 c4 = derive (Bx0-2314 ∷ []) (Bx0-3214 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   re 4 1 (Bx0-34 ∷ []) ∷
   re 7 1 (Bx0-34 ∷ []) ∷
   re 2 6 (Bx3-014 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 7 1 (Bx0-34 ∷ []) ∷
   re 10 1 (Bx0-34 ∷ []) ∷
   re 5 6 (Bx3-014 ∷ []) ∷
   re 0 6 (Bx0-3214 ∷ []) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl 288 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp 162 c4)

-- sym-ab @13243241: 18 steps
lem-sym-ab-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-ab-at13243241 c4 = derive (Bx0-3421 ∷ []) (Bx0-4321 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   re 4 1 (Bx0-41 ∷ []) ∷
   re 7 1 (Bx0-41 ∷ []) ∷
   re 2 6 (Bx4-021 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 5 (q15 c4) ∷
   re 7 1 (Bx0-41 ∷ []) ∷
   re 10 1 (Bx0-41 ∷ []) ∷
   re 5 6 (Bx4-021 ∷ []) ∷
   re 0 6 (Bx0-4321 ∷ []) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) (wl 292 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (wp 180 c4)

-- sym-ab @12243143: 18 steps
lem-sym-ab-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-ab-at12243143 c4 = derive (Bx0-2413 ∷ []) (Bx0-4213 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   re 4 1 (Bx0-43 ∷ []) ∷
   re 7 1 (Bx0-43 ∷ []) ∷
   re 2 6 (Bx4-013 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   re 7 1 (Bx0-43 ∷ []) ∷
   re 10 1 (Bx0-43 ∷ []) ∷
   re 5 6 (Bx4-013 ∷ []) ∷
   re 0 6 (Bx0-4213 ∷ []) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp 198 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ []) (wl 328 (lit c4))

-- cQ @14233142: 7 steps
lem-cQ-at14233142 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233142 c4 = derive (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  (rw 0 (q18 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q18 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp 211 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) (wp 212 c4)

-- sym-ab @13213442: 18 steps
lem-sym-ab-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-ab-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-1342 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   re 4 1 (Bx0-12 ∷ []) ∷
   re 7 1 (Bx0-12 ∷ []) ∷
   re 2 6 (Bx1-042 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   re 7 1 (Bx0-12 ∷ []) ∷
   re 10 1 (Bx0-12 ∷ []) ∷
   re 5 6 (Bx1-042 ∷ []) ∷
   re 0 6 (Bx0-1342 ∷ []) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) (wl 205 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp 216 c4)

-- sym-ab @243243: 18 steps
lem-sym-ab-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-ab-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-4123 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   re 4 1 (Bx0-43 ∷ []) ∷
   re 7 1 (Bx0-43 ∷ []) ∷
   re 2 6 (Bx4-023 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   re 7 1 (Bx0-43 ∷ []) ∷
   re 10 1 (Bx0-43 ∷ []) ∷
   re 5 6 (Bx4-023 ∷ []) ∷
   re 0 6 (Bx0-4123 ∷ []) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ014 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (wp 217 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp 218 c4)

-- sym-ab @133441: 18 steps
lem-sym-ab-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-ab-at133441 c4 = derive (Bx0-3241 ∷ []) (Bx0-2341 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   re 4 1 (Bx0-21 ∷ []) ∷
   re 7 1 (Bx0-21 ∷ []) ∷
   re 2 6 (Bx2-041 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   re 7 1 (Bx0-21 ∷ []) ∷
   re 10 1 (Bx0-21 ∷ []) ∷
   re 5 6 (Bx2-041 ∷ []) ∷
   re 0 6 (Bx0-2341 ∷ []) ∷ []) Eq.refl

-- sym-ab @12233441: 18 steps
lem-sym-ab-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-ab-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-3241 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 2 (q25 c4) ∷
   re 4 1 (Bx0-31 ∷ []) ∷
   re 7 1 (Bx0-31 ∷ []) ∷
   re 2 6 (Bx3-041 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q26 c4) ∷
   rw 5 (q25 c4) ∷
   re 7 1 (Bx0-31 ∷ []) ∷
   re 10 1 (Bx0-31 ∷ []) ∷
   re 5 6 (Bx3-041 ∷ []) ∷
   re 0 6 (Bx0-3241 ∷ []) ∷ []) Eq.refl

-- sym-ab @1221: 18 steps
lem-sym-ab-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-ab-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (Bx0-14 ∷ []) ∷
   re 7 1 (Bx0-14 ∷ []) ∷
   re 2 6 (Bx1-034 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 7 1 (Bx0-14 ∷ []) ∷
   re 10 1 (Bx0-14 ∷ []) ∷
   re 5 6 (Bx1-034 ∷ []) ∷
   re 0 6 (Bx0-1234 ∷ []) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) (wp 279 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ234 ∷ []) (wl 414 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl 415 (lit c4))

-- cQ @021021: 7 steps
lem-cQ-at021021 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at021021 c4 = derive (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  (rw 0 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q27 c4) ∷ []) Eq.refl

-- sym-ab @233442: 18 steps
lem-sym-ab-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-ab-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-3142 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q22 c4) ∷
   rw 2 (q21 c4) ∷
   re 4 1 (Bx0-32 ∷ []) ∷
   re 7 1 (Bx0-32 ∷ []) ∷
   re 2 6 (Bx3-042 ∷ []) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   re 7 1 (Bx0-32 ∷ []) ∷
   re 10 1 (Bx0-32 ∷ []) ∷
   re 5 6 (Bx3-042 ∷ []) ∷
   re 0 6 (Bx0-3142 ∷ []) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl 184 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ234 ∷ CS03 ∷ []) (CS03 ∷ CCZ234 ∷ []) (wp 294 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ234 ∷ []) (wl 432 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ234 ∷ CS13 ∷ []) (CS13 ∷ CCZ234 ∷ []) (wl 433 (lit c4))

-- cQ @03102132: 7 steps
lem-cQ-at03102132 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03102132 c4 = derive (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  (rw 0 (q32 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q32 c4) ∷ []) Eq.refl

-- sym-ab @14233142: 18 steps
lem-sym-ab-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-ab-at14233142 c4 = derive (Bx0-4312 ∷ []) (Bx0-3412 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 2 (q10 c4) ∷
   re 4 1 (Bx0-32 ∷ []) ∷
   re 7 1 (Bx0-32 ∷ []) ∷
   re 2 6 (Bx3-012 ∷ []) ∷
   re 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q11 c4) ∷
   rw 5 (q10 c4) ∷
   re 7 1 (Bx0-32 ∷ []) ∷
   re 10 1 (Bx0-32 ∷ []) ∷
   re 5 6 (Bx3-012 ∷ []) ∷
   re 0 6 (Bx0-3412 ∷ []) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ []) (wp 302 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ234 ∷ []) (wl 451 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) (wl 452 (lit c4))

-- cQ @0410213243: 7 steps
lem-cQ-at0410213243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at0410213243 c4 = derive (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  (rw 0 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q36 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp 341 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ234 ∷ []) (wp 342 c4)

-- cQ @04203243: 7 steps
lem-cQ-at04203243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at04203243 c4 = derive (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  (rw 0 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q37 c4) ∷
   rw⁻ 1 (q40 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) (wl 486 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) (wp 305 c4)

-- sym-ab @04203243: 18 steps
lem-sym-ab-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-sym-ab-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-0123 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q43 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   re 4 1 (Bx4-03 ∷ []) ∷
   re 7 1 (Bx4-03 ∷ []) ∷
   re 2 6 (Bx0-423 ∷ []) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (Bx4-03 ∷ []) ∷
   re 10 1 (Bx4-03 ∷ []) ∷
   re 5 6 (Bx0-423 ∷ []) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ []) (wl 493 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ123 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (wl 494 (lit c4))

-- sym-ab @0310243142: 18 steps
lem-sym-ab-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-ab-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-4012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   re 4 1 (Bx3-42 ∷ []) ∷
   re 7 1 (Bx3-42 ∷ []) ∷
   re 2 6 (Bx4-312 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   re 7 1 (Bx3-42 ∷ []) ∷
   re 10 1 (Bx3-42 ∷ []) ∷
   re 5 6 (Bx4-312 ∷ []) ∷
   re 0 6 (Bx3-4012 ∷ []) ∷ []) Eq.refl

-- sym-ab @0314203142: 18 steps
lem-sym-ab-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-ab-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-0412 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q46 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   re 4 1 (Bx3-02 ∷ []) ∷
   re 7 1 (Bx3-02 ∷ []) ∷
   re 2 6 (Bx0-312 ∷ []) ∷
   re 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q46 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   re 7 1 (Bx3-02 ∷ []) ∷
   re 10 1 (Bx3-02 ∷ []) ∷
   re 5 6 (Bx0-312 ∷ []) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

-- sym-ab @0410213243: 18 steps
lem-sym-ab-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-ab-at0410213243 c4 = derive (Bx4-0123 ∷ []) (Bx4-1023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (Bx4-13 ∷ []) ∷
   re 7 1 (Bx4-13 ∷ []) ∷
   re 2 6 (Bx1-423 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 7 1 (Bx4-13 ∷ []) ∷
   re 10 1 (Bx4-13 ∷ []) ∷
   re 5 6 (Bx1-423 ∷ []) ∷
   re 0 6 (Bx4-1023 ∷ []) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) (wp 280 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) (wl 518 (lit c4))

-- sym-ab @03102132: 18 steps
lem-sym-ab-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-ab-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 2 (q48 c4) ∷
   re 4 1 (Bx3-14 ∷ []) ∷
   re 7 1 (Bx3-14 ∷ []) ∷
   re 2 6 (Bx1-324 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 7 1 (Bx3-14 ∷ []) ∷
   re 10 1 (Bx3-14 ∷ []) ∷
   re 5 6 (Bx1-324 ∷ []) ∷
   re 0 6 (Bx3-1024 ∷ []) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl 477 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ234 ∷ []) (wp 363 c4)

-- cQ @032032: 7 steps
lem-cQ-at032032 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at032032 c4 = derive (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  (rw 0 (q49 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw⁻ 1 (q49 c4) ∷ []) Eq.refl

-- sym-ab @032032: 18 steps
lem-sym-ab-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-ab-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q48 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   re 4 1 (Bx3-04 ∷ []) ∷
   re 7 1 (Bx3-04 ∷ []) ∷
   re 2 6 (Bx0-324 ∷ []) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q48 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   re 7 1 (Bx3-04 ∷ []) ∷
   re 10 1 (Bx3-04 ∷ []) ∷
   re 5 6 (Bx0-324 ∷ []) ∷
   re 0 6 (Bx3-0124 ∷ []) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ014 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ013 ∷ []) (wp 398 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (wp 399 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (wp 400 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) (wl 548 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS03 ∷ Sw34 ∷ []) (Sw34 ∷ CS04 ∷ []) (wp 401 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS03⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS04⁻ ∷ []) (wp 402 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))

-- nat-S: 31 steps
lem-nat-S : Ws → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-nat-S c4 = derive (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) (Sb4-0-12-3 ∷ [])
  (re 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) ∷
   re 3 1 (CS04 ∷ []) ∷
   re 5 1 (CS04⁻ ∷ []) ∷
   re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   rw⁻ 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   re 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 5 1 (CZ04 ∷ []) ∷
   re 8 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q53 c4) ∷
   re 4 1 (Bx4-03 ∷ []) ∷
   re 7 1 (Bx4-03 ∷ []) ∷
   re 2 6 (Bx0-423 ∷ []) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q51 c4) ∷
   re 6 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 8 1 (CZ04 ∷ []) ∷
   re 11 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q53 c4) ∷
   re 7 1 (Bx4-03 ∷ []) ∷
   re 10 1 (Bx4-03 ∷ []) ∷
   re 5 6 (Bx0-423 ∷ []) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   rw 10 (q57 c4) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷
   re 2 1 (Sb4-0-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-0-3-2 ∷ []) ∷
   re 0 5 (Sb4-0-12-3 ∷ []) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (wl 549 (lit c4))

-- F4-I-I: 1 steps
lem-F4-I-I : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I c4 = derive (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp 403 c4)

-- F4-I-S0: 1 steps
lem-F4-I-S0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S0 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl 550 (lit c4))

-- F4-I-S1: 1 steps
lem-F4-I-S1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl 551 (lit c4))

-- F4-I-S2: 1 steps
lem-F4-I-S2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (wl 552 (lit c4))

-- F4-I-S3: 1 steps
lem-F4-I-S3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (wp 404 c4)

-- F4-I-K0: 1 steps
lem-F4-I-K0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K0 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl 553 (lit c4))

-- F4-I-K1: 1 steps
lem-F4-I-K1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K1 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (wl 554 (lit c4))

-- F4-I-K2: 1 steps
lem-F4-I-K2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (wl 555 (lit c4))

-- F4-I-K3: 1 steps
lem-F4-I-K3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp 410 c4)

-- F4-S0-I: 1 steps
lem-F4-S0-I : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-I c4 = derive (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp 411 c4)

-- F4-S0-S0: 1 steps
lem-F4-S0-S0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S0 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp 412 c4)

-- F4-S0-S1: 1 steps
lem-F4-S0-S1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (wp 413 c4)

-- F4-S0-S2: 1 steps
lem-F4-S0-S2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S2 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (wp 414 c4)

-- F4-S0-S3: 1 steps
lem-F4-S0-S3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S3 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (wp 415 c4)

-- F4-S0-K0: 1 steps
lem-F4-S0-K0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K0 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp 416 c4)

-- F4-S0-K1: 1 steps
lem-F4-S0-K1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K1 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (wp 417 c4)

-- F4-S0-K2: 1 steps
lem-F4-S0-K2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K2 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (wp 418 c4)

-- F4-S0-K3: 1 steps
lem-F4-S0-K3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K3 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (wl 563 (lit c4))

-- F4-S1-I: 1 steps
lem-F4-S1-I : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-I c4 = derive (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (wp 440 c4)

-- F4-S1-S0: 1 steps
lem-F4-S1-S0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S0 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl 564 (lit c4))

-- F4-S1-S1: 1 steps
lem-F4-S1-S1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (wl 565 (lit c4))

-- F4-S1-S2: 1 steps
lem-F4-S1-S2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S2 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (wl 566 (lit c4))

-- F4-S1-S3: 1 steps
lem-F4-S1-S3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S3 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (wp 441 c4)

-- F4-S1-K0: 1 steps
lem-F4-S1-K0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K0 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (wl 567 (lit c4))

-- F4-S1-K1: 1 steps
lem-F4-S1-K1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (wl 568 (lit c4))

-- F4-S1-K2: 1 steps
lem-F4-S1-K2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K2 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (wl 569 (lit c4))

-- F4-S1-K3: 1 steps
lem-F4-S1-K3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K3 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q84 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl 575 (lit c4))

-- F4-S2-I: 1 steps
lem-F4-S2-I : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I c4 = derive (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (wp 447 c4)

-- F4-S2-S0: 1 steps
lem-F4-S2-S0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S0 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (wl 576 (lit c4))

-- F4-S2-S1: 1 steps
lem-F4-S2-S1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl 577 (lit c4))

-- F4-S2-S2: 1 steps
lem-F4-S2-S2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q88 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (wl 578 (lit c4))

-- F4-S2-S3: 1 steps
lem-F4-S2-S3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q89 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (wp 448 c4)

-- F4-S2-K0: 1 steps
lem-F4-S2-K0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K0 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q90 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (wl 579 (lit c4))

-- F4-S2-K1: 1 steps
lem-F4-S2-K1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (wl 580 (lit c4))

-- F4-S2-K2: 1 steps
lem-F4-S2-K2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K2 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (wl 581 (lit c4))

-- F4-S2-K3: 1 steps
lem-F4-S2-K3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (wl 588 (lit c4))

-- F4-S3-I: 1 steps
lem-F4-S3-I : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I c4 = derive (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (wp 462 c4)

-- F4-S3-S0: 1 steps
lem-F4-S3-S0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S0 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (wl 589 (lit c4))

-- F4-S3-S1: 1 steps
lem-F4-S3-S1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (wl 590 (lit c4))

-- F4-S3-S2: 1 steps
lem-F4-S3-S2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl 591 (lit c4))

-- F4-S3-S3: 1 steps
lem-F4-S3-S3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (wp 463 c4)

-- F4-S3-K0: 1 steps
lem-F4-S3-K0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K0 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (wl 592 (lit c4))

-- F4-S3-K1: 1 steps
lem-F4-S3-K1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (wl 593 (lit c4))

-- F4-S3-K2: 1 steps
lem-F4-S3-K2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q101 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (wl 594 (lit c4))

-- F4-S3-K3: 1 steps
lem-F4-S3-K3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K3 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (wp 469 c4)

-- F4-K0-I: 1 steps
lem-F4-K0-I : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-I c4 = derive (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (wp 470 c4)

-- F4-K0-S0: 1 steps
lem-F4-K0-S0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S0 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (wp 471 c4)

-- F4-K0-S1: 1 steps
lem-F4-K0-S1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q105 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (wp 472 c4)

-- F4-K0-S2: 1 steps
lem-F4-K0-S2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S2 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (wp 473 c4)

-- F4-K0-S3: 1 steps
lem-F4-K0-S3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S3 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q107 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp 474 c4)

-- F4-K0-K0: 1 steps
lem-F4-K0-K0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K0 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (wp 475 c4)

-- F4-K0-K1: 1 steps
lem-F4-K0-K1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K1 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (wp 476 c4)

-- F4-K0-K2: 1 steps
lem-F4-K0-K2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K2 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q110 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (wp 477 c4)

-- F4-K0-K3: 1 steps
lem-F4-K0-K3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K3 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl 603 (lit c4))

-- F4-K1-I: 1 steps
lem-F4-K1-I : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-I c4 = derive (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp 494 c4)

-- F4-K1-S0: 1 steps
lem-F4-K1-S0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S0 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q113 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl 604 (lit c4))

-- F4-K1-S1: 1 steps
lem-F4-K1-S1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl 605 (lit c4))

-- F4-K1-S2: 1 steps
lem-F4-K1-S2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S2 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q115 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (wl 606 (lit c4))

-- F4-K1-S3: 1 steps
lem-F4-K1-S3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S3 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q116 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (wp 495 c4)

-- F4-K1-K0: 1 steps
lem-F4-K1-K0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K0 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q117 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl 607 (lit c4))

-- F4-K1-K1: 1 steps
lem-F4-K1-K1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (wl 608 (lit c4))

-- F4-K1-K2: 1 steps
lem-F4-K1-K2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K2 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q119 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (wl 609 (lit c4))

-- F4-K1-K3: 1 steps
lem-F4-K1-K3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K3 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q120 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) (wl 182 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ123 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (wl 610 (lit c4))

-- sym-ab @0210243143: 18 steps
lem-sym-ab-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-ab-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-4013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   re 4 1 (Bx2-43 ∷ []) ∷
   re 7 1 (Bx2-43 ∷ []) ∷
   re 2 6 (Bx4-213 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q121 c4) ∷
   rw 5 (q122 c4) ∷
   re 7 1 (Bx2-43 ∷ []) ∷
   re 10 1 (Bx2-43 ∷ []) ∷
   re 5 6 (Bx4-213 ∷ []) ∷
   re 0 6 (Bx2-4013 ∷ []) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ124 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ024 ∷ []) (wp 509 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (wp 510 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ024 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ124 ∷ []) (wp 511 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (wp 512 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Sw01 ∷ Bx2-43 ∷ []) (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))

-- nat-SWbc @0214203143: 23 steps
lem-nat-SWbc-at0214203143 : Ws → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214203143 c4 = derive (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (Bx2-4103 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   rw⁻ 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   re 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 2 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw 4 (q127 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw 7 (q127 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 9 (q123 c4) ∷
   re 11 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 10 (q125 c4) ∷
   rw 11 (q126 c4) ∷
   rw 12 (q127 c4) ∷
   rw 13 (q126 c4) ∷
   rw⁻ 14 (q125 c4) ∷
   rw 15 (q127 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (Bx4-203 ∷ []) ∷
   re 5 6 (Bx4-203 ∷ []) ∷
   re 0 6 (Bx2-4103 ∷ []) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ []) (wp 527 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (wp 528 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ []) (wp 529 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (wp 530 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (Bx0-21 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-21 ∷ []) (c₃ (CZ ↑) (Swap))

-- nat-SWbc @122441: 23 steps
lem-nat-SWbc-at122441 : Ws → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-nat-SWbc-at122441 c4 = derive (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (Bx0-2341 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw⁻ 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   re 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 2 (q131 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 6 (q131 c4) ∷
   rw⁻ 7 (q133 c4) ∷
   rw 8 (q130 c4) ∷
   rw⁻ 9 (q129 c4) ∷
   re 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 10 (q131 c4) ∷
   rw 11 (q132 c4) ∷
   rw⁻ 12 (q133 c4) ∷
   rw 13 (q132 c4) ∷
   rw⁻ 14 (q131 c4) ∷
   rw⁻ 15 (q133 c4) ∷
   rw 16 (q57 c4) ∷
   re 2 6 (Bx2-041 ∷ []) ∷
   re 5 6 (Bx2-041 ∷ []) ∷
   re 0 6 (Bx0-2341 ∷ []) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = eqn (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (wl 655 (lit c4))

-- F4-K2-I: 1 steps
lem-F4-K2-I : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I c4 = derive (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q134 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (wp 532 c4)

-- F4-K2-S0: 1 steps
lem-F4-K2-S0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S0 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (wl 656 (lit c4))

-- F4-K2-S1: 1 steps
lem-F4-K2-S1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q136 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (wl 657 (lit c4))

-- F4-K2-S2: 1 steps
lem-F4-K2-S2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = eqn (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (wl 658 (lit c4))

-- F4-K2-S3: 1 steps
lem-F4-K2-S3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q138 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (wp 533 c4)

-- F4-K2-K0: 1 steps
lem-F4-K2-K0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K0 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (wl 659 (lit c4))

-- F4-K2-K1: 1 steps
lem-F4-K2-K1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q140 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = eqn (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl 660 (lit c4))

-- F4-K2-K2: 1 steps
lem-F4-K2-K2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q141 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (wl 661 (lit c4))

-- F4-K2-K3: 1 steps
lem-F4-K2-K3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K3 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q142 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ024 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ014 ∷ []) (wp 551 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (wp 552 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ014 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ024 ∷ []) (wp 553 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (wp 554 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw12 ∷ Bx0-43 ∷ []) (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))

-- nat-SWbc @14213243: 23 steps
lem-nat-SWbc-at14213243 : Ws → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-nat-SWbc-at14213243 c4 = derive (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (Bx0-4213 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   rw⁻ 0 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   re 3 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   rw⁻ 2 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 4 (q147 c4) ∷
   rw 5 (q146 c4) ∷
   rw⁻ 6 (q145 c4) ∷
   rw 7 (q147 c4) ∷
   rw 8 (q144 c4) ∷
   rw⁻ 9 (q143 c4) ∷
   re 11 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   rw⁻ 10 (q145 c4) ∷
   rw 11 (q146 c4) ∷
   rw 12 (q147 c4) ∷
   rw 13 (q146 c4) ∷
   rw⁻ 14 (q145 c4) ∷
   rw 15 (q147 c4) ∷
   rw 16 (q148 c4) ∷
   re 2 6 (Bx4-013 ∷ []) ∷
   re 5 6 (Bx4-013 ∷ []) ∷
   re 0 6 (Bx0-4213 ∷ []) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (wl 687 (lit c4))

-- F4-K3-I: 1 steps
lem-F4-K3-I : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I c4 = derive (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q149 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (wp 557 c4)

-- F4-K3-S0: 1 steps
lem-F4-K3-S0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S0 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q150 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (wl 688 (lit c4))

-- F4-K3-S1: 1 steps
lem-F4-K3-S1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (wl 689 (lit c4))

-- F4-K3-S2: 1 steps
lem-F4-K3-S2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (wl 690 (lit c4))

-- F4-K3-S3: 1 steps
lem-F4-K3-S3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q153 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (wp 558 c4)

-- F4-K3-K0: 1 steps
lem-F4-K3-K0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K0 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (wl 691 (lit c4))

-- F4-K3-K1: 1 steps
lem-F4-K3-K1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q155 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (wl 692 (lit c4))

-- F4-K3-K2: 1 steps
lem-F4-K3-K2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K2 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q156 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl 693 (lit c4))

-- F4-K3-K3: 1 steps
lem-F4-K3-K3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q157 c4) ∷ []) Eq.refl

-- cQ @0210213443: 7 steps
lem-cQ-at0210213443 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0210213443 c4 = derive (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  (rw 0 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q27 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ013 ∷ []) (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl 231 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp 214 c4)

-- sym-ab @122441: 18 steps
lem-sym-ab-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-sym-ab-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-4231 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   re 4 1 (Bx0-41 ∷ []) ∷
   re 7 1 (Bx0-41 ∷ []) ∷
   re 2 6 (Bx4-031 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q158 c4) ∷
   rw 5 (q159 c4) ∷
   re 7 1 (Bx0-41 ∷ []) ∷
   re 10 1 (Bx0-41 ∷ []) ∷
   re 5 6 (Bx4-031 ∷ []) ∷
   re 0 6 (Bx0-4231 ∷ []) ∷ []) Eq.refl

-- cQ @14233241: 7 steps
lem-cQ-at14233241 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233241 c4 = derive (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  (rw 0 (q18 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q18 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ034 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ134 ∷ []) (wp 675 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (wp 676 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ134 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ034 ∷ []) (wp 677 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (wp 678 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (Sw01 ∷ Bx3-42 ∷ []) (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat-SWbc @0314213042: 23 steps
lem-nat-SWbc-at0314213042 : Ws → ⟪ (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314213042 c4 = derive (Sw01 ∷ Bx3-4102 ∷ Sw01 ∷ []) (Bx3-4012 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) ∷
   rw⁻ 0 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   re 3 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   rw⁻ 2 (q162 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q164 c4) ∷
   rw 5 (q163 c4) ∷
   rw⁻ 6 (q162 c4) ∷
   rw 7 (q164 c4) ∷
   rw 8 (q161 c4) ∷
   rw⁻ 9 (q160 c4) ∷
   re 11 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   rw⁻ 10 (q162 c4) ∷
   rw 11 (q163 c4) ∷
   rw 12 (q164 c4) ∷
   rw 13 (q163 c4) ∷
   rw⁻ 14 (q162 c4) ∷
   rw 15 (q164 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (Bx4-312 ∷ []) ∷
   re 5 6 (Bx4-312 ∷ []) ∷
   re 0 6 (Bx3-4012 ∷ []) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) (wp 516 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl 756 (lit c4))

-- sym-ab @0210233441: 18 steps
lem-sym-ab-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym-ab-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-3041 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   re 4 1 (Bx2-31 ∷ []) ∷
   re 7 1 (Bx2-31 ∷ []) ∷
   re 2 6 (Bx3-241 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q165 c4) ∷
   rw 5 (q166 c4) ∷
   re 7 1 (Bx2-31 ∷ []) ∷
   re 10 1 (Bx2-31 ∷ []) ∷
   re 5 6 (Bx3-241 ∷ []) ∷
   re 0 6 (Bx2-3041 ∷ []) ∷ []) Eq.refl

-- sym-ab @0213203441: 18 steps
lem-sym-ab-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym-ab-at0213203441 c4 = derive (Bx2-3041 ∷ []) (Bx2-0341 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q166 c4) ∷
   rw⁻ 2 (q165 c4) ∷
   re 4 1 (Bx2-01 ∷ []) ∷
   re 7 1 (Bx2-01 ∷ []) ∷
   re 2 6 (Bx0-241 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q166 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   re 7 1 (Bx2-01 ∷ []) ∷
   re 10 1 (Bx2-01 ∷ []) ∷
   re 5 6 (Bx0-241 ∷ []) ∷
   re 0 6 (Bx2-0341 ∷ []) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (wp 695 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (wp 696 c4)

-- nat-SWbc @0314203142: 23 steps
lem-nat-SWbc-at0314203142 : Ws → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314203142 c4 = derive (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (Bx3-4102 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q167 c4) ∷
   re 3 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   rw⁻ 2 (q160 c4) ∷
   rw 3 (q168 c4) ∷
   rw 4 (q164 c4) ∷
   rw 5 (q168 c4) ∷
   rw⁻ 6 (q160 c4) ∷
   rw 7 (q164 c4) ∷
   rw 8 (q167 c4) ∷
   rw⁻ 9 (q162 c4) ∷
   re 11 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   rw⁻ 10 (q160 c4) ∷
   rw 11 (q168 c4) ∷
   rw 12 (q164 c4) ∷
   rw 13 (q168 c4) ∷
   rw⁻ 14 (q160 c4) ∷
   rw 15 (q164 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (Bx4-302 ∷ []) ∷
   re 5 6 (Bx4-302 ∷ []) ∷
   re 0 6 (Bx3-4102 ∷ []) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (wp 714 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (wp 715 c4)

-- nat-SWbc @0214213043: 23 steps
lem-nat-SWbc-at0214213043 : Ws → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214213043 c4 = derive (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (Bx2-4013 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   rw⁻ 0 (q125 c4) ∷
   rw 1 (q169 c4) ∷
   re 3 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 2 (q123 c4) ∷
   rw 3 (q170 c4) ∷
   rw 4 (q127 c4) ∷
   rw 5 (q170 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw 7 (q127 c4) ∷
   rw 8 (q169 c4) ∷
   rw⁻ 9 (q125 c4) ∷
   re 11 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 10 (q123 c4) ∷
   rw 11 (q170 c4) ∷
   rw 12 (q127 c4) ∷
   rw 13 (q170 c4) ∷
   rw⁻ 14 (q123 c4) ∷
   rw 15 (q127 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (Bx4-213 ∷ []) ∷
   re 5 6 (Bx4-213 ∷ []) ∷
   re 0 6 (Bx2-4013 ∷ []) ∷ []) Eq.refl

-- sym-ab @0214203143: 18 steps
lem-sym-ab-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym-ab-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-0413 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 2 (q121 c4) ∷
   re 4 1 (Bx2-03 ∷ []) ∷
   re 7 1 (Bx2-03 ∷ []) ∷
   re 2 6 (Bx0-213 ∷ []) ∷
   re 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q122 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   re 7 1 (Bx2-03 ∷ []) ∷
   re 10 1 (Bx2-03 ∷ []) ∷
   re 5 6 (Bx0-213 ∷ []) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ034 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ024 ∷ []) (wp 594 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (wp 719 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (wl 814 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (wl 815 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS02 ∷ Sw23 ∷ []) (Sw23 ∷ CS03 ∷ []) (wl 816 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (CS02⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS03⁻ ∷ []) (wl 817 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))

-- nat-S @14213243: 31 steps
lem-nat-S-at14213243 : Ws → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-nat-S-at14213243 c4 = derive (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw⁻ 0 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   re 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 5 1 (CZ03 ∷ []) ∷
   re 8 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q173 c4) ∷
   re 4 1 (Bx3-02 ∷ []) ∷
   re 7 1 (Bx3-02 ∷ []) ∷
   re 2 6 (Bx0-312 ∷ []) ∷
   rw 3 (q172 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   re 6 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 8 1 (CZ03 ∷ []) ∷
   re 11 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q173 c4) ∷
   re 7 1 (Bx3-02 ∷ []) ∷
   re 10 1 (Bx3-02 ∷ []) ∷
   re 5 6 (Bx0-312 ∷ []) ∷
   rw 6 (q174 c4) ∷
   rw⁻ 7 (q175 c4) ∷
   rw 8 (q174 c4) ∷
   rw⁻ 9 (q176 c4) ∷
   rw 10 (q177 c4) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷
   re 2 1 (Sb3-0-2-1 ∷ []) ∷
   re 4 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 0 5 (Sb3-0-41-2 ∷ []) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = eqn (CCZ013 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ023 ∷ []) (wl 838 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (wl 839 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ023 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ013 ∷ []) (wl 840 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (wl 841 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (Sw12 ∷ Bx0-34 ∷ []) (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat-SWbc @1331: 23 steps
lem-nat-SWbc-at1331 : Ws → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-nat-SWbc-at1331 c4 = derive (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (Bx0-3124 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   rw⁻ 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   re 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   rw⁻ 2 (q180 c4) ∷
   rw 3 (q181 c4) ∷
   rw 4 (q182 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 6 (q180 c4) ∷
   rw 7 (q182 c4) ∷
   rw 8 (q179 c4) ∷
   rw⁻ 9 (q178 c4) ∷
   re 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   rw⁻ 10 (q180 c4) ∷
   rw 11 (q181 c4) ∷
   rw 12 (q182 c4) ∷
   rw 13 (q181 c4) ∷
   rw⁻ 14 (q180 c4) ∷
   rw 15 (q182 c4) ∷
   rw 16 (q148 c4) ∷
   re 2 6 (Bx3-024 ∷ []) ∷
   re 5 6 (Bx3-024 ∷ []) ∷
   re 0 6 (Bx0-3124 ∷ []) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp 732 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp 733 c4)

-- sym-ab @0312213440: 18 steps
lem-sym-ab-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym-ab-at0312213440 c4 = derive (Bx3-2140 ∷ []) (Bx3-1240 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 2 (q184 c4) ∷
   re 4 1 (Bx3-10 ∷ []) ∷
   re 7 1 (Bx3-10 ∷ []) ∷
   re 2 6 (Bx1-340 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q183 c4) ∷
   rw 5 (q184 c4) ∷
   re 7 1 (Bx3-10 ∷ []) ∷
   re 10 1 (Bx3-10 ∷ []) ∷
   re 5 6 (Bx1-340 ∷ []) ∷
   re 0 6 (Bx3-1240 ∷ []) ∷ []) Eq.refl

-- sym-ab @033440: 18 steps
lem-sym-ab-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-ab-at033440 c4 = derive (Bx3-1240 ∷ []) (Bx3-2140 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q184 c4) ∷
   rw 2 (q183 c4) ∷
   re 4 1 (Bx3-20 ∷ []) ∷
   re 7 1 (Bx3-20 ∷ []) ∷
   re 2 6 (Bx2-340 ∷ []) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q184 c4) ∷
   rw 5 (q183 c4) ∷
   re 7 1 (Bx3-20 ∷ []) ∷
   re 10 1 (Bx3-20 ∷ []) ∷
   re 5 6 (Bx2-340 ∷ []) ∷
   re 0 6 (Bx3-2140 ∷ []) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (wl 876 (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (wl 877 (lit c4))

-- nat-SWbc @132132: 23 steps
lem-nat-SWbc-at132132 : Ws → ⟪ (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-nat-SWbc-at132132 c4 = derive (Sw12 ∷ Bx0-3124 ∷ Sw12 ∷ []) (Bx0-3214 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   rw⁻ 0 (q180 c4) ∷
   rw 1 (q185 c4) ∷
   re 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   rw⁻ 2 (q178 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q182 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 6 (q178 c4) ∷
   rw 7 (q182 c4) ∷
   rw 8 (q185 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   re 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   rw⁻ 10 (q178 c4) ∷
   rw 11 (q186 c4) ∷
   rw 12 (q182 c4) ∷
   rw 13 (q186 c4) ∷
   rw⁻ 14 (q178 c4) ∷
   rw 15 (q182 c4) ∷
   rw 16 (q148 c4) ∷
   re 2 6 (Bx3-014 ∷ []) ∷
   re 5 6 (Bx3-014 ∷ []) ∷
   re 0 6 (Bx0-3214 ∷ []) ∷ []) Eq.refl
