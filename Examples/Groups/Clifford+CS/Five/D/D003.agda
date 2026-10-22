{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)

module Examples.Groups.Clifford+CS.Five.D.D003 where

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
  q1 c4 = wpE 1068 c4
  q2 : Ws → Eqn
  q2 c4 = wlE 1379 (lit c4)

-- sym-ab @0310213442: 18 steps
lem-sym-ab-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym-ab-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-1042 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (Bx3-12 ∷ []) ∷
   re 7 1 (Bx3-12 ∷ []) ∷
   re 2 6 (Bx1-342 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Bx3-12 ∷ []) ∷
   re 10 1 (Bx3-12 ∷ []) ∷
   re 5 6 (Bx1-342 ∷ []) ∷
   re 0 6 (Bx3-1042 ∷ []) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = wlE 477 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 433 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q6 : Ws → Eqn
  q6 c4 = wpE 363 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 294 c4

-- cQ @03203442: 7 steps
lem-cQ-at03203442 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03203442 c4 = derive (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  (rw 0 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q3 c4) ∷ []) Eq.refl

-- sym-ab @03203442: 18 steps
lem-sym-ab-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym-ab-at03203442 c4 = derive (Bx3-1042 ∷ []) (Bx3-0142 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (Bx3-02 ∷ []) ∷
   re 7 1 (Bx3-02 ∷ []) ∷
   re 2 6 (Bx0-342 ∷ []) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 7 1 (Bx3-02 ∷ []) ∷
   re 10 1 (Bx3-02 ∷ []) ∷
   re 5 6 (Bx0-342 ∷ []) ∷
   re 0 6 (Bx3-0142 ∷ []) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = wpE 131 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 130 c4

-- sym-ab @02132130: 18 steps
lem-sym-ab-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-ab-at02132130 c4 = derive (Bx2-3104 ∷ []) (Bx2-1304 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Bx2-14 ∷ []) ∷
   re 7 1 (Bx2-14 ∷ []) ∷
   re 2 6 (Bx1-204 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 7 1 (Bx2-14 ∷ []) ∷
   re 10 1 (Bx2-14 ∷ []) ∷
   re 5 6 (Bx1-204 ∷ []) ∷
   re 0 6 (Bx2-1304 ∷ []) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = wpE 262 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 1303 (lit c4)

-- sym-ab @031031: 18 steps
lem-sym-ab-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym-ab-at031031 c4 = derive (Bx3-0214 ∷ []) (Bx3-2014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   re 4 1 (Bx3-24 ∷ []) ∷
   re 7 1 (Bx3-24 ∷ []) ∷
   re 2 6 (Bx2-314 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 7 1 (Bx3-24 ∷ []) ∷
   re 10 1 (Bx3-24 ∷ []) ∷
   re 5 6 (Bx2-314 ∷ []) ∷
   re 0 6 (Bx3-2014 ∷ []) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = wlE 344 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 661 c4

-- sym-ab @03243042: 18 steps
lem-sym-ab-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-ab-at03243042 c4 = derive (Bx3-1402 ∷ []) (Bx3-4102 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   re 4 1 (Bx3-42 ∷ []) ∷
   re 7 1 (Bx3-42 ∷ []) ∷
   re 2 6 (Bx4-302 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw 5 (q13 c4) ∷
   re 7 1 (Bx3-42 ∷ []) ∷
   re 10 1 (Bx3-42 ∷ []) ∷
   re 5 6 (Bx4-302 ∷ []) ∷
   re 0 6 (Bx3-4102 ∷ []) ∷ []) Eq.refl

-- sym-ab @0314213042: 18 steps
lem-sym-ab-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym-ab-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-1402 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   re 4 1 (Bx3-12 ∷ []) ∷
   re 7 1 (Bx3-12 ∷ []) ∷
   re 2 6 (Bx1-302 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (Bx3-12 ∷ []) ∷
   re 10 1 (Bx3-12 ∷ []) ∷
   re 5 6 (Bx1-302 ∷ []) ∷
   re 0 6 (Bx3-1402 ∷ []) ∷ []) Eq.refl

-- sym-ab @142142: 18 steps
lem-sym-ab-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym-ab-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-1432 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   re 4 1 (Bx0-12 ∷ []) ∷
   re 7 1 (Bx0-12 ∷ []) ∷
   re 2 6 (Bx1-032 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (Bx0-12 ∷ []) ∷
   re 10 1 (Bx0-12 ∷ []) ∷
   re 5 6 (Bx1-032 ∷ []) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

-- sym-ab @2442: 18 steps
lem-sym-ab-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-ab-at2442 c4 = derive (Bx0-1432 ∷ []) (Bx0-4132 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   re 4 1 (Bx0-42 ∷ []) ∷
   re 7 1 (Bx0-42 ∷ []) ∷
   re 2 6 (Bx4-032 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw 5 (q13 c4) ∷
   re 7 1 (Bx0-42 ∷ []) ∷
   re 10 1 (Bx0-42 ∷ []) ∷
   re 5 6 (Bx4-032 ∷ []) ∷
   re 0 6 (Bx0-4132 ∷ []) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wpE 1232 c4
  q15 : Ws → Eqn
  q15 c4 = wlE 1341 (lit c4)

-- sym-ab @02102331: 18 steps
lem-sym-ab-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym-ab-at02102331 c4 = derive (Bx2-0314 ∷ []) (Bx2-3014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   re 4 1 (Bx2-34 ∷ []) ∷
   re 7 1 (Bx2-34 ∷ []) ∷
   re 2 6 (Bx3-214 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   re 7 1 (Bx2-34 ∷ []) ∷
   re 10 1 (Bx2-34 ∷ []) ∷
   re 5 6 (Bx3-214 ∷ []) ∷
   re 0 6 (Bx2-3014 ∷ []) ∷ []) Eq.refl

-- sym-ab @02132031: 18 steps
lem-sym-ab-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym-ab-at02132031 c4 = derive (Bx2-3014 ∷ []) (Bx2-0314 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   re 4 1 (Bx2-04 ∷ []) ∷
   re 7 1 (Bx2-04 ∷ []) ∷
   re 2 6 (Bx0-214 ∷ []) ∷
   re 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 7 1 (Bx2-04 ∷ []) ∷
   re 10 1 (Bx2-04 ∷ []) ∷
   re 5 6 (Bx0-214 ∷ []) ∷
   re 0 6 (Bx2-0314 ∷ []) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = wpE 404 c4

-- F4-I-K2 @02132031: 1 steps
lem-F4-I-K2-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2-at02132031 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = wpE 441 c4

-- F4-S3-K2 @02132031: 1 steps
lem-F4-S3-K2-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2-at02132031 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = wpE 474 c4

-- F4-K2-K2 @02132031: 1 steps
lem-F4-K2-K2-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2-at02132031 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = wlE 550 (lit c4)

-- F4-I-S3 @02132031: 1 steps
lem-F4-I-S3-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3-at02132031 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = wlE 564 (lit c4)

-- F4-S3-S3 @02132031: 1 steps
lem-F4-S3-S3-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3-at02132031 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wpE 471 c4

-- F4-K2-S3 @02132031: 1 steps
lem-F4-K2-S3-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3-at02132031 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = wlE 549 (lit c4)

-- F4-I-I @02132031: 1 steps
lem-F4-I-I-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I-at02132031 c4 = derive (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = wlE 563 (lit c4)

-- F4-S3-I @02132031: 1 steps
lem-F4-S3-I-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I-at02132031 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = wpE 469 c4

-- F4-K2-I @02132031: 1 steps
lem-F4-K2-I-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I-at02132031 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = wpE 403 c4

-- F4-I-S2 @02132031: 1 steps
lem-F4-I-S2-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2-at02132031 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q25 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = wpE 440 c4

-- F4-S3-S2 @02132031: 1 steps
lem-F4-S3-S2-at02132031 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2-at02132031 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wpE 470 c4

-- F4-K2-S2 @02132031: 1 steps
lem-F4-K2-S2-at02132031 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2-at02132031 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = wlE 553 (lit c4)

-- F4-I-K2 @132132: 1 steps
lem-F4-I-K2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2-at132132 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 579 (lit c4)

-- F4-S3-K2 @132132: 1 steps
lem-F4-S3-K2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2-at132132 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = wlE 607 (lit c4)

-- F4-K2-K2 @132132: 1 steps
lem-F4-K2-K2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2-at132132 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = wlE 551 (lit c4)

-- F4-I-S3 @132132: 1 steps
lem-F4-I-S3-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3-at132132 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = wlE 577 (lit c4)

-- F4-S3-S3 @132132: 1 steps
lem-F4-S3-S3-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3-at132132 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = wlE 605 (lit c4)

-- F4-K2-S3 @132132: 1 steps
lem-F4-K2-S3-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3-at132132 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q33 c4) ∷ []) Eq.refl

-- F4-I-I @132132: 1 steps
lem-F4-I-I-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I-at132132 c4 = derive (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q22 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = wlE 575 (lit c4)

-- F4-S3-I @132132: 1 steps
lem-F4-S3-I-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I-at132132 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = wlE 603 (lit c4)

-- F4-K2-I @132132: 1 steps
lem-F4-K2-I-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I-at132132 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q35 c4) ∷ []) Eq.refl

-- F4-I-S2 @132132: 1 steps
lem-F4-I-S2-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2-at132132 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q19 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wlE 576 (lit c4)

-- F4-S3-S2 @132132: 1 steps
lem-F4-S3-S2-at132132 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2-at132132 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = wlE 604 (lit c4)

-- F4-K2-S2 @132132: 1 steps
lem-F4-K2-S2-at132132 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2-at132132 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q37 c4) ∷ []) Eq.refl

-- F4-I-K3 @02132031: 1 steps
lem-F4-I-K3-at02132031 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3-at02132031 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q28 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = wpE 416 c4

-- F4-S2-K3 @02132031: 1 steps
lem-F4-S2-K3-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3-at02132031 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q38 c4) ∷ []) Eq.refl

-- F4-K3-K3 @02132031: 1 steps
lem-F4-K3-K3-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3-at02132031 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wpE 411 c4

-- F4-S2-S2 @02132031: 1 steps
lem-F4-S2-S2-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2-at02132031 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = wpE 494 c4

-- F4-K3-S2 @02132031: 1 steps
lem-F4-K3-S2-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2-at02132031 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = wpE 410 c4

-- F4-S2-I @02132031: 1 steps
lem-F4-S2-I-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I-at02132031 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q41 c4) ∷ []) Eq.refl

-- F4-K3-I @02132031: 1 steps
lem-F4-K3-I-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I-at02132031 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = wpE 412 c4

-- F4-S2-S3 @02132031: 1 steps
lem-F4-S2-S3-at02132031 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3-at02132031 c4 = derive (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q42 c4) ∷ []) Eq.refl

-- F4-K3-S3 @02132031: 1 steps
lem-F4-K3-S3-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3-at02132031 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q37 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = wlE 554 (lit c4)

-- F4-I-K3 @132132: 1 steps
lem-F4-I-K3-at132132 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3-at132132 c4 = derive (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  (rw⁻ 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = wlE 568 (lit c4)

-- F4-S2-K3 @132132: 1 steps
lem-F4-S2-K3-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3-at132132 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wlE 660 (lit c4)

-- F4-K3-K3 @132132: 1 steps
lem-F4-K3-K3-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-K3-at132132 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q45 c4) ∷ []) Eq.refl

-- F4-S2-S2 @132132: 1 steps
lem-F4-S2-S2-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2-at132132 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = wlE 656 (lit c4)

-- F4-K3-S2 @132132: 1 steps
lem-F4-K3-S2-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S2-at132132 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q46 c4) ∷ []) Eq.refl

-- F4-S2-I @132132: 1 steps
lem-F4-S2-I-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I-at132132 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q23 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = wlE 655 (lit c4)

-- F4-K3-I @132132: 1 steps
lem-F4-K3-I-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-I-at132132 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = wlE 565 (lit c4)

-- F4-S2-S3 @132132: 1 steps
lem-F4-S2-S3-at132132 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3-at132132 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 657 (lit c4)

-- F4-K3-S3 @132132: 1 steps
lem-F4-K3-S3-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-S3-at132132 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = wlE 1440 (lit c4)

-- F4-I-K3 @0213243140: 1 steps
lem-F4-I-K3-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K3-at0213243140 c4 = derive (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = wpE 1293 c4

-- F4-S2-K3 @0213243140: 1 steps
lem-F4-S2-K3-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-K3-at0213243140 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = wlE 1444 (lit c4)

-- F4-K3-K3 @0213243140: 1 steps
lem-F4-K3-K3-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K3-at0213243140 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wpE 1295 c4

-- F4-I-S2 @0213243140: 1 steps
lem-F4-I-S2-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-S2-at0213243140 c4 = derive (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = wpE 1296 c4

-- F4-S2-S2 @0213243140: 1 steps
lem-F4-S2-S2-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-S2-at0213243140 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wpE 1299 c4

-- F4-K3-S2 @0213243140: 1 steps
lem-F4-K3-S2-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-S2-at0213243140 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = wlE 1445 (lit c4)

-- F4-I-I @0213243140: 1 steps
lem-F4-I-I-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-I-at0213243140 c4 = derive (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = wpE 1300 c4

-- F4-S2-I @0213243140: 1 steps
lem-F4-S2-I-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-I-at0213243140 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = wlE 1449 (lit c4)

-- F4-K3-I @0213243140: 1 steps
lem-F4-K3-I-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-I-at0213243140 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = wlE 1450 (lit c4)

-- F4-I-S3 @0213243140: 1 steps
lem-F4-I-S3-at0213243140 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-S3-at0213243140 c4 = derive (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = wpE 1303 c4

-- F4-S2-S3 @0213243140: 1 steps
lem-F4-S2-S3-at0213243140 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S2-S3-at0213243140 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 1454 (lit c4)

-- F4-K3-S3 @0213243140: 1 steps
lem-F4-K3-S3-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-S3-at0213243140 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = wlE 1476 (lit c4)

-- F4-K2-K1 @0440: 1 steps
lem-F4-K2-K1-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K1-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = wlE 1531 (lit c4)

-- F4-K2-K2 @0440: 1 steps
lem-F4-K2-K2-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K2-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = wlE 1532 (lit c4)

-- F4-I-K2 @0440: 1 steps
lem-F4-I-K2-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K2-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q64 c4) ∷ []) Eq.refl

-- F4-I-K1 @0440: 1 steps
lem-F4-I-K1-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K1-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 1556 (lit c4)

-- F4-K2-I @0440: 1 steps
lem-F4-K2-I-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-I-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (rw⁻ 0 (q65 c4) ∷ []) Eq.refl

-- F4-I-I @0440: 1 steps
lem-F4-I-I-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-I-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 1559 (lit c4)

-- F4-K3-I @0440: 1 steps
lem-F4-K3-I-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-I-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = wlE 1560 (lit c4)

-- F4-K3-K2 @0440: 1 steps
lem-F4-K3-K2-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K2-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wlE 1271 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 1048 c4

-- sym-ab @04122041: 18 steps
lem-sym-ab-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-sym-ab-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-0231 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   re 4 1 (Bx4-01 ∷ []) ∷
   re 7 1 (Bx4-01 ∷ []) ∷
   re 2 6 (Bx0-431 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q68 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   re 7 1 (Bx4-01 ∷ []) ∷
   re 10 1 (Bx4-01 ∷ []) ∷
   re 5 6 (Bx0-431 ∷ []) ∷
   re 0 6 (Bx4-0231 ∷ []) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = wpE 594 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 987 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 596 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 986 c4
  q74 : Ws → Eqn
  q74 c4 = eqn (Bx4-01 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-01 ∷ []) (c₂ (CZ) (Swap))
  q75 : Ws → Eqn
  q75 c4 = wlE 3 (lit c4)

-- nat-SWbc @041041: 23 steps
lem-nat-SWbc-at041041 : Ws → ⟪ (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-nat-SWbc-at041041 c4 = derive (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (Bx4-0321 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   re 3 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw 8 (q71 c4) ∷
   rw⁻ 9 (q70 c4) ∷
   re 11 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q73 c4) ∷
   rw⁻ 12 (q74 c4) ∷
   rw 13 (q73 c4) ∷
   rw⁻ 14 (q72 c4) ∷
   rw⁻ 15 (q74 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (Bx0-421 ∷ []) ∷
   re 5 6 (Bx0-421 ∷ []) ∷
   re 0 6 (Bx4-0321 ∷ []) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = wlE 1573 (lit c4)

-- F4-K3-K1 @0440: 1 steps
lem-F4-K3-K1-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K1-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (rw⁻ 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = wlE 1578 (lit c4)

-- F4-K3-K3 @0440: 1 steps
lem-F4-K3-K3-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K3-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (rw⁻ 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = wlE 1579 (lit c4)

-- F4-I-K3 @0440: 1 steps
lem-F4-I-K3-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K3-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = wlE 1580 (lit c4)

-- F4-K2-K3 @0440: 1 steps
lem-F4-K2-K3-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K3-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (rw⁻ 0 (q79 c4) ∷ []) Eq.refl

-- F4-K1-I @0440: 1 steps
lem-F4-K1-I-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-I-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = wlE 1582 (lit c4)

-- F4-K1-K3 @0440: 1 steps
lem-F4-K1-K3-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K3-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wlE 1584 (lit c4)

-- F4-K1-K2 @0440: 1 steps
lem-F4-K1-K2-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K2-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q81 c4) ∷ []) Eq.refl

-- F4-K1-K1 @0440: 1 steps
lem-F4-K1-K1-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K1-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = wpE 766 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 767 c4

-- sym-ab @0413213240: 18 steps
lem-sym-ab-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym-ab-at0413213240 c4 = derive (Bx4-3120 ∷ []) (Bx4-1320 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   re 4 1 (Bx4-10 ∷ []) ∷
   re 7 1 (Bx4-10 ∷ []) ∷
   re 2 6 (Bx1-420 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   re 7 1 (Bx4-10 ∷ []) ∷
   re 10 1 (Bx4-10 ∷ []) ∷
   re 5 6 (Bx1-420 ∷ []) ∷
   re 0 6 (Bx4-1320 ∷ []) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wlE 1592 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 1593 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 1594 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 1595 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Bx4-10 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-10 ∷ []) (c₂ (CZ) (Swap))

-- nat-SWbc @04233240: 23 steps
lem-nat-SWbc-at04233240 : Ws → ⟪ (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-nat-SWbc-at04233240 c4 = derive (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (Bx4-1230 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   re 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 3 (q87 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw 8 (q85 c4) ∷
   rw⁻ 9 (q84 c4) ∷
   re 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 10 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw 13 (q87 c4) ∷
   rw⁻ 14 (q86 c4) ∷
   rw⁻ 15 (q88 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (Bx1-430 ∷ []) ∷
   re 5 6 (Bx1-430 ∷ []) ∷
   re 0 6 (Bx4-1230 ∷ []) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = wlE 1126 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 992 c4

-- sym-ab @022440: 18 steps
lem-sym-ab-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym-ab-at022440 c4 = derive (Bx2-1430 ∷ []) (Bx2-4130 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   re 4 1 (Bx2-40 ∷ []) ∷
   re 7 1 (Bx2-40 ∷ []) ∷
   re 2 6 (Bx4-230 ∷ []) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   re 7 1 (Bx2-40 ∷ []) ∷
   re 10 1 (Bx2-40 ∷ []) ∷
   re 5 6 (Bx4-230 ∷ []) ∷
   re 0 6 (Bx2-4130 ∷ []) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = wpE 677 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 678 c4
  q93 : Ws → Eqn
  q93 c4 = wpE 675 c4
  q94 : Ws → Eqn
  q94 c4 = wpE 676 c4
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw01 ∷ Bx4-32 ∷ []) (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))
  q96 : Ws → Eqn
  q96 c4 = wlE 18 (lit c4)

-- nat-SWbc @0413203142: 23 steps
lem-nat-SWbc-at0413203142 : Ws → ⟪ (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413203142 c4 = derive (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (Bx4-3102 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   re 3 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw 7 (q95 c4) ∷
   rw 8 (q92 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   re 11 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   rw⁻ 10 (q93 c4) ∷
   rw 11 (q94 c4) ∷
   rw 12 (q95 c4) ∷
   rw 13 (q94 c4) ∷
   rw⁻ 14 (q93 c4) ∷
   rw 15 (q95 c4) ∷
   rw 16 (q96 c4) ∷
   re 2 6 (Bx3-402 ∷ []) ∷
   re 5 6 (Bx3-402 ∷ []) ∷
   re 0 6 (Bx4-3102 ∷ []) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = wpE 211 c4
  q98 : Ws → Eqn
  q98 c4 = wpE 212 c4

-- sym-ab @0413213042: 18 steps
lem-sym-ab-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-sym-ab-at0413213042 c4 = derive (Bx4-3102 ∷ []) (Bx4-1302 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q97 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   re 4 1 (Bx4-12 ∷ []) ∷
   re 7 1 (Bx4-12 ∷ []) ∷
   re 2 6 (Bx1-402 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   re 7 1 (Bx4-12 ∷ []) ∷
   re 10 1 (Bx4-12 ∷ []) ∷
   re 5 6 (Bx1-402 ∷ []) ∷
   re 0 6 (Bx4-1302 ∷ []) ∷ []) Eq.refl

-- sym-ab @04233042: 18 steps
lem-sym-ab-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym-ab-at04233042 c4 = derive (Bx4-1302 ∷ []) (Bx4-3102 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q98 c4) ∷
   rw 2 (q97 c4) ∷
   re 4 1 (Bx4-32 ∷ []) ∷
   re 7 1 (Bx4-32 ∷ []) ∷
   re 2 6 (Bx3-402 ∷ []) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q98 c4) ∷
   rw 5 (q97 c4) ∷
   re 7 1 (Bx4-32 ∷ []) ∷
   re 10 1 (Bx4-32 ∷ []) ∷
   re 5 6 (Bx3-402 ∷ []) ∷
   re 0 6 (Bx4-3102 ∷ []) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = wpE 696 c4
  q100 : Ws → Eqn
  q100 c4 = wpE 695 c4

-- nat-SWbc @0413213042: 23 steps
lem-nat-SWbc-at0413213042 : Ws → ⟪ (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413213042 c4 = derive (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (Bx4-3012 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) ∷
   rw⁻ 0 (q93 c4) ∷
   rw 1 (q99 c4) ∷
   re 3 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   rw⁻ 2 (q91 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q100 c4) ∷
   rw⁻ 6 (q91 c4) ∷
   rw 7 (q95 c4) ∷
   rw 8 (q99 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   re 11 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   rw⁻ 10 (q91 c4) ∷
   rw 11 (q100 c4) ∷
   rw 12 (q95 c4) ∷
   rw 13 (q100 c4) ∷
   rw⁻ 14 (q91 c4) ∷
   rw 15 (q95 c4) ∷
   rw 16 (q96 c4) ∷
   re 2 6 (Bx3-412 ∷ []) ∷
   re 5 6 (Bx3-412 ∷ []) ∷
   re 0 6 (Bx4-3012 ∷ []) ∷ []) Eq.refl

-- sym-ab @02142140: 18 steps
lem-sym-ab-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym-ab-at02142140 c4 = derive (Bx2-4130 ∷ []) (Bx2-1430 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q90 c4) ∷
   rw 2 (q89 c4) ∷
   re 4 1 (Bx2-10 ∷ []) ∷
   re 7 1 (Bx2-10 ∷ []) ∷
   re 2 6 (Bx1-230 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q90 c4) ∷
   rw 5 (q89 c4) ∷
   re 7 1 (Bx2-10 ∷ []) ∷
   re 10 1 (Bx2-10 ∷ []) ∷
   re 5 6 (Bx1-230 ∷ []) ∷
   re 0 6 (Bx2-1430 ∷ []) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = wlE 1613 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 1614 (lit c4)

-- nat-SWbc @0440: 23 steps
lem-nat-SWbc-at0440 : Ws → ⟪ (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-nat-SWbc-at0440 c4 = derive (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (Bx4-1320 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   rw⁻ 0 (q86 c4) ∷
   rw 1 (q101 c4) ∷
   re 3 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 9 (q86 c4) ∷
   re 11 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 10 (q84 c4) ∷
   rw 11 (q102 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw 13 (q102 c4) ∷
   rw⁻ 14 (q84 c4) ∷
   rw⁻ 15 (q88 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (Bx1-420 ∷ []) ∷
   re 5 6 (Bx1-420 ∷ []) ∷
   re 0 6 (Bx4-1320 ∷ []) ∷ []) Eq.refl

-- sym-ab @04233240: 18 steps
lem-sym-ab-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym-ab-at04233240 c4 = derive (Bx4-1320 ∷ []) (Bx4-3120 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 2 (q82 c4) ∷
   re 4 1 (Bx4-30 ∷ []) ∷
   re 7 1 (Bx4-30 ∷ []) ∷
   re 2 6 (Bx3-420 ∷ []) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q83 c4) ∷
   rw 5 (q82 c4) ∷
   re 7 1 (Bx4-30 ∷ []) ∷
   re 10 1 (Bx4-30 ∷ []) ∷
   re 5 6 (Bx3-420 ∷ []) ∷
   re 0 6 (Bx4-3120 ∷ []) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = wpE 719 c4
  q104 : Ws → Eqn
  q104 c4 = wlE 1659 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 1660 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 11 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 12 (lit c4)

-- nat-S @0410213243: 31 steps
lem-nat-S-at0410213243 : Ws → ⟪ (Sw23 ∷ Sb2-4-01-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ []) ⟫ʷ
lem-nat-S-at0410213243 c4 = derive (Sw23 ∷ Sb2-4-01-3 ∷ Sw23 ∷ []) (Sb3-4-01-2 ∷ [])
  (re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q103 c4) ∷
   re 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 5 1 (CZ34 ∷ []) ∷
   re 8 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q104 c4) ∷
   re 4 1 (Bx3-42 ∷ []) ∷
   re 7 1 (Bx3-42 ∷ []) ∷
   re 2 6 (Bx4-312 ∷ []) ∷
   rw 3 (q103 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 6 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 8 1 (CZ34 ∷ []) ∷
   re 11 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q104 c4) ∷
   re 7 1 (Bx3-42 ∷ []) ∷
   re 10 1 (Bx3-42 ∷ []) ∷
   re 5 6 (Bx4-312 ∷ []) ∷
   rw 6 (q105 c4) ∷
   rw⁻ 7 (q106 c4) ∷
   rw 8 (q105 c4) ∷
   rw⁻ 9 (q107 c4) ∷
   rw 10 (q75 c4) ∷
   re 0 6 (Bx3-4012 ∷ []) ∷
   re 2 1 (Sb3-4-2-1 ∷ []) ∷
   re 4 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 0 5 (Sb3-4-01-2 ∷ []) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = wpE 732 c4
  q109 : Ws → Eqn
  q109 c4 = wpE 733 c4

-- sym-ab @04122140: 18 steps
lem-sym-ab-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-sym-ab-at04122140 c4 = derive (Bx4-2130 ∷ []) (Bx4-1230 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   re 4 1 (Bx4-10 ∷ []) ∷
   re 7 1 (Bx4-10 ∷ []) ∷
   re 2 6 (Bx1-430 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 5 (q109 c4) ∷
   re 7 1 (Bx4-10 ∷ []) ∷
   re 10 1 (Bx4-10 ∷ []) ∷
   re 5 6 (Bx1-430 ∷ []) ∷
   re 0 6 (Bx4-1230 ∷ []) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = wlE 1596 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wpE 1437 c4

-- sym-ab @0413203142: 18 steps
lem-sym-ab-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-sym-ab-at0413203142 c4 = derive (Bx4-3012 ∷ []) (Bx4-0312 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q110 c4) ∷
   rw⁻ 2 (q111 c4) ∷
   re 4 1 (Bx4-02 ∷ []) ∷
   re 7 1 (Bx4-02 ∷ []) ∷
   re 2 6 (Bx0-412 ∷ []) ∷
   re 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q110 c4) ∷
   rw⁻ 5 (q111 c4) ∷
   re 7 1 (Bx4-02 ∷ []) ∷
   re 10 1 (Bx4-02 ∷ []) ∷
   re 5 6 (Bx0-412 ∷ []) ∷
   re 0 6 (Bx4-0312 ∷ []) ∷ []) Eq.refl

-- sym-ab @0410233142: 18 steps
lem-sym-ab-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym-ab-at0410233142 c4 = derive (Bx4-0312 ∷ []) (Bx4-3012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q111 c4) ∷
   rw 2 (q110 c4) ∷
   re 4 1 (Bx4-32 ∷ []) ∷
   re 7 1 (Bx4-32 ∷ []) ∷
   re 2 6 (Bx3-412 ∷ []) ∷
   re 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q111 c4) ∷
   rw 5 (q110 c4) ∷
   re 7 1 (Bx4-32 ∷ []) ∷
   re 10 1 (Bx4-32 ∷ []) ∷
   re 5 6 (Bx3-412 ∷ []) ∷
   re 0 6 (Bx4-3012 ∷ []) ∷ []) Eq.refl

-- sym-ab @0440: 18 steps
lem-sym-ab-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-sym-ab-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-2130 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 2 (q108 c4) ∷
   re 4 1 (Bx4-20 ∷ []) ∷
   re 7 1 (Bx4-20 ∷ []) ∷
   re 2 6 (Bx2-430 ∷ []) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q109 c4) ∷
   rw 5 (q108 c4) ∷
   re 7 1 (Bx4-20 ∷ []) ∷
   re 10 1 (Bx4-20 ∷ []) ∷
   re 5 6 (Bx2-430 ∷ []) ∷
   re 0 6 (Bx4-2130 ∷ []) ∷ []) Eq.refl

-- F4-S0-K1 @0440: 1 steps
lem-F4-S0-K1-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K1-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = wpE 516 c4
  q113 : Ws → Eqn
  q113 c4 = wlE 756 (lit c4)

-- sym-ab @0410233241: 18 steps
lem-sym-ab-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ []) ⟫ʷ
lem-sym-ab-at0410233241 c4 = derive (Bx4-0321 ∷ []) (Bx4-3021 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q112 c4) ∷
   rw 2 (q113 c4) ∷
   re 4 1 (Bx4-31 ∷ []) ∷
   re 7 1 (Bx4-31 ∷ []) ∷
   re 2 6 (Bx3-421 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q112 c4) ∷
   rw 5 (q113 c4) ∷
   re 7 1 (Bx4-31 ∷ []) ∷
   re 10 1 (Bx4-31 ∷ []) ∷
   re 5 6 (Bx3-421 ∷ []) ∷
   re 0 6 (Bx4-3021 ∷ []) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = wpE 1488 c4

-- F4-S0-K2 @0440: 1 steps
lem-F4-S0-K2-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K2-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = wpE 1436 c4
  q116 : Ws → Eqn
  q116 c4 = wpE 1503 c4

-- sym-ab @0412233140: 18 steps
lem-sym-ab-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-sym-ab-at0412233140 c4 = derive (Bx4-2310 ∷ []) (Bx4-3210 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   re 4 1 (Bx4-30 ∷ []) ∷
   re 7 1 (Bx4-30 ∷ []) ∷
   re 2 6 (Bx3-410 ∷ []) ∷
   re 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q115 c4) ∷
   rw 5 (q116 c4) ∷
   re 7 1 (Bx4-30 ∷ []) ∷
   re 10 1 (Bx4-30 ∷ []) ∷
   re 5 6 (Bx3-410 ∷ []) ∷
   re 0 6 (Bx4-3210 ∷ []) ∷ []) Eq.refl

-- sym-ab @04133140: 18 steps
lem-sym-ab-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-sym-ab-at04133140 c4 = derive (Bx4-3210 ∷ []) (Bx4-2310 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q116 c4) ∷
   rw 2 (q115 c4) ∷
   re 4 1 (Bx4-20 ∷ []) ∷
   re 7 1 (Bx4-20 ∷ []) ∷
   re 2 6 (Bx2-410 ∷ []) ∷
   re 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 5 (q115 c4) ∷
   re 7 1 (Bx4-20 ∷ []) ∷
   re 10 1 (Bx4-20 ∷ []) ∷
   re 5 6 (Bx2-410 ∷ []) ∷
   re 0 6 (Bx4-2310 ∷ []) ∷ []) Eq.refl

-- F4-S0-I @0440: 1 steps
lem-F4-S0-I-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-I-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = wpE 1518 c4

-- F4-S0-K3 @0440: 1 steps
lem-F4-S0-K3-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K3-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (rw⁻ 0 (q117 c4) ∷ []) Eq.refl
