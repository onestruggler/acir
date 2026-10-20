{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D073 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K3-at02132031 ; lem-F4-I-K3-at132132 ; lem-F4-I-S2-at02132031 ; lem-F4-I-S2-at132132 ; lem-F4-K3-K3-at02132031 ; lem-F4-K3-K3-at132132 ; lem-F4-S2-I-at02132031 ; lem-F4-S2-I-at132132 ; lem-F4-S2-K3-at02132031 ; lem-F4-S2-K3-at132132 ; lem-F4-S2-S2-at02132031 ; lem-F4-S2-S2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-CS2-at132132 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-I-at132132 ; lem-F4-CS2-S2-at02132031 ; lem-F4-CS2-S2-at132132 ; lem-F4-I-CS2-at02132031 ; lem-F4-I-CS2-at132132 ; lem-F4-S2-CS2-at02132031 ; lem-F4-S2-CS2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at02132031 ; lem-F5-23-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F4-CS2-K3-at02132031 ; lem-F4-CS2-K3-at132132 ; lem-F4-K3-CS2-at02132031 ; lem-F4-K3-CS2-at132132)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-23-at02132031 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl 1417 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-CS2-at02132031 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at02132031 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-K3-at02132031 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp 1267 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-CS2-at02132031 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-K3-at02132031 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S2-at02132031 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl 1411 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at02132031 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-I-at02132031 c4)

-- deb-P-lo-split-a @02132031: 136 steps
lem-deb-P-lo-split-a-at02132031 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-lo-split-a-at02132031 c4 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw 28 (q3 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 36 (q3 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 34 (q6 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw 44 (q7 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 35 (q8 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 33 (q8 c4) ∷
   rw 48 (q7 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw 52 (q7 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q9 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 56 (q11 c4) ∷
   rw⁻ 55 (q12 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw⁻ 52 (q13 c4) ∷
   rw⁻ 51 (q14 c4) ∷
   rw⁻ 50 (q13 c4) ∷
   rw⁻ 49 (q14 c4) ∷
   rw⁻ 48 (q13 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 46 (q13 c4) ∷
   rw⁻ 45 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 43 (q13 c4) ∷
   rw⁻ 42 (q13 c4) ∷
   rw 60 (q7 c4) ∷
   rw⁻ 59 (q15 c4) ∷
   rw⁻ 58 (q10 c4) ∷
   rw⁻ 57 (q10 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 55 (q8 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   rw⁻ 53 (q8 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw⁻ 51 (q8 c4) ∷
   rw⁻ 50 (q8 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q8 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q8 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)

-- deb-P-lo-split-b @02132031: 66 steps
lem-deb-P-lo-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-deb-P-lo-split-b-at02132031 c4 = derive (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw⁻ 34 (q17 c4) ∷
   rw⁻ 33 (q17 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   rw⁻ 38 (q16 c4) ∷
   rw⁻ 37 (q17 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q2 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-23-at132132 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at132132 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl 1409 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K3-CS2-at132132 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at132132 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K3-K3-at132132 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl 1412 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-CS2-at132132 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-K3-at132132 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-S2-at132132 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at132132 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at132132 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-I-at132132 c4)

-- deb-P-lo-split-a @132132: 136 steps
lem-deb-P-lo-split-a-at132132 : Ws → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-lo-split-a-at132132 c4 = derive (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw 28 (q20 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 32 (q18 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 29 (q19 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 36 (q20 c4) ∷
   rw⁻ 35 (q21 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 33 (q21 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 40 (q18 c4) ∷
   rw⁻ 39 (q22 c4) ∷
   rw⁻ 38 (q19 c4) ∷
   rw⁻ 37 (q22 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 35 (q19 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw 44 (q24 c4) ∷
   rw⁻ 43 (q25 c4) ∷
   rw⁻ 42 (q26 c4) ∷
   rw⁻ 41 (q25 c4) ∷
   rw⁻ 40 (q26 c4) ∷
   rw⁻ 39 (q25 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 37 (q25 c4) ∷
   rw⁻ 36 (q25 c4) ∷
   rw⁻ 35 (q25 c4) ∷
   rw⁻ 34 (q25 c4) ∷
   rw⁻ 33 (q25 c4) ∷
   rw 48 (q24 c4) ∷
   rw⁻ 47 (q27 c4) ∷
   rw⁻ 46 (q25 c4) ∷
   rw⁻ 45 (q26 c4) ∷
   rw⁻ 44 (q25 c4) ∷
   rw⁻ 43 (q26 c4) ∷
   rw⁻ 42 (q25 c4) ∷
   rw⁻ 41 (q25 c4) ∷
   rw⁻ 40 (q25 c4) ∷
   rw⁻ 39 (q25 c4) ∷
   rw⁻ 38 (q25 c4) ∷
   rw⁻ 37 (q25 c4) ∷
   rw⁻ 36 (q25 c4) ∷
   rw 52 (q24 c4) ∷
   rw⁻ 51 (q27 c4) ∷
   rw⁻ 50 (q27 c4) ∷
   rw⁻ 49 (q25 c4) ∷
   rw⁻ 48 (q26 c4) ∷
   rw⁻ 47 (q25 c4) ∷
   rw⁻ 46 (q26 c4) ∷
   rw⁻ 45 (q25 c4) ∷
   rw⁻ 44 (q25 c4) ∷
   rw⁻ 43 (q25 c4) ∷
   rw⁻ 42 (q25 c4) ∷
   rw⁻ 41 (q25 c4) ∷
   rw⁻ 40 (q25 c4) ∷
   rw⁻ 39 (q25 c4) ∷
   rw⁻ 56 (q11 c4) ∷
   rw⁻ 55 (q28 c4) ∷
   rw⁻ 54 (q28 c4) ∷
   rw⁻ 53 (q28 c4) ∷
   rw⁻ 52 (q29 c4) ∷
   rw⁻ 51 (q30 c4) ∷
   rw⁻ 50 (q29 c4) ∷
   rw⁻ 49 (q30 c4) ∷
   rw⁻ 48 (q29 c4) ∷
   rw⁻ 47 (q29 c4) ∷
   rw⁻ 46 (q29 c4) ∷
   rw⁻ 45 (q29 c4) ∷
   rw⁻ 44 (q29 c4) ∷
   rw⁻ 43 (q29 c4) ∷
   rw⁻ 42 (q29 c4) ∷
   rw 60 (q24 c4) ∷
   rw⁻ 59 (q31 c4) ∷
   rw⁻ 58 (q27 c4) ∷
   rw⁻ 57 (q27 c4) ∷
   rw⁻ 56 (q27 c4) ∷
   rw⁻ 55 (q25 c4) ∷
   rw⁻ 54 (q26 c4) ∷
   rw⁻ 53 (q25 c4) ∷
   rw⁻ 52 (q26 c4) ∷
   rw⁻ 51 (q25 c4) ∷
   rw⁻ 50 (q25 c4) ∷
   rw⁻ 49 (q25 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 47 (q25 c4) ∷
   rw⁻ 46 (q25 c4) ∷
   rw⁻ 45 (q25 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at132132 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4)

-- deb-P-lo-split-b @132132: 66 steps
lem-deb-P-lo-split-b-at132132 : Ws → ⟪ (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-deb-P-lo-split-b-at132132 c4 = derive (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 18 (q26 c4) ∷
   rw⁻ 17 (q25 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw 24 (q24 c4) ∷
   rw⁻ 23 (q27 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 21 (q26 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw⁻ 19 (q26 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw 28 (q24 c4) ∷
   rw⁻ 27 (q27 c4) ∷
   rw⁻ 26 (q27 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw⁻ 22 (q26 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw⁻ 30 (q28 c4) ∷
   rw⁻ 29 (q28 c4) ∷
   rw⁻ 28 (q29 c4) ∷
   rw⁻ 27 (q30 c4) ∷
   rw⁻ 26 (q29 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw⁻ 24 (q29 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw⁻ 35 (q32 c4) ∷
   rw⁻ 34 (q33 c4) ∷
   rw⁻ 33 (q33 c4) ∷
   rw⁻ 32 (q33 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw⁻ 29 (q19 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 40 (q18 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw⁻ 38 (q32 c4) ∷
   rw⁻ 37 (q33 c4) ∷
   rw⁻ 36 (q33 c4) ∷
   rw⁻ 35 (q33 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q19 c4) ∷ []) Eq.refl

-- deb-Q-lo-split-a @02132031: 55 steps
lem-deb-Q-lo-split-a-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-a-at02132031 c4 = derive (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 35 (q15 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw⁻ 32 (q10 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw⁻ 30 (q9 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw⁻ 28 (q9 c4) ∷
   rw⁻ 27 (q8 c4) ∷ []) Eq.refl

-- deb-Q-lo-split-b @02132031: 45 steps
lem-deb-Q-lo-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-b-at02132031 c4 = derive (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷ []) Eq.refl
