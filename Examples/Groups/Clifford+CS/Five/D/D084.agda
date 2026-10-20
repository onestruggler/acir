{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D084 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1409 ; wl1411 ; wl1419)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-K1 ; lem-F4-I-K2 ; lem-F4-K2-I ; lem-F4-K2-K1 ; lem-F4-K2-K2 ; lem-F4-K3-I ; lem-F4-K3-K1 ; lem-F4-K3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS1-I ; lem-F4-CS1-K1 ; lem-F4-CS2-I ; lem-F4-I-CS1 ; lem-F4-I-CS2 ; lem-F4-K2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F4-CS2-K2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F4-CS1-CS1 ; lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F4-CS2-K1 ; lem-F4-CS2-K3 ; lem-F4-K3-CS1 ; lem-F4-K3-CS2 ; lem-F5-12 ; lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-F4-CS1-K2 ; lem-F4-K2-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F4-CS1-CS2 ; lem-F4-CS2-CS1)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS1 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K1 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-I c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS1 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K1 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-12 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-K2 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-CS2 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-I c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-CS1 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-K1 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl1411 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS1 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K1 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-I c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K2 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS1 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS2 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K1 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K3 c4)

-- ckt-TST part8: 106 steps
lem-ckt-TST-part8 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part8 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 220 (q1 c4) ∷
   rw⁻ 219 (q2 c4) ∷
   rw⁻ 218 (q3 c4) ∷
   rw⁻ 217 (q4 c4) ∷
   rw⁻ 229 (q5 c4) ∷
   rw⁻ 228 (q3 c4) ∷
   rw⁻ 227 (q3 c4) ∷
   rw⁻ 226 (q6 c4) ∷
   rw⁻ 225 (q2 c4) ∷
   rw⁻ 224 (q1 c4) ∷
   rw⁻ 223 (q1 c4) ∷
   rw⁻ 222 (q2 c4) ∷
   rw⁻ 221 (q3 c4) ∷
   rw⁻ 220 (q4 c4) ∷
   rw 233 (q7 c4) ∷
   rw⁻ 232 (q8 c4) ∷
   rw⁻ 231 (q8 c4) ∷
   rw⁻ 230 (q8 c4) ∷
   rw⁻ 229 (q9 c4) ∷
   rw⁻ 228 (q10 c4) ∷
   rw⁻ 227 (q11 c4) ∷
   rw⁻ 226 (q11 c4) ∷
   rw⁻ 225 (q10 c4) ∷
   rw⁻ 224 (q8 c4) ∷
   rw⁻ 223 (q12 c4) ∷
   rw⁻ 237 (q13 c4) ∷
   rw⁻ 236 (q14 c4) ∷
   rw⁻ 235 (q15 c4) ∷
   rw⁻ 234 (q15 c4) ∷
   rw⁻ 233 (q15 c4) ∷
   rw⁻ 232 (q16 c4) ∷
   rw⁻ 231 (q14 c4) ∷
   rw⁻ 230 (q17 c4) ∷
   rw⁻ 229 (q17 c4) ∷
   rw⁻ 228 (q14 c4) ∷
   rw⁻ 227 (q15 c4) ∷
   rw⁻ 226 (q18 c4) ∷
   rw⁻ 241 (q13 c4) ∷
   rw⁻ 240 (q17 c4) ∷
   rw⁻ 239 (q14 c4) ∷
   rw⁻ 238 (q15 c4) ∷
   rw⁻ 237 (q15 c4) ∷
   rw⁻ 236 (q15 c4) ∷
   rw⁻ 235 (q16 c4) ∷
   rw⁻ 234 (q14 c4) ∷
   rw⁻ 233 (q17 c4) ∷
   rw⁻ 232 (q17 c4) ∷
   rw⁻ 231 (q14 c4) ∷
   rw⁻ 230 (q15 c4) ∷
   rw⁻ 229 (q18 c4) ∷
   rw 245 (q7 c4) ∷
   rw⁻ 244 (q11 c4) ∷
   rw⁻ 243 (q11 c4) ∷
   rw⁻ 242 (q10 c4) ∷
   rw⁻ 241 (q8 c4) ∷
   rw⁻ 240 (q8 c4) ∷
   rw⁻ 239 (q8 c4) ∷
   rw⁻ 238 (q9 c4) ∷
   rw⁻ 237 (q10 c4) ∷
   rw⁻ 236 (q11 c4) ∷
   rw⁻ 235 (q11 c4) ∷
   rw⁻ 234 (q10 c4) ∷
   rw⁻ 233 (q8 c4) ∷
   rw⁻ 232 (q12 c4) ∷
   rw⁻ 249 (q19 c4) ∷
   rw⁻ 248 (q20 c4) ∷
   rw⁻ 247 (q21 c4) ∷
   rw⁻ 246 (q21 c4) ∷
   rw⁻ 245 (q20 c4) ∷
   rw⁻ 244 (q22 c4) ∷
   rw⁻ 243 (q22 c4) ∷
   rw⁻ 242 (q22 c4) ∷
   rw⁻ 241 (q23 c4) ∷
   rw⁻ 240 (q20 c4) ∷
   rw⁻ 239 (q21 c4) ∷
   rw⁻ 238 (q21 c4) ∷
   rw⁻ 237 (q20 c4) ∷
   rw⁻ 236 (q22 c4) ∷
   rw⁻ 235 (q24 c4) ∷
   rw 253 (q25 c4) ∷
   rw⁻ 252 (q26 c4) ∷
   rw⁻ 251 (q27 c4) ∷
   rw⁻ 250 (q28 c4) ∷
   rw⁻ 249 (q28 c4) ∷
   rw⁻ 248 (q27 c4) ∷
   rw⁻ 247 (q29 c4) ∷
   rw⁻ 246 (q29 c4) ∷
   rw⁻ 245 (q29 c4) ∷
   rw⁻ 244 (q26 c4) ∷
   rw⁻ 243 (q27 c4) ∷
   rw⁻ 242 (q28 c4) ∷
   rw⁻ 241 (q28 c4) ∷
   rw⁻ 240 (q27 c4) ∷
   rw⁻ 239 (q29 c4) ∷
   rw⁻ 238 (q30 c4) ∷
   rw⁻ 257 (q5 c4) ∷
   rw⁻ 256 (q31 c4) ∷
   rw⁻ 255 (q6 c4) ∷
   rw⁻ 254 (q2 c4) ∷
   rw⁻ 253 (q1 c4) ∷
   rw⁻ 252 (q1 c4) ∷
   rw⁻ 251 (q2 c4) ∷
   rw⁻ 250 (q3 c4) ∷
   rw⁻ 249 (q3 c4) ∷
   rw⁻ 248 (q3 c4) ∷
   rw⁻ 247 (q6 c4) ∷ []) Eq.refl
