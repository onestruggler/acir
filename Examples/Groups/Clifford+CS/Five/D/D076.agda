{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D076 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1409 ; wl1411 ; wl1417 ; wl1419)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-K1 ; lem-F4-I-K2 ; lem-F4-I-K3 ; lem-F4-K2-I ; lem-F4-K2-K1 ; lem-F4-K2-K2 ; lem-F4-K2-K3 ; lem-F4-K3-I ; lem-F4-K3-K1 ; lem-F4-K3-K2 ; lem-F4-K3-K3)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS1-I ; lem-F4-CS1-K1 ; lem-F4-CS2-I ; lem-F4-I-CS1 ; lem-F4-I-CS2 ; lem-F4-K2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F4-CS2-K2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F4-CS1-CS1 ; lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F4-CS2-K1 ; lem-F4-CS2-K3 ; lem-F4-K3-CS1 ; lem-F4-K3-CS2 ; lem-F5-12 ; lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-F4-CS1-K2 ; lem-F4-K2-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F4-CS1-CS2 ; lem-F4-CS2-CS1)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K1 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-12 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-K2 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-CS2 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-K1 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-CS1 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS1 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl1411 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS1 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K1 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS1 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-I c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS1-I c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl1419 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-I c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K2 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS1 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS2 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K1 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K3 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K3 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K3 c4)

-- ckt-TST part0: 216 steps
lem-ckt-TST-part0 : Ws → ⟪ (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part0 c4 = derive (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 12 (q7 c4) ∷
   rw⁻ 11 (q8 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 9 (q10 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 14 (q8 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw⁻ 12 (q10 c4) ∷
   rw 20 (q4 c4) ∷
   rw⁻ 19 (q12 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw⁻ 17 (q13 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw⁻ 23 (q15 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 22 (q22 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 35 (q22 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 32 (q20 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw 40 (q4 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 36 (q23 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 34 (q12 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 41 (q9 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q11 c4) ∷
   rw⁻ 36 (q11 c4) ∷
   rw⁻ 35 (q8 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw⁻ 48 (q7 c4) ∷
   rw⁻ 47 (q11 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw⁻ 42 (q24 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q11 c4) ∷
   rw⁻ 39 (q11 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q9 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw 52 (q4 c4) ∷
   rw⁻ 51 (q12 c4) ∷
   rw⁻ 50 (q12 c4) ∷
   rw⁻ 49 (q13 c4) ∷
   rw⁻ 48 (q5 c4) ∷
   rw⁻ 47 (q5 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 45 (q23 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw⁻ 42 (q12 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw⁻ 56 (q14 c4) ∷
   rw⁻ 55 (q15 c4) ∷
   rw⁻ 54 (q16 c4) ∷
   rw⁻ 53 (q16 c4) ∷
   rw⁻ 52 (q15 c4) ∷
   rw⁻ 51 (q17 c4) ∷
   rw⁻ 50 (q17 c4) ∷
   rw⁻ 49 (q17 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 47 (q15 c4) ∷
   rw⁻ 46 (q16 c4) ∷
   rw⁻ 45 (q16 c4) ∷
   rw⁻ 44 (q15 c4) ∷
   rw⁻ 43 (q17 c4) ∷
   rw⁻ 42 (q18 c4) ∷
   rw 60 (q26 c4) ∷
   rw⁻ 59 (q27 c4) ∷
   rw⁻ 58 (q28 c4) ∷
   rw⁻ 57 (q29 c4) ∷
   rw⁻ 56 (q29 c4) ∷
   rw⁻ 55 (q28 c4) ∷
   rw⁻ 54 (q30 c4) ∷
   rw⁻ 53 (q30 c4) ∷
   rw⁻ 52 (q30 c4) ∷
   rw⁻ 51 (q27 c4) ∷
   rw⁻ 50 (q28 c4) ∷
   rw⁻ 49 (q29 c4) ∷
   rw⁻ 48 (q29 c4) ∷
   rw⁻ 47 (q28 c4) ∷
   rw⁻ 46 (q30 c4) ∷
   rw⁻ 45 (q31 c4) ∷
   rw⁻ 64 (q2 c4) ∷
   rw⁻ 63 (q32 c4) ∷
   rw⁻ 62 (q19 c4) ∷
   rw⁻ 61 (q20 c4) ∷
   rw⁻ 60 (q21 c4) ∷
   rw⁻ 59 (q21 c4) ∷
   rw⁻ 58 (q20 c4) ∷
   rw⁻ 57 (q22 c4) ∷
   rw⁻ 56 (q22 c4) ∷
   rw⁻ 55 (q22 c4) ∷
   rw⁻ 54 (q19 c4) ∷
   rw⁻ 53 (q20 c4) ∷
   rw⁻ 52 (q21 c4) ∷
   rw⁻ 51 (q21 c4) ∷
   rw⁻ 50 (q20 c4) ∷
   rw⁻ 49 (q22 c4) ∷
   rw⁻ 48 (q3 c4) ∷
   rw⁻ 68 (q2 c4) ∷
   rw⁻ 67 (q22 c4) ∷
   rw⁻ 66 (q32 c4) ∷
   rw⁻ 65 (q19 c4) ∷
   rw⁻ 64 (q20 c4) ∷
   rw⁻ 63 (q21 c4) ∷
   rw⁻ 62 (q21 c4) ∷
   rw⁻ 61 (q20 c4) ∷
   rw⁻ 60 (q22 c4) ∷
   rw⁻ 59 (q22 c4) ∷
   rw⁻ 58 (q22 c4) ∷
   rw⁻ 57 (q19 c4) ∷
   rw⁻ 56 (q20 c4) ∷
   rw⁻ 55 (q21 c4) ∷
   rw⁻ 54 (q21 c4) ∷
   rw⁻ 53 (q20 c4) ∷
   rw⁻ 52 (q22 c4) ∷
   rw⁻ 51 (q3 c4) ∷
   rw 72 (q26 c4) ∷
   rw⁻ 71 (q30 c4) ∷
   rw⁻ 70 (q30 c4) ∷
   rw⁻ 69 (q33 c4) ∷
   rw⁻ 68 (q27 c4) ∷
   rw⁻ 67 (q28 c4) ∷
   rw⁻ 66 (q29 c4) ∷
   rw⁻ 65 (q29 c4) ∷
   rw⁻ 64 (q28 c4) ∷
   rw⁻ 63 (q30 c4) ∷
   rw⁻ 62 (q30 c4) ∷
   rw⁻ 61 (q30 c4) ∷
   rw⁻ 60 (q27 c4) ∷
   rw⁻ 59 (q28 c4) ∷
   rw⁻ 58 (q29 c4) ∷
   rw⁻ 57 (q29 c4) ∷
   rw⁻ 56 (q28 c4) ∷
   rw⁻ 55 (q30 c4) ∷
   rw⁻ 54 (q31 c4) ∷
   rw⁻ 76 (q14 c4) ∷
   rw⁻ 75 (q34 c4) ∷
   rw⁻ 74 (q17 c4) ∷
   rw⁻ 73 (q17 c4) ∷
   rw⁻ 72 (q34 c4) ∷
   rw⁻ 71 (q25 c4) ∷
   rw⁻ 70 (q15 c4) ∷
   rw⁻ 69 (q16 c4) ∷
   rw⁻ 68 (q16 c4) ∷
   rw⁻ 67 (q15 c4) ∷
   rw⁻ 66 (q17 c4) ∷
   rw⁻ 65 (q17 c4) ∷
   rw⁻ 64 (q17 c4) ∷
   rw⁻ 63 (q25 c4) ∷
   rw⁻ 62 (q15 c4) ∷
   rw⁻ 61 (q16 c4) ∷
   rw⁻ 60 (q16 c4) ∷
   rw⁻ 59 (q15 c4) ∷
   rw⁻ 58 (q17 c4) ∷
   rw⁻ 57 (q18 c4) ∷
   rw 80 (q4 c4) ∷
   rw⁻ 79 (q23 c4) ∷
   rw⁻ 78 (q35 c4) ∷
   rw⁻ 77 (q5 c4) ∷
   rw⁻ 76 (q5 c4) ∷
   rw⁻ 75 (q35 c4) ∷ []) Eq.refl
