{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D212 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-I-at0440 ; lem-F4-I-K1-at0440 ; lem-F4-I-K2-at0440 ; lem-F4-I-K3-at0440 ; lem-F4-K1-I-at0440 ; lem-F4-K1-K1-at0440 ; lem-F4-K1-K2-at0440 ; lem-F4-K1-K3-at0440 ; lem-F4-S0-I-at0440 ; lem-F4-S0-K1-at0440 ; lem-F4-S0-K2-at0440 ; lem-F4-S0-K3-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-F4-S0-CS1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-F4-I-CS1-at0440 ; lem-F4-K1-CS1-at0440 ; lem-F4-S0-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F4-I-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D024 using (lem-F4-CS0-CS0-at0440 ; lem-F4-CS0-I-at0440 ; lem-F4-I-CS0-at0440 ; lem-F4-S0-CS0-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-F4-K1-CS0-at0440 ; lem-F4-K1-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-F4-CS0-K1-at0440 ; lem-F4-CS0-K3-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D066 using (lem-F4-CS0-K2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D146 using (lem-F4-CS0-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D203 using (lem-F4-CS0-CS1-at0440)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-CS2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-K3-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-K3-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-K3-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-I-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-I-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-I-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-I-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-CS1-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-CS1-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-CS1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-K2-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-K2-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-K2-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K1-at0440 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-K1-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-K1-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-K1-at0440 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS0-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S0-CS0-at0440 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS0-CS0-at0440 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K1-CS0-at0440 c4)

-- F1-ck-tct@0 part1: 241 steps
lem-F1-ck-tctat0-part1 : Ws → ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
lem-F1-ck-tctat0-part1 c4 = derive (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ [])
  (rw 32 (q1 c4) ∷
   rw 29 (q2 c4) ∷
   rw 26 (q1 c4) ∷
   rw 51 (q3 c4) ∷
   rw 48 (q4 c4) ∷
   rw 45 (q4 c4) ∷
   rw 42 (q4 c4) ∷
   rw 39 (q1 c4) ∷
   rw 36 (q2 c4) ∷
   rw 33 (q1 c4) ∷
   rw 30 (q2 c4) ∷
   rw 27 (q1 c4) ∷
   rw 52 (q5 c4) ∷
   rw 49 (q6 c4) ∷
   rw 46 (q6 c4) ∷
   rw 43 (q6 c4) ∷
   rw 40 (q7 c4) ∷
   rw 37 (q8 c4) ∷
   rw 34 (q7 c4) ∷
   rw 31 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw 53 (q9 c4) ∷
   rw 50 (q10 c4) ∷
   rw 47 (q10 c4) ∷
   rw 44 (q10 c4) ∷
   rw 41 (q11 c4) ∷
   rw 38 (q12 c4) ∷
   rw 35 (q11 c4) ∷
   rw 32 (q12 c4) ∷
   rw 29 (q11 c4) ∷
   rw 54 (q13 c4) ∷
   rw 51 (q14 c4) ∷
   rw 48 (q14 c4) ∷
   rw 45 (q14 c4) ∷
   rw 42 (q15 c4) ∷
   rw 39 (q16 c4) ∷
   rw 36 (q15 c4) ∷
   rw 33 (q16 c4) ∷
   rw 30 (q15 c4) ∷
   rw 55 (q5 c4) ∷
   rw 52 (q6 c4) ∷
   rw 49 (q6 c4) ∷
   rw 46 (q6 c4) ∷
   rw 43 (q7 c4) ∷
   rw 40 (q8 c4) ∷
   rw 37 (q7 c4) ∷
   rw 34 (q8 c4) ∷
   rw 31 (q7 c4) ∷
   rw 56 (q3 c4) ∷
   rw 53 (q4 c4) ∷
   rw 50 (q4 c4) ∷
   rw 47 (q4 c4) ∷
   rw 44 (q1 c4) ∷
   rw 41 (q2 c4) ∷
   rw 38 (q1 c4) ∷
   rw 35 (q2 c4) ∷
   rw 32 (q1 c4) ∷
   rw 57 (q3 c4) ∷
   rw 54 (q4 c4) ∷
   rw 51 (q4 c4) ∷
   rw 48 (q4 c4) ∷
   rw 45 (q1 c4) ∷
   rw 42 (q2 c4) ∷
   rw 39 (q1 c4) ∷
   rw 36 (q2 c4) ∷
   rw 33 (q1 c4) ∷
   rw 58 (q5 c4) ∷
   rw 55 (q6 c4) ∷
   rw 52 (q6 c4) ∷
   rw 49 (q6 c4) ∷
   rw 46 (q7 c4) ∷
   rw 43 (q8 c4) ∷
   rw 40 (q7 c4) ∷
   rw 37 (q8 c4) ∷
   rw 34 (q7 c4) ∷
   rw 59 (q9 c4) ∷
   rw 56 (q10 c4) ∷
   rw 53 (q10 c4) ∷
   rw 50 (q10 c4) ∷
   rw 47 (q11 c4) ∷
   rw 44 (q12 c4) ∷
   rw 41 (q11 c4) ∷
   rw 38 (q12 c4) ∷
   rw 35 (q11 c4) ∷
   rw 60 (q17 c4) ∷
   rw 57 (q18 c4) ∷
   rw 54 (q18 c4) ∷
   rw 51 (q18 c4) ∷
   rw 48 (q19 c4) ∷
   rw 45 (q20 c4) ∷
   rw 42 (q19 c4) ∷
   rw 39 (q20 c4) ∷
   rw 36 (q19 c4) ∷
   rw 61 (q3 c4) ∷
   rw 58 (q4 c4) ∷
   rw 55 (q4 c4) ∷
   rw 52 (q4 c4) ∷
   rw 49 (q1 c4) ∷
   rw 46 (q2 c4) ∷
   rw 43 (q1 c4) ∷
   rw 40 (q2 c4) ∷
   rw 37 (q1 c4) ∷
   rw 62 (q3 c4) ∷
   rw 59 (q4 c4) ∷
   rw 56 (q4 c4) ∷
   rw 53 (q4 c4) ∷
   rw 50 (q1 c4) ∷
   rw 47 (q2 c4) ∷
   rw 44 (q1 c4) ∷
   rw 41 (q2 c4) ∷
   rw 38 (q1 c4) ∷
   rw 63 (q17 c4) ∷
   rw 60 (q18 c4) ∷
   rw 57 (q18 c4) ∷
   rw 54 (q18 c4) ∷
   rw 51 (q19 c4) ∷
   rw 48 (q20 c4) ∷
   rw 45 (q19 c4) ∷
   rw 42 (q20 c4) ∷
   rw 39 (q19 c4) ∷
   rw 64 (q9 c4) ∷
   rw 61 (q10 c4) ∷
   rw 58 (q10 c4) ∷
   rw 55 (q10 c4) ∷
   rw 52 (q11 c4) ∷
   rw 49 (q12 c4) ∷
   rw 46 (q11 c4) ∷
   rw 43 (q12 c4) ∷
   rw 40 (q11 c4) ∷
   rw 65 (q5 c4) ∷
   rw 62 (q6 c4) ∷
   rw 59 (q6 c4) ∷
   rw 56 (q6 c4) ∷
   rw 53 (q7 c4) ∷
   rw 50 (q8 c4) ∷
   rw 47 (q7 c4) ∷
   rw 44 (q8 c4) ∷
   rw 41 (q7 c4) ∷
   rw 66 (q3 c4) ∷
   rw 63 (q4 c4) ∷
   rw 60 (q4 c4) ∷
   rw 57 (q4 c4) ∷
   rw 54 (q1 c4) ∷
   rw 51 (q2 c4) ∷
   rw 48 (q1 c4) ∷
   rw 45 (q2 c4) ∷
   rw 42 (q1 c4) ∷
   rw 67 (q3 c4) ∷
   rw 64 (q4 c4) ∷
   rw 61 (q4 c4) ∷
   rw 58 (q4 c4) ∷
   rw 55 (q1 c4) ∷
   rw 52 (q2 c4) ∷
   rw 49 (q1 c4) ∷
   rw 46 (q2 c4) ∷
   rw 43 (q1 c4) ∷
   rw 68 (q5 c4) ∷
   rw 65 (q6 c4) ∷
   rw 62 (q6 c4) ∷
   rw 59 (q6 c4) ∷
   rw 56 (q7 c4) ∷
   rw 53 (q8 c4) ∷
   rw 50 (q7 c4) ∷
   rw 47 (q8 c4) ∷
   rw 44 (q7 c4) ∷
   rw 69 (q9 c4) ∷
   rw 66 (q10 c4) ∷
   rw 63 (q10 c4) ∷
   rw 60 (q10 c4) ∷
   rw 57 (q11 c4) ∷
   rw 54 (q12 c4) ∷
   rw 51 (q11 c4) ∷
   rw 48 (q12 c4) ∷
   rw 45 (q11 c4) ∷
   rw 70 (q21 c4) ∷
   rw 67 (q22 c4) ∷
   rw 64 (q22 c4) ∷
   rw 61 (q22 c4) ∷
   rw 58 (q23 c4) ∷
   rw 55 (q24 c4) ∷
   rw 52 (q23 c4) ∷
   rw 49 (q24 c4) ∷
   rw 46 (q23 c4) ∷
   rw 71 (q9 c4) ∷
   rw 68 (q10 c4) ∷
   rw 65 (q10 c4) ∷
   rw 62 (q10 c4) ∷
   rw 59 (q11 c4) ∷
   rw 56 (q12 c4) ∷
   rw 53 (q11 c4) ∷
   rw 50 (q12 c4) ∷
   rw 47 (q11 c4) ∷
   rw 72 (q25 c4) ∷
   rw 69 (q26 c4) ∷
   rw 66 (q26 c4) ∷
   rw 63 (q26 c4) ∷
   rw 60 (q27 c4) ∷
   rw 57 (q28 c4) ∷
   rw 54 (q27 c4) ∷
   rw 51 (q28 c4) ∷
   rw 48 (q27 c4) ∷
   rw 73 (q21 c4) ∷
   rw 70 (q22 c4) ∷
   rw 67 (q22 c4) ∷
   rw 64 (q22 c4) ∷
   rw 61 (q23 c4) ∷
   rw 58 (q24 c4) ∷
   rw 55 (q23 c4) ∷
   rw 52 (q24 c4) ∷
   rw 49 (q23 c4) ∷
   rw 74 (q3 c4) ∷
   rw 71 (q4 c4) ∷
   rw 68 (q4 c4) ∷
   rw 65 (q4 c4) ∷
   rw 62 (q1 c4) ∷
   rw 59 (q2 c4) ∷
   rw 56 (q1 c4) ∷
   rw 53 (q2 c4) ∷
   rw 50 (q1 c4) ∷
   rw 75 (q17 c4) ∷
   rw 72 (q18 c4) ∷
   rw 69 (q18 c4) ∷
   rw 66 (q18 c4) ∷
   rw 63 (q19 c4) ∷
   rw 60 (q20 c4) ∷
   rw 57 (q19 c4) ∷
   rw 54 (q20 c4) ∷
   rw 51 (q19 c4) ∷
   rw 76 (q13 c4) ∷
   rw 73 (q14 c4) ∷
   rw 70 (q14 c4) ∷
   rw 67 (q14 c4) ∷
   rw 64 (q15 c4) ∷
   rw 61 (q16 c4) ∷
   rw 58 (q15 c4) ∷
   rw 55 (q16 c4) ∷
   rw 52 (q15 c4) ∷
   rw 77 (q13 c4) ∷
   rw 74 (q14 c4) ∷
   rw 71 (q14 c4) ∷
   rw 68 (q14 c4) ∷ []) Eq.refl
