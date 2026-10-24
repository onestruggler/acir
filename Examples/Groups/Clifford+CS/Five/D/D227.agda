{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD227 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D227 (Sᴰ : SD227) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1686
  lem-F4-I-K3-at0440 = pickᴰ 3 Sᴰ
  lem-F4-K1-I-at0440 : Ws → St 1687
  lem-F4-K1-I-at0440 = pickᴰ 4 Sᴰ
  lem-F4-K1-K1-at0440 : Ws → St 1688
  lem-F4-K1-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-K1-K2-at0440 : Ws → St 1689
  lem-F4-K1-K2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-K1-K3-at0440 : Ws → St 1690
  lem-F4-K1-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-S0-I-at0440 : Ws → St 2128
  lem-F4-S0-I-at0440 = pickᴰ 8 Sᴰ
  lem-F4-S0-K1-at0440 : Ws → St 2129
  lem-F4-S0-K1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-S0-K2-at0440 : Ws → St 2130
  lem-F4-S0-K2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-S0-K3-at0440 : Ws → St 2131
  lem-F4-S0-K3-at0440 = pickᴰ 11 Sᴰ
  lem-F4-S0-CS1-at0440 : Ws → St 2132
  lem-F4-S0-CS1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 13 Sᴰ
  lem-F4-K1-CS1-at0440 : Ws → St 1692
  lem-F4-K1-CS1-at0440 = pickᴰ 14 Sᴰ
  lem-F4-S0-CS2-at0440 : Ws → St 2133
  lem-F4-S0-CS2-at0440 = pickᴰ 15 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS0-I-at0440 : Ws → St 2135
  lem-F4-CS0-I-at0440 = pickᴰ 17 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 18 Sᴰ
  lem-F4-CS0-K1-at0440 : Ws → St 2137
  lem-F4-CS0-K1-at0440 = pickᴰ 19 Sᴰ
  lem-F4-CS0-K3-at0440 : Ws → St 2138
  lem-F4-CS0-K3-at0440 = pickᴰ 20 Sᴰ
  lem-F4-CS0-K2-at0440 : Ws → St 2139
  lem-F4-CS0-K2-at0440 = pickᴰ 21 Sᴰ
  lem-F4-CS0-CS2-at0440 : Ws → St 2140
  lem-F4-CS0-CS2-at0440 = pickᴰ 22 Sᴰ
  lem-F4-CS0-CS1-at0440 : Ws → St 2141
  lem-F4-CS0-CS1-at0440 = pickᴰ 23 Sᴰ
  lem-ckt-A : Ws → St 2343
  lem-ckt-A = pickᴰ 24 Sᴰ
  lem-ckt-B : Ws → St 2344
  lem-ckt-B = pickᴰ 25 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2343 (lem-ckt-A c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2344 (lem-ckt-B c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2129 (lem-F4-S0-K1-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2137 (lem-F4-CS0-K1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1688 (lem-F4-K1-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 2133 (lem-F4-S0-CS2-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2140 (lem-F4-CS0-CS2-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1694 (lem-F4-K1-CS2-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 2130 (lem-F4-S0-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 2139 (lem-F4-CS0-K2-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1689 (lem-F4-K1-K2-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 2132 (lem-F4-S0-CS1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 2141 (lem-F4-CS0-CS1-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1692 (lem-F4-K1-CS1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 2128 (lem-F4-S0-I-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 2135 (lem-F4-CS0-I-at0440 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1687 (lem-F4-K1-I-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 2131 (lem-F4-S0-K3-at0440 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 2138 (lem-F4-CS0-K3-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1690 (lem-F4-K1-K3-at0440 c4)

-- F1-ck-tct@0 part0: 242 steps
lem-F1-ck-tctat0-part0 : Ws → ⟪ (ℓ "亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主与俊与与中与与俊与俵与中与与俊与与丽与与丽与与丽与与上与俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-F1-ck-tctat0-part0 c4 = derive (ℓ "亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主与俊与与中与与俊与俵与中与与俊与与丽与与丽与与丽与与上与俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw 0 (q1 c4) ∷
   rw 27 (q2 c4) ∷
   rw 24 (q3 c4) ∷
   rw 21 (q4 c4) ∷
   rw 18 (q4 c4) ∷
   rw 15 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 6 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 0 (q5 c4) ∷
   rw 25 (q7 c4) ∷
   rw 22 (q8 c4) ∷
   rw 19 (q8 c4) ∷
   rw 16 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 7 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 1 (q9 c4) ∷
   rw 26 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 17 (q12 c4) ∷
   rw 14 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   rw 5 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   rw 27 (q15 c4) ∷
   rw 24 (q16 c4) ∷
   rw 21 (q16 c4) ∷
   rw 18 (q16 c4) ∷
   rw 15 (q17 c4) ∷
   rw 12 (q18 c4) ∷
   rw 9 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw 3 (q17 c4) ∷
   rw 28 (q15 c4) ∷
   rw 25 (q16 c4) ∷
   rw 22 (q16 c4) ∷
   rw 19 (q16 c4) ∷
   rw 16 (q17 c4) ∷
   rw 13 (q18 c4) ∷
   rw 10 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 4 (q17 c4) ∷
   rw 29 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 23 (q12 c4) ∷
   rw 20 (q12 c4) ∷
   rw 17 (q13 c4) ∷
   rw 14 (q14 c4) ∷
   rw 11 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw 30 (q19 c4) ∷
   rw 27 (q20 c4) ∷
   rw 24 (q20 c4) ∷
   rw 21 (q20 c4) ∷
   rw 18 (q21 c4) ∷
   rw 15 (q22 c4) ∷
   rw 12 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 6 (q21 c4) ∷
   rw 31 (q7 c4) ∷
   rw 28 (q8 c4) ∷
   rw 25 (q8 c4) ∷
   rw 22 (q8 c4) ∷
   rw 19 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 13 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 7 (q9 c4) ∷
   rw 32 (q7 c4) ∷
   rw 29 (q8 c4) ∷
   rw 26 (q8 c4) ∷
   rw 23 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 14 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 8 (q9 c4) ∷
   rw 33 (q7 c4) ∷
   rw 30 (q8 c4) ∷
   rw 27 (q8 c4) ∷
   rw 24 (q8 c4) ∷
   rw 21 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 15 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 9 (q9 c4) ∷
   rw 34 (q11 c4) ∷
   rw 31 (q12 c4) ∷
   rw 28 (q12 c4) ∷
   rw 25 (q12 c4) ∷
   rw 22 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw 16 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw 10 (q13 c4) ∷
   rw 35 (q15 c4) ∷
   rw 32 (q16 c4) ∷
   rw 29 (q16 c4) ∷
   rw 26 (q16 c4) ∷
   rw 23 (q17 c4) ∷
   rw 20 (q18 c4) ∷
   rw 17 (q17 c4) ∷
   rw 14 (q18 c4) ∷
   rw 11 (q17 c4) ∷
   rw 36 (q15 c4) ∷
   rw 33 (q16 c4) ∷
   rw 30 (q16 c4) ∷
   rw 27 (q16 c4) ∷
   rw 24 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw 18 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw 12 (q17 c4) ∷
   rw 37 (q11 c4) ∷
   rw 34 (q12 c4) ∷
   rw 31 (q12 c4) ∷
   rw 28 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 22 (q14 c4) ∷
   rw 19 (q13 c4) ∷
   rw 16 (q14 c4) ∷
   rw 13 (q13 c4) ∷
   rw 38 (q19 c4) ∷
   rw 35 (q20 c4) ∷
   rw 32 (q20 c4) ∷
   rw 29 (q20 c4) ∷
   rw 26 (q21 c4) ∷
   rw 23 (q22 c4) ∷
   rw 20 (q21 c4) ∷
   rw 17 (q22 c4) ∷
   rw 14 (q21 c4) ∷
   rw 39 (q23 c4) ∷
   rw 36 (q24 c4) ∷
   rw 33 (q24 c4) ∷
   rw 30 (q24 c4) ∷
   rw 27 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw 21 (q25 c4) ∷
   rw 18 (q26 c4) ∷
   rw 15 (q25 c4) ∷
   rw 40 (q7 c4) ∷
   rw 37 (q8 c4) ∷
   rw 34 (q8 c4) ∷
   rw 31 (q8 c4) ∷
   rw 28 (q9 c4) ∷
   rw 25 (q10 c4) ∷
   rw 22 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 16 (q9 c4) ∷
   rw 41 (q7 c4) ∷
   rw 38 (q8 c4) ∷
   rw 35 (q8 c4) ∷
   rw 32 (q8 c4) ∷
   rw 29 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 23 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 17 (q9 c4) ∷
   rw 42 (q23 c4) ∷
   rw 39 (q24 c4) ∷
   rw 36 (q24 c4) ∷
   rw 33 (q24 c4) ∷
   rw 30 (q25 c4) ∷
   rw 27 (q26 c4) ∷
   rw 24 (q25 c4) ∷
   rw 21 (q26 c4) ∷
   rw 18 (q25 c4) ∷
   rw 43 (q19 c4) ∷
   rw 40 (q20 c4) ∷
   rw 37 (q20 c4) ∷
   rw 34 (q20 c4) ∷
   rw 31 (q21 c4) ∷
   rw 28 (q22 c4) ∷
   rw 25 (q21 c4) ∷
   rw 22 (q22 c4) ∷
   rw 19 (q21 c4) ∷
   rw 44 (q11 c4) ∷
   rw 41 (q12 c4) ∷
   rw 38 (q12 c4) ∷
   rw 35 (q12 c4) ∷
   rw 32 (q13 c4) ∷
   rw 29 (q14 c4) ∷
   rw 26 (q13 c4) ∷
   rw 23 (q14 c4) ∷
   rw 20 (q13 c4) ∷
   rw 45 (q7 c4) ∷
   rw 42 (q8 c4) ∷
   rw 39 (q8 c4) ∷
   rw 36 (q8 c4) ∷
   rw 33 (q9 c4) ∷
   rw 30 (q10 c4) ∷
   rw 27 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 21 (q9 c4) ∷
   rw 46 (q7 c4) ∷
   rw 43 (q8 c4) ∷
   rw 40 (q8 c4) ∷
   rw 37 (q8 c4) ∷
   rw 34 (q9 c4) ∷
   rw 31 (q10 c4) ∷
   rw 28 (q9 c4) ∷
   rw 25 (q10 c4) ∷
   rw 22 (q9 c4) ∷
   rw 47 (q11 c4) ∷
   rw 44 (q12 c4) ∷
   rw 41 (q12 c4) ∷
   rw 38 (q12 c4) ∷
   rw 35 (q13 c4) ∷
   rw 32 (q14 c4) ∷
   rw 29 (q13 c4) ∷
   rw 26 (q14 c4) ∷
   rw 23 (q13 c4) ∷
   rw 48 (q19 c4) ∷
   rw 45 (q20 c4) ∷
   rw 42 (q20 c4) ∷
   rw 39 (q20 c4) ∷
   rw 36 (q21 c4) ∷
   rw 33 (q22 c4) ∷
   rw 30 (q21 c4) ∷
   rw 27 (q22 c4) ∷
   rw 24 (q21 c4) ∷
   rw 49 (q23 c4) ∷
   rw 46 (q24 c4) ∷
   rw 43 (q24 c4) ∷
   rw 40 (q24 c4) ∷
   rw 37 (q25 c4) ∷
   rw 34 (q26 c4) ∷
   rw 31 (q25 c4) ∷
   rw 28 (q26 c4) ∷
   rw 25 (q25 c4) ∷
   rw 50 (q7 c4) ∷
   rw 47 (q8 c4) ∷
   rw 44 (q8 c4) ∷
   rw 41 (q8 c4) ∷
   rw 38 (q9 c4) ∷
   rw 35 (q10 c4) ∷ []) Eq.refl
