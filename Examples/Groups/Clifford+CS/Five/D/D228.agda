{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD228 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D228 (Sᴰ : SD228) where

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
  lem-F4-S0-CS2-at0440 : Ws → St 2133
  lem-F4-S0-CS2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS0-I-at0440 : Ws → St 2135
  lem-F4-CS0-I-at0440 = pickᴰ 14 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 15 Sᴰ
  lem-F4-CS0-K1-at0440 : Ws → St 2137
  lem-F4-CS0-K1-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS0-K3-at0440 : Ws → St 2138
  lem-F4-CS0-K3-at0440 = pickᴰ 17 Sᴰ
  lem-F4-CS0-K2-at0440 : Ws → St 2139
  lem-F4-CS0-K2-at0440 = pickᴰ 18 Sᴰ
  lem-F4-CS0-CS2-at0440 : Ws → St 2140
  lem-F4-CS0-CS2-at0440 = pickᴰ 19 Sᴰ
  lem-ckt-A : Ws → St 2343
  lem-ckt-A = pickᴰ 20 Sᴰ
  lem-ckt-B : Ws → St 2344
  lem-ckt-B = pickᴰ 21 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2131 (lem-F4-S0-K3-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2138 (lem-F4-CS0-K3-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1690 (lem-F4-K1-K3-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2133 (lem-F4-S0-CS2-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2140 (lem-F4-CS0-CS2-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1694 (lem-F4-K1-CS2-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 2128 (lem-F4-S0-I-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 2135 (lem-F4-CS0-I-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1687 (lem-F4-K1-I-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 2130 (lem-F4-S0-K2-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 2139 (lem-F4-CS0-K2-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1689 (lem-F4-K1-K2-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2129 (lem-F4-S0-K1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 2137 (lem-F4-CS0-K1-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1688 (lem-F4-K1-K1-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 2344 (lem-ckt-B c4)
  q22 : Ws → Eqn
  q22 c4 = sE 2343 (lem-ckt-A c4)

-- F1-ck-tct@0 part3: 153 steps
lem-F1-ck-tctat0-part3 : Ws → ⟪ (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与俊与与中与与俊与与中与与俊与与丽与与丽与主与丽与与上与俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢") ⟫ʷ
lem-F1-ck-tctat0-part3 c4 = derive (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与俊与与中与与俊与与中与与俊与与丽与与丽与主与丽与与上与俵俵主上临俵俵临上主俵俵主上中上") (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢")
  (rw 98 (q1 c4) ∷
   rw 95 (q1 c4) ∷
   rw 92 (q2 c4) ∷
   rw 89 (q3 c4) ∷
   rw 86 (q2 c4) ∷
   rw 83 (q3 c4) ∷
   rw 80 (q2 c4) ∷
   rw 105 (q4 c4) ∷
   rw 102 (q5 c4) ∷
   rw 99 (q5 c4) ∷
   rw 96 (q5 c4) ∷
   rw 93 (q6 c4) ∷
   rw 90 (q7 c4) ∷
   rw 87 (q6 c4) ∷
   rw 84 (q7 c4) ∷
   rw 81 (q6 c4) ∷
   rw 106 (q4 c4) ∷
   rw 103 (q5 c4) ∷
   rw 100 (q5 c4) ∷
   rw 97 (q5 c4) ∷
   rw 94 (q6 c4) ∷
   rw 91 (q7 c4) ∷
   rw 88 (q6 c4) ∷
   rw 85 (q7 c4) ∷
   rw 82 (q6 c4) ∷
   rw 107 (q8 c4) ∷
   rw 104 (q1 c4) ∷
   rw 101 (q1 c4) ∷
   rw 98 (q1 c4) ∷
   rw 95 (q2 c4) ∷
   rw 92 (q3 c4) ∷
   rw 89 (q2 c4) ∷
   rw 86 (q3 c4) ∷
   rw 83 (q2 c4) ∷
   rw 108 (q9 c4) ∷
   rw 105 (q10 c4) ∷
   rw 102 (q10 c4) ∷
   rw 99 (q10 c4) ∷
   rw 96 (q11 c4) ∷
   rw 93 (q12 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q12 c4) ∷
   rw 84 (q11 c4) ∷
   rw 109 (q13 c4) ∷
   rw 106 (q14 c4) ∷
   rw 103 (q14 c4) ∷
   rw 100 (q14 c4) ∷
   rw 97 (q15 c4) ∷
   rw 94 (q16 c4) ∷
   rw 91 (q15 c4) ∷
   rw 88 (q16 c4) ∷
   rw 85 (q15 c4) ∷
   rw 110 (q4 c4) ∷
   rw 107 (q5 c4) ∷
   rw 104 (q5 c4) ∷
   rw 101 (q5 c4) ∷
   rw 98 (q6 c4) ∷
   rw 95 (q7 c4) ∷
   rw 92 (q6 c4) ∷
   rw 89 (q7 c4) ∷
   rw 86 (q6 c4) ∷
   rw 111 (q4 c4) ∷
   rw 108 (q5 c4) ∷
   rw 105 (q5 c4) ∷
   rw 102 (q5 c4) ∷
   rw 99 (q6 c4) ∷
   rw 96 (q7 c4) ∷
   rw 93 (q6 c4) ∷
   rw 90 (q7 c4) ∷
   rw 87 (q6 c4) ∷
   rw 112 (q13 c4) ∷
   rw 109 (q14 c4) ∷
   rw 106 (q14 c4) ∷
   rw 103 (q14 c4) ∷
   rw 100 (q15 c4) ∷
   rw 97 (q16 c4) ∷
   rw 94 (q15 c4) ∷
   rw 91 (q16 c4) ∷
   rw 88 (q15 c4) ∷
   rw 113 (q9 c4) ∷
   rw 110 (q10 c4) ∷
   rw 107 (q10 c4) ∷
   rw 104 (q10 c4) ∷
   rw 101 (q11 c4) ∷
   rw 98 (q12 c4) ∷
   rw 95 (q11 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q11 c4) ∷
   rw 114 (q8 c4) ∷
   rw 111 (q1 c4) ∷
   rw 108 (q1 c4) ∷
   rw 105 (q1 c4) ∷
   rw 102 (q2 c4) ∷
   rw 99 (q3 c4) ∷
   rw 96 (q2 c4) ∷
   rw 93 (q3 c4) ∷
   rw 90 (q2 c4) ∷
   rw 115 (q4 c4) ∷
   rw 112 (q5 c4) ∷
   rw 109 (q5 c4) ∷
   rw 106 (q5 c4) ∷
   rw 103 (q6 c4) ∷
   rw 100 (q7 c4) ∷
   rw 97 (q6 c4) ∷
   rw 94 (q7 c4) ∷
   rw 91 (q6 c4) ∷
   rw 116 (q4 c4) ∷
   rw 113 (q5 c4) ∷
   rw 110 (q5 c4) ∷
   rw 107 (q5 c4) ∷
   rw 104 (q6 c4) ∷
   rw 101 (q7 c4) ∷
   rw 98 (q6 c4) ∷
   rw 95 (q7 c4) ∷
   rw 92 (q6 c4) ∷
   rw 117 (q8 c4) ∷
   rw 114 (q1 c4) ∷
   rw 111 (q1 c4) ∷
   rw 108 (q1 c4) ∷
   rw 105 (q2 c4) ∷
   rw 102 (q3 c4) ∷
   rw 99 (q2 c4) ∷
   rw 96 (q3 c4) ∷
   rw 93 (q2 c4) ∷
   rw 118 (q9 c4) ∷
   rw 115 (q10 c4) ∷
   rw 112 (q10 c4) ∷
   rw 109 (q10 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q12 c4) ∷
   rw 100 (q11 c4) ∷
   rw 97 (q12 c4) ∷
   rw 94 (q11 c4) ∷
   rw 119 (q17 c4) ∷
   rw 116 (q18 c4) ∷
   rw 113 (q18 c4) ∷
   rw 110 (q18 c4) ∷
   rw 107 (q19 c4) ∷
   rw 104 (q20 c4) ∷
   rw 101 (q19 c4) ∷
   rw 98 (q20 c4) ∷
   rw 95 (q19 c4) ∷
   rw 120 (q9 c4) ∷
   rw 117 (q10 c4) ∷
   rw 114 (q10 c4) ∷
   rw 111 (q10 c4) ∷
   rw 108 (q11 c4) ∷
   rw 105 (q12 c4) ∷
   rw 102 (q11 c4) ∷
   rw 99 (q12 c4) ∷
   rw 96 (q11 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw⁻ 97 (q22 c4) ∷ []) Eq.refl
