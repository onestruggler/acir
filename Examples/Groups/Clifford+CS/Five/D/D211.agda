{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD211 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D211 (Sᴰ : SD211) where

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
  lem-ckt-TT-at0440 : Ws → St 2127
  lem-ckt-TT-at0440 = pickᴰ 0 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 1423 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2127 (lem-ckt-TT-at0440 c4)

-- ckt-TST @0440 part69: 85 steps
lem-ckt-TST-at0440-part69 : Ws → ⟪ (ℓ "与中俵临俭俭临上俵俵俵临俭俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part69 c4 = derive (ℓ "与中俵临俭俭临上俵俵俵临俭俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q1 c4) ∷
   rw 45 (q1 c4) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw 63 (q1 c4) ∷
   rw 64 (q1 c4) ∷
   rw 65 (q1 c4) ∷
   rw 66 (q1 c4) ∷
   rw 67 (q1 c4) ∷
   rw 68 (q1 c4) ∷
   rw 69 (q1 c4) ∷
   rw 70 (q1 c4) ∷
   rw 71 (q1 c4) ∷
   rw 72 (q1 c4) ∷
   rw 73 (q1 c4) ∷
   rw 74 (q1 c4) ∷
   rw 75 (q1 c4) ∷
   rw 76 (q1 c4) ∷
   rw 77 (q1 c4) ∷
   rw 78 (q1 c4) ∷
   rw 79 (q1 c4) ∷
   rw 80 (q1 c4) ∷
   rw 81 (q1 c4) ∷
   rw 82 (q1 c4) ∷
   rw 83 (q1 c4) ∷
   rw 84 (q1 c4) ∷
   rw 85 (q1 c4) ∷
   rw 86 (q1 c4) ∷
   rw 87 (q1 c4) ∷
   rw 88 (q1 c4) ∷
   rw 89 (q1 c4) ∷
   rw 90 (q1 c4) ∷
   rw 91 (q1 c4) ∷
   rw 92 (q1 c4) ∷
   rw 93 (q1 c4) ∷
   rw 94 (q1 c4) ∷
   rw 95 (q1 c4) ∷
   rw 96 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl
