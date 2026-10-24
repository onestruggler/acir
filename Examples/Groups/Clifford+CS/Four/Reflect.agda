------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire derivations by reflection
--
-- A derivation of Four/D as a list of steps checked by running it, as
-- Clifford+CS.Engine does over generators: `rw k e` replaces the
-- left-hand side of an equation e found at position k by its right-hand
-- side (`rw⁻` the other way round), and `re k n ys` replaces the n
-- letters at k by ys when the two spell the same generators (a
-- re-bracketing, `by-assoc`).  The line is a list of macro letters
-- (Four.Letters), so that a step costs a comparison of a few letters;
-- only a re-bracketing compares generators (sameG).  The line is a
-- zipper, so that a step at position k costs its distance from the step
-- before rather than k.  `derive l r ss Eq.refl` checks the whole run
-- in one evaluation, its result compared with r inside it, and gives
-- ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ.  Written by
-- `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Reflect where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; take ; drop ; map)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; pred ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)

open Assoc (_VRel,_===_ 4) using (to-list)

------------------------------------------------------------------------
-- Codes

private
  ix : {A : Set} → A → List A → ℕ → A
  ix d []       _       = d
  ix d (x ∷ xs) zero    = x
  ix d (x ∷ xs) (suc n) = ix d xs n

codeM : Mac → ℕ
codeM (ι)       = 0
codeM (ι1)      = 1
codeM (ι2)      = 2
codeM (ι3)      = 3
codeM (ι⁻)      = 4
codeM (ι1⁻)     = 5
codeM (ι2⁻)     = 6
codeM (ι3⁻)     = 7
codeM (S0)      = 8
codeM (S0⁻)     = 9
codeM (K0)      = 10
codeM (K0⁻)     = 11
codeM (X0)      = 12
codeM (Z0)      = 13
codeM (S1)      = 14
codeM (S1⁻)     = 15
codeM (K1)      = 16
codeM (K1⁻)     = 17
codeM (X1)      = 18
codeM (Z1)      = 19
codeM (S2)      = 20
codeM (S2⁻)     = 21
codeM (K2)      = 22
codeM (K2⁻)     = 23
codeM (X2)      = 24
codeM (Z2)      = 25
codeM (S3)      = 26
codeM (S3⁻)     = 27
codeM (K3)      = 28
codeM (K3⁻)     = 29
codeM (X3)      = 30
codeM (Z3)      = 31
codeM (CS01)    = 32
codeM (CS01⁻)   = 33
codeM (CZ01)    = 34
codeM (CX01)    = 35
codeM (CK01)    = 36
codeM (CK01⁻)   = 37
codeM (Sw01)    = 38
codeM (CS02)    = 39
codeM (CS02⁻)   = 40
codeM (CZ02)    = 41
codeM (CX02)    = 42
codeM (CK02)    = 43
codeM (CK02⁻)   = 44
codeM (CS03)    = 45
codeM (CS03⁻)   = 46
codeM (CZ03)    = 47
codeM (CX03)    = 48
codeM (CK03)    = 49
codeM (CK03⁻)   = 50
codeM (CX10)    = 51
codeM (CK10)    = 52
codeM (CK10⁻)   = 53
codeM (CS12)    = 54
codeM (CS12⁻)   = 55
codeM (CZ12)    = 56
codeM (CX12)    = 57
codeM (CK12)    = 58
codeM (CK12⁻)   = 59
codeM (Sw12)    = 60
codeM (CS13)    = 61
codeM (CS13⁻)   = 62
codeM (CZ13)    = 63
codeM (CX13)    = 64
codeM (CK13)    = 65
codeM (CK13⁻)   = 66
codeM (CX20)    = 67
codeM (CK20)    = 68
codeM (CK20⁻)   = 69
codeM (CX21)    = 70
codeM (CK21)    = 71
codeM (CK21⁻)   = 72
codeM (CS23)    = 73
codeM (CS23⁻)   = 74
codeM (CZ23)    = 75
codeM (CX23)    = 76
codeM (CK23)    = 77
codeM (CK23⁻)   = 78
codeM (Sw23)    = 79
codeM (CX30)    = 80
codeM (CK30)    = 81
codeM (CK30⁻)   = 82
codeM (CX31)    = 83
codeM (CK31)    = 84
codeM (CK31⁻)   = 85
codeM (CX32)    = 86
codeM (CK32)    = 87
codeM (CK32⁻)   = 88
codeM (CCZ012)  = 89
codeM (CCZ013)  = 90
codeM (CCZ023)  = 91
codeM (CCZ123)  = 92
codeM (Toff012) = 93
codeM (Toff013) = 94
codeM (Toff023) = 95
codeM (Toff102) = 96
codeM (Toff103) = 97
codeM (Toff123) = 98
codeM (Toff201) = 99
codeM (Toff203) = 100
codeM (Toff213) = 101
codeM (Toff301) = 102
codeM (Toff302) = 103
codeM (Toff312) = 104

tableM : List (Mac)
tableM =
  (ι) ∷
  (ι1) ∷
  (ι2) ∷
  (ι3) ∷
  (ι⁻) ∷
  (ι1⁻) ∷
  (ι2⁻) ∷
  (ι3⁻) ∷
  (S0) ∷
  (S0⁻) ∷
  (K0) ∷
  (K0⁻) ∷
  (X0) ∷
  (Z0) ∷
  (S1) ∷
  (S1⁻) ∷
  (K1) ∷
  (K1⁻) ∷
  (X1) ∷
  (Z1) ∷
  (S2) ∷
  (S2⁻) ∷
  (K2) ∷
  (K2⁻) ∷
  (X2) ∷
  (Z2) ∷
  (S3) ∷
  (S3⁻) ∷
  (K3) ∷
  (K3⁻) ∷
  (X3) ∷
  (Z3) ∷
  (CS01) ∷
  (CS01⁻) ∷
  (CZ01) ∷
  (CX01) ∷
  (CK01) ∷
  (CK01⁻) ∷
  (Sw01) ∷
  (CS02) ∷
  (CS02⁻) ∷
  (CZ02) ∷
  (CX02) ∷
  (CK02) ∷
  (CK02⁻) ∷
  (CS03) ∷
  (CS03⁻) ∷
  (CZ03) ∷
  (CX03) ∷
  (CK03) ∷
  (CK03⁻) ∷
  (CX10) ∷
  (CK10) ∷
  (CK10⁻) ∷
  (CS12) ∷
  (CS12⁻) ∷
  (CZ12) ∷
  (CX12) ∷
  (CK12) ∷
  (CK12⁻) ∷
  (Sw12) ∷
  (CS13) ∷
  (CS13⁻) ∷
  (CZ13) ∷
  (CX13) ∷
  (CK13) ∷
  (CK13⁻) ∷
  (CX20) ∷
  (CK20) ∷
  (CK20⁻) ∷
  (CX21) ∷
  (CK21) ∷
  (CK21⁻) ∷
  (CS23) ∷
  (CS23⁻) ∷
  (CZ23) ∷
  (CX23) ∷
  (CK23) ∷
  (CK23⁻) ∷
  (Sw23) ∷
  (CX30) ∷
  (CK30) ∷
  (CK30⁻) ∷
  (CX31) ∷
  (CK31) ∷
  (CK31⁻) ∷
  (CX32) ∷
  (CK32) ∷
  (CK32⁻) ∷
  (CCZ012) ∷
  (CCZ013) ∷
  (CCZ023) ∷
  (CCZ123) ∷
  (Toff012) ∷
  (Toff013) ∷
  (Toff023) ∷
  (Toff102) ∷
  (Toff103) ∷
  (Toff123) ∷
  (Toff201) ∷
  (Toff203) ∷
  (Toff213) ∷
  (Toff301) ∷
  (Toff302) ∷
  (Toff312) ∷
  []

decodeM : ℕ → Mac
decodeM n = ix (ι) tableM n

decode-codeM : ∀ x → decodeM (codeM x) ≡ x
decode-codeM (ι)       = Eq.refl
decode-codeM (ι1)      = Eq.refl
decode-codeM (ι2)      = Eq.refl
decode-codeM (ι3)      = Eq.refl
decode-codeM (ι⁻)      = Eq.refl
decode-codeM (ι1⁻)     = Eq.refl
decode-codeM (ι2⁻)     = Eq.refl
decode-codeM (ι3⁻)     = Eq.refl
decode-codeM (S0)      = Eq.refl
decode-codeM (S0⁻)     = Eq.refl
decode-codeM (K0)      = Eq.refl
decode-codeM (K0⁻)     = Eq.refl
decode-codeM (X0)      = Eq.refl
decode-codeM (Z0)      = Eq.refl
decode-codeM (S1)      = Eq.refl
decode-codeM (S1⁻)     = Eq.refl
decode-codeM (K1)      = Eq.refl
decode-codeM (K1⁻)     = Eq.refl
decode-codeM (X1)      = Eq.refl
decode-codeM (Z1)      = Eq.refl
decode-codeM (S2)      = Eq.refl
decode-codeM (S2⁻)     = Eq.refl
decode-codeM (K2)      = Eq.refl
decode-codeM (K2⁻)     = Eq.refl
decode-codeM (X2)      = Eq.refl
decode-codeM (Z2)      = Eq.refl
decode-codeM (S3)      = Eq.refl
decode-codeM (S3⁻)     = Eq.refl
decode-codeM (K3)      = Eq.refl
decode-codeM (K3⁻)     = Eq.refl
decode-codeM (X3)      = Eq.refl
decode-codeM (Z3)      = Eq.refl
decode-codeM (CS01)    = Eq.refl
decode-codeM (CS01⁻)   = Eq.refl
decode-codeM (CZ01)    = Eq.refl
decode-codeM (CX01)    = Eq.refl
decode-codeM (CK01)    = Eq.refl
decode-codeM (CK01⁻)   = Eq.refl
decode-codeM (Sw01)    = Eq.refl
decode-codeM (CS02)    = Eq.refl
decode-codeM (CS02⁻)   = Eq.refl
decode-codeM (CZ02)    = Eq.refl
decode-codeM (CX02)    = Eq.refl
decode-codeM (CK02)    = Eq.refl
decode-codeM (CK02⁻)   = Eq.refl
decode-codeM (CS03)    = Eq.refl
decode-codeM (CS03⁻)   = Eq.refl
decode-codeM (CZ03)    = Eq.refl
decode-codeM (CX03)    = Eq.refl
decode-codeM (CK03)    = Eq.refl
decode-codeM (CK03⁻)   = Eq.refl
decode-codeM (CX10)    = Eq.refl
decode-codeM (CK10)    = Eq.refl
decode-codeM (CK10⁻)   = Eq.refl
decode-codeM (CS12)    = Eq.refl
decode-codeM (CS12⁻)   = Eq.refl
decode-codeM (CZ12)    = Eq.refl
decode-codeM (CX12)    = Eq.refl
decode-codeM (CK12)    = Eq.refl
decode-codeM (CK12⁻)   = Eq.refl
decode-codeM (Sw12)    = Eq.refl
decode-codeM (CS13)    = Eq.refl
decode-codeM (CS13⁻)   = Eq.refl
decode-codeM (CZ13)    = Eq.refl
decode-codeM (CX13)    = Eq.refl
decode-codeM (CK13)    = Eq.refl
decode-codeM (CK13⁻)   = Eq.refl
decode-codeM (CX20)    = Eq.refl
decode-codeM (CK20)    = Eq.refl
decode-codeM (CK20⁻)   = Eq.refl
decode-codeM (CX21)    = Eq.refl
decode-codeM (CK21)    = Eq.refl
decode-codeM (CK21⁻)   = Eq.refl
decode-codeM (CS23)    = Eq.refl
decode-codeM (CS23⁻)   = Eq.refl
decode-codeM (CZ23)    = Eq.refl
decode-codeM (CX23)    = Eq.refl
decode-codeM (CK23)    = Eq.refl
decode-codeM (CK23⁻)   = Eq.refl
decode-codeM (Sw23)    = Eq.refl
decode-codeM (CX30)    = Eq.refl
decode-codeM (CK30)    = Eq.refl
decode-codeM (CK30⁻)   = Eq.refl
decode-codeM (CX31)    = Eq.refl
decode-codeM (CK31)    = Eq.refl
decode-codeM (CK31⁻)   = Eq.refl
decode-codeM (CX32)    = Eq.refl
decode-codeM (CK32)    = Eq.refl
decode-codeM (CK32⁻)   = Eq.refl
decode-codeM (CCZ012)  = Eq.refl
decode-codeM (CCZ013)  = Eq.refl
decode-codeM (CCZ023)  = Eq.refl
decode-codeM (CCZ123)  = Eq.refl
decode-codeM (Toff012) = Eq.refl
decode-codeM (Toff013) = Eq.refl
decode-codeM (Toff023) = Eq.refl
decode-codeM (Toff102) = Eq.refl
decode-codeM (Toff103) = Eq.refl
decode-codeM (Toff123) = Eq.refl
decode-codeM (Toff201) = Eq.refl
decode-codeM (Toff203) = Eq.refl
decode-codeM (Toff213) = Eq.refl
decode-codeM (Toff301) = Eq.refl
decode-codeM (Toff302) = Eq.refl
decode-codeM (Toff312) = Eq.refl

codeG : Gen 4 → ℕ
codeG (gate₀ I-gate)         = 0
codeG (gate₀ I-gate ↥)       = 1
codeG (gate₀ I-gate ↥ ↥)     = 2
codeG (gate₀ I-gate ↥ ↥ ↥)   = 3
codeG (gate₀ I-gate ↥ ↥ ↥ ↥) = 4
codeG (gate₁ S-gate)         = 5
codeG (gate₁ K-gate)         = 6
codeG (gate₁ S-gate ↥)       = 7
codeG (gate₁ K-gate ↥)       = 8
codeG (gate₁ S-gate ↥ ↥)     = 9
codeG (gate₁ K-gate ↥ ↥)     = 10
codeG (gate₁ S-gate ↥ ↥ ↥)   = 11
codeG (gate₁ K-gate ↥ ↥ ↥)   = 12
codeG (gate₂ CS-gate)        = 13
codeG (gate₂ CS-gate ↥)      = 14
codeG (gate₂ CS-gate ↥ ↥)    = 15

tableG : List (Gen 4)
tableG =
  (gate₀ I-gate) ∷
  (gate₀ I-gate ↥) ∷
  (gate₀ I-gate ↥ ↥) ∷
  (gate₀ I-gate ↥ ↥ ↥) ∷
  (gate₀ I-gate ↥ ↥ ↥ ↥) ∷
  (gate₁ S-gate) ∷
  (gate₁ K-gate) ∷
  (gate₁ S-gate ↥) ∷
  (gate₁ K-gate ↥) ∷
  (gate₁ S-gate ↥ ↥) ∷
  (gate₁ K-gate ↥ ↥) ∷
  (gate₁ S-gate ↥ ↥ ↥) ∷
  (gate₁ K-gate ↥ ↥ ↥) ∷
  (gate₂ CS-gate) ∷
  (gate₂ CS-gate ↥) ∷
  (gate₂ CS-gate ↥ ↥) ∷
  []

decodeG : ℕ → Gen 4
decodeG n = ix (gate₀ I-gate) tableG n

decode-codeG : ∀ x → decodeG (codeG x) ≡ x
decode-codeG (gate₀ I-gate)         = Eq.refl
decode-codeG (gate₀ I-gate ↥)       = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥)     = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥ ↥)   = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥ ↥ ↥) = Eq.refl
decode-codeG (gate₁ S-gate)         = Eq.refl
decode-codeG (gate₁ K-gate)         = Eq.refl
decode-codeG (gate₁ S-gate ↥)       = Eq.refl
decode-codeG (gate₁ K-gate ↥)       = Eq.refl
decode-codeG (gate₁ S-gate ↥ ↥)     = Eq.refl
decode-codeG (gate₁ K-gate ↥ ↥)     = Eq.refl
decode-codeG (gate₁ S-gate ↥ ↥ ↥)   = Eq.refl
decode-codeG (gate₁ K-gate ↥ ↥ ↥)   = Eq.refl
decode-codeG (gate₂ CS-gate)        = Eq.refl
decode-codeG (gate₂ CS-gate ↥)      = Eq.refl
decode-codeG (gate₂ CS-gate ↥ ↥)    = Eq.refl

private
  ≡ᵇ-sound : ∀ x y → (x ≡ᵇ y) ≡ true → x ≡ y
  ≡ᵇ-sound x y h = ≡ᵇ⇒≡ x y (Eq.subst T (Eq.sym h) tt)

eqLM : List Mac → List Mac → Bool
eqLM []       []       = true
eqLM []       (y ∷ ys) = false
eqLM (x ∷ xs) []       = false
eqLM (x ∷ xs) (y ∷ ys) = (codeM x ≡ᵇ codeM y) ∧ eqLM xs ys

eqLM-sound : (xs ys : List Mac) → eqLM xs ys ≡ true → xs ≡ ys
eqLM-sound []       []       h = Eq.refl
eqLM-sound []       (y ∷ ys) ()
eqLM-sound (x ∷ xs) []       ()
eqLM-sound (x ∷ xs) (y ∷ ys) h with codeM x ≡ᵇ codeM y in e
eqLM-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.sym (decode-codeM x))
      (Eq.trans (Eq.cong decodeM (≡ᵇ-sound (codeM x) (codeM y) e)) (decode-codeM y)))
    (eqLM-sound xs ys h)
eqLM-sound (x ∷ xs) (y ∷ ys) () | false

eqLG : List (Gen 4) → List (Gen 4) → Bool
eqLG []       []       = true
eqLG []       (y ∷ ys) = false
eqLG (x ∷ xs) []       = false
eqLG (x ∷ xs) (y ∷ ys) = (codeG x ≡ᵇ codeG y) ∧ eqLG xs ys

eqLG-sound : (xs ys : List (Gen 4)) → eqLG xs ys ≡ true → xs ≡ ys
eqLG-sound []       []       h = Eq.refl
eqLG-sound []       (y ∷ ys) ()
eqLG-sound (x ∷ xs) []       ()
eqLG-sound (x ∷ xs) (y ∷ ys) h with codeG x ≡ᵇ codeG y in e
eqLG-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.sym (decode-codeG x))
      (Eq.trans (Eq.cong decodeG (≡ᵇ-sound (codeG x) (codeG y) e)) (decode-codeG y)))
    (eqLG-sound xs ys h)
eqLG-sound (x ∷ xs) (y ∷ ys) () | false

------------------------------------------------------------------------
-- Equations and steps

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List Mac
    prf     : ⟪ lhs ⟫ʷ ≈ ⟪ rhs ⟫ʷ

open Eqn public

data Step : Set where
  rw rw⁻ : ℕ → Eqn → Step
  re     : ℕ → ℕ → List Mac → Step

flat : List Mac → List (Gen 4)
flat ms = to-list ⟪ ms ⟫ʷ

------------------------------------------------------------------------
-- Each letter's generators, by their codes

-- Read off the letter's word at every re-bracketing, the generators of
-- a letter cost about a millisecond, most of the time of running a
-- Four/D derivation; here they are a table, checked once.  The codes
-- are scratchpad/four/codes_Four.txt, which codes.sh computes.
codesM : Mac → List ℕ
codesM (ι)       = 0 ∷ []
codesM (ι1)      = 1 ∷ []
codesM (ι2)      = 2 ∷ []
codesM (ι3)      = 3 ∷ []
codesM (ι⁻)      = 0 ∷ 0 ∷ 0 ∷ []
codesM (ι1⁻)     = 1 ∷ 1 ∷ 1 ∷ []
codesM (ι2⁻)     = 2 ∷ 2 ∷ 2 ∷ []
codesM (ι3⁻)     = 3 ∷ 3 ∷ 3 ∷ []
codesM (S0)      = 5 ∷ []
codesM (S0⁻)     = 5 ∷ 5 ∷ 5 ∷ []
codesM (K0)      = 6 ∷ []
codesM (K0⁻)     = 6 ∷ 0 ∷ []
codesM (X0)      = 6 ∷ 5 ∷ 5 ∷ 6 ∷ 0 ∷ []
codesM (Z0)      = 5 ∷ 5 ∷ []
codesM (S1)      = 7 ∷ []
codesM (S1⁻)     = 7 ∷ 7 ∷ 7 ∷ []
codesM (K1)      = 8 ∷ []
codesM (K1⁻)     = 8 ∷ 1 ∷ []
codesM (X1)      = 8 ∷ 7 ∷ 7 ∷ 8 ∷ 1 ∷ []
codesM (Z1)      = 7 ∷ 7 ∷ []
codesM (S2)      = 9 ∷ []
codesM (S2⁻)     = 9 ∷ 9 ∷ 9 ∷ []
codesM (K2)      = 10 ∷ []
codesM (K2⁻)     = 10 ∷ 2 ∷ []
codesM (X2)      = 10 ∷ 9 ∷ 9 ∷ 10 ∷ 2 ∷ []
codesM (Z2)      = 9 ∷ 9 ∷ []
codesM (S3)      = 11 ∷ []
codesM (S3⁻)     = 11 ∷ 11 ∷ 11 ∷ []
codesM (K3)      = 12 ∷ []
codesM (K3⁻)     = 12 ∷ 3 ∷ []
codesM (X3)      = 12 ∷ 11 ∷ 11 ∷ 12 ∷ 3 ∷ []
codesM (Z3)      = 11 ∷ 11 ∷ []
codesM (CS01)    = 13 ∷ []
codesM (CS01⁻)   = 13 ∷ 13 ∷ 13 ∷ []
codesM (CZ01)    = 13 ∷ 13 ∷ []
codesM (CX01)    = 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ []
codesM (CK01)    = 13 ∷ 8 ∷ 13 ∷ 8 ∷ 13 ∷ 5 ∷ 5 ∷ 5 ∷ 0 ∷ []
codesM (CK01⁻)   = 5 ∷ 13 ∷ 8 ∷ 13 ∷ 8 ∷ 13 ∷ 5 ∷ 5 ∷ 5 ∷ 0 ∷ []
codesM (Sw01)    = 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ []
codesM (CS02)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CS02⁻)   = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 13 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CZ02)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CX02)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CK02)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 8 ∷ 13 ∷ 8 ∷ 13 ∷ 5 ∷ 5 ∷ 5 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CK02⁻)   = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 5 ∷ 13 ∷ 8 ∷ 13 ∷ 8 ∷ 13 ∷ 5 ∷ 5 ∷ 5 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CS03)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CS03⁻)   = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 13 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CZ03)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX03)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK03)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 8 ∷ 13 ∷ 8 ∷ 13 ∷ 5 ∷ 5 ∷ 5 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK03⁻)   = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 5 ∷ 13 ∷ 8 ∷ 13 ∷ 8 ∷ 13 ∷ 5 ∷ 5 ∷ 5 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX10)    = 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ []
codesM (CK10)    = 13 ∷ 6 ∷ 13 ∷ 6 ∷ 13 ∷ 7 ∷ 7 ∷ 7 ∷ 0 ∷ []
codesM (CK10⁻)   = 7 ∷ 13 ∷ 6 ∷ 13 ∷ 6 ∷ 13 ∷ 7 ∷ 7 ∷ 7 ∷ 0 ∷ []
codesM (CS12)    = 14 ∷ []
codesM (CS12⁻)   = 14 ∷ 14 ∷ 14 ∷ []
codesM (CZ12)    = 14 ∷ 14 ∷ []
codesM (CX12)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CK12)    = 14 ∷ 10 ∷ 14 ∷ 10 ∷ 14 ∷ 7 ∷ 7 ∷ 7 ∷ 1 ∷ []
codesM (CK12⁻)   = 7 ∷ 14 ∷ 10 ∷ 14 ∷ 10 ∷ 14 ∷ 7 ∷ 7 ∷ 7 ∷ 1 ∷ []
codesM (Sw12)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CS13)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CS13⁻)   = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 14 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CZ13)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX13)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK13)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 10 ∷ 14 ∷ 10 ∷ 14 ∷ 7 ∷ 7 ∷ 7 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK13⁻)   = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 7 ∷ 14 ∷ 10 ∷ 14 ∷ 10 ∷ 14 ∷ 7 ∷ 7 ∷ 7 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX20)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CK20)    = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 6 ∷ 13 ∷ 6 ∷ 13 ∷ 7 ∷ 7 ∷ 7 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CK20⁻)   = 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 7 ∷ 13 ∷ 6 ∷ 13 ∷ 6 ∷ 13 ∷ 7 ∷ 7 ∷ 7 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CX21)    = 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ []
codesM (CK21)    = 14 ∷ 8 ∷ 14 ∷ 8 ∷ 14 ∷ 9 ∷ 9 ∷ 9 ∷ 1 ∷ []
codesM (CK21⁻)   = 9 ∷ 14 ∷ 8 ∷ 14 ∷ 8 ∷ 14 ∷ 9 ∷ 9 ∷ 9 ∷ 1 ∷ []
codesM (CS23)    = 15 ∷ []
codesM (CS23⁻)   = 15 ∷ 15 ∷ 15 ∷ []
codesM (CZ23)    = 15 ∷ 15 ∷ []
codesM (CX23)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK23)    = 15 ∷ 12 ∷ 15 ∷ 12 ∷ 15 ∷ 9 ∷ 9 ∷ 9 ∷ 2 ∷ []
codesM (CK23⁻)   = 9 ∷ 15 ∷ 12 ∷ 15 ∷ 12 ∷ 15 ∷ 9 ∷ 9 ∷ 9 ∷ 2 ∷ []
codesM (Sw23)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX30)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK30)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 6 ∷ 13 ∷ 6 ∷ 13 ∷ 7 ∷ 7 ∷ 7 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK30⁻)   = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 7 ∷ 13 ∷ 6 ∷ 13 ∷ 6 ∷ 13 ∷ 7 ∷ 7 ∷ 7 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX31)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK31)    = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 8 ∷ 14 ∷ 8 ∷ 14 ∷ 9 ∷ 9 ∷ 9 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CK31⁻)   = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 9 ∷ 14 ∷ 8 ∷ 14 ∷ 8 ∷ 14 ∷ 9 ∷ 9 ∷ 9 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CX32)    = 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ []
codesM (CK32)    = 15 ∷ 10 ∷ 15 ∷ 10 ∷ 15 ∷ 11 ∷ 11 ∷ 11 ∷ 2 ∷ []
codesM (CK32⁻)   = 11 ∷ 15 ∷ 10 ∷ 15 ∷ 10 ∷ 15 ∷ 11 ∷ 11 ∷ 11 ∷ 2 ∷ []
codesM (CCZ012)  = 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ []
codesM (CCZ013)  = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (CCZ023)  = 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ []
codesM (CCZ123)  = 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (Toff012) = 6 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 6 ∷ 0 ∷ []
codesM (Toff013) = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 6 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 6 ∷ 0 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (Toff023) = 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 8 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 8 ∷ 1 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ []
codesM (Toff102) = 8 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 0 ∷ []
codesM (Toff103) = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 8 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 0 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (Toff123) = 8 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 8 ∷ 1 ∷ []
codesM (Toff201) = 10 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 10 ∷ 0 ∷ []
codesM (Toff203) = 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 1 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ []
codesM (Toff213) = 10 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 1 ∷ []
codesM (Toff301) = 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 14 ∷ 14 ∷ 14 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 13 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 8 ∷ 14 ∷ 14 ∷ 8 ∷ 1 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 10 ∷ 0 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ []
codesM (Toff302) = 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 12 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 12 ∷ 1 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ 6 ∷ 13 ∷ 13 ∷ 6 ∷ 0 ∷ 8 ∷ 13 ∷ 13 ∷ 8 ∷ 0 ∷ []
codesM (Toff312) = 12 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 15 ∷ 15 ∷ 15 ∷ 10 ∷ 14 ∷ 14 ∷ 10 ∷ 1 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 14 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 10 ∷ 15 ∷ 15 ∷ 10 ∷ 2 ∷ 12 ∷ 15 ∷ 15 ∷ 12 ∷ 2 ∷ 12 ∷ 1 ∷ []

codesM-ok : ∀ x → codesM x ≡ map codeG (flat (x ∷ []))
codesM-ok (ι)       = Eq.refl
codesM-ok (ι1)      = Eq.refl
codesM-ok (ι2)      = Eq.refl
codesM-ok (ι3)      = Eq.refl
codesM-ok (ι⁻)      = Eq.refl
codesM-ok (ι1⁻)     = Eq.refl
codesM-ok (ι2⁻)     = Eq.refl
codesM-ok (ι3⁻)     = Eq.refl
codesM-ok (S0)      = Eq.refl
codesM-ok (S0⁻)     = Eq.refl
codesM-ok (K0)      = Eq.refl
codesM-ok (K0⁻)     = Eq.refl
codesM-ok (X0)      = Eq.refl
codesM-ok (Z0)      = Eq.refl
codesM-ok (S1)      = Eq.refl
codesM-ok (S1⁻)     = Eq.refl
codesM-ok (K1)      = Eq.refl
codesM-ok (K1⁻)     = Eq.refl
codesM-ok (X1)      = Eq.refl
codesM-ok (Z1)      = Eq.refl
codesM-ok (S2)      = Eq.refl
codesM-ok (S2⁻)     = Eq.refl
codesM-ok (K2)      = Eq.refl
codesM-ok (K2⁻)     = Eq.refl
codesM-ok (X2)      = Eq.refl
codesM-ok (Z2)      = Eq.refl
codesM-ok (S3)      = Eq.refl
codesM-ok (S3⁻)     = Eq.refl
codesM-ok (K3)      = Eq.refl
codesM-ok (K3⁻)     = Eq.refl
codesM-ok (X3)      = Eq.refl
codesM-ok (Z3)      = Eq.refl
codesM-ok (CS01)    = Eq.refl
codesM-ok (CS01⁻)   = Eq.refl
codesM-ok (CZ01)    = Eq.refl
codesM-ok (CX01)    = Eq.refl
codesM-ok (CK01)    = Eq.refl
codesM-ok (CK01⁻)   = Eq.refl
codesM-ok (Sw01)    = Eq.refl
codesM-ok (CS02)    = Eq.refl
codesM-ok (CS02⁻)   = Eq.refl
codesM-ok (CZ02)    = Eq.refl
codesM-ok (CX02)    = Eq.refl
codesM-ok (CK02)    = Eq.refl
codesM-ok (CK02⁻)   = Eq.refl
codesM-ok (CS03)    = Eq.refl
codesM-ok (CS03⁻)   = Eq.refl
codesM-ok (CZ03)    = Eq.refl
codesM-ok (CX03)    = Eq.refl
codesM-ok (CK03)    = Eq.refl
codesM-ok (CK03⁻)   = Eq.refl
codesM-ok (CX10)    = Eq.refl
codesM-ok (CK10)    = Eq.refl
codesM-ok (CK10⁻)   = Eq.refl
codesM-ok (CS12)    = Eq.refl
codesM-ok (CS12⁻)   = Eq.refl
codesM-ok (CZ12)    = Eq.refl
codesM-ok (CX12)    = Eq.refl
codesM-ok (CK12)    = Eq.refl
codesM-ok (CK12⁻)   = Eq.refl
codesM-ok (Sw12)    = Eq.refl
codesM-ok (CS13)    = Eq.refl
codesM-ok (CS13⁻)   = Eq.refl
codesM-ok (CZ13)    = Eq.refl
codesM-ok (CX13)    = Eq.refl
codesM-ok (CK13)    = Eq.refl
codesM-ok (CK13⁻)   = Eq.refl
codesM-ok (CX20)    = Eq.refl
codesM-ok (CK20)    = Eq.refl
codesM-ok (CK20⁻)   = Eq.refl
codesM-ok (CX21)    = Eq.refl
codesM-ok (CK21)    = Eq.refl
codesM-ok (CK21⁻)   = Eq.refl
codesM-ok (CS23)    = Eq.refl
codesM-ok (CS23⁻)   = Eq.refl
codesM-ok (CZ23)    = Eq.refl
codesM-ok (CX23)    = Eq.refl
codesM-ok (CK23)    = Eq.refl
codesM-ok (CK23⁻)   = Eq.refl
codesM-ok (Sw23)    = Eq.refl
codesM-ok (CX30)    = Eq.refl
codesM-ok (CK30)    = Eq.refl
codesM-ok (CK30⁻)   = Eq.refl
codesM-ok (CX31)    = Eq.refl
codesM-ok (CK31)    = Eq.refl
codesM-ok (CK31⁻)   = Eq.refl
codesM-ok (CX32)    = Eq.refl
codesM-ok (CK32)    = Eq.refl
codesM-ok (CK32⁻)   = Eq.refl
codesM-ok (CCZ012)  = Eq.refl
codesM-ok (CCZ013)  = Eq.refl
codesM-ok (CCZ023)  = Eq.refl
codesM-ok (CCZ123)  = Eq.refl
codesM-ok (Toff012) = Eq.refl
codesM-ok (Toff013) = Eq.refl
codesM-ok (Toff023) = Eq.refl
codesM-ok (Toff102) = Eq.refl
codesM-ok (Toff103) = Eq.refl
codesM-ok (Toff123) = Eq.refl
codesM-ok (Toff201) = Eq.refl
codesM-ok (Toff203) = Eq.refl
codesM-ok (Toff213) = Eq.refl
codesM-ok (Toff301) = Eq.refl
codesM-ok (Toff302) = Eq.refl
codesM-ok (Toff312) = Eq.refl

flatC : List Mac → List ℕ
flatC []       = []
flatC (x ∷ xs) = codesM x ++ flatC xs

eqLN : List ℕ → List ℕ → Bool
eqLN []       []       = true
eqLN []       (y ∷ ys) = false
eqLN (x ∷ xs) []       = false
eqLN (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqLN xs ys

private
  eqLN-sound : (xs ys : List ℕ) → eqLN xs ys ≡ true → xs ≡ ys
  eqLN-sound []       []       h = Eq.refl
  eqLN-sound []       (y ∷ ys) ()
  eqLN-sound (x ∷ xs) []       ()
  eqLN-sound (x ∷ xs) (y ∷ ys) h with x ≡ᵇ y in e
  eqLN-sound (x ∷ xs) (y ∷ ys) h  | true  = Eq.cong₂ _∷_ (≡ᵇ-sound x y e) (eqLN-sound xs ys h)
  eqLN-sound (x ∷ xs) (y ∷ ys) () | false

  map-++ : (xs ys : List (Gen 4)) → map codeG (xs ++ ys) ≡ map codeG xs ++ map codeG ys
  map-++ []       ys = Eq.refl
  map-++ (x ∷ xs) ys = Eq.cong (codeG x ∷_) (map-++ xs ys)

  ++-[] : (xs : List (Gen 4)) → xs ++ [] ≡ xs
  ++-[] []       = Eq.refl
  ++-[] (x ∷ xs) = Eq.cong (x ∷_) (++-[] xs)

  flat-∷ : (x : Mac) (xs : List Mac) → flat (x ∷ xs) ≡ flat (x ∷ []) ++ flat xs
  flat-∷ x []       = Eq.sym (++-[] (flat (x ∷ [])))
  flat-∷ x (m ∷ ms) = Eq.refl

  flatC-ok : (xs : List Mac) → flatC xs ≡ map codeG (flat xs)
  flatC-ok []       = Eq.refl
  flatC-ok (x ∷ xs) =
    Eq.trans (Eq.cong₂ _++_ (codesM-ok x) (flatC-ok xs))
      (Eq.trans (Eq.sym (map-++ (flat (x ∷ [])) (flat xs))) (Eq.cong (map codeG) (Eq.sym (flat-∷ x xs))))

  map-inj : (xs ys : List (Gen 4)) → map codeG xs ≡ map codeG ys → xs ≡ ys
  map-inj []       []       h = Eq.refl
  map-inj []       (y ∷ ys) ()
  map-inj (x ∷ xs) []       ()
  map-inj (x ∷ xs) (y ∷ ys) h =
    Eq.cong₂ _∷_
      (Eq.trans (Eq.sym (decode-codeG x)) (Eq.trans (Eq.cong decodeG (∷-head h)) (decode-codeG y)))
      (map-inj xs ys (∷-tail h))
    where
    ∷-head : ∀ {a b : ℕ} {as bs} → a ∷ as ≡ b ∷ bs → a ≡ b
    ∷-head Eq.refl = Eq.refl
    ∷-tail : ∀ {a b : ℕ} {as bs} → a ∷ as ≡ b ∷ bs → as ≡ bs
    ∷-tail Eq.refl = Eq.refl

  flat-eq : (xs ys : List Mac) → eqLN (flatC xs) (flatC ys) ≡ true → flat xs ≡ flat ys
  flat-eq xs ys h =
    map-inj (flat xs) (flat ys)
      (Eq.trans (Eq.sym (flatC-ok xs)) (Eq.trans (eqLN-sound (flatC xs) (flatC ys) h) (flatC-ok ys)))

-- Whether two runs of letters spell the same generators.
sameG : List Mac → List Mac → Bool
sameG xs ys = eqLN (flatC xs) (flatC ys)

sameG-ok : (xs ys : List Mac) → sameG xs ys ≡ true → flat xs ≡ flat ys
sameG-ok = flat-eq

------------------------------------------------------------------------
-- The line as a zipper

-- The letters before the focus, last first, and the letters from it on,
-- with the index of the focus.  A step at position k moves the focus
-- there, which costs the distance from the step before: two letters on
-- average in Four/D and Five/D, whose steps are at positions 30 and 47
-- on average, and the line as a list was walked from its start at every
-- step (take, drop and next).  The equation's sides and the parts of
-- the line are handed on as arguments (runZ-rw, runZ-at, runZ-seg), so
-- that Agda's evaluator computes each once.  The engine is that of
-- Qutrit-Clifford.Engine on the ten-completeness branch.
data Zip : Set where
  zp : ℕ → List Mac → List Mac → Zip

revApp : List Mac → List Mac → List Mac
revApp []       ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

plug : Zip → List Mac
plug (zp _ b a) = revApp b a

goL goR : ℕ → Zip → Maybe Zip
goL zero    z                = just z
goL (suc k) (zp c (x ∷ b) a) = goL k (zp (pred c) b (x ∷ a))
goL (suc k) (zp c [] a)      = nothing
goR zero    z                = just z
goR (suc k) (zp c b (x ∷ a)) = goR k (zp (suc c) (x ∷ b) a)
goR (suc k) (zp c b [])      = nothing

seek : ℕ → Zip → Maybe Zip
seek i (zp c b a) = if i <ᵇ c then goL (c ∸ i) (zp c b a) else goR (i ∸ c) (zp c b a)

-- What follows l in a, when l begins a.
strip : List Mac → List Mac → Maybe (List Mac)
strip []      a       = just a
strip (x ∷ l) []      = nothing
strip (x ∷ l) (y ∷ a) = if codeM x ≡ᵇ codeM y then strip l a else nothing

mutual
  runZ : List Step → Zip → Maybe Zip
  runZ []               z = just z
  runZ (rw k e ∷ ss)    z = runZ-rw ss (lhs e) (rhs e) (seek k z)
  runZ (rw⁻ k e ∷ ss)   z = runZ-rw ss (rhs e) (lhs e) (seek k z)
  runZ (re k n ys ∷ ss) z = runZ-re ss n ys (seek k z)

  runZ-rw : List Step → (l r : List Mac) → Maybe Zip → Maybe Zip
  runZ-rw ss l r nothing           = nothing
  runZ-rw ss l r (just (zp c b a)) = runZ-at ss r c b (strip l a)

  runZ-at : List Step → List Mac → ℕ → List Mac → Maybe (List Mac) → Maybe Zip
  runZ-at ss r c b nothing     = nothing
  runZ-at ss r c b (just rest) = runZ ss (zp c b (r ++ rest))

  runZ-re : List Step → ℕ → List Mac → Maybe Zip → Maybe Zip
  runZ-re ss n ys nothing           = nothing
  runZ-re ss n ys (just (zp c b a)) = runZ-seg ss ys c b (take n a) (drop n a)

  runZ-seg : List Step → List Mac → ℕ → (b seg rest : List Mac) → Maybe Zip
  runZ-seg ss ys c b seg rest =
    if sameG seg ys then runZ ss (zp c b (ys ++ rest)) else nothing

okZ : List Mac → Maybe Zip → Bool
okZ r (just z) = eqLM (plug z) r
okZ r nothing  = false

check : List Step → List Mac → List Mac → Bool
check ss l r = okZ r (runZ ss (zp 0 [] l))

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  ≡⇒≈ Eq.refl = refl

  code-eq : ∀ x y → (codeM x ≡ᵇ codeM y) ≡ true → x ≡ y
  code-eq x y e =
    Eq.trans (Eq.sym (decode-codeM x))
      (Eq.trans (Eq.cong decodeM (≡ᵇ-sound (codeM x) (codeM y) e)) (decode-codeM y))

  lc-∷ : ∀ ℓ ls → ⟪ ℓ ∷ ls ⟫ʷ ≈ ⟪ ℓ ⟫ • ⟪ ls ⟫ʷ
  lc-∷ ℓ []       = sym right-unit
  lc-∷ ℓ (m ∷ ls) = refl

  lc-++ : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
  lc-++ []       ys = sym left-unit
  lc-++ (x ∷ xs) ys =
    trans (lc-∷ x (xs ++ ys))
    (trans (back ⟪ x ⟫ (lc-++ xs ys))
    (trans (sym assoc) (front ⟪ ys ⟫ʷ (sym (lc-∷ x xs)))))

  ++-congˡ : ∀ {x y} s → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ x ++ s ⟫ʷ ≈ ⟪ y ++ s ⟫ʷ
  ++-congˡ {x} {y} s e = trans (lc-++ x s) (trans (front ⟪ s ⟫ʷ e) (sym (lc-++ y s)))

  revApp-cong : (b : List Mac) {x y : List Mac} → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ revApp b x ⟫ʷ ≈ ⟪ revApp b y ⟫ʷ
  revApp-cong []      e = e
  revApp-cong (g ∷ b) {x} {y} e =
    revApp-cong b (trans (lc-∷ g x) (trans (back ⟪ g ⟫ e) (sym (lc-∷ g y))))

  take++drop : (n : ℕ) (xs : List Mac) → take n xs ++ drop n xs ≡ xs
  take++drop zero    xs       = Eq.refl
  take++drop (suc n) []       = Eq.refl
  take++drop (suc n) (x ∷ xs) = Eq.cong (x ∷_) (take++drop n xs)

  -- Moving the focus keeps the line.
  goL-un : (k : ℕ) (z z′ : Zip) → goL k z ≡ just z′ → plug z′ ≡ plug z
  goL-un zero    z                z′ Eq.refl = Eq.refl
  goL-un (suc k) (zp c (x ∷ b) a) z′ h       = goL-un k (zp (pred c) b (x ∷ a)) z′ h
  goL-un (suc k) (zp c [] a)      z′ ()

  goR-un : (k : ℕ) (z z′ : Zip) → goR k z ≡ just z′ → plug z′ ≡ plug z
  goR-un zero    z                z′ Eq.refl = Eq.refl
  goR-un (suc k) (zp c b (x ∷ a)) z′ h       = goR-un k (zp (suc c) (x ∷ b) a) z′ h
  goR-un (suc k) (zp c b [])      z′ ()

  seek-un : (i : ℕ) (z z′ : Zip) → seek i z ≡ just z′ → plug z′ ≡ plug z
  seek-un i (zp c b a) z′ h with i <ᵇ c
  seek-un i (zp c b a) z′ h | true  = goL-un (c ∸ i) (zp c b a) z′ h
  seek-un i (zp c b a) z′ h | false = goR-un (i ∸ c) (zp c b a) z′ h

  strip-sound : (l a rest : List Mac) → strip l a ≡ just rest → a ≡ l ++ rest
  strip-sound []      a       rest Eq.refl = Eq.refl
  strip-sound (x ∷ l) []      rest ()
  strip-sound (x ∷ l) (y ∷ a) rest h with codeM x ≡ᵇ codeM y in e
  strip-sound (x ∷ l) (y ∷ a) rest h  | true  =
    Eq.cong₂ _∷_ (Eq.sym (code-eq x y e)) (strip-sound l a rest h)
  strip-sound (x ∷ l) (y ∷ a) rest () | false

  mutual
    runZ-sound : (ss : List Step) (z z′ : Zip) → runZ ss z ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-sound []               z z′ Eq.refl = refl
    runZ-sound (rw k e ∷ ss)    z z′ h =
      runZ-rw-sound ss (lhs e) (rhs e) (prf e) z (seek k z) (seek-un k z) z′ h
    runZ-sound (rw⁻ k e ∷ ss)   z z′ h =
      runZ-rw-sound ss (rhs e) (lhs e) (sym (prf e)) z (seek k z) (seek-un k z) z′ h
    runZ-sound (re k n ys ∷ ss) z z′ h =
      runZ-re-sound ss n ys z (seek k z) (seek-un k z) z′ h

    runZ-rw-sound : (ss : List Step) (l r : List Mac) → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → (z : Zip) (m : Maybe Zip) →
                    (∀ z₁ → m ≡ just z₁ → plug z₁ ≡ plug z) → (z′ : Zip) →
                    runZ-rw ss l r m ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-rw-sound ss l r p z nothing           u z′ ()
    runZ-rw-sound ss l r p z (just (zp c b a)) u z′ h =
      trans (≡⇒≈ (Eq.sym (u (zp c b a) Eq.refl)))
            (runZ-at-sound ss l r p c b a (strip l a) Eq.refl z′ h)

    runZ-at-sound : (ss : List Step) (l r : List Mac) → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → (c : ℕ) (b a : List Mac) →
                    (m : Maybe (List Mac)) → strip l a ≡ m → (z′ : Zip) →
                    runZ-at ss r c b m ≡ just z′ → ⟪ revApp b a ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-at-sound ss l r p c b a nothing     s z′ ()
    runZ-at-sound ss l r p c b a (just rest) s z′ h =
      trans (revApp-cong b (trans (≡⇒≈ (strip-sound l a rest s)) (++-congˡ {l} {r} rest p)))
            (runZ-sound ss (zp c b (r ++ rest)) z′ h)

    runZ-re-sound : (ss : List Step) (n : ℕ) (ys : List Mac) (z : Zip) (m : Maybe Zip) →
                    (∀ z₁ → m ≡ just z₁ → plug z₁ ≡ plug z) → (z′ : Zip) →
                    runZ-re ss n ys m ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-re-sound ss n ys z nothing           u z′ ()
    runZ-re-sound ss n ys z (just (zp c b a)) u z′ h =
      trans (≡⇒≈ (Eq.sym (u (zp c b a) Eq.refl)))
      (trans (≡⇒≈ (Eq.cong (revApp b) (Eq.sym (take++drop n a))))
             (runZ-seg-sound ss ys c b (take n a) (drop n a) z′ h))

    runZ-seg-sound : (ss : List Step) (ys : List Mac) (c : ℕ) (b seg rest : List Mac) (z′ : Zip) →
                     runZ-seg ss ys c b seg rest ≡ just z′ → ⟪ revApp b (seg ++ rest) ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-seg-sound ss ys c b seg rest z′ h with sameG seg ys in g
    runZ-seg-sound ss ys c b seg rest z′ h  | true  =
      trans (revApp-cong b (++-congˡ {seg} {ys} rest (by-assoc {⟪ seg ⟫ʷ} {⟪ ys ⟫ʷ} (sameG-ok seg ys g))))
            (runZ-sound ss (zp c b (ys ++ rest)) z′ h)
    runZ-seg-sound ss ys c b seg rest z′ () | false

check-sound : (ss : List Step) (l r : List Mac) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
check-sound ss l r h with runZ ss (zp 0 [] l) in e
check-sound ss l r h  | just z  = trans (runZ-sound ss (zp 0 [] l) z e) (≡⇒≈ (eqLM-sound (plug z) r h))
check-sound ss l r () | nothing

-- The equation of a derivation, checked by running it.
derive : (l r : List Mac) (ss : List Step) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
derive l r ss h = check-sound ss l r h
