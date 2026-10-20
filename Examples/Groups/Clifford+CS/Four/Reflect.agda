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
-- only a re-bracketing compares generators.  `derive l r ss Eq.refl`
-- checks the whole run in one evaluation, its result compared with r
-- inside it, and gives ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ.  Written by
-- `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Reflect where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

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

run : List Step → List Mac → Maybe (List Mac)
run []                xs = just xs
run (rw k e ∷ ss)     xs =
  if eqLM (take (length (lhs e)) (drop k xs)) (lhs e)
  then run ss (next k (length (lhs e)) (rhs e) xs) else nothing
run (rw⁻ k e ∷ ss)    xs =
  if eqLM (take (length (rhs e)) (drop k xs)) (rhs e)
  then run ss (next k (length (rhs e)) (lhs e) xs) else nothing
run (re k n ys ∷ ss)  xs =
  if eqLG (flat (take n (drop k xs))) (flat ys)
  then run ss (next k n ys xs) else nothing

check : List Step → List Mac → List Mac → Bool
check ss l r with run ss l
... | just xs = eqLM xs r
... | nothing = false

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  ≡⇒≈ Eq.refl = refl

run-sound : (ss : List Step) (xs ys : List Mac) → run ss xs ≡ just ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
run-sound []               xs ys Eq.refl = refl
run-sound (rw k e ∷ ss)    xs ys h with eqLM (take (length (lhs e)) (drop k xs)) (lhs e) in c
run-sound (rw k e ∷ ss)    xs ys h  | true  =
  trans (step k (length (lhs e)) xs (rhs e) (trans (≡⇒≈ (eqLM-sound (take (length (lhs e)) (drop k xs)) (lhs e) c)) (prf e)))
        (run-sound ss _ ys h)
run-sound (rw k e ∷ ss)    xs ys () | false
run-sound (rw⁻ k e ∷ ss)   xs ys h with eqLM (take (length (rhs e)) (drop k xs)) (rhs e) in c
run-sound (rw⁻ k e ∷ ss)   xs ys h  | true  =
  trans (step k (length (rhs e)) xs (lhs e) (trans (≡⇒≈ (eqLM-sound (take (length (rhs e)) (drop k xs)) (rhs e) c)) (sym (prf e))))
        (run-sound ss _ ys h)
run-sound (rw⁻ k e ∷ ss)   xs ys () | false
run-sound (re k n zs ∷ ss) xs ys h with eqLG (flat (take n (drop k xs))) (flat zs) in c
run-sound (re k n zs ∷ ss) xs ys h  | true  =
  trans (step k n xs zs (by-assoc {⟪ take n (drop k xs) ⟫ʷ} {⟪ zs ⟫ʷ} (eqLG-sound (flat (take n (drop k xs))) (flat zs) c))) (run-sound ss _ ys h)
run-sound (re k n zs ∷ ss) xs ys () | false

check-sound : (ss : List Step) (l r : List Mac) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
check-sound ss l r h with run ss l in e
check-sound ss l r h  | just xs = trans (run-sound ss l xs e) (≡⇒≈ (eqLM-sound xs r h))
check-sound ss l r () | nothing

-- The equation of a derivation, checked by running it.
derive : (l r : List Mac) (ss : List Step) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
derive l r ss h = check-sound ss l r h
