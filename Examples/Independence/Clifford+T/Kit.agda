------------------------------------------------------------------------
-- Presentations of groups
--
-- The proof engine at CliffT₂: letters, and the axioms as equations
--
-- Examples.Independence.Engine instantiated at the gates of CliffT₂.
-- The letters are ωₗ, Hₗ, Tₗ, CXₗ and σₗ, shifted by _↥; a scalar is
-- never shifted.  Each axiom of CliffT₂ and each symmetry rule is an
-- equation between letter lists on the bottom wires of a circuit of
-- any width, and lift⁼ moves it up.  The shortcuts are spelled out in
-- T (S is T T, S† T⁶, X H T⁴ H, T† T⁷), as Syntactics defines them and
-- Examples/Independence/gen/tcliff.py spells them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (ax-at)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq ω-gate  ω-gate  = true
  gate-eq H-gate  H-gate  = true
  gate-eq H-gate  T-gate  = false
  gate-eq T-gate  H-gate  = false
  gate-eq T-gate  T-gate  = true
  gate-eq CX-gate CX-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound ω-gate  ω-gate  _ = refl
  gate-eq-sound H-gate  H-gate  _ = refl
  gate-eq-sound T-gate  T-gate  _ = refl
  gate-eq-sound CX-gate CX-gate _ = refl
  gate-eq-sound H-gate  T-gate  ()
  gate-eq-sound T-gate  H-gate  ()

  code : Gate k → ℕ
  code ω-gate  = 0
  code H-gate  = 0
  code T-gate  = 1
  code CX-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one ω-gate ω-gate = refl

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit _SRel,_===_ public

------------------------------------------------------------------------
-- Letters

pattern ωₗ  = gate₀ ⌈ ω-gate ⌉
pattern Hₗ  = gate₁ ⌈ H-gate ⌉
pattern Tₗ  = gate₁ ⌈ T-gate ⌉
pattern CXₗ = gate₂ ⌈ CX-gate ⌉
pattern σₗ  = gate₂ swap

------------------------------------------------------------------------
-- The axioms

ω⁸⁼ : Eqn n
ω⁸⁼ {n} = eqnʷ
  (ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ [])
  []
  (ax-at ω⁸ n) refl refl

T⁸⁼ : Eqn (₁₊ n)
T⁸⁼ {n} = eqnʷ
  (Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ [])
  []
  (ax-at T⁸ n) refl refl

H²⁼ : Eqn (₁₊ n)
H²⁼ {n} = eqnʷ
  (Hₗ ∷ Hₗ ∷ [])
  []
  (ax-at H² n) refl refl

E⁼ : Eqn (₁₊ n)
E⁼ {n} = eqnʷ
  (Hₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ [])
  (ωₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   [])
  (ax-at E n) refl refl

TX⁼ : Eqn (₁₊ n)
TX⁼ {n} = eqnʷ
  (ωₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷
   [])
  (Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ [])
  (ax-at TX n) refl refl

CPh⁼ : Eqn (₂₊ n)
CPh⁼ {n} = eqnʷ
  (CXₗ ∷ Tₗ ↥ ∷ CXₗ ∷ [])
  (Tₗ ↥ ∷ [])
  (ax-at CPh n) refl refl

B⁼ : Eqn (₂₊ n)
B⁼ {n} = eqnʷ
  (CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (σₗ ∷ CXₗ ∷ [])
  (ax-at B n) refl refl

CZ⁼ : Eqn (₂₊ n)
CZ⁼ {n} = eqnʷ
  (Hₗ ∷ CXₗ ∷ Hₗ ∷ [])
  (Tₗ ↥ ∷ Tₗ ↥ ∷ Tₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ CXₗ ∷ [])
  (ax-at CZ n) refl refl

CSH⁼ : Eqn (₂₊ n)
CSH⁼ {n} = eqnʷ
  (Tₗ ↥ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷
   Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Hₗ ∷ [])
  (Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ↥ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ CXₗ ∷ [])
  (ax-at CSH n) refl refl

HT²⁼ : Eqn (₂₊ n)
HT²⁼ {n} = eqnʷ
  (Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ [])
  (Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ [])
  (ax-at HT² n) refl refl

HTH⁼ : Eqn (₂₊ n)
HTH⁼ {n} = eqnʷ
  (Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ σₗ ∷ Tₗ ∷ Tₗ ∷
   Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ σₗ ∷ Tₗ ↥ ∷ σₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ σₗ ∷ [])
  (σₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ σₗ ∷ Tₗ ↥ ∷ σₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷
   CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Tₗ ∷ σₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ CXₗ ∷
   Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Hₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷ Tₗ ∷
   [])
  (ax-at HTH n) refl refl

------------------------------------------------------------------------
-- The symmetry rules

σσ⁼ : Eqn (₂₊ n)
σσ⁼ = eqnʷ (σₗ ∷ σₗ ∷ []) [] (sym-rule σ-inv) refl refl

σH⁼ σT⁼ : Eqn (₂₊ n)
σH⁼ = eqnʷ (Hₗ ∷ σₗ ∷ []) (σₗ ∷ Hₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ H-gate ⌉)) refl refl
σT⁼ = eqnʷ (Tₗ ∷ σₗ ∷ []) (σₗ ∷ Tₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ T-gate ⌉)) refl refl

σCX⁼ σσσ⁼ : Eqn (₃₊ n)
σCX⁼ = eqnʷ (CXₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ CXₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ ⌈ CX-gate ⌉)) refl refl
σσσ⁼ = eqnʷ (σₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ σₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ swap)) refl refl
