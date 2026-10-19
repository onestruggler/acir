------------------------------------------------------------------------
-- Presentations of groups
--
-- The proof engine at Cliff₂: letters, and the axioms as equations
--
-- Examples.Independence.Engine instantiated at the gates of Cliff₂.
-- The letters are ωₗ, Hₗ, Sₗ, CXₗ and σₗ, shifted by _↥; a scalar is
-- never shifted.  Each axiom of Cliff₂ and each symmetry rule is an
-- equation between letter lists on the bottom wires of a circuit of
-- any width, and lift⁼ moves it up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Independence.Clifford.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (ax-at)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq ω-gate  ω-gate  = true
  gate-eq H-gate  H-gate  = true
  gate-eq H-gate  S-gate  = false
  gate-eq S-gate  H-gate  = false
  gate-eq S-gate  S-gate  = true
  gate-eq CX-gate CX-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound ω-gate  ω-gate  _ = refl
  gate-eq-sound H-gate  H-gate  _ = refl
  gate-eq-sound S-gate  S-gate  _ = refl
  gate-eq-sound CX-gate CX-gate _ = refl
  gate-eq-sound H-gate  S-gate  ()
  gate-eq-sound S-gate  H-gate  ()

  code : Gate k → ℕ
  code ω-gate  = 0
  code H-gate  = 0
  code S-gate  = 1
  code CX-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one ω-gate ω-gate = refl

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit _SRel,_===_ public

------------------------------------------------------------------------
-- Letters

pattern ωₗ  = gate₀ ⌈ ω-gate ⌉
pattern Hₗ  = gate₁ ⌈ H-gate ⌉
pattern Sₗ  = gate₁ ⌈ S-gate ⌉
pattern CXₗ = gate₂ ⌈ CX-gate ⌉
pattern σₗ  = gate₂ swap

------------------------------------------------------------------------
-- The axioms

ω⁸⁼ : Eqn n
ω⁸⁼ {n} = eqnʷ (ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ []) [] (ax-at ω⁸ n) refl refl

H²⁼ : Eqn (₁₊ n)
H²⁼ {n} = eqnʷ (Hₗ ∷ Hₗ ∷ []) [] (ax-at H² n) refl refl

S⁴⁼ : Eqn (₁₊ n)
S⁴⁼ {n} = eqnʷ (Sₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ []) [] (ax-at S⁴ n) refl refl

E⁼ : Eqn (₁₊ n)
E⁼ {n} = eqnʷ (Hₗ ∷ Sₗ ∷ Hₗ ∷ [])
              (ωₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ Hₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ []) (ax-at E n) refl refl

CPh⁼ : Eqn (₂₊ n)
CPh⁼ {n} = eqnʷ (CXₗ ∷ Sₗ ↥ ∷ CXₗ ∷ []) (Sₗ ↥ ∷ []) (ax-at CPh n) refl refl

B⁼ : Eqn (₂₊ n)
B⁼ {n} = eqnʷ (CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) (σₗ ∷ CXₗ ∷ []) (ax-at B n) refl refl

CZ⁼ : Eqn (₂₊ n)
CZ⁼ {n} = eqnʷ (Hₗ ∷ CXₗ ∷ Hₗ ∷ [])
               (Sₗ ↥ ∷ Sₗ ∷ CXₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ CXₗ ∷ []) (ax-at CZ n) refl refl

I⁼ : Eqn (₃₊ n)
I⁼ {n} = eqnʷ (CXₗ ∷ CXₗ ↥ ∷ σₗ ∷ CXₗ ↥ ∷ σₗ ∷ []) (CXₗ ↥ ∷ CXₗ ∷ []) (ax-at I n) refl refl

------------------------------------------------------------------------
-- The symmetry rules

σσ⁼ : Eqn (₂₊ n)
σσ⁼ = eqnʷ (σₗ ∷ σₗ ∷ []) [] (sym-rule σ-inv) refl refl

σH⁼ σS⁼ : Eqn (₂₊ n)
σH⁼ = eqnʷ (Hₗ ∷ σₗ ∷ []) (σₗ ∷ Hₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ H-gate ⌉)) refl refl
σS⁼ = eqnʷ (Sₗ ∷ σₗ ∷ []) (σₗ ∷ Sₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ S-gate ⌉)) refl refl

σCX⁼ σσσ⁼ : Eqn (₃₊ n)
σCX⁼ = eqnʷ (CXₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ CXₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ ⌈ CX-gate ⌉)) refl refl
σσσ⁼ = eqnʷ (σₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ σₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ swap)) refl refl

------------------------------------------------------------------------
-- A check of the engine: Derivation A.1, Z Z = ε

private
  A1 : Eqn (₁₊ n)
  A1 = derive (Sₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ []) [] (rw 0 S⁴⁼ ∷ []) refl

  -- Commuting letters, and an equation one wire up.
  test : Eqn (₂₊ n)
  test = derive (Hₗ ↥ ∷ Sₗ ∷ Hₗ ↥ ∷ []) (Sₗ ∷ [])
                (perm (Sₗ ∷ Hₗ ↥ ∷ Hₗ ↥ ∷ []) ∷ rw 1 (lift⁼ H²⁼) ∷ []) refl
