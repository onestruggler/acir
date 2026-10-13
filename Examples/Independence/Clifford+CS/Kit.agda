------------------------------------------------------------------------
-- Presentations of groups
--
-- The proof engine at CliffCS₂: letters, and the axioms as equations
--
-- Examples.Independence.Engine instantiated at the gates of CliffCS₂.
-- The letters are ωₗ, Hₗ, Sₗ, CSₗ and σₗ, shifted by _↥; a scalar is
-- never shifted.  Z, X and S† are spelt over S and CX over H and CS,
-- as the syntax defines them, so each axiom's letters are those of its
-- two sides
-- (generated, with Examples/Independence/gen/cliffCS.py).  Each axiom
-- of CliffCS₂ and each symmetry rule is an equation between letter
-- lists on the bottom wires of a circuit of any width, and lift⁼ moves
-- it up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (ax-at ; sym-rule)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq ω-gate  ω-gate  = true
  gate-eq H-gate  H-gate  = true
  gate-eq H-gate  S-gate  = false
  gate-eq S-gate  H-gate  = false
  gate-eq S-gate  S-gate  = true
  gate-eq CS-gate CS-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound ω-gate  ω-gate  _ = refl
  gate-eq-sound H-gate  H-gate  _ = refl
  gate-eq-sound S-gate  S-gate  _ = refl
  gate-eq-sound CS-gate CS-gate _ = refl
  gate-eq-sound H-gate  S-gate  ()
  gate-eq-sound S-gate  H-gate  ()

  code : Gate k → ℕ
  code ω-gate  = 0
  code H-gate  = 0
  code S-gate  = 1
  code CS-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one ω-gate ω-gate = refl

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit arity lhs rhs public

------------------------------------------------------------------------
-- Letters

pattern ωₗ  = gate₀ ⌈ ω-gate ⌉
pattern Hₗ  = gate₁ ⌈ H-gate ⌉
pattern Sₗ  = gate₁ ⌈ S-gate ⌉
pattern CSₗ = gate₂ ⌈ CS-gate ⌉
pattern σₗ  = gate₂ swap

------------------------------------------------------------------------
-- The axioms

ω⁸⁼ : Eqn n
ω⁸⁼ {n} = eqnʷ
  (ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ ωₗ ∷ [])
  ([])
  (ax-at ω⁸ n) refl refl

H²⁼ : Eqn (₁₊ n)
H²⁼ {n} = eqnʷ
  (Hₗ ∷ Hₗ ∷ [])
  ([])
  (ax-at H² n) refl refl

S⁴⁼ : Eqn (₁₊ n)
S⁴⁼ {n} = eqnʷ
  (Sₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ [])
  ([])
  (ax-at S⁴ n) refl refl

E⁼ : Eqn (₁₊ n)
E⁼ {n} = eqnʷ
  (Hₗ ∷ Sₗ ∷ Hₗ ∷ [])
  (ωₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ Hₗ ∷ Sₗ ∷ Sₗ ∷ Sₗ ∷ [])
  (ax-at E n) refl refl

CPh⁼ : Eqn (₂₊ n)
CPh⁼ {n} = eqnʷ
  (CSₗ ∷ Sₗ ↥ ∷ CSₗ ∷ CSₗ ∷ CSₗ ∷ [])
  (Sₗ ↥ ∷ [])
  (ax-at CPh n) refl refl

CSr⁼ : Eqn (₂₊ n)
CSr⁼ {n} = eqnʷ
  (CSₗ ∷ [])
  (σₗ ∷ CSₗ ∷ σₗ ∷ [])
  (ax-at CSr n) refl refl

B⁼ : Eqn (₂₊ n)
B⁼ {n} = eqnʷ
  (Hₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ∷ σₗ ∷ Hₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ∷ σₗ ∷ [])
  (σₗ ∷ Hₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ∷ [])
  (ax-at B n) refl refl

XCS⁼ : Eqn (₂₊ n)
XCS⁼ {n} = eqnʷ
  (Hₗ ↥ ∷ Sₗ ↥ ∷ Sₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ∷ [])
  (CSₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ↥ ∷ Sₗ ↥ ∷ Sₗ ↥ ∷ Hₗ ↥ ∷ Sₗ ∷ [])
  (ax-at XCS n) refl refl

CE⁼ : Eqn (₂₊ n)
CE⁼ {n} = eqnʷ
  (Sₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ [])
  (CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ Sₗ ↥ ∷ [])
  (ax-at CE n) refl refl

I⁼ : Eqn (₃₊ n)
I⁼ {n} = eqnʷ
  (Hₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ σₗ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ σₗ ∷ [])
  (Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ Hₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ∷ [])
  (ax-at I n) refl refl

SH₀⁼ : Eqn (₃₊ n)
SH₀⁼ {n} = eqnʷ
  (CSₗ ∷ Hₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ [])
  (CSₗ ↥ ∷ Hₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ [])
  (ax-at SH₀ n) refl refl

SH₁⁼ : Eqn (₃₊ n)
SH₁⁼ {n} = eqnʷ
  (CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ [])
  (CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ [])
  (ax-at SH₁ n) refl refl

SH₂⁼ : Eqn (₃₊ n)
SH₂⁼ {n} = eqnʷ
  (CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ [])
  (CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ CSₗ ∷ [])
  (ax-at SH₂ n) refl refl

SH₃⁼ : Eqn (₃₊ n)
SH₃⁼ {n} = eqnʷ
  (CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ CSₗ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ [])
  (CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ CSₗ ↥ ∷ Hₗ ↥ ∷ CSₗ ∷ Hₗ ↥ ∷ CSₗ ∷ CSₗ ∷ CSₗ ∷ [])
  (ax-at SH₃ n) refl refl

------------------------------------------------------------------------
-- The symmetry rules

σσ⁼ : Eqn (₂₊ n)
σσ⁼ = eqnʷ (σₗ ∷ σₗ ∷ []) ([])
  (sym-rule (σ-inv)) refl refl

σH⁼ : Eqn (₂₊ n)
σH⁼ = eqnʷ (Hₗ ∷ σₗ ∷ []) (σₗ ∷ Hₗ ↥ ∷ [])
  (sym-rule (σ-nat₁ H-gate)) refl refl

σS⁼ : Eqn (₂₊ n)
σS⁼ = eqnʷ (Sₗ ∷ σₗ ∷ []) (σₗ ∷ Sₗ ↥ ∷ [])
  (sym-rule (σ-nat₁ S-gate)) refl refl

σCS⁼ : Eqn (₃₊ n)
σCS⁼ = eqnʷ (CSₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ CSₗ ↥ ∷ [])
  (sym-rule (σ-nat₂ ⌈ CS-gate ⌉)) refl refl

σσσ⁼ : Eqn (₃₊ n)
σσσ⁼ = eqnʷ (σₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ σₗ ↥ ∷ [])
  (sym-rule (σ-nat₂ swap)) refl refl
