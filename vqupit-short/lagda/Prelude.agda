------------------------------------------------------------------------
-- The scope shared by the three example snippets of §2 of the
-- five-page paper (lagda/ex-*.lagda.tex): the circuit syntax of the
-- library, with the gates and the congruence postulated so that each
-- snippet fits on a few lines.  Nothing here is part of the
-- development; the snippets are rendered with
--   agda --latex --only-scope-checking   (make agda)
-- and this module only has to typecheck.
------------------------------------------------------------------------

module vqupit-short.lagda.Prelude where

open import Data.Nat using (ℕ) public
open import Notations using (₁₊ ; ₂₊) public
open import Word.Base using (Word ; WRel ; ε ; _•_ ; _^_) public

private variable
  n : ℕ

infixl 30 _↑ _↓
infix  4 _≈_
infix  1 begin_
infixr 2 _≈⟨_⟩_
infix  3 _∎
infixl 3 cleft_ cright_

postulate
  Gen : ℕ → Set
  H S : Word (Gen (₁₊ n))
  CZ  : Word (Gen (₂₊ n))
  _↑  : Word (Gen n) → Word (Gen (₁₊ n))

-- The lower copy of a gate: the identity on circuits, there to make
-- "the gate on the bottom wire" visible in a rule.
_↓ : Word (Gen n) → Word (Gen n)
w ↓ = w

postulate
  _≈_        : Word (Gen n) → Word (Gen n) → Set
  begin_     : ∀ {w v : Word (Gen n)} → w ≈ v → w ≈ v
  _≈⟨_⟩_     : ∀ (w : Word (Gen n)) {v u} → w ≈ v → v ≈ u → w ≈ u
  _∎         : ∀ (w : Word (Gen n)) → w ≈ w
  sym        : ∀ {w v : Word (Gen n)} → w ≈ v → v ≈ w
  assoc      : ∀ {w v u : Word (Gen n)} → (w • v) • u ≈ w • (v • u)
  right-unit : ∀ {w : Word (Gen n)} → w • ε ≈ w
  cleft_     : ∀ {w v u : Word (Gen n)} → w ≈ v → w • u ≈ v • u
  cright_    : ∀ {w v u : Word (Gen n)} → w ≈ v → u • w ≈ u • v
