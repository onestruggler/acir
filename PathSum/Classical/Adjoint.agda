------------------------------------------------------------------------
-- Presentations of groups
--
-- The adjoint of a circuit computing a permutation computes the
-- inverse permutation (Amy, QPL 2018, sections 3 and 5.2)
--
-- The paper's tool uncomputes by running the adjoint of what it
-- computed (Bennett's compute-copy-uncompute, with dagger = reverse .
-- map daggerGate in its src/Feynman/Core.hs), and PathSum.CRK.Adjoint's
-- C† is that operation on circuits over {H, CNOT, R_k, R_k†}: the gates
-- last to first, each inverted, R_k and R_k† swapped.  Here is what it
-- does to a circuit whose path-sum computes a Boolean function F
-- (PathSum.Classical: the unnormalised amplitude from x to z is
-- √2^k δ (F x) z): if F has an inverse G, then C† computes G
-- (†-computes).
--
-- The proof: the amplitude of ⟦ C† ⟧ from x to z is the conjugate of
-- that of ⟦ C ⟧ from z to x (PathSum.CRK.Conjugate.circuit-adjoint),
-- which is √2^k δ (F z) x; √2 and the basis columns are real
-- (PathSum.Ring.Laws.conj-scale, PathSum.Adjoint.Gates.conj-δ), and
-- F z is x exactly when z is G x (δ-inverse), so it is √2^k δ (G x) z;
-- and C† has C's normalisation (PathSum.CRK.Adjoint.norm-†).  F and G
-- are functions on assignments, compared pointwise, so they are asked
-- to respect pointwise equality (Respects), as every function built
-- from bits does.
--
-- Two cases are singled out: a circuit computing an involution
-- computes it again when inverted (†-involution; a Toffoli circuit is
-- one), and a circuit computing a netlist's function, run gs, is
-- inverted into one computing the reversed netlist's
-- (†-run: every gate of a netlist is an involution, so the reversed
-- netlist inverts it, PathSum.Reversible.run-reverse).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Classical.Adjoint (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; reverse)
open import Data.List.Properties using (reverse-involutive)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; subst)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint.Gates M₀ using (conj-δ)
open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Assign using (same; same-true; same-intro)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computing; amp-computes)
open import PathSum.Compose.Sum M₀ using (if-cong)
open import PathSum.CRK.Adjoint M using (_†; norm-†)
open import PathSum.CRK.Conjugate M₀ using (circuit-adjoint)
open import PathSum.CRK.Path M₀ using (Circuit; ⟦_⟧; norm)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; scale; scale-map)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Reversible using (Gate; run; run-cong; run-reverse)
open import PathSum.Ring M₀ using (conj; conj-cong)
open import PathSum.Ring.Laws M₀ using (conj-scale)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  -- Two Booleans true together are equal.

  bool-≡ : {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
           a ≡ b
  bool-≡ {true}  {true}  _ _ = refl
  bool-≡ {true}  {false} f _ = sym (f refl)
  bool-≡ {false} {true}  _ g = g refl
  bool-≡ {false} {false} _ _ = refl


------------------------------------------------------------------------
-- Inverse functions

-- A function on assignments that only reads values.

Respects : (Assign n → Assign n) → Set
Respects {n} F = {x x′ : Assign n} → (∀ w → x w ≡ x′ w) →
                 ∀ w → F x w ≡ F x′ w

-- For mutually inverse F and G, F z is the basis state x exactly when
-- G x is z.

δ-inverse : {F G : Assign n → Assign n} → Respects F → Respects G →
            (∀ x w → F (G x) w ≡ x w) → (∀ x w → G (F x) w ≡ x w) →
            ∀ x z → δ (F z) x ≐ δ (G x) z
δ-inverse {F = F} {G} rF rG FG GF x z =
  if-cong {p = same (F z) x} {q = same (G x) z} (bool-≡ to from)
          (λ _ → refl)
  where
  to : same (F z) x ≡ true → same (G x) z ≡ true
  to e = same-intro (G x) z
           (λ w → trans (sym (rG (same-true (F z) x e) w)) (GF z w))

  from : same (G x) z ≡ true → same (F z) x ≡ true
  from e = same-intro (F z) x
             (λ w → trans (sym (rF (same-true (G x) z e) w)) (FG x w))


------------------------------------------------------------------------
-- The adjoint computes the inverse

-- If C computes F, and G is F's inverse, then C† computes G: the
-- amplitude of ⟦ C† ⟧ from x to z is the conjugate of ⟦ C ⟧'s from z
-- to x, √2^k δ (F z) x, which is real and is √2^k δ (G x) z.

†-computes : (C : Circuit n) {F G : Assign n → Assign n} →
             Respects F → Respects G →
             (∀ x w → F (G x) w ≡ x w) → (∀ x w → G (F x) w ≡ x w) →
             ⟦ C ⟧ computes F → ⟦ C † ⟧ computes G
†-computes C {F} {G} rF rG FG GF cF = computing λ x z →
  circuit-adjoint C x z
  ∙ conj-cong {a = amp ⟦ C ⟧ z x} {b = scale (norm C) (δ (F z) x)}
              (amp-computes cF z x)
  ∙ conj-scale (norm C) (δ (F z) x)
  ∙ scale-map (norm C) (conj-δ (F z) x)
  ∙ scale-map (norm C) (δ-inverse rF rG FG GF x z)
  ∙ scale-exp (δ (G x) z) (sym (norm-† C))

-- A circuit computing an involution computes it again when inverted.

†-involution : (C : Circuit n) {F : Assign n → Assign n} → Respects F →
               (∀ x w → F (F x) w ≡ x w) →
               ⟦ C ⟧ computes F → ⟦ C † ⟧ computes F
†-involution C rF FF = †-computes C rF rF FF FF

-- A circuit computing a netlist's function, inverted, computes the
-- reversed netlist's.

†-run : (C : Circuit n) (gs : List (Gate n)) →
        ⟦ C ⟧ computes run gs → ⟦ C † ⟧ computes run (reverse gs)
†-run C gs =
  †-computes C (run-cong gs) (run-cong (reverse gs)) back (run-reverse gs)
  where
  back : ∀ x w → run gs (run (reverse gs) x) w ≡ x w
  back x w = subst (λ hs → run hs (run (reverse gs) x) w ≡ x w)
                   (reverse-involutive gs) (run-reverse (reverse gs) x w)
