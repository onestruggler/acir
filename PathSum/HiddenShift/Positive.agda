------------------------------------------------------------------------
-- Presentations of groups
--
-- Every maximal output-safe, Clifford-safe reduction finds the shift
--
-- Section 5.2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018) reports that the calculus
-- finds |s⟩ from the hidden shift circuit "even without providing the
-- specification".  PathSum.HiddenShift.Stuck shows that this fails for
-- some maximal reductions: rules of figure 2 can get stuck with path
-- variables left.  This module proves that it holds for every maximal
-- reduction within a natural class of strategies, for every m, every
-- g : Poly m 0 and every shift s.
--
-- The class (PathSum.HiddenShift.Positive.Class).  Steps are those of
-- PathSum.Full's _⟶ᶠ_ -- all of figure 2, at any variables -- and an
-- [HH] that substitutes Q for y_i (after its head y_j) must be
--
-- * output-safe: if Q mentions an internal path variable (one absent
--   from every output modulo 2), y_i is internal too;
-- * Clifford-safe: every internal variable that occurs in the phase
--   only quadratically (its quotient is linear modulo 1) still does in
--   the reduct.
--
-- Every other step of figure 2 -- every [Elim], [ω] and [Case], in
-- each of _⟶ᶠ_'s shapes -- is admissible.  Admissibility is decidable
-- (Class.Admᶠ?) and stated without reference to the hidden shift.  The
-- class admits Exists' three passes (below), whose [HH]s substitute
-- constants or, in the first pass, a_i ⊕ s_L,i for the internal d_i.
-- It does not admit every [HH] that solves for an internal Clifford
-- variable: with phase ½(y₀y_i + y₀y_ay_b + y_iy_v) and y₀, y_i, y_v
-- internal, [HH] at y₀ with y_i ← y_ay_b leaves ½y_ay_by_v, so y_v is
-- no longer Clifford and the step is not Clifford-safe.
--
-- The theorem (hidden-shift-positive).  Every chain of admissible steps
-- from the circuit on |0⟩ that ends at a path-sum to which no admissible
-- step applies ends with no path variables, and so -- whatever the chain
-- -- at |x⟩ ↦ |s⟩ coefficient by coefficient (hidden-shift-positive-finds,
-- through PathSum.HiddenShift.Simulation.hidden-shift-reduces).  Rules of
-- the class are figure 2's, so termination is ⟶ᶠ-SN's.
--
-- The proof.  An invariant (PathSum.HiddenShift.Positive.Invariant's
-- Inv) holds of the circuit on |0⟩ (Initial.inv₀) and is kept by every
-- admissible step (Invariant.Inv-chain); every reachable path-sum is
-- equivalent to the specification (Stuck.reachable-≋); and a path-sum
-- with both properties and a path variable left admits an admissible
-- step (Progress.progress).  The invariant: the outputs determine the
-- variables they read, and some set of internal Clifford variables --
-- initially the block b -- is such that the partial sum of (-1)^F over
-- it is stabilizer-like, a quadratic phase on an affine subspace.  When
-- that set is empty F itself is quadratic, so an internal Clifford
-- variable always exists while internal variables do; at it the
-- derivative of F is affine, and [Elim] or a suitable [HH] applies --
-- or the amplitudes would contradict the specification.
--
-- Non-triviality.  The class excludes HSFIND's stuck chain: no chain of
-- the class reaches its stuck path-sum at all (stuck-excluded), since
-- that path-sum is irreducible and has ten path variables -- in
-- particular the chain itself is not one of the class.  (Its third
-- [HH] substitutes for the output variable h₀ a form in six internal
-- variables: it is not output-safe.)  More generally no chain of the
-- class reaches any irreducible path-sum with path variables left
-- (stuck-unreachable).  That the class admits the complete reductions
-- PathSum.HiddenShift.Exists builds is PathSum.HiddenShift.Positive.
-- Exists, where Exists' passes are rebuilt rule for rule (Exists'
-- construction is private, so the chain is a copy, not Exists' term).
--
-- What is not proved.  The theorem is about the circuit on |0⟩ as a
-- composite of path-sums, at0 (HS g s), and about nothing else: not
-- about every path-sum written as the circuit's (Exists' Written; only
-- the admission of Exists' passes, written-admits, is stated for
-- those), not about figure 3's circuits (PathSum.HiddenShift.
-- ExistsCircuit and ExistsSymbolic, the |0⟩|s⟩ ↦ |s⟩|s⟩ version
-- included), and not about the tool's circuits (PathSum.HiddenShift.
-- ToolExists).  Whether the class avoids StuckTool's stuck reduction
-- is open.  Feynman's 2018 strategy (src/Feynman/Verification/SOP.hs:
-- Simplify, then HHStrict, SH3, Unify) is not shown to lie in the
-- class.  Maximal is not shown decidable, nor every chain of the class
-- extendable to a maximal one; only termination is proved, since
-- forget maps a chain of the class to one of figure 2 (⟶ᶠ-SN).  How
-- the class was found is unformalised evidence, not part of the proof:
-- a search over the path-sums reachable from the circuit on |0⟩, done
-- outside Agda on the Boolean representation.  A first class
-- (output-safe only) never got stuck at m ≤ 3 for every g and s, nor
-- on random instances at m = 4, but no invariant was found for it.
-- For the class here, the invariant was checked numerically before it
-- was proved.
--
-- Departures from the paper.  The paper's sentence is about figure 3's
-- benchmark circuits, as its tool generated them; the theorem is about
-- the composite H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n} on |0⟩
-- (PathSum.HiddenShift's HS), and about a class of strategies the
-- paper does not state.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive (M₀ : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift M₀ using (HS)
open import PathSum.HiddenShift.Positive.Class M₀ using
  (_⟶ᴷ*_; Maximal; forget)
open import PathSum.HiddenShift.Positive.Initial M₀ using (inv₀)
open import PathSum.HiddenShift.Positive.Invariant M₀ using (Inv-chain)
open import PathSum.HiddenShift.Positive.Progress M₀ using (progress)
open import PathSum.HiddenShift.Simulation M₀ using
  (at0; hidden-shift-reduces)
open import PathSum.HiddenShift.Stuck M₀ using
  (reachable-≋; hidden-shift-stuck) renaming (g to gˢ; s to sˢ)
open import PathSum.Polynomial using (Poly; κ; 0ᴾ; _≈[_]_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full.Match M using (Irreducibleᶠ)
open import PathSum.Order M using (pow)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Every maximal chain of the class is complete

hidden-shift-positive :
  (g : Poly m 0) (s : Assign (m ℕ+ m)) {k′ m′ : ℕ}
  {ζ : PathSum (m ℕ+ m) k′ m′} →
  at0 (HS g s) ⟶ᴷ* ζ → Maximal ζ → m′ ≡ 0
hidden-shift-positive g s {m′ = zero}   c mx = refl
hidden-shift-positive g s {m′ = suc m′} c mx = ⊥-elim
  (progress s (Inv-chain (inv₀ g s) c) (reachable-≋ g s (forget c)) mx)

-- ... and ends at |x⟩ ↦ |s⟩: no normalisation, the outputs s modulo 2
-- and the phase 0 modulo 1, coefficient by coefficient.

data Finds {n : ℕ} (s : Assign n) : ∀ {k′ m′} → PathSum n k′ m′ → Set where
  finds : ∀ {k′} {ζ : PathSum n k′ 0} → k′ ≡ 0 →
          (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) →
          phase ζ ≈[ pow M ] 0ᴾ → Finds s ζ

hidden-shift-positive-finds :
  (g : Poly m 0) (s : Assign (m ℕ+ m)) {k′ m′ : ℕ}
  {ζ : PathSum (m ℕ+ m) k′ m′} →
  at0 (HS g s) ⟶ᴷ* ζ → Maximal ζ → Finds s ζ
hidden-shift-positive-finds g s c mx =
  go (hidden-shift-positive g s c mx) c
  where
  go : ∀ {k′ m′} {ζ : PathSum _ k′ m′} → m′ ≡ 0 →
       at0 (HS g s) ⟶ᴷ* ζ → Finds s ζ
  go refl c′ = finds (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
    where
    r = hidden-shift-reduces g s (forget c′)


------------------------------------------------------------------------
-- HSFIND's stuck chain is excluded

-- A path-sum no rule of figure 2 applies to is maximal for the class.

irreducible-maximal : {ξ : PathSum n k m} → Irreducibleᶠ ξ → Maximal ξ
irreducible-maximal irr s _ = irr s

-- No chain of the class reaches an irreducible path-sum with path
-- variables left ...

stuck-unreachable :
  (g : Poly m 0) (s : Assign (m ℕ+ m)) {k′ m′ : ℕ}
  {ζ : PathSum (m ℕ+ m) k′ (suc m′)} →
  Irreducibleᶠ ζ → ¬ (at0 (HS g s) ⟶ᴷ* ζ)
stuck-unreachable g s irr c =
  suc≢0 (hidden-shift-positive g s c (irreducible-maximal irr))
  where
  suc≢0 : ∀ {j} → ¬ (suc j ≡ 0)
  suc≢0 ()

-- ... in particular not the stuck path-sum of PathSum.HiddenShift.Stuck
-- (m = 3, g = x₀x₁ + x₀x₂ + x₁x₂, s = 0, ten path variables left), so
-- that HSFIND's chain to it is not one of the class.

stuck-excluded : ¬ (at0 (HS gˢ sˢ) ⟶ᴷ* proj₁ hidden-shift-stuck)
stuck-excluded c = 10≢0
  (hidden-shift-positive gˢ sˢ c
    (irreducible-maximal (proj₂ (proj₂ hidden-shift-stuck))))
  where
  10≢0 : ¬ (10 ≡ 0)
  10≢0 ()
