------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of figure 2 can get stuck on the hidden shift circuit
--
-- Section 5.2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018) reports that the calculus
-- "further finds the correct output |s⟩ ... even without providing the
-- specification, effectively simulating the algorithm".  Two halves of
-- that are proved already, for every m, g and s: a reduction of the
-- circuit on |0⟩ to a path-sum with no path variables exists
-- (PathSum.HiddenShift.Exists), and every such complete reduction ends
-- at |x⟩ ↦ |s⟩, whatever rules it applies in whatever order
-- (PathSum.HiddenShift.Simulation.hidden-shift-reduces).  What was
-- left open is whether every maximal reduction is complete -- whether
-- reducing until no rule applies always eliminates every path
-- variable, so that any strategy finds |s⟩.
--
-- It is not.  At m = 3 (n = 6 qubits), with g the majority of three
-- bits,
--
--    g(x₀, x₁, x₂) = x₀x₁ + x₀x₂ + x₁x₂            (degree 2),
--
-- and shift s = 0, the circuit on |0⟩ has 18 path variables, the six
-- blocks a, b, c, d, e, h of PathSum.HiddenShift.Blocks (the outputs
-- being e and h), and four [HH] steps, each followed by the [Elim] of
-- the variable it substituted, reach a path-sum with 10 path variables
-- to which no rule of figure 2 applies at any variable or pair
-- (hidden-shift-stuck):
--
--    [HH] at a₀, b₀ ← a₁ ⊕ a₂ ⊕ c₀
--    [HH] at a₁, d₀ ← a₂ ⊕ b₁ ⊕ c₁
--    [HH] at a₂, h₀ ← 1 ⊕ b₁ ⊕ b₂ ⊕ c₁ ⊕ c₂ ⊕ d₁ ⊕ d₂
--    [HH] at c₀, e₀ ← 0
--
-- The phase has degree 2 -- g is quadratic, so the oracles are Clifford
-- -- and every quotient is a Z₂-linear form: the chain is one of the
-- linear rules of PathSum.Anywhere (_⟶ᵍ_, lemma 4.3's [Elim] and [HH],
-- which PathSum.Cost's polynomial-time normaliser uses), hence of
-- PathSum.Full's _⟶ᶠ_, all of figure 2 at any variables.  The third
-- [HH] substitutes for the output variable h₀ a form in six internal
-- variables, after which every one of the 10 remaining variables
-- b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ h₁ h₂ occurs in an output:
--
--    phase    ½(b₁b₂ + b₂c₁ + b₁c₂ + c₁c₂ + b₁d₁ + c₁d₁ + b₂d₂ + c₂d₂
--               + d₁d₂ + c₁e₁ + c₂e₂ + d₁h₁ + d₂h₂),
--    outputs  0, e₁, e₂, 1 ⊕ b₁ ⊕ b₂ ⊕ c₁ ⊕ c₂ ⊕ d₁ ⊕ d₂, h₁, h₂.
--
-- Every rule eliminates an internal variable (one absent from the
-- outputs), so none applies (PathSum.HiddenShift.Stuck.Machine's
-- occurs⇒irreducible).  The path-sum still denotes |x⟩ ↦ |s⟩ -- the
-- rules are sound (reachable-≋) -- but no chain of rules leads from it
-- to a path-sum without path variables (stuck-incomplete), so this
-- maximal reduction never produces |s⟩.  Hence the statement "every
-- path-sum reachable from the circuit on |0⟩ that is irreducible has no
-- path variables" is false, for figure 2 and for the linear rules alike
-- (not-every-maximal-reduction-complete, its -linear form), and the
-- paper's sentence needs a qualification: the calculus finds |s⟩
-- along a suitable reduction (Exists' three passes, or any complete
-- one), not along every one.  The theorem holds of every path-sum
-- written as the circuit's (PathSum.HiddenShift.Exists' Written: the
-- circuit's 18 path variables, its outputs and its phase modulo 1), not
-- only of the composite (hidden-shift-stuck-written); and figure 2's
-- rules get stuck on the tool's own circuit too, with a cubic g and a
-- non-linear quotient (PathSum.HiddenShift.StuckTool).
--
-- How it is proved.  Nothing reads the composite's polynomials, only
-- its values (PathSum.HiddenShift.Track): the phase is ½F modulo 1 and
-- the outputs G modulo 2, F being hs-parity on |0⟩.  F and G are given
-- in algebraic normal form (PathSum.Polynomial.ANF; the instance and
-- its values, pF₀ and pG₀ with parity-ANF and out-ANF, are
-- PathSum.HiddenShift.Stuck.Instance), and every step's side
-- conditions -- the derivative of F in the eliminated variable is a
-- linear form containing y_i, and no output depends on the variable --
-- are computed and checked by refl, on the normal forms the previous
-- stage carries (PathSum.HiddenShift.Stuck.Linear's stepL), as are the
-- values of the end (endF, endG) and the certificate that every
-- variable occurs in an output (end-occurs).
--
-- How it was found.  At order 1 -- every phase here is ½ times a
-- Boolean polynomial, and the rules keep that -- only [Elim] and [HH]
-- can apply ([ω] and [Case] need a coefficient ¼), and a path-sum is
-- its Boolean phase and outputs.  An exhaustive search over all the
-- path-sums reachable from the circuit on |0⟩ by figure 2's rules,
-- done outside Agda on that representation, found no stuck one at
-- m ≤ 2 (every g, s = 0 and three random shifts), and at m = 3 stuck
-- ones for exactly the g of degree 2 whose quadratic part is
-- x₀x₁ + x₀x₂ + x₁x₂, whatever its terms of degree 0 and 1 (32 of the
-- 512 pairs of g and shift tried, every g of degree at most 3 with two
-- shifts; none with the cubic monomial); in all of them every remaining
-- variable is in an output.  With a cubic g at m = 4 it also found
-- stuck path-sums that only a non-linear [HH] reaches (StuckTool's
-- instance).
--
-- Departures from the paper: none in the statement; the instance is a
-- single m, g and s (a counterexample needs no more), at every
-- precision M₀.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Stuck (M₀ : ℕ) where

open import Data.Bool.Base using (true)
open import Data.Fin using (#_)
open import Data.Integer.Base using (_-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Nat.Base using (suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase)
open import PathSum.Denotation M₀ using (Assign; _≋_; ≋-sym; ≋-trans)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.HiddenShift M₀ using (HS; hs-norm; specᴾ)
open import PathSum.HiddenShift.Exists M₀ using
  (Written; written₀; written-tracks; parity-blocks; out-blocks)
open import PathSum.HiddenShift.Simulation M₀ using (at0; hidden-shift-≋)
open import PathSum.HiddenShift.Stuck.Instance M₀ public using
  (g; s; gᵇ; bool-g; pF₀; pG₀; parity-ANF; out-ANF; endF; endG;
   end-occurs)
open import PathSum.HiddenShift.Stuck.Linear M₀ using (module ReduceL)
open import PathSum.HiddenShift.Stuck.Machine M₀ using
  (tracks-cong; occurs⇒irreducible)
open import PathSum.HiddenShift.Track M₀ using (Tracks; phase-at; out-at)
open import PathSum.Polynomial using (Poly; eval)
open import PathSum.Polynomial.ANF using
  (RM; evalᴿ; eqᴿ; eqᴿ-sound; allFin; allFin-sound)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (_⟶ᵍ*_; εᵍ)
open import PathSum.Anywhere.Match M using (Irreducible)
open import PathSum.Full M using (_⟶ᶠ*_; ⟶ᵍ*⇒⟶ᶠ*)
open import PathSum.Full.Match M using
  (Irreducibleᶠ; Irreducibleᶠ⇒Irreducible)
open import PathSum.Full.Obstruction M using (irreducible-stuck)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)


------------------------------------------------------------------------
-- The reduction of a path-sum written as the circuit's

module _ (ξ₀ : PathSum (3 ℕ+ 3) (hs-norm (3 ℕ+ 3)) (hs-norm (3 ℕ+ 3)))
         (wr : Written g s ξ₀) where

  open ReduceL ξ₀

  private
    -- The values of a written path-sum, from Exists' written-tracks:
    -- the conversions it makes between a path-sum's outputs and their
    -- parities are made there, at a symbolic m, and not here, where the
    -- sizes are numerals and they would unfold every monomial.

    tracks₀ : Tracks ξ₀ (evalᴿ pF₀) (λ w → evalᴿ (pG₀ w))
    tracks₀ = tracks-cong (written-tracks g s ξ₀ wr)
      (λ Y → trans (sym (parity-blocks g s Y)) (parity-ANF Y))
      (λ w Y → trans (sym (out-blocks g s Y w)) (out-ANF w Y))

    -- The first stage, its values named: they cannot be read off
    -- tracks₀, evalᴿ not being injective.

    st₀ : StageL 18 pF₀ pG₀
    st₀ = stageL ξ₀ εᵍ tracks₀

    -- The four steps, each stage named: as one nested term, the side
    -- conditions of the outer steps would be checked against values not
    -- yet known, and retried.

    st₁ : StageL 16 _ _
    st₁ = stepL st₀ (# 0) (# 2) refl refl    -- [HH] at a₀, b₀ ← a₁ ⊕ a₂ ⊕ c₀

    st₂ : StageL 14 _ _
    st₂ = stepL st₁ (# 0) (# 6) refl refl    -- [HH] at a₁, d₀ ← a₂ ⊕ b₁ ⊕ c₁

    st₃ : StageL 12 _ _
    st₃ = stepL st₂ (# 0) (# 10) refl refl   -- [HH] at a₂, h₀ ← 1 ⊕ b₁ ⊕ …

    st₄ : StageL 10 _ _
    st₄ = stepL st₃ (# 2) (# 6) refl refl    -- [HH] at c₀, e₀ ← 0

    -- A stage with ten path variables whose values are endF and endG
    -- is stuck.

    finish : ∀ {pF pG} → StageL 10 pF pG → eqᴿ pF endF ≡ true →
             allFin (λ w → eqᴿ (pG w) (endG w)) ≡ true →
             Σ (PathSum 6 10 10) (λ ζ →
               (ξ₀ ⟶ᵍ* ζ) × Irreducibleᶠ ζ ×
               Tracks ζ (evalᴿ endF) (λ w → evalᴿ (endG w)))
    finish {pF} {pG} st eF eG =
      ξ st , chain st ,
      occurs⇒irreducible (ξ st) {endF} {endG} tr end-occurs , tr
      where
      tr : Tracks (ξ st) (evalᴿ endF) (λ w → evalᴿ (endG w))
      tr = tracks-cong (tracks st)
        (λ y → cong (λ p → evalᴿ p y) (eqᴿ-sound pF endF eF))
        (λ w y → cong (λ p → evalᴿ p y)
          (eqᴿ-sound (pG w) (endG w)
            (allFin-sound (λ w′ → eqᴿ (pG w′) (endG w′)) eG w)))

  -- Four [HH] steps with linear quotients, each followed by an [Elim],
  -- reach a path-sum with ten path variables, phase ½ endF and outputs
  -- endG modulo 2, to which no rule of figure 2 applies.  Each step is
  -- [HH] at the variable at position j, substituting for the one at
  -- position i of the rest, then [Elim] of that one; its side
  -- conditions, and the end's values, are checked by computation.

  hidden-shift-stuck-written :
    Σ (PathSum 6 10 10) (λ ζ →
      (ξ₀ ⟶ᵍ* ζ) × Irreducibleᶠ ζ ×
      Tracks ζ (evalᴿ endF) (λ w → evalᴿ (endG w)))
  hidden-shift-stuck-written = finish st₄ refl refl


------------------------------------------------------------------------
-- The circuit on |0⟩

-- What holds of every path-sum written as the circuit's holds of the
-- circuit on |0⟩ (Exists' written₀).  Stated for every m, so that no
-- type mentioning the closed circuit is compared at a numeral size.

private
  at-circuit : ∀ {m} (g′ : Poly m 0) (s′ : Assign (m ℕ+ m)) {ℓ}
               (P : PathSum (m ℕ+ m) (hs-norm (m ℕ+ m)) (hs-norm (m ℕ+ m)) →
                    Set ℓ) →
               (∀ ξ₀ → Written g′ s′ ξ₀ → P ξ₀) → P (at0 (HS g′ s′))
  at-circuit g′ s′ P f = f (at0 (HS g′ s′)) (written₀ g′ s′)

-- A maximal reduction of the hidden shift circuit on |0⟩ by the linear
-- rules that is not complete: ten path variables are left and no rule
-- of figure 2 applies.

hidden-shift-stuck :
  Σ (PathSum 6 10 10) (λ ζ → (at0 (HS g s) ⟶ᵍ* ζ) × Irreducibleᶠ ζ)
hidden-shift-stuck =
  proj₁ r , proj₁ (proj₂ r) , proj₁ (proj₂ (proj₂ r))
  where
  r = at-circuit g s (λ ξ₀ → Σ (PathSum 6 10 10) (λ ζ →
        (ξ₀ ⟶ᵍ* ζ) × Irreducibleᶠ ζ ×
        Tracks ζ (evalᴿ endF) (λ w → evalᴿ (endG w))))
        hidden-shift-stuck-written

-- So not every irreducible path-sum reachable from it is without path
-- variables, under all of figure 2 ...

not-every-maximal-reduction-complete :
  ¬ (∀ {k′ m′} {ζ : PathSum 6 k′ m′} →
     at0 (HS g s) ⟶ᶠ* ζ → Irreducibleᶠ ζ → m′ ≡ 0)
not-every-maximal-reduction-complete all =
  10≢0 (all (⟶ᵍ*⇒⟶ᶠ* (proj₁ (proj₂ hidden-shift-stuck)))
            (proj₂ (proj₂ hidden-shift-stuck)))
  where
  10≢0 : ¬ (10 ≡ 0)
  10≢0 ()

-- ... and under the linear rules.

not-every-maximal-reduction-complete-linear :
  ¬ (∀ {k′ m′} {ζ : PathSum 6 k′ m′} →
     at0 (HS g s) ⟶ᵍ* ζ → Irreducible ζ → m′ ≡ 0)
not-every-maximal-reduction-complete-linear all =
  10≢0 (all (proj₁ (proj₂ hidden-shift-stuck))
            (Irreducibleᶠ⇒Irreducible (proj₂ (proj₂ hidden-shift-stuck))))
  where
  10≢0 : ¬ (10 ≡ 0)
  10≢0 ()

-- From the stuck path-sum no chain of figure 2's rules reaches one
-- without path variables.

stuck-incomplete : ∀ {k′} {ζ′ : PathSum 6 k′ 0} →
                   ¬ (proj₁ hidden-shift-stuck ⟶ᶠ* ζ′)
stuck-incomplete = irreducible-stuck (proj₁ hidden-shift-stuck)
                                     (proj₂ (proj₂ hidden-shift-stuck))


------------------------------------------------------------------------
-- Whatever is reached still denotes |x⟩ ↦ |s⟩

-- The rules are sound, so every path-sum reachable from the circuit on
-- |0⟩ -- the stuck one above among them -- is equivalent to the
-- specification; a stuck reduction has not gone wrong, it has only
-- not shown it.

reachable-≋ : ∀ {m} (g′ : Poly m 0) (s′ : Assign (m ℕ+ m)) {k′ m′}
              {ζ : PathSum (m ℕ+ m) k′ m′} →
              at0 (HS g′ s′) ⟶ᶠ* ζ → ζ ≋ specᴾ s′
reachable-≋ g′ s′ {ζ = ζ} steps =
  ≋-trans {ξ = ζ} {ζ = at0 (HS g′ s′)} {χ = specᴾ s′}
    (≋-sym {ξ = at0 (HS g′ s′)} {ζ = ζ} (⟶ᶠ*-sound steps))
    (hidden-shift-≋ g′ s′)
