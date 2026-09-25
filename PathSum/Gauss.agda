------------------------------------------------------------------------
-- Presentations of groups
--
-- Reifying the isometry restriction by Gaussian elimination (Amy, QPL
-- 2018, section 4.1 and the proof of corollary 4.4)
--
-- The proof of corollary 4.4 reads: since ⟦C⟧ is well-formed, by
-- lemma 4.1 it suffices to check ⟦C⟧|f(x,y)=x ≡ |x⟩ ↦ |x⟩; "as
-- f(x,y) is linear, we can compute via Gaussian elimination a solution
-- y so that f(x,y) = x for any x -- if no such solution exists,
-- ⟦C⟧ ≢ |x⟩ ↦ |x⟩"; and each substitution y_i ← f_i keeps the order
-- of the phase (lemma 2.13).  For circuits over {H, S, CZ} the
-- restriction is reified by construction (PathSum.Circuit.⟦_⟧ᴿ) and
-- PathSum.CRK.Compile avoids the step by compiling.  This module
-- carries it out for every path-sum whose outputs are Z₂-linear forms.
--
-- Such a path-sum is a PathSum.CRK.Circuit.State -- a phase and, on
-- each wire, a form of PathSum.Linear -- read as a path-sum by
-- PathSum.CRK.Amp.toPS, whose outputs are the liftings of the forms.
-- That is exactly how PathSum.CRK.Circuit builds ⟦ C ⟧, so a circuit
-- over {H, CNOT, R_k, R_k†} plugs in definitionally (⟦ C ⟧ is
-- toPS (proj₂ (run C init))).  The normalisation k plays no part: the
-- elimination never changes it.
--
-- The plan, one path variable at a time (Gauss–Jordan elimination
-- over Z₂ with pivots among the path variables):
--
--  1. Pivot (PathSum.Gauss.Forms.pivot?): a wire w whose form f_w
--     contains a path variable y_j.  Then f_w = y_j ⊕ Q with y_j not
--     in Q, and f_w = x_w forces y_j = x_w ⊕ Q, the form
--     sol = f_w ⊕ x_w ⊕ y_j, which is free of y_j.
--  2. The step (step): substitute sol for y_j in the phase, with the
--     linear-form substitution of PathSum.Polynomial (so lemma 2.13,
--     Order.subst-Ord≤, bounds the order), and drop y_j (Reorder._∖ʸ_,
--     which keeps degrees); in every output containing y_j add the
--     gap f_w ⊕ x_w, which clears y_j, and drop y_j.  Wire w itself
--     becomes x_w (step-solves), and a wire that already read its
--     input still does (step-keeps).
--  3. Diagonal preservation (step-amp, step-diag).  Over a path g of
--     the reduct, ξ has two paths, y_j = 0 and y_j = 1.  Exactly one of
--     them, y_j = pick g, makes wire w read x_w; along it every output
--     and the phase agree with the reduct's at g (val-step,
--     eval-step), and along the other wire w reads ¬x_w (miss-step).
--     So every entry from x to a z with z_w = x_w is preserved, the
--     diagonal in particular -- not the whole operator: the reduct is
--     not equivalent to ξ, only its restriction is.
--  4. Iterate (gauss) until no output mentions a path variable; this
--     terminates since each step removes one.  Each step also settles
--     its pivot's wire -- its form loses every path variable, for good
--     (settled-step) -- so at most n path variables are removed
--     (reified-removes): section 4.1's "instantly removing up to n
--     path variables".
--  5. Then every output is a form in the inputs alone.  Either every
--     one of them is x_w, and the restriction is reified: restrict
--     final, with the identity's outputs μ x_w, the phase elimination
--     left, and only internal path variables.  Or some form reads ¬x_w
--     at an input x that Forms.verdict exhibits; no path returns x
--     and the diagonal entry at x vanishes -- "no such solution
--     exists".
--
-- The results: gauss st is either refuted x, with amp at (x , x)
-- equal to 0, whence toPS st ≢ |x⟩ ↦ |x⟩ with no hypothesis (refute,
-- through the forward half of lemma 4.1), or a Reified record: the
-- final state, the diagonal chain, the order bound and the solved
-- outputs.  Its restriction ξᴿ has the same diagonal as the original
-- path-sum (reified-diag), keeps any order bound on the phase
-- (reified-Ord≤: the proof's "ord(P[y_i ← f_i]) ≤ ord(P)"), has only
-- internal path variables (reified-Internal) and is diagonal, so by
-- lemma 4.1 at a well-formed path-sum and Isometry.diagonal-≋ at ξᴿ,
-- toPS st ≋ |x⟩ ↦ |x⟩ exactly when ξᴿ ≋ |x⟩ ↦ |x⟩ (reified-≋).
-- reification packages the two outcomes; reification-circuit states
-- it at ⟦ C ⟧ for every circuit over {H, CNOT, R_k, R_k†}, with the
-- order bound of proposition 2.14.
--
-- Departures and remarks.  The paper's section 4.1 says that when
-- f_i(x,y) = y_i ⊕ Q(x,y) "we can substitute Q(x,y) for y_i to get
-- f_i(x,y) = x_i"; that is a slip, the substitution that does so being
-- y_i ← x_i ⊕ Q (substituting Q gives f_i = 0), which is sol above.
-- The same wire index i for the output and the path variable is loose
-- notation: any output containing any path variable is a pivot here.
-- Section 4.1 ignores "restrictions
-- which can't be reified"; here, the outputs being linear, none is
-- ignored: elimination either reifies the whole restriction or
-- refutes.  Gaussian elimination is formalised as the sequence of row
-- operations above, not as a matrix algorithm, and its polynomial
-- running time -- like every complexity claim of the paper -- is not
-- formalised.  The reduction of ξᴿ by lemma 4.3 that completes the
-- corollary is in PathSum.Gauss.Corollary.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Gauss (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-same; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (outside)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; ≤-reflexive)
open import Data.Nat.Base using (zero; suc; _⊔_; _≤_)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (_∷_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (Ord≤-front)
open import PathSum.Anywhere.Sound M₀ using (Σᴮ-insert; hits-outBit)
open import PathSum.Assign using (_[_≔_]; same-intro)
open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; idPS; Internal)
open import PathSum.CRK.Amp M₀ using (toPS; ampᴸ; outBit-liftᴸ)
open import PathSum.CRK.Circuit M using
  (State; state; poly; sig; Circuit; norm; level; run; init; ⟦_⟧;
   prop-2-14)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; Σᴮ-cong; Σᴮ-+; Σᴮ-0; Respects; extend; zpow;
   scale; zpow-0≢0ᴬ; √2·-injective; √2·-0ᴬ)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; hits-elim; hits-≗³; outBit-μ; eval-false)
open import PathSum.Gauss.Forms
open import PathSum.Isometry M₀ using
  (WellFormed; Diagonal; lemma-4-1; lemma-4-1⇒; diagonal-≋)
open import PathSum.Linear using
  (Lin; valᴸ; liftᴸ; varᴸ; _⊕ᴸ_; eval-liftᴸ; valᴸ-⊕; valᴸ-var)
open import PathSum.Order M using (Ord≤; subst-Ord≤)
open import PathSum.Polynomial using (Poly; x[_]; y[_]; μ; eval; liftXor)
open import PathSum.Polynomial.Properties using (eval-cong; eval-ext)
open import PathSum.Polynomial.Substitution using
  (substᴾ; subst≡substᴾ; eval-substᴾ-≔; Absent-μ; Absent⇒NoVar)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; frontᴾ; _∖ʸ_; eval-front)

import Data.Nat.Properties as ℕ
import PathSum.CRK.Semantics
import PathSum.Polynomial as P

private
  module Sem = PathSum.CRK.Semantics M₀

  variable
    d n m k : ℕ


------------------------------------------------------------------------
-- Amplitudes

private
  if-cong : {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl _   = λ _ → refl

  if-false : (p : Bool) (a : Amp) → p ≡ false → (if p then a else 0ᴬ) ≐ 0ᴬ
  if-false false _ _ _ = refl
  if-false true  _ () _

  zpow-≡ : {a b : ℤ} → a ≡ b → zpow a ≐ zpow b
  zpow-≡ refl _ = refl

  not-xor : ∀ b → not b xor b ≡ true
  not-xor false = refl
  not-xor true  = refl

  -- √2^j ζ^0 is never zero.  (PathSum.Identity proves this too,
  -- privately.)

  scale-zpow0≢0 : ∀ j → ¬ (scale j (zpow 0ℤ) ≐ 0ᴬ)
  scale-zpow0≢0 zero    eq = zpow-0≢0ᴬ eq
  scale-zpow0≢0 (suc j) eq = scale-zpow0≢0 j
    (√2·-injective (scale j (zpow 0ℤ)) 0ᴬ
      (λ i → trans (eq i) (sym (√2·-0ᴬ i))))

-- The amplitudes of a linear path-sum do not read its normalisation:
-- CRK.Amp's ampᴸ fixes it at 0.

amp-toPS : (st : State n m) (x z : Assign n) →
           amp (toPS {k = k} st) x z ≐ ampᴸ st x z
amp-toPS st x z _ = refl


------------------------------------------------------------------------
-- Dropping a path variable from a polynomial

-- Q ∖ʸ j is the part of Q free of y_j, over the other variables: its
-- terms keep their degrees, and it reads what Q reads with y_j set to
-- 0 -- which, once y_j has been substituted away, is what Q reads.

Ord≤-∖ʸ : (j : Fin (suc m)) {Q : Poly n (suc m)} →
          Ord≤ d Q → Ord≤ d (Q ∖ʸ j)
Ord≤-∖ʸ j ordQ (α , s) = Ord≤-front j ordQ (α , outside ∷ s)

eval-∖ʸ : (j : Fin (suc m)) (Q : Poly n (suc m)) (x : Assign n)
          (g : Assign m) → eval (Q ∖ʸ j) x g ≡ eval Q x (insertᵃ j false g)
eval-∖ʸ j Q x g =
  trans (sym (eval-false (frontᴾ j Q) x g)) (eval-front j Q x (extend false g))


------------------------------------------------------------------------
-- One elimination step

-- The gap of wire w, f_w ⊕ x_w: 0 exactly on the paths where the wire
-- reads its input.

gap : State n m → Fin n → Lin n m
gap st w = sig st w ⊕ᴸ varᴸ x[ w ]

-- The value y_j must take for wire w to read x_w: f_w ⊕ x_w ⊕ y_j,
-- free of y_j when y_j occurs in f_w.

sol : State n (suc m) → Fin n → Fin (suc m) → Lin n (suc m)
sol st w j = gap st w ⊕ᴸ varᴸ y[ j ]

-- Eliminate y_j by the pivot on wire w: substitute sol for y_j in the
-- phase (lemma 2.13's substitution of a linear form) and drop it; add
-- the gap to every output containing y_j, and drop y_j there too.

step : State n (suc m) → Fin n → Fin (suc m) → State n m
step st w j = state
  (P.subst (poly st) y[ j ] (proj₁ (sol st w j)) (proj₂ (sol st w j)) ∖ʸ j)
  (λ v → dropᴸ j (elimᴸ j (gap st w) (sig st v)))

-- Over a path g of the reduct, the value of y_j on the path of the
-- original that the reduct keeps.

pick : State n (suc m) → Fin n → Fin (suc m) → Assign n → Assign m → Bool
pick st w j x g = valᴸ (sol st w j) x (insertᵃ j false g)

-- Lemma 2.13: the step does not raise the order of the phase.

step-Ord≤ : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
            Ord≤ d (poly st) → Ord≤ d (poly (step st w j))
step-Ord≤ st w j ordP = Ord≤-∖ʸ j
  (subst-Ord≤ (poly st) y[ j ] (proj₁ (sol st w j)) (proj₂ (sol st w j))
              ordP)


------------------------------------------------------------------------
-- The two paths over a path of the reduct

module _ {n m : ℕ} (st : State n (suc m)) (w : Fin n) (j : Fin (suc m))
         (piv : coefʸ (sig st w) j ≡ true) where

  private
    coef-gap : coefʸ (gap st w) j ≡ true
    coef-gap = trans (coefʸ-⊕ (sig st w) (varᴸ x[ w ]) j)
                     (cong₂ _xor_ piv (coefʸ-x w j))

    coef-sol : coefʸ (sol st w j) j ≡ false
    coef-sol = trans (coefʸ-⊕ (gap st w) (varᴸ y[ j ]) j)
                     (cong₂ _xor_ coef-gap (coefʸ-y {n = n} j))

    val-gap : ∀ x y → valᴸ (gap st w) x y ≡ valᴸ (sig st w) x y xor x w
    val-gap x y = trans (valᴸ-⊕ (sig st w) (varᴸ x[ w ]) x y)
      (cong (valᴸ (sig st w) x y xor_) (valᴸ-var x[ w ] x y))

    val-sol : ∀ x y → valᴸ (sol st w j) x y ≡ valᴸ (gap st w) x y xor y j
    val-sol x y = trans (valᴸ-⊕ (gap st w) (varᴸ y[ j ]) x y)
      (cong (valᴸ (gap st w) x y xor_) (valᴸ-var y[ j ] x y))

    -- sol does not read y_j, so it reads pick on both paths.

    sol-free : ∀ x g b → valᴸ (sol st w j) x (insertᵃ j b g) ≡ pick st w j x g
    sol-free x g b = trans (valᴸ-drop (sol st w j) j b x g coef-sol)
      (sym (valᴸ-drop (sol st w j) j false x g coef-sol))

    -- Hence the gap reads pick ⊕ y_j.

    gap-at : ∀ x g b → valᴸ (gap st w) x (insertᵃ j b g) ≡ pick st w j x g xor b
    gap-at x g b = xor-solve (valᴸ (gap st w) x y) b (pick st w j x g)
      (trans (cong (valᴸ (gap st w) x y xor_) (sym (insertᵃ-here j b g)))
             (trans (sym (val-sol x y)) (sol-free x g b)))
      where
      y = insertᵃ j b g

    gap-live : ∀ x g b → pick st w j x g ≡ b →
               valᴸ (gap st w) x (insertᵃ j b g) ≡ false
    gap-live x g b eq =
      trans (gap-at x g b) (trans (cong (_xor b) eq) (xor-same b))

    gap-dead : ∀ x g b → pick st w j x g ≡ not b →
               valᴸ (gap st w) x (insertᵃ j b g) ≡ true
    gap-dead x g b eq =
      trans (gap-at x g b) (trans (cong (_xor b) eq) (not-xor b))

  -- On the kept path every output reads what the reduct's reads.

  val-step : ∀ v x g b → pick st w j x g ≡ b →
             valᴸ (sig (step st w j) v) x g ≡ valᴸ (sig st v) x (insertᵃ j b g)
  val-step v x g b eq = trans
    (sym (valᴸ-drop (elimᴸ j (gap st w) (sig st v)) j b x g
                    (coefʸ-elimᴸ j (gap st w) (sig st v) coef-gap)))
    (valᴸ-elimᴸ j (gap st w) (sig st v) x (insertᵃ j b g) (gap-live x g b eq))

  -- On the other one wire w misses its input.

  miss-step : ∀ x g b → pick st w j x g ≡ not b →
              valᴸ (sig st w) x (insertᵃ j b g) ≡ not (x w)
  miss-step x g b eq = xor-solve (valᴸ (sig st w) x y) (x w) true
    (trans (sym (val-gap x y)) (gap-dead x g b eq))
    where
    y = insertᵃ j b g

  -- On the kept path the phase is the reduct's: substituting sol for
  -- y_j is evaluating at y_j = pick.

  eval-step : ∀ x g b → pick st w j x g ≡ b →
              eval (poly (step st w j)) x g ≡ eval (poly st) x (insertᵃ j b g)
  eval-step x g b eq = trans (eval-∖ʸ j Q x g)
    (trans (eval-ext Q (substᴾ (poly st) y[ j ] L)
                     (subst≡substᴾ (poly st) y[ j ] (proj₁ s) (proj₂ s)) x y)
    (trans (eval-substᴾ-≔ (poly st) j L x y (valᴸ s x y)
                          (sym (eval-liftᴸ s x y)))
           (eval-cong (poly st) {x} {x} {y [ j ≔ valᴸ s x y ]}
                      {insertᵃ j b g} (λ _ → refl) (λ i →
             trans (≔-insertᵃ j false (valᴸ s x y) g i)
                   (cong (λ c → insertᵃ j c g i) eq)))))
    where
    s = sol st w j
    L = liftXor (proj₁ s) (proj₂ s)
    Q = P.subst (poly st) y[ j ] (proj₁ s) (proj₂ s)
    y = insertᵃ j false g

  -- The step solves wire w, and a wire that read its input still does.

  step-solves : ∀ x g → valᴸ (sig (step st w j) w) x g ≡ x w
  step-solves x g = trans (val-step w x g (pick st w j x g) refl)
    (xor-solve (valᴸ (sig st w) x y) (x w) false
      (trans (sym (val-gap x y)) (gap-live x g (pick st w j x g) refl)))
    where
    y = insertᵃ j (pick st w j x g) g

  step-keeps : (v : Fin n) → (∀ x y → valᴸ (sig st v) x y ≡ x v) →
               ∀ x g → valᴸ (sig (step st w j) v) x g ≡ x v
  step-keeps v h x g = trans (val-step v x g (pick st w j x g) refl)
                             (h x (insertᵃ j (pick st w j x g) g))

  -- Every entry from x to an output agreeing with x on wire w is
  -- preserved.  The sum over the paths of the original splits at y_j
  -- (Anywhere.Sound.Σᴮ-insert); over each path g of the reduct, the
  -- kept path contributes the reduct's term and the other one nothing.

  step-amp : ∀ x z → z w ≡ x w → ampᴸ st x z ≐ ampᴸ (step st w j) x z
  step-amp x z zw i = trans (Σᴮ-insert j T respT i)
    (trans (sym (Σᴮ-+ (λ g → T (insertᵃ j true g))
                      (λ g → T (insertᵃ j false g)) i))
           (Σᴮ-cong per i))
    where
    ξ : PathSum n 0 (suc m)
    ξ = toPS st

    ξ′ : PathSum n 0 m
    ξ′ = toPS (step st w j)

    T : Assign (suc m) → Amp
    T y = if hits ξ x y z then zpow (eval (poly st) x y) else 0ᴬ

    T′ : Assign m → Amp
    T′ g = if hits ξ′ x g z then zpow (eval (poly (step st w j)) x g) else 0ᴬ

    respT : Respects T
    respT g h g≗h = if-cong
      (hits-≗³ ξ {x} {x} {g} {h} {z} {z} (λ _ → refl) g≗h (λ _ → refl))
      (zpow-≡ (eval-cong (poly st) {x} {x} {g} {h} (λ _ → refl) g≗h))

    live : ∀ g b → pick st w j x g ≡ b → T (insertᵃ j b g) ≐ T′ g
    live g b eq = if-cong
      (hits-outBit ξ ξ′ x (insertᵃ j b g) g z (λ v →
        trans (outBit-liftᴸ ξ x (insertᵃ j b g) v (sig st v) refl)
          (trans (sym (val-step v x g b eq))
                 (sym (outBit-liftᴸ ξ′ x g v (sig (step st w j) v) refl)))))
      (zpow-≡ (sym (eval-step x g b eq)))

    dead : ∀ g b → pick st w j x g ≡ not b → T (insertᵃ j b g) ≐ 0ᴬ
    dead g b eq = if-false (hits ξ x y z) (zpow (eval (poly st) x y))
                           (miss (hits ξ x y z) refl)
      where
      y = insertᵃ j b g

      miss : ∀ h → hits ξ x y z ≡ h → h ≡ false
      miss false _ = refl
      miss true  e = contradiction
        (trans (sym (miss-step x g b eq))
          (trans (sym (outBit-liftᴸ ξ x y w (sig st w) refl))
                 (trans (hits-elim ξ x y z e w) zw)))
        (not-≢ (x w))

    per : ∀ g → (T (insertᵃ j true g) +ᴬ T (insertᵃ j false g)) ≐ T′ g
    per g = by (pick st w j x g) refl
      where
      by : ∀ b → pick st w j x g ≡ b →
           (T (insertᵃ j true g) +ᴬ T (insertᵃ j false g)) ≐ T′ g
      by true  eq i = trans (cong₂ _+_ (live g true eq i) (dead g false eq i))
                            (+-identityʳ (T′ g i))
      by false eq i = trans (cong₂ _+_ (dead g true eq i) (live g false eq i))
                            (+-identityˡ (T′ g i))

  -- The diagonal in particular: the step preserves the isometry
  -- restriction.

  step-diag : ∀ x → amp (toPS {k = k} st) x x ≐
                    amp (toPS {k = k} (step st w j)) x x
  step-diag x = step-amp x x refl


------------------------------------------------------------------------
-- Settled wires

-- The wires whose forms mention no path variable.  A step settles its
-- pivot's wire and unsettles none, so there are at most n steps.

settled : State n m → ℕ
settled st = countᵂ (λ w → pathfree (sig st w))

settled-≤ : (st : State n m) → settled st ≤ n
settled-≤ st = countᵂ-≤ (λ w → pathfree (sig st w))

settled-step : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
               coefʸ (sig st w) j ≡ true →
               suc (settled st) ≤ settled (step st w j)
settled-step st w j piv = countᵂ-grow
  (λ v → pathfree (sig st v)) (λ v → pathfree (sig (step st w j) v))
  stays w (unsettled (pathfree (sig st w)) refl)
  (pathfree-pivot j (gap st w) (sig st w) piv (λ i →
    trans (coefʸ-⊕ (sig st w) (varᴸ x[ w ]) i)
      (trans (cong (coefʸ (sig st w) i xor_) (coefʸ-x w i))
             (xor-identityʳ (coefʸ (sig st w) i)))))
  where
  stays : ∀ v → pathfree (sig st v) ≡ true →
          pathfree (sig (step st w j) v) ≡ true
  stays v pf = trans
    (cong (λ l → pathfree (dropᴸ j l))
          (elimᴸ-off j (gap st w) (sig st v) (pathfree-true (sig st v) pf j)))
    (pathfree-drop j (sig st v) pf)

  unsettled : ∀ b → pathfree (sig st w) ≡ b → b ≡ false
  unsettled false _ = refl
  unsettled true  e =
    contradiction (trans (sym piv) (pathfree-true (sig st w) e j)) λ ()


------------------------------------------------------------------------
-- The elimination

-- What elimination leaves when it reifies the restriction: a state
-- with the same diagonal, a phase of no higher order, and every output
-- reading its input; and, for the count, every path variable removed
-- settled a wire.

record Reified {n m : ℕ} (st : State n m) : Set where
  field
    m′     : ℕ
    final  : State n m′
    diag   : ∀ x → ampᴸ st x x ≐ ampᴸ final x x
    order  : ∀ {d} → Ord≤ d (poly st) → Ord≤ d (poly final)
    solved : ∀ w x y → valᴸ (sig final w) x y ≡ x w
    budget : m ℕ+ settled st ≤ m′ ℕ+ settled final

-- Either an input at which the diagonal entry is 0, or the reified
-- restriction.

data Gauss {n m : ℕ} (st : State n m) : Set where
  refuted : (x : Assign n) → ampᴸ st x x ≐ 0ᴬ → Gauss st
  reduced : Reified st → Gauss st

-- Where some output reads the opposite of its input on every path, no
-- path returns that input.

amp-miss : (st : State n m) (w : Fin n) (x : Assign n) →
           (∀ y → valᴸ (sig st w) x y ≡ not (x w)) → ampᴸ st x x ≐ 0ᴬ
amp-miss {m = m} st w x miss i = trans (Σᴮ-cong term i) (Σᴮ-0 {m} i)
  where
  ξ : PathSum _ 0 m
  ξ = toPS st

  term : ∀ y → (if hits ξ x y x then zpow (eval (poly st) x y) else 0ᴬ) ≐ 0ᴬ
  term y = if-false (hits ξ x y x) (zpow (eval (poly st) x y))
                    (no-hit (hits ξ x y x) refl)
    where
    no-hit : ∀ h → hits ξ x y x ≡ h → h ≡ false
    no-hit false _ = refl
    no-hit true  e = contradiction
      (trans (sym (miss y))
        (trans (sym (outBit-liftᴸ ξ x y w (sig st w) refl))
               (hits-elim ξ x y x e w)))
      (not-≢ (x w))

-- No output mentions a path variable: each is a form in the inputs,
-- and either all of them read their inputs or one refutes.

private
  finish : (st : State n m) → (∀ w j → coefʸ (sig st w) j ≡ false) →
           Gauss st
  finish {n = n} {m = m} st free =
    by (some-or-all (λ w → verdict (sig st w) w (free w)))
    where
    by : (∃ λ w → ∃ λ x → ∀ y → valᴸ (sig st w) x y ≡ not (x w)) ⊎
         (∀ w x y → valᴸ (sig st w) x y ≡ x w) → Gauss st
    by (inj₁ (w , x , miss)) = refuted x (amp-miss st w x miss)
    by (inj₂ solved)         = reduced (record
      { m′ = m ; final = st ; diag = λ _ _ → refl ; order = λ o → o
      ; solved = solved ; budget = ℕ.≤-refl })

  -- A step, followed by the elimination of the reduct.

  back : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
         coefʸ (sig st w) j ≡ true → Gauss (step st w j) → Gauss st
  back st w j piv (refuted x z) =
    refuted x (λ i → trans (step-amp st w j piv x x refl i) (z i))
  back {m = m} st w j piv (reduced r) = reduced (record
    { m′     = Reified.m′ r
    ; final  = Reified.final r
    ; diag   = λ x i → trans (step-amp st w j piv x x refl i)
                             (Reified.diag r x i)
    ; order  = λ {d} o → Reified.order r {d} (step-Ord≤ {d = d} st w j o)
    ; solved = Reified.solved r
    ; budget = ℕ.≤-trans
        (ℕ.≤-reflexive (sym (ℕ.+-suc m (settled st))))
        (ℕ.≤-trans (ℕ.+-monoʳ-≤ m (settled-step st w j piv))
                   (Reified.budget r))
    })

-- Gaussian elimination: a total function, by recursion on the number
-- of path variables.

mutual
  gauss : (st : State n m) → Gauss st
  gauss st = gauss-by st (pivot? (sig st))

  gauss-by : (st : State n m) → Pivot (sig st) → Gauss st
  gauss-by {m = zero}  st (pivot w () _)
  gauss-by {m = suc m} st (pivot w j piv) =
    back st w j piv (gauss (step st w j))
  gauss-by             st (none free)     = finish st free


------------------------------------------------------------------------
-- The reified restriction

-- The phase that elimination leaves, and the identity's outputs.

restrict : State n m → PathSum n k m
restrict st = ⟨ poly st , (λ w → μ x[ w ]) ⟩

restrict-Internal : (st : State n m) → Internal (restrict {k = k} st)
restrict-Internal st j w = Absent⇒NoVar {v = y[ j ]} {P = μ x[ w ]}
  (Absent-μ x[ w ] y[ j ] ∉⊥)

restrict-Diagonal : (st : State n m) → Diagonal (restrict {k = k} st)
restrict-Diagonal {k = k} st x y z h = same-intro x z (λ w →
  trans (sym (outBit-μ (restrict {k = k} st) x y w x[ w ] refl))
        (hits-elim (restrict {k = k} st) x y z h w))

-- Once every output reads its input, replacing the outputs by the
-- input variables changes no amplitude.

restrict-amp : (st : State n m) → (∀ w x y → valᴸ (sig st w) x y ≡ x w) →
               ∀ x z → ampᴸ st x z ≐ amp (restrict {k = k} st) x z
restrict-amp {k = k} st solved x z = Σᴮ-cong (λ y → if-cong
  (hits-outBit (toPS {k = 0} st) (restrict {k = k} st) x y y z (λ v →
    trans (outBit-liftᴸ (toPS {k = 0} st) x y v (sig st v) refl)
      (trans (solved v x y)
             (sym (outBit-μ (restrict {k = k} st) x y v x[ v ] refl)))))
  (λ _ → refl))

module _ {n m : ℕ} {st : State n m} (r : Reified st) where

  open Reified r

  ξᴿ : PathSum n k m′
  ξᴿ = restrict final

  -- The restriction of toPS st and ξᴿ have the same diagonal.

  reified-diag : ∀ x → amp (toPS {k = k} st) x x ≐ amp (ξᴿ {k = k}) x x
  reified-diag {k = k} x i =
    trans (diag x i) (restrict-amp {k = k} final solved x x i)

  -- ord(P[y_i ← f_i]) ≤ ord(P).

  reified-Ord≤ : Ord≤ d (poly st) → Ord≤ d (phase (ξᴿ {k = k}))
  reified-Ord≤ = order

  reified-Internal : Internal (ξᴿ {k = k})
  reified-Internal {k = k} = restrict-Internal {k = k} final

  reified-out : ∀ w → out (ξᴿ {k = k}) w ≡ μ x[ w ]
  reified-out w = refl

  -- Section 4.1's "removing up to n path variables": each variable
  -- removed settled a wire.

  reified-removes : m ≤ m′ ℕ+ n
  reified-removes = ℕ.≤-trans (ℕ.m≤m+n m (settled st))
    (ℕ.≤-trans budget (ℕ.+-monoʳ-≤ m′ (settled-≤ final)))

  -- Lemma 4.1 at toPS st, and ξᴿ being diagonal: toPS st is the
  -- identity exactly when ξᴿ is.

  reified-≋ : WellFormed (toPS {k = k} st) →
              (toPS {k = k} st ≋ idPS ⇔ ξᴿ {k = k} ≋ idPS)
  reified-≋ {k = k} wf = mk⇔
    (λ eq → Equivalence.from
      (diagonal-≋ (ξᴿ {k = k}) (restrict-Diagonal {k = k} final))
      (λ x i → trans (sym (reified-diag {k = k} x i))
                     (lemma-4-1⇒ (toPS {k = k} st) eq x i)))
    (λ eq → Equivalence.from (lemma-4-1 (toPS {k = k} st) wf)
      (λ x i → trans (reified-diag {k = k} x i)
                     (lemma-4-1⇒ (ξᴿ {k = k}) eq x i)))


------------------------------------------------------------------------
-- The refutation

-- A vanishing diagonal entry refutes the identity: the identity's is
-- √2^k ζ^0 (lemma 4.1, forward), which is not 0.  No well-formedness
-- is needed.

refute : (st : State n m) (x : Assign n) → ampᴸ st x x ≐ 0ᴬ →
         ¬ (toPS {k = k} st ≋ idPS)
refute {k = k} st x z eq =
  scale-zpow0≢0 k (λ i →
    trans (sym (lemma-4-1⇒ (toPS {k = k} st) eq x i)) (z i))


------------------------------------------------------------------------
-- The verdict of elimination

-- Either toPS st is not the identity, or its restriction is reified
-- as a path-sum with the identity's outputs, only internal path
-- variables and a phase of no higher order, which is the identity
-- exactly when toPS st is.

Reification : (st : State n m) → ℕ → Set
Reification {n} st k =
  ¬ (toPS {k = k} st ≋ idPS) ⊎
  ∃ λ m′ → ∃ λ (ξ′ : PathSum n k m′) →
    Internal ξ′ × (∀ w → out ξ′ w ≡ μ x[ w ]) ×
    (∀ {d} → Ord≤ d (poly st) → Ord≤ d (phase ξ′)) ×
    (toPS {k = k} st ≋ idPS ⇔ ξ′ ≋ idPS)

reification : (st : State n m) → WellFormed (toPS {k = k} st) →
              Reification st k
reification {k = k} st wf = by (gauss st)
  where
  by : Gauss st → Reification st k
  by (refuted x z) = inj₁ (refute {k = k} st x z)
  by (reduced r)   = inj₂ (Reified.m′ r , ξᴿ r {k = k} ,
    reified-Internal r {k = k} , reified-out r {k = k} ,
    (λ {d} → reified-Ord≤ r {d = d} {k = k}) , reified-≋ r {k = k} wf)


------------------------------------------------------------------------
-- Circuits over {H, CNOT, R_k, R_k†}

-- ⟦ C ⟧ is, by definition, the path-sum of the state the circuit runs
-- to, so elimination applies to it; its columns have unit norm
-- (PathSum.CRK.Semantics), and its phase has order at most
-- max(2, level C) (proposition 2.14 as corrected in
-- PathSum.CRK.Circuit).

⟦⟧-state : (C : Circuit n) → ⟦ C ⟧ ≡ toPS (proj₂ (run C init))
⟦⟧-state C = refl

Reification-circuit : Circuit n → Set
Reification-circuit {n} C =
  ¬ (⟦ C ⟧ ≋ idPS) ⊎
  ∃ λ m′ → ∃ λ (ξ′ : PathSum n (norm C) m′) →
    Internal ξ′ × (∀ w → out ξ′ w ≡ μ x[ w ]) ×
    Ord≤ (2 ⊔ level C) (phase ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)

reification-circuit : (C : Circuit n) → Reification-circuit C
reification-circuit C = by
  (reification {k = norm C} (proj₂ (run C init))
    (λ x → ≤-reflexive (Sem.⟦⟧-unit-columns C x)))
  where
  by : Reification (proj₂ (run C init)) (norm C) → Reification-circuit C
  by (inj₁ ¬id) = inj₁ ¬id
  by (inj₂ (m′ , ξ′ , int , outs , ord , iff)) =
    inj₂ (m′ , ξ′ , int , outs , ord {2 ⊔ level C} (prop-2-14 C) , iff)
