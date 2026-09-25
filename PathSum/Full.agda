------------------------------------------------------------------------
-- Presentations of groups
--
-- All of figure 2 at any internal path variables
--
-- Figure 2 of Amy's paper (QPL 2018) states four rules, [Elim], [ω],
-- [HH] and [Case], "applied to path-sums in the obvious way": the
-- first three at an internal path variable y₀, which may be any of
-- them, and [Case] at any two internal variables y_i and y_j.  Two
-- partial calculi existed before this module: _⟶ᵍ_ of
-- PathSum.Anywhere has the rules of PathSum.Reduction -- [Elim], and
-- [ω] and [HH] with Z₂-linear quotients -- at any variable, and _⟶ᴳ_
-- of PathSum.Reduction.General has all four rules, with Boolean-valued
-- quotients, but at the head only.  Here they are combined:
--
--    ξ ⟶ᶠ ζ  =  Anywhere (Anywhere _⟶ᴳ_) ξ ζ,
--
-- a rule of _⟶ᴳ_ applied after renumbering the path variables by at
-- most two single renumberings (PathSum.Reorder.front).
--
-- Why two renumberings, nested.  A rule at one variable y_j is a head
-- rule on front j ξ, which lists y_j first and the others in order:
-- the derivation at j ∘ plain.  [Case] at an ordered pair (y_i , y_j)
-- of distinct variables is the head [Case] on front₂ i j i≢j ξ =
-- front (suc (skip i≢j)) (front j ξ), which lists y_i, then y_j, then
-- the others in order (PathSum.Reorder.Pair): the derivation
-- at j ∘ at (suc (skip i≢j)).  Nesting PathSum.Anywhere's generic
-- Anywhere gives both at once and needs no new calculation: soundness
-- is Anywhere.Sound.Anywhere-sound applied twice to Reduction.Sound's
-- ⟶ᴳ-sound, and termination is Anywhere-< applied twice to Reduction.
-- General's ⟶ᴳ-dec.  A dedicated relation with a front₂ constructor
-- was the alternative; it would need soundness and termination lemmas
-- of its own and would give the same steps.  The renumberings stay
-- folded into the steps -- no step only renumbers, and every step
-- removes at least one path variable -- because renumbering is a
-- bijection and a step of its own would make the calculus
-- non-terminating (Reorder.frontᴾ-swap).
--
-- The price is redundancy, and it is harmless.  A step can have more
-- than one derivation (plain ∘ at j and at j ∘ plain are the same rule
-- at y_j), and a one-variable rule can be applied under two
-- renumberings, at j ∘ at (suc i′): at the variable y_(punchIn j i′),
-- with the remaining variables listed y_j first.  That is a rule at
-- one variable followed by a renumbering of its reduct, so _⟶ᶠ_ is
-- figure 2 at every variable and every pair, closed under renumbering
-- a reduct once.
-- Every step is still sound and still removes a variable, so none of
-- the statements below is weaker for it; the smart constructors build
-- the canonical steps, whose reducts keep the remaining variables in
-- their original order.
--
-- What is proved here.
--
-- * Embeddings: ⟶ᵍ⇒⟶ᶠ (the linear rules at any variable) and ⟶ᴳ⇒⟶ᶠ
--   (all four rules at the head), and PathSum.Reduction's _⟶_ through
--   either (⟶⇒⟶ᶠ); likewise for chains.
-- * Smart constructors that state the paper's premises at the chosen
--   variables.  elimAtᶠ, ωAtᶠ and hhAtᶠ act at y_j: the quotient of the
--   phase by y_j is phase ξ /ʸ j, and y_j is absent from every output.
--   Their quotient Q and [HH]'s substituted variable y_i are in the
--   numbering of the remaining variables (y_i is the original
--   y_(punchIn j i)), as in Anywhere.hhAt.  caseAtᶠ acts at (y_i , y_j)
--   for any i ≢ j: its coefficient premises are about the quarters
--   q₁₁ʸ, q₁₀ʸ and q₀₁ʸ of the phase in y_i and y_j, both variables are
--   absent from every output, and X, Q and Q′ are polynomials in the
--   other variables, in their original order.
-- * Proposition 3.2.  Every step removes one path variable, or two for
--   [Case] (⟶ᶠ-removes), so _⟶ᶠ_ is strongly normalising (⟶ᶠ-SN), and a
--   chain from m to m′ path variables has at most m − m′ steps
--   (⟶ᶠ*-length), so at most m (⟶ᶠ*-bounded), and at least half of
--   m − m′ (⟶ᶠ*-length-lower): its length is linear in m, both ways.
--   That the chain can be continued to an irreducible path-sum is
--   PathSum.Full.Match (one-step reducibility is decidable, for all
--   four rules); the claim that matching and normalisation take
--   polynomial time is not formalised.
-- * Renumbering a pair keeps the order of the phase (Ord≤-front₂).
--
-- Proposition 3.1 for this calculus is PathSum.Full.Sound; the
-- quotients a rule needs are read off the phase by
-- PathSum.Full.Canonical; the circuit verdicts along its chains are
-- PathSum.Full.Corollary, and corollary 4.4 at every irreducible end
-- is PathSum.Full.Clifford.  The departures from the paper are those
-- of PathSum.Reduction.General (the premises of [Case] read off the
-- quarters of the phase; Boolean-valued quotients given as polynomials
-- with integer coefficients; X for the paper's input variable x), and
-- the numbering of a reduct's path variables, which is the remaining
-- ones in their original order.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full (M : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (1ℤ; +_)
open import Data.Nat.Base using (zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; n≤1+n; +-suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; cong)

open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Order M using (Ord≤; pow)
open import PathSum.Polynomial using
  (Poly; y[_]; 0ᴾ; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Polynomial.Boolean using (BoolValued)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Reduction M using
  (_⟶_; _⟶*_; ε; _◅_; elim-reduct; ¼; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; _⟶ᴳ*_; εᴳ; _◅ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; ωᴳ-reduct; hhᴳ-reduct;
   case-reduct; ⟶⇒⟶ᴳ; ⟶ᴳ-dec)
open import PathSum.Reorder using (front; _/ʸ_; NoVar-front)
open import PathSum.Reorder.Pair using
  (skip; frontᴾ₂; front₂; q₀₁ʸ; q₁₀ʸ; q₁₁ʸ; NoVar-front₂-i; NoVar-front₂-j)
open import PathSum.Anywhere M using
  (Anywhere; plain; at; Anywhere-<; SN; SN-by-<; Ord≤-front;
   _⟶ᵍ_; _⟶ᵍ*_; εᵍ; _◅ᵍ_)

private
  variable
    d n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- The calculus

infix  4 _⟶ᶠ_ _⟶ᶠ*_
infixr 5 _◅ᶠ_ _◅◅ᶠ_

_⟶ᶠ_ : PathSum n k m → PathSum n k′ m′ → Set
ξ ⟶ᶠ ζ = Anywhere (Anywhere _⟶ᴳ_) ξ ζ

-- Chains, heterogeneous in the number of path variables.

data _⟶ᶠ*_ {n : ℕ} : ∀ {k m k′ m′} →
                     PathSum n k m → PathSum n k′ m′ → Set where
  εᶠ   : ∀ {k m} {ξ : PathSum n k m} → ξ ⟶ᶠ* ξ
  _◅ᶠ_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
         {χ : PathSum n k″ m″} → ξ ⟶ᶠ ζ → ζ ⟶ᶠ* χ → ξ ⟶ᶠ* χ

_◅◅ᶠ_ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
        {χ : PathSum n k″ m″} → ξ ⟶ᶠ* ζ → ζ ⟶ᶠ* χ → ξ ⟶ᶠ* χ
εᶠ        ◅◅ᶠ steps′ = steps′
(s ◅ᶠ ss) ◅◅ᶠ steps′ = s ◅ᶠ (ss ◅◅ᶠ steps′)


------------------------------------------------------------------------
-- The partial calculi embed

-- All four rules at the head.

⟶ᴳ⇒⟶ᶠ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ ζ → ξ ⟶ᶠ ζ
⟶ᴳ⇒⟶ᶠ s = plain (plain s)

-- The linear rules at any variable: the same renumbering, and the
-- linear rule read as a general one (Reduction.General.⟶⇒⟶ᴳ).

⟶ᵍ⇒⟶ᶠ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ ζ → ξ ⟶ᶠ ζ
⟶ᵍ⇒⟶ᶠ (plain s) = plain (plain (⟶⇒⟶ᴳ s))
⟶ᵍ⇒⟶ᶠ (at j s)  = at j (plain (⟶⇒⟶ᴳ s))

⟶⇒⟶ᶠ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ⟶ᶠ ζ
⟶⇒⟶ᶠ s = ⟶ᴳ⇒⟶ᶠ (⟶⇒⟶ᴳ s)

-- And their chains.

⟶ᴳ*⇒⟶ᶠ* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
          ξ ⟶ᴳ* ζ → ξ ⟶ᶠ* ζ
⟶ᴳ*⇒⟶ᶠ* εᴳ        = εᶠ
⟶ᴳ*⇒⟶ᶠ* (s ◅ᴳ ss) = ⟶ᴳ⇒⟶ᶠ s ◅ᶠ ⟶ᴳ*⇒⟶ᶠ* ss

⟶ᵍ*⇒⟶ᶠ* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
          ξ ⟶ᵍ* ζ → ξ ⟶ᶠ* ζ
⟶ᵍ*⇒⟶ᶠ* εᵍ        = εᶠ
⟶ᵍ*⇒⟶ᶠ* (s ◅ᵍ ss) = ⟶ᵍ⇒⟶ᶠ s ◅ᶠ ⟶ᵍ*⇒⟶ᶠ* ss

⟶*⇒⟶ᶠ* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶* ζ → ξ ⟶ᶠ* ζ
⟶*⇒⟶ᶠ* ε        = εᶠ
⟶*⇒⟶ᶠ* (s ◅ ss) = ⟶⇒⟶ᶠ s ◅ᶠ ⟶*⇒⟶ᶠ* ss


------------------------------------------------------------------------
-- The rules at y_j

-- The paper's premises read at y_j: the quotient of the phase by y_j,
-- and y_j absent from every output.  The premise of the head rule on
-- front j ξ is the same statement by definition.

elimAtᶠ : (ξ : PathSum n (suc (suc k)) (suc m)) (j : Fin (suc m)) →
          (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ →
          (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
          ξ ⟶ᶠ elim-reduct (front j ξ)
elimAtᶠ ξ j eqP eqf =
  at j (plain (elimᴳ (front j ξ) eqP
                     (λ w → NoVar-front j (out ξ w) (eqf w))))

ωAtᶠ : (ξ : PathSum n (suc k) (suc m)) (j : Fin (suc m)) (Q : Poly n m) →
       BoolValued Q →
       (phase ξ /ʸ j) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) →
       (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
       ξ ⟶ᶠ ωᴳ-reduct (front j ξ) Q
ωAtᶠ ξ j Q bQ eqP eqf =
  at j (plain (ωᴳ (front j ξ) Q bQ eqP
                  (λ w → NoVar-front j (out ξ w) (eqf w))))

hhAtᶠ : (ξ : PathSum n k (suc m)) (j : Fin (suc m)) (i : Fin m)
        (Q : Poly n m) → BoolValued Q → Absent y[ i ] Q →
        (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)) →
        (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
        ξ ⟶ᶠ hhᴳ-reduct (front j ξ) i Q
hhAtᶠ ξ j i Q bQ absQ eqP eqf =
  at j (plain (hhᴳ (front j ξ) i Q bQ absQ eqP
                   (λ w → NoVar-front j (out ξ w) (eqf w))))


------------------------------------------------------------------------
-- [Case] at (y_i , y_j)

-- The paper's two decompositions of the phase, read off its quarters
-- in y_i and y_j: the y_i y_j coefficient is ½, the y_i coefficient is
-- ¼X + ½Q and the y_j coefficient is ¼(1 - X) + ½Q′; and both
-- variables are absent from every output.  The head rule on
-- front₂ i j i≢j ξ has the same premises by definition, except for
-- the outputs, which are renumbered (Reorder.Pair.NoVar-front₂-i, -j).

caseAtᶠ : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
          (i j : Fin (suc (suc m))) (i≢j : i ≢ j) (X Q Q′ : Poly n m) →
          BoolValued X → BoolValued Q → BoolValued Q′ →
          q₁₁ʸ i j i≢j (phase ξ) ≈[ pow M ] κ ½ →
          q₁₀ʸ i j i≢j (phase ξ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
          q₀₁ʸ i j i≢j (phase ξ) ≈[ pow M ]
            ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) →
          (∀ w → NoVar (+ 2) y[ i ] (out ξ w)) →
          (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
          ξ ⟶ᶠ case-reduct (front₂ i j i≢j ξ) X Q Q′
caseAtᶠ ξ i j i≢j X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ eqfᵢ eqfⱼ =
  at j (at (suc (skip i≢j))
    (caseᴳ (front₂ i j i≢j ξ) X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁
      (λ w → NoVar-front₂-i i j i≢j (out ξ w) (eqfᵢ w))
      (λ w → NoVar-front₂-j i j i≢j (out ξ w) (eqfⱼ w))))


------------------------------------------------------------------------
-- Renumbering a pair keeps the order of a polynomial

Ord≤-front₂ : (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
              {P : Poly n (suc (suc m))} →
              Ord≤ d P → Ord≤ d (frontᴾ₂ i j i≢j P)
Ord≤-front₂ i j i≢j ordP =
  Ord≤-front (suc (skip i≢j)) (Ord≤-front j ordP)


------------------------------------------------------------------------
-- Proposition 3.2: every step removes one or two path variables

-- [Case] removes two, the other rules one.  Renumbering does not
-- change the number of path variables.

⟶ᴳ-removes : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ ζ →
             m ≡ suc m′ ⊎ m ≡ suc (suc m′)
⟶ᴳ-removes (elimᴳ _ _ _)                   = inj₁ refl
⟶ᴳ-removes (ωᴳ _ _ _ _ _)                  = inj₁ refl
⟶ᴳ-removes (hhᴳ _ _ _ _ _ _ _)             = inj₁ refl
⟶ᴳ-removes (caseᴳ _ _ _ _ _ _ _ _ _ _ _ _) = inj₂ refl

⟶ᶠ-removes : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ ζ →
             m ≡ suc m′ ⊎ m ≡ suc (suc m′)
⟶ᶠ-removes (plain (plain s)) = ⟶ᴳ-removes s
⟶ᶠ-removes (plain (at _ s))  = ⟶ᴳ-removes s
⟶ᶠ-removes (at _ (plain s))  = ⟶ᴳ-removes s
⟶ᶠ-removes (at _ (at _ s))   = ⟶ᴳ-removes s

-- In particular every step lowers the number of path variables, by
-- the generic lemma for Anywhere, twice.

⟶ᶠ-< : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ ζ → m′ < m
⟶ᶠ-< {ξ = ξ} {ζ} =
  Anywhere-< {R = Anywhere _⟶ᴳ_} (Anywhere-< {R = _⟶ᴳ_} ⟶ᴳ-dec)
    {ξ = ξ} {ζ = ζ}


------------------------------------------------------------------------
-- Proposition 3.2: strong normalisation

⟶ᶠ-SN : (ξ : PathSum n k m) → SN _⟶ᶠ_ ξ
⟶ᶠ-SN = SN-by-< {R = _⟶ᶠ_} ⟶ᶠ-<


------------------------------------------------------------------------
-- Proposition 3.2: the length of a chain is linear in m

-- The length of a chain and its two bounds are computed together, by
-- one recursion whose result type does not mention the chain.  (Under
-- --cubical-compatible, matching on a chain of path-sums against a goal
-- that mentions the chain costs seconds and a gigabyte per lemma; one
-- that does not costs nothing.)  The length is the first component,
-- and it still computes: lenᶠ εᶠ is 0 and lenᶠ (s ◅ᶠ ss) is
-- suc (lenᶠ ss), by definition.

private
  two-more : ∀ {a} l b → a ≤ (l + l) + b →
             suc (suc a) ≤ (suc l + suc l) + b
  two-more l b h = ≤-trans (s≤s (s≤s h))
    (≤-reflexive (cong (λ t → suc (t + b)) (sym (+-suc l l))))

  lower-step : ∀ {a a′} l b → a ≡ suc a′ ⊎ a ≡ suc (suc a′) →
               a′ ≤ (l + l) + b → a ≤ (suc l + suc l) + b
  lower-step l b (inj₁ refl) h = ≤-trans (n≤1+n _) (two-more l b h)
  lower-step l b (inj₂ refl) h = two-more l b h

  -- A length l for a chain from m to m′ path variables: at most one
  -- step per variable removed, at least one per two.
  Bounds : ℕ → ℕ → ℕ → Set
  Bounds m m′ l = (l + m′ ≤ m) × (m ≤ (l + l) + m′)

  measure : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
            ξ ⟶ᶠ* ζ → Σ ℕ (Bounds m m′)
  measure εᶠ                   = 0 , ≤-refl , ≤-refl
  measure {m′ = m′} (s ◅ᶠ ss) =
    suc (proj₁ (measure ss)) ,
    ≤-trans (s≤s (proj₁ (proj₂ (measure ss)))) (⟶ᶠ-< s) ,
    lower-step (proj₁ (measure ss)) m′ (⟶ᶠ-removes s)
               (proj₂ (proj₂ (measure ss)))

lenᶠ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ* ζ → ℕ
lenᶠ steps = proj₁ (measure steps)

-- At most one step per path variable removed ...

⟶ᶠ*-length : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
             (steps : ξ ⟶ᶠ* ζ) → lenᶠ steps + m′ ≤ m
⟶ᶠ*-length steps = proj₁ (proj₂ (measure steps))

-- ... so no chain out of ξ is longer than ξ has path variables ...

⟶ᶠ*-bounded : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
              (steps : ξ ⟶ᶠ* ζ) → lenᶠ steps ≤ m
⟶ᶠ*-bounded steps = ≤-trans (m≤m+n (lenᶠ steps) _) (⟶ᶠ*-length steps)

-- ... and at least one step per two path variables removed: twice the
-- length is at least m − m′.

⟶ᶠ*-length-lower : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
                   (steps : ξ ⟶ᶠ* ζ) → m ≤ (lenᶠ steps + lenᶠ steps) + m′
⟶ᶠ*-length-lower steps = proj₂ (proj₂ (measure steps))
