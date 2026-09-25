------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of figure 2 at any path variable, and proposition 3.2
--
-- Amy's figure 2 (QPL 2018) states [Elim], [ω] and [HH] at a path
-- variable y₀ that may be any internal one, "applied to path-sums in
-- the obvious way".  PathSum.Reduction states them at the first
-- variable.  Here a rule at y_j is a rule at the first variable of
-- front j ξ (PathSum.Reorder), which lists y_j first and the other
-- variables in their original order.  The reduct is that of the head
-- rule, so its path variables are the others, in order: new index l
-- is old punchIn j l.  In particular the variable i and the set S of
-- [HH] are given in that reduced numbering.
--
-- The renumbering is folded into each rule rather than added as a
-- rewrite of its own.  That is essential: front is a bijection (on two
-- variables, front 1 undoes itself), so a separate reordering step
-- would make the calculus non-terminating.  With it folded in, every
-- step still removes exactly one path variable.
--
-- The construction is generic.  A relation between path-sums (PSRel)
-- R gives Anywhere R, whose steps are R-steps either on ξ itself
-- (plain) or on front j ξ (at j).  The plain constructor is kept
-- because front zero ξ is only pointwise ξ, vectors having no η-rule.
-- Relations combine by union (_∪ᴿ_), which is how rules not in
-- PathSum.Reduction can join the calculus later, each stated at the
-- head and lifted by Anywhere.  Renumbering keeps the order of the
-- phase (Ord≤-front), so lemma 4.3 applies at any variable
-- (PathSum.Anywhere.Clifford).
--
-- The general calculus is _⟶ᵍ_ = Anywhere _⟶_: the rules of
-- PathSum.Reduction -- [Elim], [ω] and [HH] with Z₂-linear quotients;
-- [Case] is not formalised -- at any path variable.  The smart
-- constructors elimAt, ωAt and hhAt state their premises at y_j
-- directly: the quotient phase ξ /ʸ j, and the absence of y_j from
-- the outputs.
--
-- Proposition 3.2.  "Every sequence of rewrites terminates" is
-- formalised as an inductive strong normalisation predicate SN
-- (⟶ᵍ-SN), and "the sequence is linear in the number of path
-- variables m" is made exact: every chain from m to m′ variables has
-- length m − m′ (⟶ᵍ*-length).  That a sequence can always be continued
-- to an irreducible path-sum is PathSum.Anywhere.Match (by a finite
-- search); the claim that matching and normalisation take polynomial
-- time is not formalised.
-- Soundness (proposition 3.1) is in PathSum.Anywhere.Sound, which is
-- where the denotation comes in.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Anywhere (M : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (∣_∣)
open import Data.Integer.Base using (+_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Nat.Base using (zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; ≤-refl; <-≤-trans; m≤m+n)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong; subst)

open import PathSum.Base
open import PathSum.Order M using (Ord≤; pow; val)
open import PathSum.Polynomial hiding (subst)
open import PathSum.Reduction M using
  (_⟶_; _⟶*_; ε; _◅_; elim; ω; hh; elim-reduct; ω-reduct; hh-reduct;
   ¼; ½)
open import PathSum.Reorder

private
  variable
    d n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Renumbering keeps the order of a polynomial

-- The order bound of a coefficient depends only on the degree of its
-- monomial, which renumbering does not change.

Ord≤-front : (j : Fin (suc m)) {P : Poly n (suc m)} →
             Ord≤ d P → Ord≤ d (frontᴾ j P)
Ord≤-front {d = d} j {P} ordP (α , b ∷ s) =
  subst (λ t → pow (val d t) ∣ P (α , insertAt s j b))
        (cong (_+_ ∣ α ∣) (∣insertAt∣ s j b))
        (ordP (α , insertAt s j b))


------------------------------------------------------------------------
-- Relations closed under renumbering

-- A heterogeneous relation between path-sums on the same qubits.

PSRel : Set₁
PSRel = ∀ {n k m k′ m′} → PathSum n k m → PathSum n k′ m′ → Set

-- An R-step on ξ itself, or on ξ with y_j moved to the front.

data Anywhere (R : PSRel) {n : ℕ} :
     ∀ {k m k′ m′} → PathSum n k m → PathSum n k′ m′ → Set where
  plain : ∀ {k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
          R ξ ζ → Anywhere R ξ ζ
  at    : ∀ {k m k′ m′} {ξ : PathSum n k (suc m)} {ζ : PathSum n k′ m′}
          (j : Fin (suc m)) → R (front j ξ) ζ → Anywhere R ξ ζ

-- The union of two relations.  This is how further rules join the
-- calculus without reopening PathSum.Reduction (and the soundness
-- proof in PathSum.Denotation): a rule stated at the head as a
-- relation of its own is lifted to any variable by Anywhere and added
-- by _∪ᴿ_; soundness and termination then follow from
-- Anywhere.Sound.∪ᴿ-sound, Anywhere-sound, ∪ᴿ-< and Anywhere-<.

infixr 5 _∪ᴿ_

data _∪ᴿ_ (R R′ : PSRel) {n : ℕ} :
     ∀ {k m k′ m′} → PathSum n k m → PathSum n k′ m′ → Set where
  inl : ∀ {k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
        R ξ ζ → (R ∪ᴿ R′) ξ ζ
  inr : ∀ {k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
        R′ ξ ζ → (R ∪ᴿ R′) ξ ζ


------------------------------------------------------------------------
-- The general calculus

infix  4 _⟶ᵍ_ _⟶ᵍ*_
infixr 5 _◅ᵍ_ _◅◅ᵍ_

_⟶ᵍ_ : PathSum n k m → PathSum n k′ m′ → Set
ξ ⟶ᵍ ζ = Anywhere _⟶_ ξ ζ

-- Its reflexive-transitive closure, heterogeneous in the number of
-- path variables like PathSum.Reduction's _⟶*_.

data _⟶ᵍ*_ {n : ℕ} : ∀ {k m k′ m′} →
                     PathSum n k m → PathSum n k′ m′ → Set where
  εᵍ   : ∀ {k m} {ξ : PathSum n k m} → ξ ⟶ᵍ* ξ
  _◅ᵍ_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
         {ξ′ : PathSum n k″ m″} → ξ ⟶ᵍ ζ → ζ ⟶ᵍ* ξ′ → ξ ⟶ᵍ* ξ′

_◅◅ᵍ_ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
        {ξ′ : PathSum n k″ m″} → ξ ⟶ᵍ* ζ → ζ ⟶ᵍ* ξ′ → ξ ⟶ᵍ* ξ′
εᵍ         ◅◅ᵍ steps′ = steps′
(s ◅ᵍ ss)  ◅◅ᵍ steps′ = s ◅ᵍ (ss ◅◅ᵍ steps′)

-- The rules at y_j, with the paper's premises read at y_j: the
-- quotient of the phase by y_j, and y_j absent from every output.
-- The premise of the head rule on front j ξ is the same statement by
-- definition (head-part of the renumbered phase is phase ξ /ʸ j).

elimAt : (ξ : PathSum n (suc (suc k)) (suc m)) (j : Fin (suc m)) →
         (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ →
         (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
         ξ ⟶ᵍ elim-reduct (front j ξ)
elimAt ξ j eqP eqf =
  at j (elim (front j ξ) eqP (λ w → NoVar-front j (out ξ w) (eqf w)))

ωAt : (ξ : PathSum n (suc k) (suc m)) (j : Fin (suc m)) (c : Bool)
      (S : Mon n m) →
      (phase ξ /ʸ j) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) →
      (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
      ξ ⟶ᵍ ω-reduct (front j ξ) c S
ωAt ξ j c S eqP eqf =
  at j (ω (front j ξ) c S eqP (λ w → NoVar-front j (out ξ w) (eqf w)))

hhAt : (ξ : PathSum n k (suc m)) (j : Fin (suc m)) (i : Fin m) (c : Bool)
       (S : Mon n m) → y[ i ] ∈ᵐ S →
       (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
       (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
       ξ ⟶ᵍ hh-reduct (front j ξ) i c S
hhAt ξ j i c S i∈S eqP eqf =
  at j (hh (front j ξ) i c S i∈S eqP (λ w → NoVar-front j (out ξ w) (eqf w)))

-- The head rules are general rules.

⟶⇒⟶ᵍ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ⟶ᵍ ζ
⟶⇒⟶ᵍ = plain

⟶*⇒⟶ᵍ* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶* ζ → ξ ⟶ᵍ* ζ
⟶*⇒⟶ᵍ* ε          = εᵍ
⟶*⇒⟶ᵍ* (s ◅ steps) = plain s ◅ᵍ ⟶*⇒⟶ᵍ* steps


------------------------------------------------------------------------
-- Proposition 3.2: every step removes one path variable

⟶-shrinks : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → suc m′ ≡ m
⟶-shrinks (elim _ _ _)         = refl
⟶-shrinks (ω    _ _ _ _ _)     = refl
⟶-shrinks (hh   _ _ _ _ _ _ _) = refl

-- Renumbering does not change the number of path variables, so a
-- general step removes exactly one too.

⟶ᵍ-shrinks : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
             ξ ⟶ᵍ ζ → suc m′ ≡ m
⟶ᵍ-shrinks (plain s) = ⟶-shrinks s
⟶ᵍ-shrinks (at _ s)  = ⟶-shrinks s

-- Likewise for any relation that shrinks the path variables.

Anywhere-< : {R : PSRel} →
             (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
              R ξ ζ → m′ < m) →
             ∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
             Anywhere R ξ ζ → m′ < m
Anywhere-< shrink (plain r) = shrink r
Anywhere-< shrink (at _ r)  = shrink r

-- And for a union of two such relations.

∪ᴿ-< : {R R′ : PSRel} →
       (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
        R ξ ζ → m′ < m) →
       (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
        R′ ξ ζ → m′ < m) →
       ∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
       (R ∪ᴿ R′) ξ ζ → m′ < m
∪ᴿ-< shrink shrink′ (inl r) = shrink r
∪ᴿ-< shrink shrink′ (inr r) = shrink′ r

-- The length of a chain is the number of path variables it removes,
-- so no chain out of ξ is longer than ξ has path variables.

lenᵍ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ* ζ → ℕ
lenᵍ εᵍ         = 0
lenᵍ (_ ◅ᵍ ss)  = suc (lenᵍ ss)

⟶ᵍ*-length : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
             (steps : ξ ⟶ᵍ* ζ) → lenᵍ steps + m′ ≡ m
⟶ᵍ*-length εᵍ        = refl
⟶ᵍ*-length (s ◅ᵍ ss) = trans (cong suc (⟶ᵍ*-length ss)) (⟶ᵍ-shrinks s)

⟶ᵍ*-bounded : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
              (steps : ξ ⟶ᵍ* ζ) → lenᵍ steps ≤ m
⟶ᵍ*-bounded steps =
  ≤-trans (m≤m+n (lenᵍ steps) _) (≤-reflexive (⟶ᵍ*-length steps))


------------------------------------------------------------------------
-- Proposition 3.2: strong normalisation

-- ξ is strongly normalising for R when every R-step out of it leads to
-- a strongly normalising path-sum: inductively, every rewrite sequence
-- out of ξ is finite.  The normalisation, the number of path variables
-- and the path-sum are indices, since a step changes all three.

data SN (R : PSRel) {n : ℕ} : ∀ {k m} → PathSum n k m → Set where
  sn : ∀ {k m} {ξ : PathSum n k m} →
       (∀ {k′ m′} {ζ : PathSum n k′ m′} → R ξ ζ → SN R ζ) → SN R ξ

-- A relation that strictly lowers the number of path variables is
-- strongly normalising, by induction on a bound for that number.

SN-by-< : {R : PSRel} →
          (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
           R ξ ζ → m′ < m) →
          ∀ {n k m} (ξ : PathSum n k m) → SN R ξ
SN-by-< {R} shrink {n} ξ = go _ ξ ≤-refl
  where
  go : ∀ b {k m} (ξ : PathSum n k m) → m < b → SN R ξ
  go zero    _ ()
  go (suc b) ξ (s≤s m≤b) = sn (λ r → go b _ (<-≤-trans (shrink r) m≤b))

⟶ᵍ-SN : (ξ : PathSum n k m) → SN _⟶ᵍ_ ξ
⟶ᵍ-SN = SN-by-< (λ r → ≤-reflexive (⟶ᵍ-shrinks r))

⟶-SN : (ξ : PathSum n k m) → SN _⟶_ ξ
⟶-SN = SN-by-< (λ r → ≤-reflexive (⟶-shrinks r))
