------------------------------------------------------------------------
-- Presentations of groups
--
-- Deciding equality of stored matrices by one boolean
--
-- An equation of stored tries proved by `refl` makes the conversion
-- checker compare the two tries component by component, reducing each
-- entry separately: nothing computed for one entry is shared with the
-- next, so a product of n gates is evaluated once per entry.  `eqM`
-- asks the same question as a boolean, which the checker reduces to
-- `true` in one run of the evaluator, sharing every intermediate trie;
-- `eqM-sound` turns the answer back into the equation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics.Decide where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; T)
open import Data.Integer using (ℤ ; +_ ; -[1+_])
open import Data.Nat using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Ring using (ℤ√2 ; _+√2_)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Tab ; Mat ; mat)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- The booleans

eqℤ : ℤ → ℤ → Bool
eqℤ (+ m)    (+ n)    = m ≡ᵇ n
eqℤ -[1+ m ] -[1+ n ] = m ≡ᵇ n
eqℤ _        _        = false

eq𝔽 : ℤ√2 → ℤ√2 → Bool
eq𝔽 (a +√2 b) (c +√2 d) = eqℤ a c ∧ eqℤ b d

eqT : ∀ k {A : Set} → (A → A → Bool) → Tab k A → Tab k A → Bool
eqT ₀      e a        b        = e a b
eqT (₁₊ k) e (a , a′) (b , b′) = eqT k e a b ∧ eqT k e a′ b′

eqM : Mat k → Mat k → Bool
eqM {k} (mat s) (mat t) = eqT k (eqT k eq𝔽) s t

------------------------------------------------------------------------
-- Soundness

private
  ∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true {true}  {true}  Eq.refl = Eq.refl , Eq.refl
  ∧-true {true}  {false} ()
  ∧-true {false} ()

  ᵇ-sound : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
  ᵇ-sound m n e = ≡ᵇ⇒≡ m n (Eq.subst T (Eq.sym e) tt)

eqℤ-sound : ∀ a b → eqℤ a b ≡ true → a ≡ b
eqℤ-sound (+ m)    (+ n)    e = Eq.cong +_ (ᵇ-sound m n e)
eqℤ-sound -[1+ m ] -[1+ n ] e = Eq.cong -[1+_] (ᵇ-sound m n e)
eqℤ-sound (+ m)    -[1+ n ] ()
eqℤ-sound -[1+ m ] (+ n)    ()

eq𝔽-sound : ∀ x y → eq𝔽 x y ≡ true → x ≡ y
eq𝔽-sound (a +√2 b) (c +√2 d) e with ∧-true {eqℤ a c} e
... | ea , eb = Eq.cong₂ _+√2_ (eqℤ-sound a c ea) (eqℤ-sound b d eb)

eqT-sound : ∀ k {A : Set} (e : A → A → Bool) → (∀ a b → e a b ≡ true → a ≡ b) →
            ∀ s t → eqT k e s t ≡ true → s ≡ t
eqT-sound ₀      e ok a        b        h = ok a b h
eqT-sound (₁₊ k) e ok (a , a′) (b , b′) h with ∧-true {eqT k e a b} h
... | h₁ , h₂ = Eq.cong₂ _,_ (eqT-sound k e ok a b h₁) (eqT-sound k e ok a′ b′ h₂)

eqM-sound : (M N : Mat k) → eqM M N ≡ true → M ≡ N
eqM-sound {k} (mat s) (mat t) h =
  Eq.cong mat (eqT-sound k (eqT k eq𝔽) (eqT-sound k eq𝔽 eq𝔽-sound) s t h)

------------------------------------------------------------------------
-- Reflexivity

private
  ᵇ-refl : ∀ m → (m ≡ᵇ m) ≡ true
  ᵇ-refl zero    = Eq.refl
  ᵇ-refl (suc m) = ᵇ-refl m

eqℤ-refl : ∀ a → eqℤ a a ≡ true
eqℤ-refl (+ m)    = ᵇ-refl m
eqℤ-refl -[1+ m ] = ᵇ-refl m

eq𝔽-refl : ∀ x → eq𝔽 x x ≡ true
eq𝔽-refl (a +√2 b) rewrite eqℤ-refl a | eqℤ-refl b = Eq.refl

eqT-refl : ∀ k {A : Set} (e : A → A → Bool) → (∀ a → e a a ≡ true) →
           ∀ s → eqT k e s s ≡ true
eqT-refl ₀      e ok a        = ok a
eqT-refl (₁₊ k) e ok (a , a′) rewrite eqT-refl k e ok a | eqT-refl k e ok a′ = Eq.refl

eqM-refl : (M : Mat k) → eqM M M ≡ true
eqM-refl {k} (mat s) = eqT-refl k (eqT k eq𝔽) (eqT-refl k eq𝔽 eq𝔽-refl) s

-- An equation of stored matrices, as the boolean.
≡-eqM : {M N : Mat k} → M ≡ N → eqM M N ≡ true
≡-eqM {M = M} Eq.refl = eqM-refl M
