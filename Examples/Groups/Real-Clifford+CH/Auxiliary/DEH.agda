------------------------------------------------------------------------
-- Presentations of groups
--
-- (DE-HH): the Hadamard obligation of Item (a)
--
-- The one letter-obligation of the Reidemeister–Schreier data that
-- needs a Hadamard rule, and so the one that cannot be read at the
-- Hadamard-free fragment where the rest of `DE` now lives.
--
-- (42) composes a Hadamard pair through `twoSmallest` — the two
-- smallest naturals not among the four given indices.  When neither 0
-- nor 1 is among them those two *are* 0 and 1, which is the pair the
-- coset action routes through, so (42) is the obligation outright.
-- What has to be done is arithmetic: make the boolean tests inside
-- `twoSmallest` reduce, and identify the ℕ-indexed letters of (42)
-- with the `Fin`-indexed ones.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.DEH (m : ℕ) where

open import Data.Bool using (false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat using (zero ; suc ; _≡ᵇ_) renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (toFin-toℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m
  using (o₁ ; z₀ ; toℕ-z₀ ; toℕ-o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (hh ; hhℕ ; twoSmallest ; distinct4)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

-- (DE-HH), where the pair 0 1 is free
--
-- (42) composes a Hadamard pair through `twoSmallest` — the two
-- smallest naturals not among the four given indices.  When neither 0
-- nor 1 is among them those two *are* 0 and 1, which is the pair the
-- coset action routes through, so (42) is the obligation outright.
-- What has to be done is arithmetic: make the boolean tests inside
-- `twoSmallest` reduce, and identify the ℕ-indexed letters of (42)
-- with the `Fin`-indexed ones.

private
  ≢⇒≡ᵇfalse : ∀ (x y : ℕ) → x ≢ y → (x ≡ᵇ y) ≡ false
  ≢⇒≡ᵇfalse zero    zero    ne = ⊥-elim (ne Eq.refl)
  ≢⇒≡ᵇfalse zero    (suc y) ne = Eq.refl
  ≢⇒≡ᵇfalse (suc x) zero    ne = Eq.refl
  ≢⇒≡ᵇfalse (suc x) (suc y) ne = ≢⇒≡ᵇfalse x y (λ e → ne (Eq.cong suc e))

  -- The two free indices are 0 and 1 when neither occurs.
  two01 : ∀ (a b c d : ℕ) → 0 ≢ a → 0 ≢ b → 0 ≢ c → 0 ≢ d →
                            1 ≢ a → 1 ≢ b → 1 ≢ c → 1 ≢ d →
          twoSmallest a b c d ≡ (0 , 1)
  two01 a b c d p q r s p′ q′ r′ s′
    rewrite ≢⇒≡ᵇfalse 0 a p  | ≢⇒≡ᵇfalse 0 b q  | ≢⇒≡ᵇfalse 0 c r  | ≢⇒≡ᵇfalse 0 d s
          | ≢⇒≡ᵇfalse 1 a p′ | ≢⇒≡ᵇfalse 1 b q′ | ≢⇒≡ᵇfalse 1 c r′ | ≢⇒≡ᵇfalse 1 d s′
    = Eq.refl

private
  -- Hence the ℕ-indexed Hadamard letter is the Fin-indexed one.
  hhℕ-hh : ∀ (a b c d : Fin N) → hhℕ {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ hh a b c d
  hhℕ-hh a b c d
    rewrite toFin-toℕ a | toFin-toℕ b | toFin-toℕ c | toFin-toℕ d = Eq.refl

  -- Distinctness from the two distinguished indices, as numerals.
  z₀≢⇒0≢ : ∀ {a : Fin N} → z₀ ≢ a → 0 ≢ toℕ a
  z₀≢⇒0≢ {a} ne e = ne (toℕ-injective (Eq.trans toℕ-z₀ e))

  o₁≢⇒1≢ : ∀ {a : Fin N} → o₁ ≢ a → 1 ≢ toℕ a
  o₁≢⇒1≢ {a} ne e = ne (toℕ-injective (Eq.trans toℕ-o₁ e))

DE-HH : ∀ (a b c d : Fin N) → (a≢b : a ≢ b) → (c≢d : c ≢ d) →
        (nd : distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ false) →
        z₀ ≢ a → z₀ ≢ b → z₀ ≢ c → z₀ ≢ d →
        o₁ ≢ a → o₁ ≢ b → o₁ ≢ c → o₁ ≢ d →
        hh a b c d ≈ hh a b z₀ o₁ • hh z₀ o₁ c d
DE-HH a b c d a≢b c≢d nd za zb zc zd oa ob oc od =
  sym (Eq.subst (λ w → w ≈ hh a b c d) bridge (axiom (r42 a b c d a≢b c≢d nd)))
  where
  ef : twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ (0 , 1)
  ef = two01 (toℕ a) (toℕ b) (toℕ c) (toℕ d)
             (z₀≢⇒0≢ za) (z₀≢⇒0≢ zb) (z₀≢⇒0≢ zc) (z₀≢⇒0≢ zd)
             (o₁≢⇒1≢ oa) (o₁≢⇒1≢ ob) (o₁≢⇒1≢ oc) (o₁≢⇒1≢ od)

  half₁ : hhℕ {₃₊ m} (toℕ a) (toℕ b) 0 1 ≡ hh a b z₀ o₁
  half₁ = Eq.trans (Eq.cong₂ (hhℕ {₃₊ m} (toℕ a) (toℕ b))
                             (Eq.sym toℕ-z₀) (Eq.sym toℕ-o₁))
                   (hhℕ-hh a b z₀ o₁)

  half₂ : hhℕ {₃₊ m} 0 1 (toℕ c) (toℕ d) ≡ hh z₀ o₁ c d
  half₂ = Eq.trans (Eq.cong₂ (λ u v → hhℕ {₃₊ m} u v (toℕ c) (toℕ d))
                             (Eq.sym toℕ-z₀) (Eq.sym toℕ-o₁))
                   (hhℕ-hh z₀ o₁ c d)

  bridge : hhℕ {₃₊ m} (toℕ a) (toℕ b)
                (proj₁ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d)))
                (proj₂ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d)))
         • hhℕ {₃₊ m} (proj₁ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d)))
                (proj₂ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d)))
                (toℕ c) (toℕ d)
         ≡ hh a b z₀ o₁ • hh z₀ o₁ c d
  bridge = Eq.trans
    (Eq.cong (λ p → hhℕ {₃₊ m} (toℕ a) (toℕ b) (proj₁ p) (proj₂ p)
                  • hhℕ {₃₊ m} (proj₁ p) (proj₂ p) (toℕ c) (toℕ d)) ef)
    (Eq.cong₂ _•_ half₁ half₂)
