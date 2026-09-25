------------------------------------------------------------------------
-- Presentations of groups
--
-- Two Hadamard pairs on disjoint indices commute
--
-- Equation (66) says that H_[a,b] H_[c,d] is H_[c,d] H_[a,b], and its
-- proof is (65), Corollary A.7 and (65) again — where A.7 asks for the
-- two sides to denote the same operator.  They do, and this is why:
-- each factor of the pair is √2 times the identity away from its own
-- two indices, so on each of the five kinds of row the two products
-- have the same entries.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.PairComm (m : ℕ) where

open import Data.Bool.Properties renaming (_≟_ to _≟ᵇ_) using ()
open import Data.Vec.Properties using (≡-dec)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.HadamardPair m
  using (HH2 ; module Entries)

private
  n : ℕ
  n = ₃₊ m

  _≟ᵇˢ_ : ∀ {k} (x y : Bits k) → Dec (x ≡ y)
  _≟ᵇˢ_ = ≡-dec _≟ᵇ_

  ≢sym : ∀ {k} {x y : Bits k} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  -- The two spellings of a row.
  ring₁ : ∀ (u v : 𝔽) → √2 * (1# * u + 1# * v) ≡ √2 * u + √2 * v
  ring₁ u v =
    Eq.trans (Eq.cong (√2 *_) (Eq.cong₂ _+_ (*-identityˡ u) (*-identityˡ v)))
             (*-distribˡ-+ √2 u v)

  ring₂ : ∀ (u v : 𝔽) → √2 * (1# * u + -1# * v) ≡ √2 * u + -1# * (√2 * v)
  ring₂ u v =
    Eq.trans (Eq.cong (√2 *_) (Eq.cong (_+ -1# * v) (*-identityˡ u)))
    (Eq.trans (*-distribˡ-+ √2 u (-1# * v))
      (Eq.cong (√2 * u +_)
        (Eq.trans (Eq.sym (*-assoc √2 -1# v))
          (Eq.trans (Eq.cong (_* v) (*-comm √2 -1#)) (*-assoc -1# √2 v)))))

module _ (p q r s : Bits n)
         (pq : p ≢ q) (rs : r ≢ s)
         (pr : p ≢ r) (ps : p ≢ s) (qr : q ≢ r) (qs : q ≢ s)
  where

  private
    module L = Entries p q r s pq rs pr ps qr qs
    module R = Entries r s p q rs pq (≢sym pr) (≢sym qr) (≢sym ps) (≢sym qs)

  HH2-comm : HH2 p q r s ≐ HH2 r s p q
  HH2-comm x y = go (x ≟ᵇˢ p) (x ≟ᵇˢ q) (x ≟ᵇˢ r) (x ≟ᵇˢ s)
    where
    go : Dec (x ≡ p) → Dec (x ≡ q) → Dec (x ≡ r) → Dec (x ≡ s) →
         HH2 p q r s x y ≡ HH2 r s p q x y
    go (yes Eq.refl) _ _ _ =
      Eq.trans (L.HH2-p y) (Eq.sym (Eq.trans (R.HH2-r y) (ring₁ (δb x y) (δb q y))))
    go (no _) (yes Eq.refl) _ _ =
      Eq.trans (L.HH2-q y) (Eq.sym (Eq.trans (R.HH2-s y) (ring₂ (δb p y) (δb x y))))
    go (no _) (no _) (yes Eq.refl) _ =
      Eq.trans (Eq.trans (L.HH2-r y) (ring₁ (δb x y) (δb s y))) (Eq.sym (R.HH2-p y))
    go (no _) (no _) (no _) (yes Eq.refl) =
      Eq.trans (Eq.trans (L.HH2-s y) (ring₂ (δb r y) (δb x y))) (Eq.sym (R.HH2-q y))
    go (no xp) (no xq) (no xr) (no xs) =
      Eq.trans (L.HH2-o x xp xq xr xs y) (Eq.sym (R.HH2-o x xr xs xp xq y))
