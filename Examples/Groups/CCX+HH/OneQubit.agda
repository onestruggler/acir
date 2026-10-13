------------------------------------------------------------------------
-- Presentations of groups
--
-- The complete one-qubit theory: X X = 1.  There are no two- or
-- three-wire gates at this width.  The normal forms are 1 and X,
-- distinguished by their action on the bit 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.OneQubit where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike)
open import Examples.Groups.CCX+HH.Syntactics

private
  empty₀ : Gen 0 → ⊥
  empty₀ (gate₀ ())

  only-X : (g : Gen 1) → g ≡ X-gen
  only-X (gate₀ ())
  only-X X-gen = Eq.refl
  only-X (g ↥) = ⊥-elim (empty₀ g)

infix 4 _===_
data _===_ : WRel (Gen 1) where
  involution : X • X === ε

open PB _===_ public using (_≈_)
private module P = PB _===_

-- The Boolean is the image of 0: false denotes identity, true X.
denote : Circuit 1 → Bool
denote [ g ]ʷ = true
denote ε = false
denote (u • v) = denote u xor denote v

normal : Bool → Circuit 1
normal false = ε
normal true = X

private
  normal-mul : ∀ a b → normal a • normal b ≈ normal (a xor b)
  normal-mul false false = P.left-unit
  normal-mul false true = P.left-unit
  normal-mul true false = P.right-unit
  normal-mul true true = P.axiom involution

normalize : (w : Circuit 1) → w ≈ normal (denote w)
normalize [ g ]ʷ = P.refl' (Eq.cong [_]ʷ (only-X g))
normalize ε = P.refl
normalize (u • v) = P.trans (P.cong (normalize u) (normalize v))
                            (normal-mul (denote u) (denote v))

private
  xor-assoc : ∀ a b c → (a xor b) xor c ≡ a xor (b xor c)
  xor-assoc false false false = Eq.refl
  xor-assoc false false true = Eq.refl
  xor-assoc false true false = Eq.refl
  xor-assoc false true true = Eq.refl
  xor-assoc true false false = Eq.refl
  xor-assoc true false true = Eq.refl
  xor-assoc true true false = Eq.refl
  xor-assoc true true true = Eq.refl

  xor-zero : ∀ a → a xor false ≡ a
  xor-zero false = Eq.refl
  xor-zero true = Eq.refl

soundness : ∀ {u v} → u ≈ v → denote u ≡ denote v
soundness P.refl = Eq.refl
soundness (P.sym h) = Eq.sym (soundness h)
soundness (P.trans h k) = Eq.trans (soundness h) (soundness k)
soundness (P.cong h k) = Eq.cong₂ _xor_ (soundness h) (soundness k)
soundness (P.assoc {w} {v} {u}) = xor-assoc (denote w) (denote v) (denote u)
soundness P.left-unit = Eq.refl
soundness (P.right-unit {w}) = xor-zero (denote w)
soundness (P.axiom involution) = Eq.refl

completeness : ∀ {u v} → denote u ≡ denote v → u ≈ v
completeness {u} {v} eq =
  P.trans (normalize u)
    (P.trans (P.refl' (Eq.cong normal eq)) (P.sym (normalize v)))

grouplike : Grouplike _===_
grouplike g = X , P.trans (P.cong P.refl (P.refl' (Eq.cong [_]ʷ (only-X g))))
                            (P.axiom involution)

-- Full permutation semantics, not just the selected matrix entry.
action : Circuit 1 → Bool → Bool
action w b = denote w xor b

action-complete : ∀ {u v} → (∀ b → action u b ≡ action v b) → u ≈ v
action-complete {u} {v} eq = completeness
  (Eq.trans (Eq.sym (xor-zero (denote u)))
    (Eq.trans (eq false) (xor-zero (denote v))))
