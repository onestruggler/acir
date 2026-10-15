------------------------------------------------------------------------
-- Presentations of groups
--
-- Relations stated on exact widths, closed under idle wires on top
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Circuit.TopPad (Gate : ℕ → Set) where

open import Data.Fin using (Fin ; zero ; suc ; inject₁ ; fromℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base
open import Circuit.Base Gate

import Presentation.Base as PB

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- One idle wire on top
--
-- The dual of _↥ and _↑, which put one below.  A gate keeps its wires
-- and only the width grows, so a closed word, ⇓'d, is the same word
-- read one wire wider (σ ⇓ is σ).

infixl 8 _↧
_↧ : Gen n → Gen (₁₊ n)
gate₀ h ↧ = gate₀ h
gate₁ h ↧ = gate₁ h
gate₂ h ↧ = gate₂ h
gate₃ h ↧ = gate₃ h
(g ↥)   ↧ = (g ↧) ↥

_⇓ : Circuit n → Circuit (₁₊ n)
w ⇓ = wmap _↧ w

-- A wire below and a wire on top are added in either order.
↑⇓ : (w : Circuit n) → (w ↑) ⇓ ≡ (w ⇓) ↑
↑⇓ [ g ]ʷ  = Eq.refl
↑⇓ ε       = Eq.refl
↑⇓ (u • t) = Eq.cong₂ _•_ (↑⇓ u) (↑⇓ t)

-- A wire of ₁₊ n is one of the n below the top, or the top itself:
-- what a semantics needs to say that ⇓ leaves the top wire idle.
data TopWire : Fin (₁₊ n) → Set where
  below : (k : Fin n) → TopWire (inject₁ k)
  top   : TopWire (fromℕ n)

top-wire : (k : Fin (₁₊ n)) → TopWire k
top-wire {₀}    zero    = top
top-wire {₁₊ n} zero    = below zero
top-wire {₁₊ n} (suc k) with top-wire k
... | below j = below (suc j)
... | top     = top

------------------------------------------------------------------------
-- Top-Pad
--
-- A relation on exact widths: each rule between circuits on its own
-- wires, n Base, w === v, with no parameter for wider circuits.
-- _VRel,_===_ embeds it (srel), closes it under one more idle wire on
-- top (cong↓) and under the structural rules of Circuit.Base's
-- Lift-Relation — one relation, where Lift-Relation over a padded
-- relation was two.  cong↓, the dual of cong↑, applies to every
-- instance, so a rule holds on the bottom wires of every wider
-- circuit, and since a closed word, ⇓'d, is the same word one wire
-- wider, the rule 3 Base, σ • σ ↑ • σ === σ ↑ • σ • σ ↑ gives, by
-- recursion on k, (₃₊ k) VRel, σ • σ ↑ • σ === σ ↑ • σ • σ ↑.
--
-- A function by cases on _VRel,_===_ owes a cong↓ clause, as it owes a
-- cong↑ one: a semantics says that ⇓ leaves the top wire idle
-- (TopWire), and a rule is matched at its own width.
--
-- Usage: state the group-specific relation on exact widths and open
-- Top-Pad in place of Lift-Relation.  The lemmas below are
-- Lift-Relation's, for this relation.

module Top-Pad (_Base,_===_ : (n : ℕ) → CRel n) where

  infix 4 _VRel,_===_
  data _VRel,_===_ : (n : ℕ) → CRel n where

    -- Embed the group-specific relation, on its own wires.
    srel  : n Base, w === v → n VRel, w === v

    -- Structural: congruence under an idle wire on top, and under
    -- wire-shifting (an idle wire below).
    cong↓ : n VRel, w === v → (₁₊ n) VRel, w ⇓ === v ⇓
    cong↑ : n VRel, w === v → (₁₊ n) VRel, w ↑ === v ↑

    -- Structural: a gate at the bottom commutes with any generator
    -- that has been shifted up past it (Lift-Relation's comm₁–comm₃),
    -- and a global gate does not depend on the wire it is written on
    -- (Lift-Relation's ω↑=ω).
    comm₁ : (h : Gate 1) (g : Gen n) → (₁₊ n) VRel,
      [ g ↥ ]ʷ • [ gate₁ h ]ʷ === [ gate₁ h ]ʷ • [ g ↥ ]ʷ
    comm₂ : (h : Gate 2) (g : Gen n) → (₂₊ n) VRel,
      [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ === [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ
    comm₃ : (h : Gate 3) (g : Gen n) → (₃₊ n) VRel,
      [ g ↥ ↥ ↥ ]ʷ • [ gate₃ h ]ʷ === [ gate₃ h ]ʷ • [ g ↥ ↥ ↥ ]ʷ
    ω↑=ω  : (ω : Gate 0) → (₁₊ n) VRel, [ gate₀ ω ]ʷ ↑ === [ gate₀ ω ]ʷ

  -- The monoid congruence at wire count n lifts to wire count ₁₊ n,
  -- with the new wire below ...
  lemma-cong↑ : ∀ {n} (w v : Circuit n)
    → let open PB (_VRel,_===_ n)       using (_≈_)
          open PB (_VRel,_===_ (₁₊ n)) renaming (_≈_ to _≈↑_) using ()
      in w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ w v PB.refl              = PB.refl
  lemma-cong↑ w v (PB.sym eq)          = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ w v (PB.trans eq eq₁)   = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v (PB.cong eq eq₁)    = PB.cong  (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v PB.assoc            = PB.assoc
  lemma-cong↑ w v PB.left-unit        = PB.left-unit
  lemma-cong↑ w v PB.right-unit       = PB.right-unit
  lemma-cong↑ w v (PB.axiom x)        = PB.axiom (cong↑ x)

  -- ... and on top.
  lemma-cong↓ : ∀ {n} (w v : Circuit n)
    → let open PB (_VRel,_===_ n)       using (_≈_)
          open PB (_VRel,_===_ (₁₊ n)) renaming (_≈_ to _≈↓_) using ()
      in w ≈ v → w ⇓ ≈↓ v ⇓
  lemma-cong↓ w v PB.refl              = PB.refl
  lemma-cong↓ w v (PB.sym eq)          = PB.sym (lemma-cong↓ v w eq)
  lemma-cong↓ w v (PB.trans eq eq₁)   = PB.trans (lemma-cong↓ _ _ eq) (lemma-cong↓ _ _ eq₁)
  lemma-cong↓ w v (PB.cong eq eq₁)    = PB.cong  (lemma-cong↓ _ _ eq) (lemma-cong↓ _ _ eq₁)
  lemma-cong↓ w v PB.assoc            = PB.assoc
  lemma-cong↓ w v PB.left-unit        = PB.left-unit
  lemma-cong↓ w v PB.right-unit       = PB.right-unit
  lemma-cong↓ w v (PB.axiom x)        = PB.axiom (cong↓ x)

  ------------------------------------------------------------------------
  -- The comm rules, extended from generators to whole circuits

  comm-gate₁-w↑ : ∀ (g : Gate 1) (w : Circuit n) ->
    let v = [ gate₁ g ]ʷ
        open PB ( (₁₊ n) VRel,_===_ )
    in  w ↑ • v ≈ v • w ↑
  comm-gate₁-w↑ g ε       = PB.trans PB.left-unit (PB.sym PB.right-unit)
  comm-gate₁-w↑ g [ x ]ʷ  = PB.axiom (comm₁ g x)
  comm-gate₁-w↑ g (u • t) =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (comm-gate₁-w↑ g t))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (comm-gate₁-w↑ g u) PB.refl)
              PB.assoc)))

  comm-gate₂-w↑↑ : ∀ (g : Gate 2) (w : Circuit n) ->
    let v = [ gate₂ g ]ʷ
        open PB ( (₂₊ n) VRel,_===_ )
    in  w ↑ ↑ • v ≈ v • w ↑ ↑
  comm-gate₂-w↑↑ g ε       = PB.trans PB.left-unit (PB.sym PB.right-unit)
  comm-gate₂-w↑↑ g [ x ]ʷ  = PB.axiom (comm₂ g x)
  comm-gate₂-w↑↑ g (u • t) =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (comm-gate₂-w↑↑ g t))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (comm-gate₂-w↑↑ g u) PB.refl)
              PB.assoc)))

  comm-gate₃-w↑↑↑ : ∀ (g : Gate 3) (w : Circuit n) ->
    let v = [ gate₃ g ]ʷ
        open PB ( (₃₊ n) VRel,_===_ )
    in  w ↑ ↑ ↑ • v ≈ v • w ↑ ↑ ↑
  comm-gate₃-w↑↑↑ g ε       = PB.trans PB.left-unit (PB.sym PB.right-unit)
  comm-gate₃-w↑↑↑ g [ x ]ʷ  = PB.axiom (comm₃ g x)
  comm-gate₃-w↑↑↑ g (u • t) =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (comm-gate₃-w↑↑↑ g t))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (comm-gate₃-w↑↑↑ g u) PB.refl)
              PB.assoc)))

  ------------------------------------------------------------------------
  -- Centrality of a scalar (Lift-Relation's Central-Scalars)

  module Central-Scalars
    (scalars-comm : ∀ {n} (h h' : Gate 0) → let open PB (n VRel,_===_) in
       [ gate₀ h' ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h' ]ʷ)
    where

    comm₀ : ∀ (h : Gate 0) (g : Gen n) → let open PB (n VRel,_===_) in
            [ g ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ g ]ʷ
    comm₀ h (gate₀ h') = scalars-comm h h'
    comm₀ h (gate₁ h₁) =
      PB.trans (PB.cong PB.refl (PB.sym (PB.axiom (ω↑=ω h))))
      (PB.trans (PB.sym (PB.axiom (comm₁ h₁ (gate₀ h))))
                (PB.cong (PB.axiom (ω↑=ω h)) PB.refl))
    comm₀ h (gate₂ h₂) =
      PB.trans (PB.cong PB.refl (PB.sym ω↑↑=ω))
      (PB.trans (PB.sym (PB.axiom (comm₂ h₂ (gate₀ h))))
                (PB.cong ω↑↑=ω PB.refl))
      where
      ω↑↑=ω : ∀ {n} → let open PB ((₂₊ n) VRel,_===_) in
              [ gate₀ {n} h ]ʷ ↑ ↑ ≈ [ gate₀ h ]ʷ
      ω↑↑=ω = PB.trans (PB.axiom (cong↑ (ω↑=ω h))) (PB.axiom (ω↑=ω h))
    comm₀ h (gate₃ h₃) =
      PB.trans (PB.cong PB.refl (PB.sym ω↑↑↑=ω))
      (PB.trans (PB.sym (PB.axiom (comm₃ h₃ (gate₀ h))))
                (PB.cong ω↑↑↑=ω PB.refl))
      where
      ω↑↑↑=ω : ∀ {n} → let open PB ((₃₊ n) VRel,_===_) in
               [ gate₀ {n} h ]ʷ ↑ ↑ ↑ ≈ [ gate₀ h ]ʷ
      ω↑↑↑=ω = PB.trans (PB.axiom (cong↑ (cong↑ (ω↑=ω h))))
               (PB.trans (PB.axiom (cong↑ (ω↑=ω h))) (PB.axiom (ω↑=ω h)))
    comm₀ h (g ↥) =
      PB.trans (PB.cong PB.refl (PB.sym (PB.axiom (ω↑=ω h))))
      (PB.trans (lemma-cong↑ _ _ (comm₀ h g))
                (PB.cong (PB.axiom (ω↑=ω h)) PB.refl))

    comm-gate₀-w : ∀ (h : Gate 0) (w : Circuit n) →
      let v = [ gate₀ h ]ʷ
          open PB (n VRel,_===_)
      in  w • v ≈ v • w
    comm-gate₀-w h ε       = PB.trans PB.left-unit (PB.sym PB.right-unit)
    comm-gate₀-w h [ x ]ʷ  = comm₀ h x
    comm-gate₀-w h (u • t) =
      PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl (comm-gate₀-w h t))
      (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong (comm-gate₀-w h u) PB.refl)
                PB.assoc)))

  module Single-Scalar (one : ∀ (h h' : Gate 0) → h ≡ h') =
    Central-Scalars
      (λ {n} h h' →
        Eq.subst (λ x → PB._≈_ (n VRel,_===_)
                          ([ gate₀ x ]ʷ • [ gate₀ h ]ʷ)
                          ([ gate₀ h ]ʷ • [ gate₀ x ]ʷ))
                 (one h h') PB.refl)
