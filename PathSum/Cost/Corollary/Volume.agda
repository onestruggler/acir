------------------------------------------------------------------------
-- Presentations of groups
--
-- The equivalence of two Clifford circuits over {H, S, CZ}, in time
-- polynomial in the volume (Amy, QPL 2018)
--
-- PathSum.Cost.Corollary decides whether two circuits C₁, C₂ over
-- {H, S, CZ} have equivalent path-sums, by their miter C₁ ++ C₂†, at a
-- cost of at most 315 (n + 3 (|C₁| + |C₂|) + 3)^12 (cost-equivᶜ), and
-- bounds the single-circuit decision in the space-time volume n · |C|
-- too, as corollary 4.4 states it.  Here is the volume form of the
-- equivalence bound, in n · (|C₁| + |C₂|):
--
--    cost (equivᶜ C₁ C₂) ≤ 315 (6 n (|C₁| + |C₂|) + 3)^12
--                                              (cost-equiv-volume),
--
-- the bound opaque as equivVolumeBound, with its defining equation
-- equivVolumeBound-def.  A gate names a wire, so n ≥ 1 as soon as one
-- of the circuits has a gate, and then
-- n + 3 (|C₁| + |C₂|) ≤ 3 (n + |C₁| + |C₂|) ≤ 6 n (|C₁| + |C₂|)
-- (PathSum.Size.Sparse.volume-≤); two empty circuits are answered in
-- one step.  equivalence-polytime-volume packages correctness, the
-- polynomial bound and the volume bound.
--
-- The factor 3 comes from the miter: S† is S³ (PathSum.Adjoint), so
-- |C₂†| ≤ 3 |C₂|.  Costs are counted in the cost model of
-- PathSum.Cost: a cost model, not a machine model; nothing is claimed
-- about Turing machines or complexity classes.  The bound is an upper
-- bound, not tight, and it is proved at a variable before being
-- instantiated (CLAUDE.md's Cost pitfall).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Cost.Corollary.Volume (M₀ : ℕ) where

open import Data.Bool.Base using (true)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (_+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; ⟦_⟧)
open import PathSum.Cost using (Cost; value; cost)
open import PathSum.Cost.Bound using (^-pos)
open import PathSum.Cost.Corollary M₀ using
  (equivᶜ; equiv-correct; cost-equiv-at; equivBound; cost-equivᶜ)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Size.Sparse M using (volume-≤)

import Data.Nat.Properties as ℕ

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The bound

opaque
  equivVolumeBound : ℕ → ℕ
  equivVolumeBound v = 315 * (3 + 6 * v) ^ 12

  equivVolumeBound-def : ∀ v → equivVolumeBound v ≡ 315 * (3 + 6 * v) ^ 12
  equivVolumeBound-def v = refl


------------------------------------------------------------------------
-- The cost in the volume

private
  gate-wire : Gate n → 1 ≤ n
  gate-wire (H w)    = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (S w)    = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (CZ w v) = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)

  -- n + 3 ℓ ≤ 3 (n + ℓ) ≤ 6 n ℓ.
  six-volume : ∀ n ℓ v → v ≡ n * ℓ → 1 ≤ n → 1 ≤ ℓ →
               3 + (n + 3 * ℓ) ≤ 3 + 6 * v
  six-volume n ℓ v eq 1≤n 1≤ℓ = ℕ.+-monoʳ-≤ 3
    (ℕ.≤-trans (ℕ.+-monoˡ-≤ (3 * ℓ) (ℕ.m≤n*m n 3))
    (ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.*-distribˡ-+ 3 n ℓ)))
    (ℕ.≤-trans (ℕ.*-monoʳ-≤ 3 (volume-≤ n ℓ 1≤n 1≤ℓ))
               (ℕ.≤-reflexive (trans (sym (ℕ.*-assoc 3 2 (n * ℓ)))
                                     (cong (6 *_) (sym eq)))))))

  volume-at : (C₁ C₂ : Circuit n) (v : ℕ) →
              v ≡ n * (length C₁ + length C₂) →
              cost (equivᶜ C₁ C₂) ≤ 315 * (3 + 6 * v) ^ 12
  volume-at [] [] v eq = ℕ.≤-trans
    (^-pos {B = 3 + 6 * v} {k = 12} (s≤s z≤n))
    (ℕ.m≤n*m ((3 + 6 * v) ^ 12) 315)
  volume-at {n} (g ∷ C₁) C₂ v eq = cost-equiv-at (g ∷ C₁) C₂ (3 + 6 * v)
    (six-volume n (length (g ∷ C₁) + length C₂) v eq (gate-wire g) (s≤s z≤n))
  volume-at {n} [] (g ∷ C₂) v eq = cost-equiv-at [] (g ∷ C₂) (3 + 6 * v)
    (six-volume n (length {A = Gate n} [] + length (g ∷ C₂)) v eq
                (gate-wire g) (s≤s z≤n))

cost-equiv-volume : (C₁ C₂ : Circuit n) →
                    cost (equivᶜ C₁ C₂) ≤
                    equivVolumeBound (n * (length C₁ + length C₂))
cost-equiv-volume {n} C₁ C₂ = subst (cost (equivᶜ C₁ C₂) ≤_)
  (sym (equivVolumeBound-def (n * (length C₁ + length C₂))))
  (volume-at C₁ C₂ (n * (length C₁ + length C₂)) refl)


------------------------------------------------------------------------
-- Equivalence of Clifford circuits, polynomial in the volume

record PolyEquivalenceᵛ {n : ℕ} (C₁ C₂ : Circuit n) : Set where
  field
    decides    : value (equivᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
    polynomial : cost (equivᶜ C₁ C₂) ≤ equivBound n (length C₁) (length C₂)
    volume     : cost (equivᶜ C₁ C₂) ≤
                 equivVolumeBound (n * (length C₁ + length C₂))

equivalence-polytime-volume : (C₁ C₂ : Circuit n) → PolyEquivalenceᵛ C₁ C₂
equivalence-polytime-volume C₁ C₂ = record
  { decides    = equiv-correct C₁ C₂
  ; polynomial = cost-equivᶜ C₁ C₂
  ; volume     = cost-equiv-volume C₁ C₂
  }
