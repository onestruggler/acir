------------------------------------------------------------------------
-- Presentations of groups
--
-- The universal commutative quotient of the physical HH circuit group.
-- These additional commutations describe a quotient, not extra circuit
-- identities.  Structural wire operations descend to this quotient.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Abelianization where

open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_,_ ; proj₂)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.GroupLike as GL
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Structural as S

data Relations (n : ℕ) : WRel (Gen n) where
  source : ∀ {u v} → P._===_ u v → Relations n u v
  commute : ∀ u v → Relations n (u • v) (v • u)

module At (n : ℕ) where
  open PB (Relations n) public hiding (_===_)
  open PP (Relations n) using (word-setoid)
  open import Relation.Binary.Reasoning.Setoid word-setoid

  source-cong : ∀ {u v : Circuit n} → u P.≈ v → u ≈ v
  source-cong PB.refl = refl
  source-cong (PB.sym p) = sym (source-cong p)
  source-cong (PB.trans p q) = trans (source-cong p) (source-cong q)
  source-cong (PB.cong p q) = cong (source-cong p) (source-cong q)
  source-cong PB.assoc = assoc
  source-cong PB.left-unit = left-unit
  source-cong PB.right-unit = right-unit
  source-cong (PB.axiom p) = axiom (source p)

  grouplike : GL.Grouplike (Relations n)
  grouplike g = [ g ]ʷ , source-cong (proj₂ (P.grouplike n g))

  involution-commutator : ∀ u v →
    (u • u) P.≈ ε → (v • v) P.≈ ε → ((u • v) • (u • v)) ≈ ε
  involution-commutator u v uu vv = begin
    (u • v) • (u • v) ≈⟨ assoc ⟩
    u • (v • (u • v)) ≈⟨ cong refl (sym assoc) ⟩
    u • ((v • u) • v) ≈⟨ cong refl (cong (axiom (commute v u)) refl) ⟩
    u • ((u • v) • v) ≈⟨ cong refl assoc ⟩
    u • (u • (v • v)) ≈⟨ sym assoc ⟩
    (u • u) • (v • v) ≈⟨ cong (source-cong uu) (source-cong vv) ⟩
    ε • ε ≈⟨ left-unit ⟩
    ε ∎

  -- Any interpretation in a commutative presented monoid factors
  -- through the stated quotient.
  module Universal {Y : Set} (Δ : WRel Y) (f : Gen n → Word.Base.Word Y)
    (source-respects : ∀ {u v} → P._===_ u v →
      PB._≈_ Δ ((f ʷ) u) ((f ʷ) v))
    (commutative : ∀ u v → PB._≈_ Δ (u • v) (v • u)) where

    private
      respects : ∀ {u v} → Relations n u v →
        PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
      respects (source p) = source-respects p
      respects (commute u v) = commutative ((f ʷ) u) ((f ʷ) v)

    factor : ∀ {u v} → u ≈ v → PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
    factor = PP.StarCongruence.fʷ-cong (Relations n) Δ f respects

module Lift (n : ℕ) where
  private
    module A = At n
    module B = At (suc n)

  shift : ∀ {u v} → u A.≈ v → (u ↑) B.≈ (v ↑)
  shift PB.refl = B.refl
  shift (PB.sym p) = B.sym (shift p)
  shift (PB.trans p q) = B.trans (shift p) (shift q)
  shift (PB.cong p q) = B.cong (shift p) (shift q)
  shift PB.assoc = B.assoc
  shift PB.left-unit = B.left-unit
  shift PB.right-unit = B.right-unit
  shift (PB.axiom (source p)) = B.source-cong (S.cong↑ (PB.axiom p))
  shift (PB.axiom (commute u v)) = B.axiom (commute (u ↑) (v ↑))

  top : ∀ {u v} → u A.≈ v → (u ⇓) B.≈ (v ⇓)
  top PB.refl = B.refl
  top (PB.sym p) = B.sym (top p)
  top (PB.trans p q) = B.trans (top p) (top q)
  top (PB.cong p q) = B.cong (top p) (top q)
  top PB.assoc = B.assoc
  top PB.left-unit = B.left-unit
  top PB.right-unit = B.right-unit
  top (PB.axiom (source p)) = B.source-cong (S.cong⇓ (PB.axiom p))
  top (PB.axiom (commute u v)) = B.axiom (commute (u ⇓) (v ⇓))
