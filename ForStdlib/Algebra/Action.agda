------------------------------------------------------------------------
-- The Agda standard library
--
-- Right actions of monoids and groups on a setoid.
--
-- A right action x ◁ g twists x by g, with composition read left to
-- right: x ◁ (g ∙ h) = (x ◁ g) ◁ h.  The left action of H on a monoid
-- by endomorphisms lives with the semidirect product
-- (ForStdlib.Algebra.Construct.SemiDirectProduct.Action).
--
-- (Staged in ForStdlib for upstreaming into Algebra.Action.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Action where

open import Algebra.Bundles using (RawMonoid; Group)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Right actions

-- A right action of the monoid M on the setoid S: acting by the unit
-- is the identity, and acting by a product is acting by its factors in
-- turn.  A right action of a group is a right action of its underlying
-- monoid (instantiate M with Group.rawMonoid); the inverse laws are
-- then derivable, see Group-Lemmas below.

record RightAction (M : RawMonoid b ℓ₂) (S : Setoid a ℓ₁) :
                   Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module M = RawMonoid M
    module S = Setoid S
  infixl 7 _◁_
  field
    _◁_        : S.Carrier → M.Carrier → S.Carrier
    ◁-cong     : ∀ {x x′ g g′} → x S.≈ x′ → g M.≈ g′ → x ◁ g S.≈ x′ ◁ g′
    ◁-identity : ∀ x → x ◁ M.ε S.≈ x
    ◁-compose  : ∀ x g h → x ◁ (g M.∙ h) S.≈ (x ◁ g) ◁ h

------------------------------------------------------------------------
-- Consequences for group actions

-- When the acting monoid is (the underlying monoid of) a group, every
-- g acts invertibly — the inverse action is _◁ g ⁻¹ — so acting by a
-- fixed g is injective.

module Group-Lemmas (G : Group b ℓ₂) (S : Setoid a ℓ₁)
                    (φ : RightAction (Group.rawMonoid G) S) where
  private
    module G = Group G
    module S = Setoid S
  open RightAction φ
  open ≈-Reasoning S

  ◁-inverseʳ : ∀ x g → (x ◁ g) ◁ g G.⁻¹ S.≈ x
  ◁-inverseʳ x g = begin
    (x ◁ g) ◁ g G.⁻¹    ≈⟨ S.sym (◁-compose x g (g G.⁻¹)) ⟩
    x ◁ (g G.∙ g G.⁻¹)  ≈⟨ ◁-cong S.refl (G.inverseʳ g) ⟩
    x ◁ G.ε             ≈⟨ ◁-identity x ⟩
    x                   ∎

  ◁-inverseˡ : ∀ x g → (x ◁ g G.⁻¹) ◁ g S.≈ x
  ◁-inverseˡ x g = begin
    (x ◁ g G.⁻¹) ◁ g    ≈⟨ S.sym (◁-compose x (g G.⁻¹) g) ⟩
    x ◁ (g G.⁻¹ G.∙ g)  ≈⟨ ◁-cong S.refl (G.inverseˡ g) ⟩
    x ◁ G.ε             ≈⟨ ◁-identity x ⟩
    x                   ∎

  ◁-cancelʳ : ∀ g {x y} → x ◁ g S.≈ y ◁ g → x S.≈ y
  ◁-cancelʳ g {x} {y} eq = begin
    x                 ≈⟨ S.sym (◁-inverseʳ x g) ⟩
    (x ◁ g) ◁ g G.⁻¹  ≈⟨ ◁-cong eq G.refl ⟩
    (y ◁ g) ◁ g G.⁻¹  ≈⟨ ◁-inverseʳ y g ⟩
    y                 ∎
