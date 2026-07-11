------------------------------------------------------------------------
-- The Agda standard library
--
-- Extensions of groups.
--
-- An extension of H by N is a short exact sequence of groups
--
--               incl       proj
--   1 ─────→ N ───────→ G ───────→ H ─────→ 1
--
-- i.e. incl is injective, proj is surjective, and the image of incl is
-- exactly the kernel of proj.  Unlike a split extension there need be no
-- section of proj.  Every semidirect product N ⋊ H is such an extension.
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Construct.Extension.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Construct.Extension where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂ ; ∃-syntax)
open import Function.Definitions using (Injective)
open import Level using (Level ; _⊔_ ; suc)

open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action ; group)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Extensions

-- An extension of H by N: a group total = G with group homomorphisms
-- incl : N → G and proj : G → H forming a short exact sequence.

record Extension (N : Group a ℓ₁) (H : Group b ℓ₂)
                 : Set (suc (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)) where
  private
    module GN = Group N
    module GH = Group H
  field
    total : Group (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  private
    module GG = Group total
    module ιM = GroupMorphisms (Group.rawGroup N)     (Group.rawGroup total)
    module πM = GroupMorphisms (Group.rawGroup total) (Group.rawGroup H)
  field
    incl : GN.Carrier → GG.Carrier
    proj : GG.Carrier → GH.Carrier

    incl-homo : ιM.IsGroupHomomorphism incl
    proj-homo : πM.IsGroupHomomorphism proj

    -- exact at N: incl is injective.
    incl-injective  : Injective GN._≈_ GG._≈_ incl
    -- exact at H: proj is surjective.
    proj-surjective : ∀ h → ∃[ g ] proj g GH.≈ h
    -- exact at G: image of incl = kernel of proj.
    proj-kills-incl : ∀ n → proj (incl n) GH.≈ GH.ε
    ker⊆im-incl     : ∀ g → proj g GH.≈ GH.ε → ∃[ n ] incl n GG.≈ g

------------------------------------------------------------------------
-- The semidirect product is an extension
--
-- N ⋊ H is an extension of H by N: the inclusion is n ↦ (n , ε), the
-- projection is the second component (which is onto, hit by (ε , h)).

semidirect : (N : Group a ℓ₁) (H : Group b ℓ₂)
             (φ : Action (Group.rawMonoid N) (Group.rawMonoid H)) →
             Extension N H
semidirect N H φ = record
  { total           = G⋊
  ; incl            = λ n → n , GH.ε
  ; proj            = proj₂
  ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism N G⋊ incl-mon
  ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism G⋊ H proj-mon
  ; incl-injective  = λ eq → proj₁ eq
  ; proj-surjective = λ h → (GN.ε , h) , GH.refl
  ; proj-kills-incl = λ n → GH.refl
  ; ker⊆im-incl     = λ g eq → proj₁ g , (GN.refl , GH.sym eq)
  }
  where
  module GN = Group N
  module GH = Group H
  G⋊ = group N H φ
  open Action φ
  module MN = MonoidMorphisms (Group.rawMonoid N)  (Group.rawMonoid G⋊)
  module MP = MonoidMorphisms (Group.rawMonoid G⋊) (Group.rawMonoid H)

  -- incl n = (n , ε): a homomorphism because ε acts trivially.
  incl-mon : MN.IsMonoidHomomorphism (λ n → n , GH.ε)
  incl-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ eq → eq , GH.refl }
      ; homo = λ x y → GN.sym (GN.∙-cong GN.refl (act-identity y))
                     , GH.sym (GH.identityˡ GH.ε)
      }
    ; ε-homo = GN.refl , GH.refl
    }

  -- proj = proj₂: a homomorphism on the nose.
  proj-mon : MP.IsMonoidHomomorphism proj₂
  proj-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = proj₂ }
      ; homo = λ _ _ → GH.refl
      }
    ; ε-homo = GH.refl
    }
