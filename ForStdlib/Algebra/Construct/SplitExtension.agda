------------------------------------------------------------------------
-- The Agda standard library
--
-- Split extensions of groups.
--
-- A split extension of H by N is a short exact sequence of groups
--
--      incl        proj
--   1 ─────→ N ───────→ G ───────→ H ─────→ 1
--                       ↖________/
--                          sect
--
-- that is split: proj has a homomorphic section sect (proj ∘ sect ≈ id).
-- Every semidirect product N ⋊ H is such an extension, with the obvious
-- inclusion, projection and section; this is the canonical model, and
-- (by the splitting lemma) every split extension arises this way.
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Construct.SplitExtension.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Construct.SplitExtension where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂ ; ∃-syntax)
open import Function.Definitions using (Injective)
open import Level using (Level ; _⊔_ ; suc)

open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action ; group)
open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Split extensions

-- A split extension of H by N: a group total = G together with group
-- homomorphisms incl : N → G, proj : G → H and a section sect : H → G,
-- such that the sequence 1 → N → G → H → 1 is exact and proj ∘ sect ≈ id.

record SplitExtension (N : Group a ℓ₁) (H : Group b ℓ₂)
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
    module σM = GroupMorphisms (Group.rawGroup H)     (Group.rawGroup total)
  field
    incl : GN.Carrier → GG.Carrier
    proj : GG.Carrier → GH.Carrier
    sect : GH.Carrier → GG.Carrier

    incl-homo : ιM.IsGroupHomomorphism incl
    proj-homo : πM.IsGroupHomomorphism proj
    sect-homo : σM.IsGroupHomomorphism sect

    -- exact at N: incl is injective.
    incl-injective   : Injective GN._≈_ GG._≈_ incl
    -- split: sect is a section of proj (hence exact at H, proj onto).
    proj-splits-sect : ∀ h → proj (sect h) GH.≈ h
    -- exact at G: image of incl = kernel of proj.
    proj-kills-incl  : ∀ n → proj (incl n) GH.≈ GH.ε
    ker⊆im-incl      : ∀ g → proj g GH.≈ GH.ε → ∃[ n ] incl n GG.≈ g

------------------------------------------------------------------------
-- The semidirect product is a split extension
--
-- N ⋊ H is a split extension of H by N: the inclusion is n ↦ (n , ε),
-- the projection is the second component, and the section is h ↦ (ε , h).

semidirect : (N : Group a ℓ₁) (H : Group b ℓ₂)
             (φ : Action (Group.rawMonoid N) (Group.rawMonoid H)) →
             SplitExtension N H
semidirect N H φ = record
  { total            = G⋊
  ; incl             = λ n → n , GH.ε
  ; proj             = proj₂
  ; sect             = λ h → GN.ε , h
  ; incl-homo        = isMonoidHomomorphism⇒isGroupHomomorphism N G⋊ incl-mon
  ; proj-homo        = isMonoidHomomorphism⇒isGroupHomomorphism G⋊ H proj-mon
  ; sect-homo        = isMonoidHomomorphism⇒isGroupHomomorphism H G⋊ sect-mon
  ; incl-injective   = λ eq → proj₁ eq
  ; proj-splits-sect = λ h → GH.refl
  ; proj-kills-incl  = λ n → GH.refl
  ; ker⊆im-incl      = λ g eq → proj₁ g , (GN.refl , GH.sym eq)
  }
  where
  module GN = Group N
  module GH = Group H
  G⋊ = group N H φ
  open Action φ
  module MN = MonoidMorphisms (Group.rawMonoid N)  (Group.rawMonoid G⋊)
  module MP = MonoidMorphisms (Group.rawMonoid G⋊) (Group.rawMonoid H)
  module MS = MonoidMorphisms (Group.rawMonoid H)  (Group.rawMonoid G⋊)

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

  -- sect h = (ε , h): a homomorphism because act _ ε ≈ ε.
  sect-mon : MS.IsMonoidHomomorphism (λ h → GN.ε , h)
  sect-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ eq → GN.refl , eq }
      ; homo = λ x y → GN.sym (GN.trans (GN.∙-cong GN.refl (act-ε-homo x))
                                        (GN.identityˡ GN.ε))
                     , GH.refl
      }
    ; ε-homo = GN.refl , GH.refl
    }

------------------------------------------------------------------------
-- A split extension is an extension
--
-- Forgetting the section yields a plain extension; the projection is
-- onto because it has a section.

extension : {N : Group a ℓ₁} {H : Group b ℓ₂} →
            SplitExtension N H → Extension N H
extension se = record
  { total           = SE.total
  ; incl            = SE.incl
  ; proj            = SE.proj
  ; incl-homo       = SE.incl-homo
  ; proj-homo       = SE.proj-homo
  ; incl-injective  = SE.incl-injective
  ; proj-surjective = λ h → SE.sect h , SE.proj-splits-sect h
  ; proj-kills-incl = SE.proj-kills-incl
  ; ker⊆im-incl     = SE.ker⊆im-incl
  }
  where module SE = SplitExtension se
