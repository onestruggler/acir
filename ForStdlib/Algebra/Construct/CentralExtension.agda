------------------------------------------------------------------------
-- The Agda standard library
--
-- Central extensions of a group H by an abelian group A, presented by a
-- normalised 2-cocycle.
--
--               incl       proj
--   1 ─────→ A ───────→ A ×_c H ───────→ H ─────→ 1
--
-- Elements are pairs |A| × |H|, as for the direct product, but the first
-- component is twisted on multiplication by a cocycle c : H → H → A:
--
--     (a , x) ∙ (b , y) = (a ∙ b ∙ c x y , x ∙ y).
--
-- Unlike ForStdlib.Algebra.Construct.SemiDirectProduct, H does not act
-- on A — the image of A is central — so this construction reaches the
-- extensions a semidirect product cannot: taking c ≡ ε recovers the
-- direct product, and a cohomologically nontrivial c gives a NON-SPLIT
-- extension, one with no homomorphic section of proj.
--
-- The cocycle identity is exactly what makes the twisted product
-- associative, and normalisation (c ε x = c x ε = ε) is what makes
-- (ε , ε) a unit.  Commutativity of A is needed for associativity: the
-- three A-components and the two cocycle terms must be rearranged past
-- one another.
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Construct.CentralExtension.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Construct.CentralExtension where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Algebra.Core using (Op₁ ; Op₂)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Algebra.Structures using (IsGroup)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (Pointwise ; ×-isEquivalence)
open import Level using (Level ; _⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Normalised 2-cocycles

-- c x y is the A-valued defect incurred when the chosen lifts of x and
-- y are multiplied.  A section of proj exists precisely when c is a
-- coboundary; c ≡ ε is the split case.

record Cocycle (A : AbelianGroup a ℓ₁) (H : Group b ℓ₂) :
               Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module A = AbelianGroup A
    module H = Group H
  field
    c       : H.Carrier → H.Carrier → A.Carrier
    c-cong  : ∀ {x x′ y y′} → x H.≈ x′ → y H.≈ y′ → c x y A.≈ c x′ y′
    -- Normalisation: the unit lifts to the unit.
    c-εˡ    : ∀ x → c H.ε x A.≈ A.ε
    c-εʳ    : ∀ x → c x H.ε A.≈ A.ε
    -- The cocycle identity, i.e. associativity of the lifts.
    cocycle : ∀ x y z →
              (c x y A.∙ c (x H.∙ y) z) A.≈ (c y z A.∙ c x (y H.∙ z))

------------------------------------------------------------------------
-- The twisted product A ×_c H

module _ (A : AbelianGroup a ℓ₁) (H : Group b ℓ₂) (γ : Cocycle A H) where

  private
    module A = AbelianGroup A
    module H = Group H
  open Cocycle γ
  open ≈-Reasoning A.setoid

  infixl 7 _∙′_
  infix  8 _⁻¹′

  Carrier′ : Set (a ⊔ b)
  Carrier′ = A.Carrier × H.Carrier

  _≈′_ : Carrier′ → Carrier′ → Set (ℓ₁ ⊔ ℓ₂)
  _≈′_ = Pointwise A._≈_ H._≈_

  _∙′_ : Op₂ Carrier′
  (a₁ , x) ∙′ (a₂ , y) = ((a₁ A.∙ a₂) A.∙ c x y) , (x H.∙ y)

  ε′ : Carrier′
  ε′ = A.ε , H.ε

  -- The inverse must also undo the cocycle defect c x x⁻¹.
  _⁻¹′ : Op₁ Carrier′
  (a₁ , x) ⁻¹′ = (a₁ A.∙ c x (x H.⁻¹)) A.⁻¹ , x H.⁻¹

  ------------------------------------------------------------------------
  -- Two rearrangements in the abelian group A

  private
    shuffleˡ : ∀ p q u r v →
               (((p A.∙ q) A.∙ u) A.∙ r) A.∙ v A.≈ ((p A.∙ q) A.∙ r) A.∙ (u A.∙ v)
    shuffleˡ p q u r v = begin
      (((p A.∙ q) A.∙ u) A.∙ r) A.∙ v
        ≈⟨ A.∙-congʳ (A.assoc (p A.∙ q) u r) ⟩
      ((p A.∙ q) A.∙ (u A.∙ r)) A.∙ v
        ≈⟨ A.∙-congʳ (A.∙-congˡ (A.comm u r)) ⟩
      ((p A.∙ q) A.∙ (r A.∙ u)) A.∙ v
        ≈⟨ A.∙-congʳ (A.sym (A.assoc (p A.∙ q) r u)) ⟩
      (((p A.∙ q) A.∙ r) A.∙ u) A.∙ v
        ≈⟨ A.assoc ((p A.∙ q) A.∙ r) u v ⟩
      ((p A.∙ q) A.∙ r) A.∙ (u A.∙ v) ∎

    shuffleʳ : ∀ p q r u v →
               (p A.∙ ((q A.∙ r) A.∙ u)) A.∙ v A.≈ ((p A.∙ q) A.∙ r) A.∙ (u A.∙ v)
    shuffleʳ p q r u v = begin
      (p A.∙ ((q A.∙ r) A.∙ u)) A.∙ v
        ≈⟨ A.∙-congʳ (A.sym (A.assoc p (q A.∙ r) u)) ⟩
      ((p A.∙ (q A.∙ r)) A.∙ u) A.∙ v
        ≈⟨ A.∙-congʳ (A.∙-congʳ (A.sym (A.assoc p q r))) ⟩
      (((p A.∙ q) A.∙ r) A.∙ u) A.∙ v
        ≈⟨ A.assoc ((p A.∙ q) A.∙ r) u v ⟩
      ((p A.∙ q) A.∙ r) A.∙ (u A.∙ v) ∎

    -- c x x⁻¹ ≈ c x⁻¹ x, from the cocycle identity at (x , x⁻¹ , x):
    -- both middle terms normalise away.
    c-inv-sym : ∀ x → c x (x H.⁻¹) A.≈ c (x H.⁻¹) x
    c-inv-sym x = begin
      c x (x H.⁻¹)
        ≈⟨ A.sym (A.identityʳ _) ⟩
      c x (x H.⁻¹) A.∙ A.ε
        ≈⟨ A.∙-congˡ (A.sym mid₁) ⟩
      c x (x H.⁻¹) A.∙ c (x H.∙ x H.⁻¹) x
        ≈⟨ cocycle x (x H.⁻¹) x ⟩
      c (x H.⁻¹) x A.∙ c x (x H.⁻¹ H.∙ x)
        ≈⟨ A.∙-congˡ mid₂ ⟩
      c (x H.⁻¹) x A.∙ A.ε
        ≈⟨ A.identityʳ _ ⟩
      c (x H.⁻¹) x ∎
      where
      mid₁ : c (x H.∙ x H.⁻¹) x A.≈ A.ε
      mid₁ = A.trans (c-cong (H.inverseʳ x) H.refl) (c-εˡ x)
      mid₂ : c x (x H.⁻¹ H.∙ x) A.≈ A.ε
      mid₂ = A.trans (c-cong H.refl (H.inverseˡ x)) (c-εʳ x)

    -- (a ∙ (a ∙ C)⁻¹) ∙ C ≈ ε: the shape both inverse laws reduce to.
    cancel : ∀ a₁ C → (a₁ A.∙ (a₁ A.∙ C) A.⁻¹) A.∙ C A.≈ A.ε
    cancel a₁ C = begin
      (a₁ A.∙ (a₁ A.∙ C) A.⁻¹) A.∙ C
        ≈⟨ A.assoc a₁ ((a₁ A.∙ C) A.⁻¹) C ⟩
      a₁ A.∙ ((a₁ A.∙ C) A.⁻¹ A.∙ C)
        ≈⟨ A.∙-congˡ (A.comm ((a₁ A.∙ C) A.⁻¹) C) ⟩
      a₁ A.∙ (C A.∙ (a₁ A.∙ C) A.⁻¹)
        ≈⟨ A.sym (A.assoc a₁ C ((a₁ A.∙ C) A.⁻¹)) ⟩
      (a₁ A.∙ C) A.∙ (a₁ A.∙ C) A.⁻¹
        ≈⟨ A.inverseʳ (a₁ A.∙ C) ⟩
      A.ε ∎

  ------------------------------------------------------------------------
  -- The group laws

  private
    assoc′ : ∀ u v w → ((u ∙′ v) ∙′ w) ≈′ (u ∙′ (v ∙′ w))
    assoc′ (a₁ , x) (a₂ , y) (a₃ , z) = first , H.assoc x y z
      where
      first : (((a₁ A.∙ a₂) A.∙ c x y) A.∙ a₃) A.∙ c (x H.∙ y) z
            A.≈ (a₁ A.∙ ((a₂ A.∙ a₃) A.∙ c y z)) A.∙ c x (y H.∙ z)
      first = begin
        (((a₁ A.∙ a₂) A.∙ c x y) A.∙ a₃) A.∙ c (x H.∙ y) z
          ≈⟨ shuffleˡ a₁ a₂ (c x y) a₃ (c (x H.∙ y) z) ⟩
        ((a₁ A.∙ a₂) A.∙ a₃) A.∙ (c x y A.∙ c (x H.∙ y) z)
          ≈⟨ A.∙-congˡ (cocycle x y z) ⟩
        ((a₁ A.∙ a₂) A.∙ a₃) A.∙ (c y z A.∙ c x (y H.∙ z))
          ≈⟨ A.sym (shuffleʳ a₁ a₂ a₃ (c y z) (c x (y H.∙ z))) ⟩
        (a₁ A.∙ ((a₂ A.∙ a₃) A.∙ c y z)) A.∙ c x (y H.∙ z) ∎

    identityˡ′ : ∀ u → (ε′ ∙′ u) ≈′ u
    identityˡ′ (a₁ , x) = first , H.identityˡ x
      where
      first : (A.ε A.∙ a₁) A.∙ c H.ε x A.≈ a₁
      first = begin
        (A.ε A.∙ a₁) A.∙ c H.ε x ≈⟨ A.∙-congˡ (c-εˡ x) ⟩
        (A.ε A.∙ a₁) A.∙ A.ε     ≈⟨ A.identityʳ _ ⟩
        A.ε A.∙ a₁               ≈⟨ A.identityˡ a₁ ⟩
        a₁ ∎

    identityʳ′ : ∀ u → (u ∙′ ε′) ≈′ u
    identityʳ′ (a₁ , x) = first , H.identityʳ x
      where
      first : (a₁ A.∙ A.ε) A.∙ c x H.ε A.≈ a₁
      first = begin
        (a₁ A.∙ A.ε) A.∙ c x H.ε ≈⟨ A.∙-congˡ (c-εʳ x) ⟩
        (a₁ A.∙ A.ε) A.∙ A.ε     ≈⟨ A.identityʳ _ ⟩
        a₁ A.∙ A.ε               ≈⟨ A.identityʳ a₁ ⟩
        a₁ ∎

    inverseˡ′ : ∀ u → ((u ⁻¹′) ∙′ u) ≈′ ε′
    inverseˡ′ (a₁ , x) = first , H.inverseˡ x
      where
      C = c x (x H.⁻¹)
      first : ((a₁ A.∙ C) A.⁻¹ A.∙ a₁) A.∙ c (x H.⁻¹) x A.≈ A.ε
      first = begin
        ((a₁ A.∙ C) A.⁻¹ A.∙ a₁) A.∙ c (x H.⁻¹) x
          ≈⟨ A.∙-congˡ (A.sym (c-inv-sym x)) ⟩
        ((a₁ A.∙ C) A.⁻¹ A.∙ a₁) A.∙ C
          ≈⟨ A.∙-congʳ (A.comm ((a₁ A.∙ C) A.⁻¹) a₁) ⟩
        (a₁ A.∙ (a₁ A.∙ C) A.⁻¹) A.∙ C
          ≈⟨ cancel a₁ C ⟩
        A.ε ∎

    inverseʳ′ : ∀ u → (u ∙′ (u ⁻¹′)) ≈′ ε′
    inverseʳ′ (a₁ , x) = cancel a₁ (c x (x H.⁻¹)) , H.inverseʳ x

    ∙-cong′ : ∀ {u u′ v v′} → u ≈′ u′ → v ≈′ v′ → (u ∙′ v) ≈′ (u′ ∙′ v′)
    ∙-cong′ (ea , ex) (eb , ey) =
      A.∙-cong (A.∙-cong ea eb) (c-cong ex ey) , H.∙-cong ex ey

    ⁻¹-cong′ : ∀ {u u′} → u ≈′ u′ → (u ⁻¹′) ≈′ (u′ ⁻¹′)
    ⁻¹-cong′ (ea , ex) =
      A.⁻¹-cong (A.∙-cong ea (c-cong ex (H.⁻¹-cong ex))) , H.⁻¹-cong ex

  isGroup′ : IsGroup _≈′_ _∙′_ ε′ _⁻¹′
  isGroup′ = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ×-isEquivalence A.isEquivalence H.isEquivalence
          ; ∙-cong        = ∙-cong′
          }
        ; assoc = assoc′
        }
      ; identity = identityˡ′ , identityʳ′
      }
    ; inverse = inverseˡ′ , inverseʳ′
    ; ⁻¹-cong = ⁻¹-cong′
    }

  group : Group (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
  group = record { isGroup = isGroup′ }

------------------------------------------------------------------------
-- The trivial cocycle
--
-- c ≡ ε satisfies the laws, and the product it twists is untwisted: the
-- direct product A × H, which is the semidirect product with a trivial
-- action.  This is the split case, and it makes precise what a non-split
-- extension needs — not a different construction, but a cocycle that is
-- not a coboundary.

trivialCocycle : (A : AbelianGroup a ℓ₁) (H : Group b ℓ₂) → Cocycle A H
trivialCocycle A H = record
  { c       = λ _ _ → A.ε
  ; c-cong  = λ _ _ → A.refl
  ; c-εˡ    = λ _ → A.refl
  ; c-εʳ    = λ _ → A.refl
  ; cocycle = λ _ _ _ → A.refl
  }
  where module A = AbelianGroup A

------------------------------------------------------------------------
-- The twisted product is an extension
--
-- incl a = (a , ε) and proj = proj₂, exactly as for the semidirect
-- product; what changes is only the multiplication they sit inside.

centralExtension : (A : AbelianGroup a ℓ₁) (H : Group b ℓ₂)
                   (γ : Cocycle A H) →
                   Extension (AbelianGroup.group A) H
centralExtension A H γ = record
  { total           = G
  ; incl            = λ a₁ → a₁ , H.ε
  ; proj            = proj₂
  ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                        (AbelianGroup.group A) G incl-mon
  ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                        G H proj-mon
  ; incl-injective  = λ eq → proj₁ eq
  ; proj-surjective = λ h → (A.ε , h) , H.refl
  ; proj-kills-incl = λ _ → H.refl
  ; ker⊆im-incl     = λ u eq → proj₁ u , (A.refl , H.sym eq)
  }
  where
  module A = AbelianGroup A
  module H = Group H
  open Cocycle γ
  open ≈-Reasoning A.setoid

  G = group A H γ

  module MA = MonoidMorphisms (Group.rawMonoid (AbelianGroup.group A))
                              (Group.rawMonoid G)
  module MP = MonoidMorphisms (Group.rawMonoid G) (Group.rawMonoid H)

  -- incl is a homomorphism because c is normalised: the two lifted units
  -- multiply with no defect.
  incl-mon : MA.IsMonoidHomomorphism (λ a₁ → a₁ , H.ε)
  incl-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ eq → eq , H.refl }
      ; homo              = λ a₁ a₂ → homo a₁ a₂ , H.sym (H.identityˡ H.ε)
      }
    ; ε-homo = A.refl , H.refl
    }
    where
    homo : ∀ a₁ a₂ → (a₁ A.∙ a₂) A.≈ (a₁ A.∙ a₂) A.∙ c H.ε H.ε
    homo a₁ a₂ = A.sym (begin
      (a₁ A.∙ a₂) A.∙ c H.ε H.ε ≈⟨ A.∙-congˡ (c-εˡ H.ε) ⟩
      (a₁ A.∙ a₂) A.∙ A.ε       ≈⟨ A.identityʳ _ ⟩
      a₁ A.∙ a₂ ∎)

  -- proj = proj₂ is a homomorphism on the nose: the cocycle only ever
  -- touches the first component.
  proj-mon : MP.IsMonoidHomomorphism proj₂
  proj-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = proj₂ }
      ; homo              = λ _ _ → H.refl
      }
    ; ε-homo = H.refl
    }
