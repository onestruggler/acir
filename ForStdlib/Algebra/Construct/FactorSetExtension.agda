------------------------------------------------------------------------
-- The Agda standard library
--
-- Extensions of a group Q by an abelian group K carrying an action of
-- Q, presented by a factor set.
--
--               incl              proj
--   1 ─────→ K ───────→ K ×_f Q ───────→ Q ─────→ 1
--
-- Elements are pairs |K| × |Q|, as for the direct product, but the
-- first component is twisted both by the action of Q on K and by a
-- factor set f : Q → Q → K:
--
--     (a , x) ∙ (b , y) = ((a ∙ act x b) ∙ f x y , x ∙ y).
--
-- This subsumes the two neighbouring constructions:
--
--   * f ≡ ε gives the semidirect product K ⋊ Q of
--     ForStdlib.Algebra.Construct.SemiDirectProduct — up to the
--     trailing ∙ ε, this is its multiplication — the split case;
--   * a trivial action gives exactly the multiplication of the central
--     extension of ForStdlib.Algebra.Construct.CentralExtension, where
--     the image of K is central;
--   * both trivial gives the direct product.
--
-- The main result is Theorem 9.8 of Rotman, "An Introduction to
-- Homological Algebra" (2nd ed., §9.1.2): the factor sets are exactly
-- the normalised 2-cocycles.  That is, f arises as the defect
--
--     ℓ x ∙ ℓ y = incl (f x y) ∙ ℓ (x ∙ y)
--
-- of a lifting ℓ of *some* extension of Q by K realising the action if
-- and only if f is normalised (f ε x ≈ ε ≈ f x ε) and satisfies the
-- cocycle identity
--
--     f x y ∙ f (x ∙ y) z ≈ act x (f y z) ∙ f x (y ∙ z).
--
-- Necessity is Proposition 9.7 there — it is just associativity in the
-- total group, read through the lifting.  Sufficiency is the twisted
-- product above, together with the lifting ℓ x = (ε , x).  So a factor
-- set is the obstruction to a lifting being a homomorphism, and the
-- construction below turns any such obstruction back into a group.
--
-- Commutativity of K is needed for associativity: the three K-components
-- and the two factor-set terms must be rearranged past one another.
--
-- (Staged in ForStdlib for upstreaming into
-- Algebra.Construct.FactorSetExtension.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Construct.FactorSetExtension where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Algebra.Core using (Op₁ ; Op₂)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Algebra.Structures using (IsGroup)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (Pointwise ; ×-isEquivalence)
open import Level using (Level ; _⊔_ ; suc)
import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import ForStdlib.Algebra.Construct.CentralExtension using (Cocycle)
open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Normalised 2-cocycles

-- f x y is the K-valued defect incurred when the chosen lifts of x and
-- y are multiplied.  A homomorphic lifting exists precisely when f is a
-- coboundary; f ≡ ε is the split case.

record IsNormalisedCocycle
         (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
         (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q))
         (f : Group.Carrier Q → Group.Carrier Q → AbelianGroup.Carrier K) :
         Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module K = AbelianGroup K
    module Q = Group Q
  open Action φ
  field
    f-cong  : ∀ {x x′ y y′} → x Q.≈ x′ → y Q.≈ y′ → f x y K.≈ f x′ y′
    -- Normalisation: the unit lifts to the unit.
    f-εˡ    : ∀ x → f Q.ε x K.≈ K.ε
    f-εʳ    : ∀ x → f x Q.ε K.≈ K.ε
    -- The cocycle identity, i.e. associativity of the lifts.
    cocycle : ∀ x y z →
              (f x y K.∙ f (x Q.∙ y) z) K.≈ (act x (f y z) K.∙ f x (y Q.∙ z))

record FactorSet (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
                 (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q)) :
                 Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    f : Group.Carrier Q → Group.Carrier Q → AbelianGroup.Carrier K
    isNormalisedCocycle : IsNormalisedCocycle K Q φ f

  open IsNormalisedCocycle isNormalisedCocycle public

------------------------------------------------------------------------
-- Being a factor set

-- What it means for f to *be* a factor set: some extension of Q by K
-- realising the action has a lifting whose defect is f.  A lifting is a
-- section of proj that preserves the unit; it need not be a
-- homomorphism, and realising the action means that conjugating the
-- image of K by a lift is acting.

record IsFactorSet (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
                   (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q))
                   (f : Group.Carrier Q → Group.Carrier Q →
                        AbelianGroup.Carrier K) :
                   Set (suc (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)) where
  private
    module K = AbelianGroup K
    module Q = Group Q
  open Action φ
  field
    extension : Extension K.group Q
  private
    module E = Extension extension
    module G = Group E.total
  field
    lifting      : Q.Carrier → G.Carrier
    lifting-cong : ∀ {x y} → x Q.≈ y → lifting x G.≈ lifting y
    lifting-ε    : lifting Q.ε G.≈ G.ε
    lifting-proj : ∀ x → E.proj (lifting x) Q.≈ x
    -- The extension realises the action.
    realizes     : ∀ x u → (lifting x G.∙ E.incl u) G.∙ (lifting x) G.⁻¹
                           G.≈ E.incl (act x u)
    -- f is the defect of the lifting.
    factors      : ∀ x y → lifting x G.∙ lifting y
                           G.≈ E.incl (f x y) G.∙ lifting (x Q.∙ y)

------------------------------------------------------------------------
-- The twisted product K ×_f Q

module _ (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
         (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q))
         (γ : FactorSet K Q φ) where

  private
    module K = AbelianGroup K
    module Q = Group Q
  open Action φ
  open FactorSet γ
  open ≈-Reasoning K.setoid

  infixl 7 _∙′_
  infix  8 _⁻¹′

  Carrier′ : Set (a ⊔ b)
  Carrier′ = K.Carrier × Q.Carrier

  _≈′_ : Carrier′ → Carrier′ → Set (ℓ₁ ⊔ ℓ₂)
  _≈′_ = Pointwise K._≈_ Q._≈_

  _∙′_ : Op₂ Carrier′
  (a₁ , x) ∙′ (a₂ , y) = ((a₁ K.∙ act x a₂) K.∙ f x y) , (x Q.∙ y)

  ε′ : Carrier′
  ε′ = K.ε , Q.ε

  -- The inverse must undo both the action and the defect f x x⁻¹.
  _⁻¹′ : Op₁ Carrier′
  (a₁ , x) ⁻¹′ = act (x Q.⁻¹) ((a₁ K.∙ f x (x Q.⁻¹)) K.⁻¹) , x Q.⁻¹

  ------------------------------------------------------------------------
  -- Rearrangements in K and consequences of the action laws

  private
    shuffleˡ : ∀ p q u r v →
               (((p K.∙ q) K.∙ u) K.∙ r) K.∙ v K.≈ ((p K.∙ q) K.∙ r) K.∙ (u K.∙ v)
    shuffleˡ p q u r v = begin
      (((p K.∙ q) K.∙ u) K.∙ r) K.∙ v
        ≈⟨ K.∙-congʳ (K.assoc (p K.∙ q) u r) ⟩
      ((p K.∙ q) K.∙ (u K.∙ r)) K.∙ v
        ≈⟨ K.∙-congʳ (K.∙-congˡ (K.comm u r)) ⟩
      ((p K.∙ q) K.∙ (r K.∙ u)) K.∙ v
        ≈⟨ K.∙-congʳ (K.sym (K.assoc (p K.∙ q) r u)) ⟩
      (((p K.∙ q) K.∙ r) K.∙ u) K.∙ v
        ≈⟨ K.assoc ((p K.∙ q) K.∙ r) u v ⟩
      ((p K.∙ q) K.∙ r) K.∙ (u K.∙ v) ∎

    shuffleʳ : ∀ p q r u v →
               (p K.∙ ((q K.∙ r) K.∙ u)) K.∙ v K.≈ ((p K.∙ q) K.∙ r) K.∙ (u K.∙ v)
    shuffleʳ p q r u v = begin
      (p K.∙ ((q K.∙ r) K.∙ u)) K.∙ v
        ≈⟨ K.∙-congʳ (K.sym (K.assoc p (q K.∙ r) u)) ⟩
      ((p K.∙ (q K.∙ r)) K.∙ u) K.∙ v
        ≈⟨ K.∙-congʳ (K.∙-congʳ (K.sym (K.assoc p q r))) ⟩
      (((p K.∙ q) K.∙ r) K.∙ u) K.∙ v
        ≈⟨ K.assoc ((p K.∙ q) K.∙ r) u v ⟩
      ((p K.∙ q) K.∙ r) K.∙ (u K.∙ v) ∎

    -- (a ∙ (a ∙ C)⁻¹) ∙ C ≈ ε: the shape both inverse laws reduce to.
    cancel : ∀ a₁ C → (a₁ K.∙ (a₁ K.∙ C) K.⁻¹) K.∙ C K.≈ K.ε
    cancel a₁ C = begin
      (a₁ K.∙ (a₁ K.∙ C) K.⁻¹) K.∙ C
        ≈⟨ K.assoc a₁ ((a₁ K.∙ C) K.⁻¹) C ⟩
      a₁ K.∙ ((a₁ K.∙ C) K.⁻¹ K.∙ C)
        ≈⟨ K.∙-congˡ (K.comm ((a₁ K.∙ C) K.⁻¹) C) ⟩
      a₁ K.∙ (C K.∙ (a₁ K.∙ C) K.⁻¹)
        ≈⟨ K.sym (K.assoc a₁ C ((a₁ K.∙ C) K.⁻¹)) ⟩
      (a₁ K.∙ C) K.∙ (a₁ K.∙ C) K.⁻¹
        ≈⟨ K.inverseʳ (a₁ K.∙ C) ⟩
      K.ε ∎

    -- Acting by x undoes acting by x ⁻¹.
    act-inverseʳ : ∀ x u → act x (act (x Q.⁻¹) u) K.≈ u
    act-inverseʳ x u = begin
      act x (act (x Q.⁻¹) u)  ≈⟨ K.sym (act-compose x (x Q.⁻¹) u) ⟩
      act (x Q.∙ x Q.⁻¹) u    ≈⟨ act-cong (Q.inverseʳ x) K.refl ⟩
      act Q.ε u               ≈⟨ act-identity u ⟩
      u                       ∎

    -- f x⁻¹ x ≈ x⁻¹ · f x x⁻¹, from the cocycle identity at
    -- (x⁻¹ , x , x⁻¹): both middle terms normalise away.
    f-inv-sym : ∀ x → f (x Q.⁻¹) x K.≈ act (x Q.⁻¹) (f x (x Q.⁻¹))
    f-inv-sym x = begin
      f (x Q.⁻¹) x
        ≈⟨ K.sym (K.identityʳ _) ⟩
      f (x Q.⁻¹) x K.∙ K.ε
        ≈⟨ K.∙-congˡ (K.sym mid₁) ⟩
      f (x Q.⁻¹) x K.∙ f (x Q.⁻¹ Q.∙ x) (x Q.⁻¹)
        ≈⟨ cocycle (x Q.⁻¹) x (x Q.⁻¹) ⟩
      act (x Q.⁻¹) (f x (x Q.⁻¹)) K.∙ f (x Q.⁻¹) (x Q.∙ x Q.⁻¹)
        ≈⟨ K.∙-congˡ mid₂ ⟩
      act (x Q.⁻¹) (f x (x Q.⁻¹)) K.∙ K.ε
        ≈⟨ K.identityʳ _ ⟩
      act (x Q.⁻¹) (f x (x Q.⁻¹)) ∎
      where
      mid₁ : f (x Q.⁻¹ Q.∙ x) (x Q.⁻¹) K.≈ K.ε
      mid₁ = K.trans (f-cong (Q.inverseˡ x) Q.refl) (f-εˡ (x Q.⁻¹))
      mid₂ : f (x Q.⁻¹) (x Q.∙ x Q.⁻¹) K.≈ K.ε
      mid₂ = K.trans (f-cong Q.refl (Q.inverseʳ x)) (f-εʳ (x Q.⁻¹))

  ------------------------------------------------------------------------
  -- The group laws

  private
    assoc′ : ∀ u v w → ((u ∙′ v) ∙′ w) ≈′ (u ∙′ (v ∙′ w))
    assoc′ (a₁ , x) (a₂ , y) (a₃ , z) = first , Q.assoc x y z
      where
      expand : act x ((a₂ K.∙ act y a₃) K.∙ f y z)
               K.≈ (act x a₂ K.∙ act (x Q.∙ y) a₃) K.∙ act x (f y z)
      expand = begin
        act x ((a₂ K.∙ act y a₃) K.∙ f y z)
          ≈⟨ act-∙-homo x (a₂ K.∙ act y a₃) (f y z) ⟩
        act x (a₂ K.∙ act y a₃) K.∙ act x (f y z)
          ≈⟨ K.∙-congʳ (act-∙-homo x a₂ (act y a₃)) ⟩
        (act x a₂ K.∙ act x (act y a₃)) K.∙ act x (f y z)
          ≈⟨ K.∙-congʳ (K.∙-congˡ (K.sym (act-compose x y a₃))) ⟩
        (act x a₂ K.∙ act (x Q.∙ y) a₃) K.∙ act x (f y z) ∎

      first : (((a₁ K.∙ act x a₂) K.∙ f x y) K.∙ act (x Q.∙ y) a₃)
                K.∙ f (x Q.∙ y) z
            K.≈ (a₁ K.∙ act x ((a₂ K.∙ act y a₃) K.∙ f y z)) K.∙ f x (y Q.∙ z)
      first = begin
        (((a₁ K.∙ act x a₂) K.∙ f x y) K.∙ act (x Q.∙ y) a₃) K.∙ f (x Q.∙ y) z
          ≈⟨ shuffleˡ a₁ (act x a₂) (f x y) (act (x Q.∙ y) a₃) (f (x Q.∙ y) z) ⟩
        ((a₁ K.∙ act x a₂) K.∙ act (x Q.∙ y) a₃)
          K.∙ (f x y K.∙ f (x Q.∙ y) z)
          ≈⟨ K.∙-congˡ (cocycle x y z) ⟩
        ((a₁ K.∙ act x a₂) K.∙ act (x Q.∙ y) a₃)
          K.∙ (act x (f y z) K.∙ f x (y Q.∙ z))
          ≈⟨ K.sym (shuffleʳ a₁ (act x a₂) (act (x Q.∙ y) a₃)
                             (act x (f y z)) (f x (y Q.∙ z))) ⟩
        (a₁ K.∙ ((act x a₂ K.∙ act (x Q.∙ y) a₃) K.∙ act x (f y z)))
          K.∙ f x (y Q.∙ z)
          ≈⟨ K.∙-congʳ (K.∙-congˡ (K.sym expand)) ⟩
        (a₁ K.∙ act x ((a₂ K.∙ act y a₃) K.∙ f y z)) K.∙ f x (y Q.∙ z) ∎

    identityˡ′ : ∀ u → (ε′ ∙′ u) ≈′ u
    identityˡ′ (a₁ , x) = first , Q.identityˡ x
      where
      first : (K.ε K.∙ act Q.ε a₁) K.∙ f Q.ε x K.≈ a₁
      first = begin
        (K.ε K.∙ act Q.ε a₁) K.∙ f Q.ε x ≈⟨ K.∙-congˡ (f-εˡ x) ⟩
        (K.ε K.∙ act Q.ε a₁) K.∙ K.ε     ≈⟨ K.identityʳ _ ⟩
        K.ε K.∙ act Q.ε a₁               ≈⟨ K.identityˡ _ ⟩
        act Q.ε a₁                       ≈⟨ act-identity a₁ ⟩
        a₁ ∎

    identityʳ′ : ∀ u → (u ∙′ ε′) ≈′ u
    identityʳ′ (a₁ , x) = first , Q.identityʳ x
      where
      first : (a₁ K.∙ act x K.ε) K.∙ f x Q.ε K.≈ a₁
      first = begin
        (a₁ K.∙ act x K.ε) K.∙ f x Q.ε ≈⟨ K.∙-congˡ (f-εʳ x) ⟩
        (a₁ K.∙ act x K.ε) K.∙ K.ε     ≈⟨ K.identityʳ _ ⟩
        a₁ K.∙ act x K.ε               ≈⟨ K.∙-congˡ (act-ε-homo x) ⟩
        a₁ K.∙ K.ε                     ≈⟨ K.identityʳ a₁ ⟩
        a₁ ∎

    inverseˡ′ : ∀ u → ((u ⁻¹′) ∙′ u) ≈′ ε′
    inverseˡ′ (a₁ , x) = first , Q.inverseˡ x
      where
      C = f x (x Q.⁻¹)
      first : (act (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹) K.∙ act (x Q.⁻¹) a₁)
                K.∙ f (x Q.⁻¹) x
            K.≈ K.ε
      first = begin
        (act (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹) K.∙ act (x Q.⁻¹) a₁) K.∙ f (x Q.⁻¹) x
          ≈⟨ K.∙-congʳ (K.sym (act-∙-homo (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹) a₁)) ⟩
        act (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹ K.∙ a₁) K.∙ f (x Q.⁻¹) x
          ≈⟨ K.∙-congˡ (f-inv-sym x) ⟩
        act (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹ K.∙ a₁) K.∙ act (x Q.⁻¹) C
          ≈⟨ K.sym (act-∙-homo (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹ K.∙ a₁) C) ⟩
        act (x Q.⁻¹) (((a₁ K.∙ C) K.⁻¹ K.∙ a₁) K.∙ C)
          ≈⟨ act-cong Q.refl (K.∙-congʳ (K.comm ((a₁ K.∙ C) K.⁻¹) a₁)) ⟩
        act (x Q.⁻¹) ((a₁ K.∙ (a₁ K.∙ C) K.⁻¹) K.∙ C)
          ≈⟨ act-cong Q.refl (cancel a₁ C) ⟩
        act (x Q.⁻¹) K.ε
          ≈⟨ act-ε-homo (x Q.⁻¹) ⟩
        K.ε ∎

    inverseʳ′ : ∀ u → (u ∙′ (u ⁻¹′)) ≈′ ε′
    inverseʳ′ (a₁ , x) = first , Q.inverseʳ x
      where
      C = f x (x Q.⁻¹)
      first : (a₁ K.∙ act x (act (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹))) K.∙ C K.≈ K.ε
      first = begin
        (a₁ K.∙ act x (act (x Q.⁻¹) ((a₁ K.∙ C) K.⁻¹))) K.∙ C
          ≈⟨ K.∙-congʳ (K.∙-congˡ (act-inverseʳ x ((a₁ K.∙ C) K.⁻¹))) ⟩
        (a₁ K.∙ (a₁ K.∙ C) K.⁻¹) K.∙ C
          ≈⟨ cancel a₁ C ⟩
        K.ε ∎

    ∙-cong′ : ∀ {u u′ v v′} → u ≈′ u′ → v ≈′ v′ → (u ∙′ v) ≈′ (u′ ∙′ v′)
    ∙-cong′ (ea , ex) (eb , ey) =
      K.∙-cong (K.∙-cong ea (act-cong ex eb)) (f-cong ex ey) , Q.∙-cong ex ey

    ⁻¹-cong′ : ∀ {u u′} → u ≈′ u′ → (u ⁻¹′) ≈′ (u′ ⁻¹′)
    ⁻¹-cong′ (ea , ex) =
      act-cong (Q.⁻¹-cong ex)
               (K.⁻¹-cong (K.∙-cong ea (f-cong ex (Q.⁻¹-cong ex))))
      , Q.⁻¹-cong ex

  isGroup′ : IsGroup _≈′_ _∙′_ ε′ _⁻¹′
  isGroup′ = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ×-isEquivalence K.isEquivalence Q.isEquivalence
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
  -- The twisted product is an extension
  --
  -- incl a = (a , ε) and proj = proj₂, exactly as for the semidirect
  -- product; what changes is only the multiplication they sit inside.

  factorSetExtension : Extension K.group Q
  factorSetExtension = record
    { total           = group
    ; incl            = λ a₁ → a₁ , Q.ε
    ; proj            = proj₂
    ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          K.group group incl-mon
    ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          group Q proj-mon
    ; incl-injective  = λ eq → proj₁ eq
    ; proj-surjective = λ x → (K.ε , x) , Q.refl
    ; proj-kills-incl = λ _ → Q.refl
    ; ker⊆im-incl     = λ u eq → proj₁ u , (K.refl , Q.sym eq)
    }
    where
    module MK = MonoidMorphisms (Group.rawMonoid K.group) (Group.rawMonoid group)
    module MP = MonoidMorphisms (Group.rawMonoid group)   (Group.rawMonoid Q)

    -- incl is a homomorphism because f is normalised and the unit acts
    -- trivially: the two lifted units multiply with no defect.
    incl-mon : MK.IsMonoidHomomorphism (λ a₁ → a₁ , Q.ε)
    incl-mon = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ eq → eq , Q.refl }
        ; homo              = λ a₁ a₂ → homo a₁ a₂ , Q.sym (Q.identityˡ Q.ε)
        }
      ; ε-homo = K.refl , Q.refl
      }
      where
      homo : ∀ a₁ a₂ → (a₁ K.∙ a₂) K.≈ (a₁ K.∙ act Q.ε a₂) K.∙ f Q.ε Q.ε
      homo a₁ a₂ = K.sym (begin
        (a₁ K.∙ act Q.ε a₂) K.∙ f Q.ε Q.ε ≈⟨ K.∙-congˡ (f-εˡ Q.ε) ⟩
        (a₁ K.∙ act Q.ε a₂) K.∙ K.ε       ≈⟨ K.identityʳ _ ⟩
        a₁ K.∙ act Q.ε a₂                 ≈⟨ K.∙-congˡ (act-identity a₂) ⟩
        a₁ K.∙ a₂ ∎)

    -- proj = proj₂ is a homomorphism on the nose: the twisting only ever
    -- touches the first component.
    proj-mon : MP.IsMonoidHomomorphism proj₂
    proj-mon = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = proj₂ }
        ; homo              = λ _ _ → Q.refl
        }
      ; ε-homo = Q.refl
      }

  ------------------------------------------------------------------------
  -- Theorem 9.8, sufficiency
  --
  -- The extension above realises the action, and the lifting x ↦ (ε , x)
  -- has f for its factor set.  So every normalised 2-cocycle is a factor
  -- set.

  private
    lifting′ : Q.Carrier → Carrier′
    lifting′ x = K.ε , x

    realizes′ : ∀ x u →
                ((lifting′ x ∙′ (u , Q.ε)) ∙′ (lifting′ x ⁻¹′)) ≈′ (act x u , Q.ε)
    realizes′ x u = first , second
      where
      C = f x (x Q.⁻¹)

      unit : ((K.ε K.∙ act x u) K.∙ f x Q.ε) K.≈ act x u
      unit = begin
        (K.ε K.∙ act x u) K.∙ f x Q.ε ≈⟨ K.∙-congˡ (f-εʳ x) ⟩
        (K.ε K.∙ act x u) K.∙ K.ε     ≈⟨ K.identityʳ _ ⟩
        K.ε K.∙ act x u               ≈⟨ K.identityˡ _ ⟩
        act x u ∎

      undo : ∀ v → act (x Q.∙ Q.ε) (act (x Q.⁻¹) v) K.≈ v
      undo v = begin
        act (x Q.∙ Q.ε) (act (x Q.⁻¹) v) ≈⟨ act-cong (Q.identityʳ x) K.refl ⟩
        act x (act (x Q.⁻¹) v)           ≈⟨ act-inverseʳ x v ⟩
        v ∎

      first : (((K.ε K.∙ act x u) K.∙ f x Q.ε)
                 K.∙ act (x Q.∙ Q.ε) (act (x Q.⁻¹) ((K.ε K.∙ C) K.⁻¹)))
                K.∙ f (x Q.∙ Q.ε) (x Q.⁻¹)
            K.≈ act x u
      first = begin
        (((K.ε K.∙ act x u) K.∙ f x Q.ε)
           K.∙ act (x Q.∙ Q.ε) (act (x Q.⁻¹) ((K.ε K.∙ C) K.⁻¹)))
          K.∙ f (x Q.∙ Q.ε) (x Q.⁻¹)
          ≈⟨ K.∙-cong (K.∙-cong unit (undo ((K.ε K.∙ C) K.⁻¹)))
                      (f-cong (Q.identityʳ x) Q.refl) ⟩
        (act x u K.∙ (K.ε K.∙ C) K.⁻¹) K.∙ C
          ≈⟨ K.∙-congʳ (K.∙-congˡ (K.⁻¹-cong (K.identityˡ C))) ⟩
        (act x u K.∙ C K.⁻¹) K.∙ C
          ≈⟨ K.assoc (act x u) (C K.⁻¹) C ⟩
        act x u K.∙ (C K.⁻¹ K.∙ C)
          ≈⟨ K.∙-congˡ (K.inverseˡ C) ⟩
        act x u K.∙ K.ε
          ≈⟨ K.identityʳ _ ⟩
        act x u ∎

      second : (x Q.∙ Q.ε) Q.∙ x Q.⁻¹ Q.≈ Q.ε
      second = Q.trans (Q.∙-congʳ (Q.identityʳ x)) (Q.inverseʳ x)

    factors′ : ∀ x y → (lifting′ x ∙′ lifting′ y)
                       ≈′ ((f x y , Q.ε) ∙′ lifting′ (x Q.∙ y))
    factors′ x y = first , Q.sym (Q.identityˡ (x Q.∙ y))
      where
      first : (K.ε K.∙ act x K.ε) K.∙ f x y
            K.≈ (f x y K.∙ act Q.ε K.ε) K.∙ f Q.ε (x Q.∙ y)
      first = begin
        (K.ε K.∙ act x K.ε) K.∙ f x y
          ≈⟨ K.∙-congʳ (K.∙-congˡ (act-ε-homo x)) ⟩
        (K.ε K.∙ K.ε) K.∙ f x y
          ≈⟨ K.∙-congʳ (K.identityʳ K.ε) ⟩
        K.ε K.∙ f x y
          ≈⟨ K.identityˡ _ ⟩
        f x y
          ≈⟨ K.sym (K.identityʳ _) ⟩
        f x y K.∙ K.ε
          ≈⟨ K.∙-congˡ (K.sym (act-ε-homo Q.ε)) ⟩
        f x y K.∙ act Q.ε K.ε
          ≈⟨ K.sym (K.identityʳ _) ⟩
        (f x y K.∙ act Q.ε K.ε) K.∙ K.ε
          ≈⟨ K.∙-congˡ (K.sym (f-εˡ (x Q.∙ y))) ⟩
        (f x y K.∙ act Q.ε K.ε) K.∙ f Q.ε (x Q.∙ y) ∎

  isFactorSet : IsFactorSet K Q φ f
  isFactorSet = record
    { extension    = factorSetExtension
    ; lifting      = lifting′
    ; lifting-cong = λ eq → K.refl , eq
    ; lifting-ε    = K.refl , Q.refl
    ; lifting-proj = λ _ → Q.refl
    ; realizes     = realizes′
    ; factors      = factors′
    }

------------------------------------------------------------------------
-- Theorem 9.8
--
-- f is a factor set if and only if it is a normalised 2-cocycle.

-- Sufficiency: the twisted product above, with the lifting x ↦ (ε , x).

isNormalisedCocycle⇒isFactorSet :
  (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
  (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q))
  {f : Group.Carrier Q → Group.Carrier Q → AbelianGroup.Carrier K} →
  IsNormalisedCocycle K Q φ f → IsFactorSet K Q φ f
isNormalisedCocycle⇒isFactorSet K Q φ {f} nc =
  isFactorSet K Q φ record { f = f ; isNormalisedCocycle = nc }

-- Necessity (Rotman, Proposition 9.7): normalisation is the lifting
-- preserving the unit, and the cocycle identity is associativity in the
-- total group, read through the lifting and pulled back along incl.

isFactorSet⇒isNormalisedCocycle :
  (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
  (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q))
  {f : Group.Carrier Q → Group.Carrier Q → AbelianGroup.Carrier K} →
  IsFactorSet K Q φ f → IsNormalisedCocycle K Q φ f
isFactorSet⇒isNormalisedCocycle K Q φ {f} ifs = record
  { f-cong  = f-cong
  ; f-εˡ    = f-εˡ
  ; f-εʳ    = f-εʳ
  ; cocycle = cocycle
  }
  where
  module K = AbelianGroup K
  module Q = Group Q
  open Action φ
  open IsFactorSet ifs
  open Extension extension using (incl ; incl-homo ; incl-injective)
  module G = Group (Extension.total extension)
  module ιM = GroupMorphisms K.rawGroup (Group.rawGroup (Extension.total extension))
  open ιM.IsGroupHomomorphism incl-homo using (homo ; ε-homo)
  open GroupProperties (Extension.total extension) using (∙-cancelʳ)
  open ≈-Reasoning G.setoid

  -- Conjugating incl u by a lift of x is acting by x.
  conj : ∀ x u → lifting x G.∙ incl u G.≈ incl (act x u) G.∙ lifting x
  conj x u = begin
    lifting x G.∙ incl u
      ≈⟨ G.sym (G.identityʳ _) ⟩
    (lifting x G.∙ incl u) G.∙ G.ε
      ≈⟨ G.∙-congˡ (G.sym (G.inverseˡ (lifting x))) ⟩
    (lifting x G.∙ incl u) G.∙ ((lifting x) G.⁻¹ G.∙ lifting x)
      ≈⟨ G.sym (G.assoc _ _ _) ⟩
    ((lifting x G.∙ incl u) G.∙ (lifting x) G.⁻¹) G.∙ lifting x
      ≈⟨ G.∙-congʳ (realizes x u) ⟩
    incl (act x u) G.∙ lifting x ∎

  f-cong : ∀ {x x′ y y′} → x Q.≈ x′ → y Q.≈ y′ → f x y K.≈ f x′ y′
  f-cong {x} {x′} {y} {y′} ex ey =
    incl-injective (∙-cancelʳ (lifting (x Q.∙ y)) _ _ (begin
      incl (f x y) G.∙ lifting (x Q.∙ y)
        ≈⟨ G.sym (factors x y) ⟩
      lifting x G.∙ lifting y
        ≈⟨ G.∙-cong (lifting-cong ex) (lifting-cong ey) ⟩
      lifting x′ G.∙ lifting y′
        ≈⟨ factors x′ y′ ⟩
      incl (f x′ y′) G.∙ lifting (x′ Q.∙ y′)
        ≈⟨ G.∙-congˡ (lifting-cong (Q.sym (Q.∙-cong ex ey))) ⟩
      incl (f x′ y′) G.∙ lifting (x Q.∙ y) ∎))

  f-εˡ : ∀ x → f Q.ε x K.≈ K.ε
  f-εˡ x = incl-injective (∙-cancelʳ (lifting x) _ _ (begin
    incl (f Q.ε x) G.∙ lifting x
      ≈⟨ G.∙-congˡ (lifting-cong (Q.sym (Q.identityˡ x))) ⟩
    incl (f Q.ε x) G.∙ lifting (Q.ε Q.∙ x)
      ≈⟨ G.sym (factors Q.ε x) ⟩
    lifting Q.ε G.∙ lifting x
      ≈⟨ G.∙-congʳ lifting-ε ⟩
    G.ε G.∙ lifting x
      ≈⟨ G.∙-congʳ (G.sym ε-homo) ⟩
    incl K.ε G.∙ lifting x ∎))

  f-εʳ : ∀ x → f x Q.ε K.≈ K.ε
  f-εʳ x = incl-injective (∙-cancelʳ (lifting x) _ _ (begin
    incl (f x Q.ε) G.∙ lifting x
      ≈⟨ G.∙-congˡ (lifting-cong (Q.sym (Q.identityʳ x))) ⟩
    incl (f x Q.ε) G.∙ lifting (x Q.∙ Q.ε)
      ≈⟨ G.sym (factors x Q.ε) ⟩
    lifting x G.∙ lifting Q.ε
      ≈⟨ G.∙-congˡ lifting-ε ⟩
    lifting x G.∙ G.ε
      ≈⟨ G.identityʳ _ ⟩
    lifting x
      ≈⟨ G.sym (G.identityˡ _) ⟩
    G.ε G.∙ lifting x
      ≈⟨ G.∙-congʳ (G.sym ε-homo) ⟩
    incl K.ε G.∙ lifting x ∎))

  cocycle : ∀ x y z →
            (f x y K.∙ f (x Q.∙ y) z) K.≈ (act x (f y z) K.∙ f x (y Q.∙ z))
  cocycle x y z =
    incl-injective (∙-cancelʳ (lifting ((x Q.∙ y) Q.∙ z)) _ _ (begin
      incl (f x y K.∙ f (x Q.∙ y) z) G.∙ lifting ((x Q.∙ y) Q.∙ z)
        ≈⟨ G.∙-congʳ (homo (f x y) (f (x Q.∙ y) z)) ⟩
      (incl (f x y) G.∙ incl (f (x Q.∙ y) z)) G.∙ lifting ((x Q.∙ y) Q.∙ z)
        ≈⟨ G.assoc _ _ _ ⟩
      incl (f x y) G.∙ (incl (f (x Q.∙ y) z) G.∙ lifting ((x Q.∙ y) Q.∙ z))
        ≈⟨ G.∙-congˡ (G.sym (factors (x Q.∙ y) z)) ⟩
      incl (f x y) G.∙ (lifting (x Q.∙ y) G.∙ lifting z)
        ≈⟨ G.sym (G.assoc _ _ _) ⟩
      (incl (f x y) G.∙ lifting (x Q.∙ y)) G.∙ lifting z
        ≈⟨ G.∙-congʳ (G.sym (factors x y)) ⟩
      (lifting x G.∙ lifting y) G.∙ lifting z
        ≈⟨ G.assoc _ _ _ ⟩
      lifting x G.∙ (lifting y G.∙ lifting z)
        ≈⟨ G.∙-congˡ (factors y z) ⟩
      lifting x G.∙ (incl (f y z) G.∙ lifting (y Q.∙ z))
        ≈⟨ G.sym (G.assoc _ _ _) ⟩
      (lifting x G.∙ incl (f y z)) G.∙ lifting (y Q.∙ z)
        ≈⟨ G.∙-congʳ (conj x (f y z)) ⟩
      (incl (act x (f y z)) G.∙ lifting x) G.∙ lifting (y Q.∙ z)
        ≈⟨ G.assoc _ _ _ ⟩
      incl (act x (f y z)) G.∙ (lifting x G.∙ lifting (y Q.∙ z))
        ≈⟨ G.∙-congˡ (factors x (y Q.∙ z)) ⟩
      incl (act x (f y z))
        G.∙ (incl (f x (y Q.∙ z)) G.∙ lifting (x Q.∙ (y Q.∙ z)))
        ≈⟨ G.sym (G.assoc _ _ _) ⟩
      (incl (act x (f y z)) G.∙ incl (f x (y Q.∙ z)))
        G.∙ lifting (x Q.∙ (y Q.∙ z))
        ≈⟨ G.∙-congʳ (G.sym (homo (act x (f y z)) (f x (y Q.∙ z)))) ⟩
      incl (act x (f y z) K.∙ f x (y Q.∙ z)) G.∙ lifting (x Q.∙ (y Q.∙ z))
        ≈⟨ G.∙-congˡ (lifting-cong (Q.sym (Q.assoc x y z))) ⟩
      incl (act x (f y z) K.∙ f x (y Q.∙ z)) G.∙ lifting ((x Q.∙ y) Q.∙ z) ∎))

------------------------------------------------------------------------
-- Special cases

-- The trivial action, under which every extension below is central.

trivialAction : (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂) →
                Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q)
trivialAction K Q = record
  { act          = λ _ u → u
  ; act-cong     = λ _ eq → eq
  ; act-ε-homo   = λ _ → K.refl
  ; act-∙-homo   = λ _ _ _ → K.refl
  ; act-identity = λ _ → K.refl
  ; act-compose  = λ _ _ _ → K.refl
  }
  where module K = AbelianGroup K

-- A central extension is the special case of a trivial action: the
-- cocycles of ForStdlib.Algebra.Construct.CentralExtension are exactly
-- the factor sets for the trivial action, and the twisted products they
-- name carry the very same multiplication, unit and inverse.

fromCocycle : (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂) →
              Cocycle K Q → FactorSet K Q (trivialAction K Q)
fromCocycle K Q γ = record
  { f                   = c
  ; isNormalisedCocycle = record
    { f-cong  = c-cong
    ; f-εˡ    = c-εˡ
    ; f-εʳ    = c-εʳ
    ; cocycle = cocycle
    }
  }
  where open Cocycle γ

-- The trivial factor set, whose twisted product is the semidirect
-- product K ⋊ Q up to the trailing ∙ ε: the split case, where the
-- lifting x ↦ (ε , x) is a homomorphism.

trivialFactorSet : (K : AbelianGroup a ℓ₁) (Q : Group b ℓ₂)
                   (φ : Action (AbelianGroup.rawMonoid K)
                               (Group.rawMonoid Q)) →
                   FactorSet K Q φ
trivialFactorSet K Q φ = record
  { f                   = λ _ _ → K.ε
  ; isNormalisedCocycle = record
    { f-cong  = λ _ _ → K.refl
    ; f-εˡ    = λ _ → K.refl
    ; f-εʳ    = λ _ → K.refl
    ; cocycle = λ x _ _ → K.∙-congʳ (K.sym (act-ε-homo x))
    }
  }
  where
  module K = AbelianGroup K
  open Action φ
