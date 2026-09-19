------------------------------------------------------------------------
-- Presentations of groups
--
-- Independence of the structural rules
--
-- Circuit.Base's Lift-Relation extends any gate-specific relation with
-- four structural rules: cong↑, comm₁, comm₂ and ω↑=ω.  This module
-- asks whether any of them is redundant, and answers with the models
-- of Presentation.Independence: for each rule, a family of monoids —
-- one per width, related by a shift homomorphism — in which the other
-- three hold and that rule fails.  All four are independent of one
-- another.  A fifth rule, comm₀ — a scalar commutes with every
-- generator — used to be structural; it is now Circuit.Base's theorem
-- Central-Scalars.comm₀, derived from these four once scalars commute
-- with one another.  That hypothesis cannot be dropped: in the pure
-- structural theory two distinct scalars need not commute, which is
-- the last model here.
--
-- The models are all built from the depths of letters — how many
-- times a generator has been shifted — because that is what the
-- structural rules are about: cong↑ relates depths, the comm rules
-- separate depth 0 from depth ≥ 1 or ≥ 2, and ω↑=ω says depth does
-- not matter for scalars.  Words are read into (ℕ, +) or into a free
-- monoid of depths, List ℕ under _++_, forgetting exactly what the
-- retained rules are allowed to forget: a commutative target validates
-- every comm rule at once, since each just permutes two letters, and
-- a free one validates a comm rule as soon as the gate it commutes is
-- read as ε.
--
-- The theorems are stated for the pure structural theory, the lift of
-- the empty relation, so that they hold for every gate family; adding
-- gate-specific axioms can only make more derivable.  The soundness
-- engine (Structural.Soundness) takes an arbitrary gate-specific
-- relation, so independence within a particular circuit theory is a
-- matter of supplying a model of its axioms too.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)

module Circuit.Independence (Gate : ℕ → Set) where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_ ; map)
open import Data.List.Properties
  using (++-monoid ; ++-identityʳ ; map-++ ; ∷-injectiveˡ)
open import Data.Nat using (_*_ ; _^_)
open import Data.Nat.Properties using (+-0-monoid ; +-comm ; *-distribˡ-+)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Negation using (¬_)

open import Notations
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Circuit.Base Gate
import Presentation.Base as PB
open import Presentation.Construct.Base using (EmptyRel)
open import Presentation.Independence

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- Depth of a generator: how many times it has been shifted up

depth : Gen n → ℕ
depth (gate₀ _) = 0
depth (gate₁ _) = 0
depth (gate₂ _) = 0
depth (g ↥)     = suc (depth g)

------------------------------------------------------------------------
-- Structural rules of a lifted relation

module Structural (_SRel,_===_ : (n : ℕ) → CRel n) where

  open Lift-Relation _SRel,_===_

  -- The four structural rules, by name.  The names are those of the
  -- constructors of _VRel,_===_; Agda tells the two apart by type.
  data Rule : Set where
    cong↑ comm₁ comm₂ ω↑=ω : Rule

  -- Uses r a: the rule r occurs in the axiom instance a.  Only cong↑
  -- has a premise, so only it recurses: removing a rule removes its
  -- shifted instances as well.
  Uses : Rule → n VRel, w === v → Set
  Uses r (srel _)    = ⊥
  Uses r (cong↑ a)   = r ≡ cong↑ ⊎ Uses r a
  Uses r (comm₁ _ _) = r ≡ comm₁
  Uses r (comm₂ _ _) = r ≡ comm₂
  Uses r (ω↑=ω _)    = r ≡ ω↑=ω

  -- The selection of every axiom instance not using r.
  Without : Rule → Select (n VRel,_===_)
  Without r a = ¬ Uses r a

  -- Removing r removes the shifts of what it removes, and, unless r is
  -- cong↑ itself, keeps the shifts of what it keeps.
  Without-cong↑⁻ : ∀ r {a : n VRel, w === v} →
                   Without r (cong↑ a) → Without r a
  Without-cong↑⁻ r ¬u u = ¬u (inj₂ u)

  Without-cong↑⁺ : ∀ r → r ≢ cong↑ → {a : n VRel, w === v} →
                   Without r a → Without r (cong↑ a)
  Without-cong↑⁺ r r≢cong↑ ¬u (inj₁ e) = r≢cong↑ e
  Without-cong↑⁺ r r≢cong↑ ¬u (inj₂ u) = ¬u u

  -- Derivability of an instance from the axioms not using r, and its
  -- negation.
  infix 4 _DerivableWithout_ _IndependentOf_

  _DerivableWithout_ : n VRel, w === v → Rule → Set
  a DerivableWithout r = Derivable (_ VRel,_===_) (Without r) a

  _IndependentOf_ : n VRel, w === v → Rule → Set
  a IndependentOf r = Independent (_ VRel,_===_) (Without r) a

  ----------------------------------------------------------------------
  -- Lifting a restricted congruence one wire up
  --
  -- Lift-Relation.lemma-cong↑ for a selection closed under cong↑, and
  -- so for Without r whenever r is not cong↑ itself: what is derivable
  -- without r at width n is derivable without r one wire up.

  module Lift (P : ∀ {n} → Select (n VRel,_===_))
              (P-cong↑ : ∀ {n} {w v : Circuit n} {a : n VRel, w === v} →
                         P a → P (cong↑ a))
              where

    lemma-cong↑∣ : ∀ {n} {w v : Circuit n} →
      let open PB ((n VRel,_===_) ∣ P) using (_≈_)
          open PB (((₁₊ n) VRel,_===_) ∣ P) using ()
            renaming (_≈_ to _≈↑_)
      in w ≈ v → w ↑ ≈↑ v ↑
    lemma-cong↑∣ PB.refl              = PB.refl
    lemma-cong↑∣ (PB.sym e)           = PB.sym (lemma-cong↑∣ e)
    lemma-cong↑∣ (PB.trans e e₁)      =
      PB.trans (lemma-cong↑∣ e) (lemma-cong↑∣ e₁)
    lemma-cong↑∣ (PB.cong e e₁)       =
      PB.cong (lemma-cong↑∣ e) (lemma-cong↑∣ e₁)
    lemma-cong↑∣ PB.assoc             = PB.assoc
    lemma-cong↑∣ PB.left-unit         = PB.left-unit
    lemma-cong↑∣ PB.right-unit        = PB.right-unit
    lemma-cong↑∣ (PB.axiom (a , p))   = PB.axiom (cong↑ a , P-cong↑ p)

  ----------------------------------------------------------------------
  -- Soundness of a family of models for a selection of the rules
  --
  -- A model is a monoid per width and a reading of the generators.
  -- Rules supplies soundness of each rule, guarded by the selection —
  -- for an excluded rule the guard is refutable and nothing is owed —
  -- and derives soundness of the congruence the selected axioms
  -- generate, hence independence of any instance the model separates.
  -- Shift derives the cong↑ obligation from a shift homomorphism σ
  -- that reads g ↥ as σ ⟦ g ⟧₀, which every model of a circuit theory
  -- with a stable semantics has; the model of cong↑'s own independence
  -- is the one that cannot.

  module Soundness
    (P : ∀ {n} → Select (n VRel,_===_))
    (P-cong↑ : ∀ {n} {w v : Circuit n} {a : n VRel, w === v} →
               P (cong↑ a) → P a)
    (mon : ℕ → Monoid 0ℓ 0ℓ)
    (⟦_⟧₀ : ∀ {n} → Gen n → Monoid.Carrier (mon n))
    where

    private
      module Mon {n} = Monoid (mon n)
      module M {n} = Model (n VRel,_===_) (P {n}) (mon n) (⟦_⟧₀ {n})

    open M public using (⟦_⟧)

    infix 4 _≈ₘ_
    _≈ₘ_ : Rel (Monoid.Carrier (mon n)) 0ℓ
    _≈ₘ_ = Mon._≈_

    Sound-cong↑ : Set
    Sound-cong↑ = ∀ {n} {w v : Circuit n} (a : n VRel, w === v) →
                  P (cong↑ a) → ⟦ w ⟧ ≈ₘ ⟦ v ⟧ → ⟦ w ↑ ⟧ ≈ₘ ⟦ v ↑ ⟧

    module Shift
      (σ : ∀ {n} → Monoid.Carrier (mon n) → Monoid.Carrier (mon (suc n)))
      (σ-hom : ∀ {n} → MonoidMorphisms.IsMonoidHomomorphism
                         (Monoid.rawMonoid (mon n))
                         (Monoid.rawMonoid (mon (suc n))) σ)
      (⟦↥⟧ : ∀ {n} (g : Gen n) → ⟦ g ↥ ⟧₀ ≈ₘ σ ⟦ g ⟧₀)
      where

      private
        module σ {n} = MonoidMorphisms.IsMonoidHomomorphism (σ-hom {n})

      ⟦↑⟧ : (w : Circuit n) → ⟦ w ↑ ⟧ ≈ₘ σ ⟦ w ⟧
      ⟦↑⟧ [ x ]ʷ  = ⟦↥⟧ x
      ⟦↑⟧ ε       = Mon.sym σ.ε-homo
      ⟦↑⟧ (w • v) = Mon.trans (Mon.∙-cong (⟦↑⟧ w) (⟦↑⟧ v))
                              (Mon.sym (σ.homo ⟦ w ⟧ ⟦ v ⟧))

      sound-cong↑ : Sound-cong↑
      sound-cong↑ {w = w} {v} _ _ e =
        Mon.trans (⟦↑⟧ w) (Mon.trans (σ.⟦⟧-cong e) (Mon.sym (⟦↑⟧ v)))

    module Rules
      (sound-srel : ∀ {n} {w v : Circuit n} (s : n SRel, w === v) →
                    P (srel s) → ⟦ w ⟧ ≈ₘ ⟦ v ⟧)
      (sound-cong↑ : Sound-cong↑)
      (sound-comm₁ : ∀ {n} (h : Gate 1) (g : Gen n) → P (comm₁ h g) →
                     ⟦ [ g ↥ ]ʷ • [ gate₁ h ]ʷ ⟧ ≈ₘ
                     ⟦ [ gate₁ h ]ʷ • [ g ↥ ]ʷ ⟧)
      (sound-comm₂ : ∀ {n} (h : Gate 2) (g : Gen n) → P (comm₂ h g) →
                     ⟦ [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ⟧ ≈ₘ
                     ⟦ [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ ⟧)
      (sound-ω↑=ω : ∀ {n} (ω : Gate 0) → P (ω↑=ω {n} ω) →
                    ⟦ [ gate₀ {n} ω ]ʷ ↑ ⟧ ≈ₘ ⟦ [ gate₀ ω ]ʷ ⟧)
      where

      sound-ax : (a : n VRel, w === v) → P a → ⟦ w ⟧ ≈ₘ ⟦ v ⟧
      sound-ax (srel s)    p = sound-srel s p
      sound-ax (cong↑ a)   p = sound-cong↑ a p (sound-ax a (P-cong↑ p))
      sound-ax (comm₁ h g) p = sound-comm₁ h g p
      sound-ax (comm₂ h g) p = sound-comm₂ h g p
      sound-ax (ω↑=ω ω)    p = sound-ω↑=ω ω p

      private
        module S {n} = M.Sound {n} sound-ax

      open S public using (sound ; independent)

------------------------------------------------------------------------
-- The pure structural theory
--
-- The lift of the empty relation: the structural rules and nothing
-- else.  Each rule is shown independent of the other three by a model
-- that reads letters by depth; a last model shows that the centrality
-- of a scalar needs its hypothesis.

module Pure where

  open Lift-Relation (λ n → EmptyRel) public
  open Structural (λ n → EmptyRel) public

  ----------------------------------------------------------------------
  -- ω↑=ω: weights
  --
  -- Read a letter as 2 ^ depth in (ℕ, +); shifting doubles.  Every
  -- comm rule permutes two letters, so holds in a commutative monoid;
  -- ω↑=ω would identify weights 2 and 1.

  module Weight where

    ⟦_⟧ʷ : Gen n → ℕ
    ⟦ g ⟧ʷ = 2 ^ depth g

    open Soundness (Without ω↑=ω) (Without-cong↑⁻ ω↑=ω)
      (λ _ → +-0-monoid) ⟦_⟧ʷ
    open Shift (2 *_)
      (record { isMagmaHomomorphism = record
                  { isRelHomomorphism = record { cong = Eq.cong (2 *_) }
                  ; homo = *-distribˡ-+ 2 }
              ; ε-homo = refl })
      (λ _ → refl)
    open Rules (λ ()) sound-cong↑
      (λ h g _ → +-comm ⟦ g ↥ ⟧ʷ 1)
      (λ h g _ → +-comm ⟦ g ↥ ↥ ⟧ʷ 1)
      (λ ω ¬u → ⊥-elim (¬u refl))

    ω↑=ω-independent : (ω : Gate 0) → ω↑=ω {n} ω IndependentOf ω↑=ω
    ω↑=ω-independent ω = independent (ω↑=ω ω) λ ()

  ----------------------------------------------------------------------
  -- comm₁: depths of the one-wire gates
  --
  -- Read a one-wire gate as its depth, and everything else as ε, in
  -- the free monoid List ℕ; shifting is map suc.  comm₂ commutes a
  -- letter read as ε, so holds; comm₁ would commute depths 1 and 0.

  module Depth₁ where

    ⟦_⟧¹ : Gen n → List ℕ
    ⟦ gate₀ _ ⟧¹ = []
    ⟦ gate₁ _ ⟧¹ = [ 0 ]
    ⟦ gate₂ _ ⟧¹ = []
    ⟦ g ↥ ⟧¹     = map suc ⟦ g ⟧¹

    open Soundness (Without comm₁) (Without-cong↑⁻ comm₁)
      (λ _ → ++-monoid ℕ) ⟦_⟧¹
    open Shift (map suc)
      (record { isMagmaHomomorphism = record
                  { isRelHomomorphism = record { cong = Eq.cong (map suc) }
                  ; homo = map-++ suc }
              ; ε-homo = refl })
      (λ _ → refl)
    open Rules (λ ()) sound-cong↑
      (λ h g ¬u → ⊥-elim (¬u refl))
      (λ h g _ → ++-identityʳ ⟦ g ↥ ↥ ⟧¹)
      (λ ω _ → refl)

    comm₁-independent : (h : Gate 1) →
                        comm₁ h (gate₁ {n} h) IndependentOf comm₁
    comm₁-independent h =
      independent (comm₁ h (gate₁ h)) λ e → case ∷-injectiveˡ e of λ ()

  ----------------------------------------------------------------------
  -- comm₂: depths of the two-wire gates, symmetrically

  module Depth₂ where

    ⟦_⟧² : Gen n → List ℕ
    ⟦ gate₀ _ ⟧² = []
    ⟦ gate₁ _ ⟧² = []
    ⟦ gate₂ _ ⟧² = [ 0 ]
    ⟦ g ↥ ⟧²     = map suc ⟦ g ⟧²

    open Soundness (Without comm₂) (Without-cong↑⁻ comm₂)
      (λ _ → ++-monoid ℕ) ⟦_⟧²
    open Shift (map suc)
      (record { isMagmaHomomorphism = record
                  { isRelHomomorphism = record { cong = Eq.cong (map suc) }
                  ; homo = map-++ suc }
              ; ε-homo = refl })
      (λ _ → refl)
    open Rules (λ ()) sound-cong↑
      (λ h g _ → ++-identityʳ ⟦ g ↥ ⟧²)
      (λ h g ¬u → ⊥-elim (¬u refl))
      (λ ω _ → refl)

    comm₂-independent : (h : Gate 2) →
                        comm₂ h (gate₂ {n} h) IndependentOf comm₂
    comm₂-independent h =
      independent (comm₂ h (gate₂ h)) λ e → case ∷-injectiveˡ e of λ ()

  ----------------------------------------------------------------------
  -- cong↑: depths beyond the reach of the other rules
  --
  -- Without cong↑ the remaining rules are all stated at the bottom of
  -- the circuit: comm₁ and comm₂ commute a gate at depth 0, and ω↑=ω
  -- identifies a scalar at depth 1 with one at depth 0.  So read a
  -- wire gate as its depth once that is at least 1, a scalar as its
  -- depth once that is at least 2, and everything shallower as ε, in
  -- List ℕ.  Every retained rule then holds, and no shift homomorphism
  -- is needed since none is sound.  A shifted comm₁, comm₂ or ω↑=ω is
  -- separated: it would commute depths 2 and 1, or 3 and 1, or
  -- identify depth 2 with ε.

  module Shiftless where

    -- at g k reads g at depth k more than it carries.
    at : Gen n → ℕ → List ℕ
    at (gate₀ _) zero      = []
    at (gate₀ _) (₁₊ zero) = []
    at (gate₀ _) (₂₊ k)    = [ ₂₊ k ]
    at (gate₁ _) zero      = []
    at (gate₁ _) (₁₊ k)    = [ ₁₊ k ]
    at (gate₂ _) zero      = []
    at (gate₂ _) (₁₊ k)    = [ ₁₊ k ]
    at (g ↥)     k         = at g (suc k)

    ⟦_⟧ᶜ : Gen n → List ℕ
    ⟦ g ⟧ᶜ = at g 0

    open Soundness (Without cong↑) (Without-cong↑⁻ cong↑)
      (λ _ → ++-monoid ℕ) ⟦_⟧ᶜ
    open Rules (λ ()) (λ a ¬u _ → ⊥-elim (¬u (inj₁ refl)))
      (λ h g _ → ++-identityʳ ⟦ g ↥ ⟧ᶜ)
      (λ h g _ → ++-identityʳ ⟦ g ↥ ↥ ⟧ᶜ)
      (λ ω _ → refl)

    cong↑-independent₁ : (h : Gate 1) →
                         cong↑ (comm₁ h (gate₁ {n} h)) IndependentOf cong↑
    cong↑-independent₁ h =
      independent (cong↑ (comm₁ h (gate₁ h)))
        λ e → case ∷-injectiveˡ e of λ ()

    cong↑-independent₂ : (h : Gate 2) →
                         cong↑ (comm₂ h (gate₂ {n} h)) IndependentOf cong↑
    cong↑-independent₂ h =
      independent (cong↑ (comm₂ h (gate₂ h)))
        λ e → case ∷-injectiveˡ e of λ ()

    cong↑-independent₀ : (ω : Gate 0) →
                         cong↑ (ω↑=ω {n} ω) IndependentOf cong↑
    cong↑-independent₀ ω = independent (cong↑ (ω↑=ω ω)) λ ()

  ----------------------------------------------------------------------
  -- Centrality needs its hypothesis: the scalars, in order
  --
  -- Circuit.Base derives comm₀ from the four rules and the assumption
  -- that scalars commute with one another.  The assumption is not
  -- redundant: read a scalar gate as itself, at any depth, and a wire
  -- gate as ε, in the free monoid List (Gate 0), with the identity as
  -- shift.  All four rules hold — the selection keeps every axiom —
  -- and two distinct scalars do not commute.

  module Scalars where

    ⟦_⟧ˢ : Gen n → List (Gate 0)
    ⟦ gate₀ ω ⟧ˢ = [ ω ]
    ⟦ gate₁ _ ⟧ˢ = []
    ⟦ gate₂ _ ⟧ˢ = []
    ⟦ g ↥ ⟧ˢ     = ⟦ g ⟧ˢ

    open Soundness (λ {n} → all (n VRel,_===_)) (λ _ → tt)
      (λ _ → ++-monoid (Gate 0)) ⟦_⟧ˢ
    open Shift (λ x → x)
      (record { isMagmaHomomorphism = record
                  { isRelHomomorphism = record { cong = λ e → e }
                  ; homo = λ _ _ → refl }
              ; ε-homo = refl })
      (λ _ → refl)
    open Rules (λ ()) sound-cong↑
      (λ h g _ → ++-identityʳ ⟦ g ↥ ⟧ˢ)
      (λ h g _ → ++-identityʳ ⟦ g ↥ ↥ ⟧ˢ)
      (λ ω _ → refl)

    -- Two distinct scalars need not commute.
    scalars-comm-needed : (ω ω' : Gate 0) → ω ≢ ω' →
      let open PB (n VRel,_===_) in
      ¬ ([ gate₀ {n} ω' ]ʷ • [ gate₀ ω ]ʷ ≈ [ gate₀ ω ]ʷ • [ gate₀ ω' ]ʷ)
    scalars-comm-needed ω ω' ω≢ω' e =
      ω≢ω' (Eq.sym (∷-injectiveˡ (sound (≈-all (_ VRel,_===_) e))))

  open Weight    public using (ω↑=ω-independent)
  open Depth₁    public using (comm₁-independent)
  open Depth₂    public using (comm₂-independent)
  open Shiftless public
    using (cong↑-independent₀ ; cong↑-independent₁ ; cong↑-independent₂)
  open Scalars   public using (scalars-comm-needed)
