------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 2.55 applied to the qubit Clifford extension (p = 2):
-- _Clifford,_===_ presents CMS n.
--
-- Everything the proposition needs about the group is already built:
--
--   * the extension  1 → Pauli n → CMS n → Sp(2n,2) → 1  is
--     CMS.Clifford-extension (the Vec-based extension of
--     Qubit.CliffordGroup, transported to the nested Pauli-group that a
--     presentation produces);
--   * the kernel is presented by Γ-H ⊕^ n   (Pauli.Presentation), and
--   * the quotient by the simplified symplectic rule set
--     (Symplectic.Simplified.Presentation);
--   * conj and corr are Qubit.Presentation's, and the extension relation
--     _Clifford,_===_ is by definition extension-presentation of exactly
--     these four.
--
-- What is assembled here is the instantiation, and the interpretation
-- ⟦_⟧₀ of the generators in CMS n: a gate is itself, a Pauli generator is
-- conjugation by the corresponding Pauli operator (CMS.pauliIncl).
--
-- Of the proposition's six inputs, four are discharged here:
--
--   nfpQ      Simplified.Bijective — the coset-tower normal form
--             upgraded to a bijection (nf ∘ inv-nf ≡ id from uniqueness
--             of the section), with both congruences routed through
--             Simplified.Iso;
--   nfpS      read off the Pauli presentation itself: it is already an
--             isomorphism onto Pauli-group n, and composing with the
--             coordinate map vec lands it in Pauli n, a type with
--             propositional equality (bijectiveᴾ below).  The quotient
--             factor cannot be done this way — Sp(2n,2)'s elements are
--             records of functions compared pointwise;
--   real-Q    a gate projects to its symplectic value: both sides are
--             ⟦ x ⟧ᵍ, so this is refl;
--   sound-ax  the substance — conj records conjugation in CMS n, and
--             each twisted relator's correction word is the Pauli that
--             lifting it accumulates.  Both families are proved in
--             Qubit.ExtensionSoundness over plain Clifford words
--             (conj-sound, twisted-sound); all that happens here is
--             reading them through ⟦_⟧ on the mixed alphabet, which is
--             structural since ⟦_⟧ is a monoid map into CMS n and CMS's
--             product is concatenation.
--
-- Two remain, as arguments of `presentation`:
--
--   Realises  a Pauli generator is interpreted as the inclusion of its
--             Pauli value.  Both sides are conjugation by a Pauli
--             operator, so this reduces to the coordinate identity
--             genToVec y ≡ vec n ⟦ [ y ]ʷ ⟧N, i.e. that the Pauli
--             presentation's generator values are the basis vectors;
--   nf-ε      the quotient normal form's section sends ε to ε.  NOT true
--             by computation at a variable width — the coset tower is
--             stuck on n — so it wants an induction over the levels.
--
-- Why this module exists: with `presentation` in hand, completeness of
-- _Clifford,_===_ for CMS n is one projection away, and composing it
-- with Selinger.Iso gives Selinger.Scalars.Complete-mod-scalars — the
-- single input still missing from ExactData.scalars.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.ExtensionPresentation where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Level using (0ℓ)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Presentation.Construct.Base
  using (_⊕^_ ; [_]ₗ ; [_]ᵣ ; left ; right ; comm)
open import Presentation.Construct.Properties.Extension using (tw)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.NormalForm.Setoid as SNF
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Presentation.Construct.Properties.Extension as Ext

open import Examples.Groups.Clifford.Qubit.Presentation
  using (p-2 ; p-prime ; PauliGen ; genToVec ; conj ; corr ; _Clifford,_===_)
open import Examples.Groups.Clifford.Qubit.ExtensionSoundness
  using (pw ; conj-sound ; twisted-sound)

open import Examples.Groups.Pauli.Presentation p-2 p-prime
  using (Γ-H ; Pauli-group ; Pauli-presentation)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (g* ; g-gen)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (_QRel,_===_)
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen
  as SimP

open import Data.Unit using (tt)
open import Data.Vec using (_∷_)
open import Notations
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli ; pI)
open import Examples.Groups.Clifford.Qubit.CMS
  using ( Clifford-extension ; Clifford-group ; pauliIncl
        ; vec ; nest ; vec∘nest ; vec-cong ; vec-injective )

------------------------------------------------------------------------
-- The interpretation of the generators in CMS n
--
-- A gate generator is the one-letter Clifford word; a Pauli generator is
-- conjugation by the Pauli operator it names, which is exactly the
-- inclusion of the extension (CMS.pauliIncl, i.e. the pauliWord circuit).

⟦_⟧₀ : {n : ℕ} → (PauliGen n ⊎ Gen n) → Group.Carrier (Clifford-group n)
⟦_⟧₀ {n} (inj₁ y) = pauliIncl n (genToVec y)
⟦_⟧₀     (inj₂ g) = [ g ]ʷ

------------------------------------------------------------------------
-- Proposition 2.55, instantiated

------------------------------------------------------------------------
-- The two normal-form witnesses
--
-- The quotient factor's is Simplified.Bijective's: the coset-tower
-- normal form upgraded to a bijection, using uniqueness of the section
-- for the round trip nf ∘ inv-nf ≡ id.

open import Examples.Groups.Symplectic.Simplified.Bijective p-2 p-prime g* g-gen
  using (bijective₂)

-- The Pauli factor's needs no normal-form development at all: its
-- presentation IS an isomorphism onto Pauli-group n, so composing with
-- the coordinate map vec (which is injective, and hits every vector)
-- turns it into a bijection onto Pauli n — a type with propositional
-- equality, which is what BijectiveNormalForm wants.  The quotient
-- factor cannot be handled this way: Sp(2n,2)'s elements are records of
-- functions, compared pointwise, not propositionally.

private
  module PNiso (n : ℕ) where
    module PN = _IsPresentationOf_ (Pauli-presentation n)
    open GroupMorphisms (Group.rawGroup PN.GL.•-ε-group)
                        (Group.rawGroup (Pauli-group n))
    mono   = IsGroupIsomorphism.isGroupMonomorphism PN.iso
    hom    = IsGroupMonomorphism.isGroupHomomorphism mono
    cong-N = IsGroupHomomorphism.⟦⟧-cong hom
    inj-N  = IsGroupMonomorphism.injective mono
    surj-N = IsGroupIsomorphism.surjective PN.iso
    ⟦_⟧N   = PN.⟦_⟧

-- A Pauli word's normal form is the vector it denotes.
nfᴾ : (n : ℕ) → Word (PauliGen n) → Pauli n
nfᴾ n w = vec n (PNiso.⟦_⟧N n w)

bijectiveᴾ : (n : ℕ) → BijectiveNormalForm (Γ-H ⊕^ n) (Pauli n)
bijectiveᴾ n = record
  { bijection = record
    { to        = nfᴾ n
    ; cong      = λ eq → vec-cong n (PNiso.cong-N n eq)
    ; bijective =
        (λ eq → PNiso.inj-N n (vec-injective n eq))
      , λ P → proj₁ (PNiso.surj-N n (nest n P)) , λ {z} z≈ →
          Eq.trans (vec-cong n (proj₂ (PNiso.surj-N n (nest n P)) z≈))
                   (vec∘nest n P)
    }
  }

-- NOTE for `Realises`.  It reduces to the coordinate identity
--
--   gen-vec : vec m ⟦ [ y ]ʷ ⟧N ≡ genToVec y
--
-- and the width-1 cases of that hold by `refl`.  The width-≥2 cases do
-- NOT, and the reason is not mathematical: `vec` comes from Qubit.CMS,
-- which instantiates Pauli.Semantics at ITS OWN p-2 / p-prime, while
-- `genToVec` and `pIₙ` come from Qubit.Presentation's instantiation.
-- The two are definitionally equal values of two different module
-- instances, so the tail `vec (₁₊ m) (⟦ … ⟧N .proj₂)` does not meet
-- `pIₙ` syntactically.  Align the instances first (have one module take
-- the prime from the other, as ExactExtension takes it from
-- CliffordGroup) and the recursion should go through.

module Clifford (n : ℕ) where

  nfpS = bijectiveᴾ n
  nfpQ = bijective₂ n

  -- (The proposition's own module is opened publicly; it internally
  -- names a module E, so this one is EP.)
  open module EP = Ext.Presentation
    (Γ-H ⊕^ n) (n QRel,_===_) conj corr
    (Pauli-group n) (Sp-group n) (Clifford-extension n)
    (Pauli-presentation n) (SimP.presentation {n})
    ⟦_⟧₀ nfpS nfpQ
    public

  -- One of the four is free: a gate generator's projection into
  -- Sp(2n,2) is its symplectic denotation, which is also what the
  -- quotient presentation reads off a one-letter word.  Both sides are
  -- ⟦ x ⟧ᵍ after unfolding, so the symplectic maps are equal on the nose.
  real-Q : ∀ x → Group._≈_ (Sp-group n) (proj ⟦ inj₂ x ⟧₀) ⟦ [ x ]ʷ ⟧Q
  real-Q x _ = Eq.refl

  ------------------------------------------------------------------
  -- sound-ax
  --
  -- Both families are proved in Qubit.ExtensionSoundness, over plain
  -- Clifford words; all that is needed here is to read them through the
  -- proposition's ⟦_⟧ on the mixed alphabet.  ⟦_⟧ is the monoid
  -- extension of ⟦_⟧₀ into CMS n, whose product IS concatenation, so
  -- both embeddings are structural.

  private
    embʳ : (w : Word (Gen n)) → ⟦ [ w ]ᵣ ⟧ ≡ w
    embʳ [ g ]ʷ  = Eq.refl
    embʳ ε       = Eq.refl
    embʳ (w • v) = Eq.cong₂ _•_ (embʳ w) (embʳ v)

    embˡ : (c : Word (PauliGen n)) → ⟦ [ c ]ₗ ⟧ ≡ pw c
    embˡ [ y ]ʷ  = Eq.refl
    embˡ ε       = Eq.refl
    embˡ (c • d) = Eq.cong₂ _•_ (embˡ c) (embˡ d)

  ------------------------------------------------------------------
  -- Realises
  --
  -- Both sides are conjugation by a Pauli operator — the transported
  -- inclusion is pauliIncl ∘ vec — so everything reduces to the
  -- coordinate identity: the Pauli presentation's generator values are
  -- the basis vectors genToVec names.

  sound-ax : {w v : Word (PauliGen n ⊎ Gen n)} →
             Ext.extp (Γ-H ⊕^ n) (n QRel,_===_) conj corr w v →
             Group._≈_ (Clifford-group n) ⟦ w ⟧ ⟦ v ⟧
  sound-ax (left (comm y x)) rewrite embˡ (conj x y) = conj-sound y x
  sound-ax (right (tw {u} {v} r̄))
    rewrite embʳ u | embˡ (corr r̄) | embʳ v = twisted-sound r̄

  -- The headline, once the two remaining compatibility inputs are
  -- supplied.
  presentation :
    Realises →
    SNF.BijectiveNormalForm.inv-nf nfpQ (SNF.BijectiveNormalForm.nf nfpQ ε) ≡ ε →
    (n Clifford,_===_) IsPresentationOf (Clifford-group n)
  presentation real nf-ε = dpres real sound-ax nf-ε real-Q
