------------------------------------------------------------------------
-- Presentations of groups
--
-- The group presented by the qubit Clifford relation _Clifford,_===_
-- (p = 2): the Clifford group modulo scalars, CMS n, as an extension
--
--     1 ─→ Pauli n ─→ CMS n ─→ Sp(2n, 2) ─→ 1
--
-- whose kernel is the group that the Pauli relation Γ-H ⊕^ n presents.
--
-- Examples.Groups.ProjectiveClifford.Qubit.Cocycle builds the syntactic side
-- as extension-presentation (Γ-H ⊕^ n) (n QRel,_===_) conj corr, and
-- Proposition 2.55 (Presentation.Construct.Properties.Extension) asks for
-- an Extension record whose kernel group is presented by the left factor
-- of that relation — here Pauli-group n, the iterated direct product of
-- Examples.Groups.ProjectivePauli.Presentation.
--
-- The semantic extension assembled in Qubit.CliffordGroup has for kernel
-- the Vec-based Pauli group +ₚ-group n instead.  The two are the same
-- group written differently — a nested tuple (ℤ/2 × ℤ/2) × (… × ⊤)
-- versus a vector Vec (ℤ/2 × ℤ/2) n — so this module gives the
-- isomorphism (vec / nest, reassociating the coordinates) and transports
-- the extension along it: incl is precomposed with vec, everything else
-- is inherited.  The total group is untouched, Clifford-group n =
-- CMS-group n.
--
-- The presentation statement itself — that _Clifford,_===_ presents this
-- group — lives in Qubit.Presentation, which imports this module.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.CMS where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_,_ ; ∃-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Notations using (₁₊ ; ₂₊)

-- This module is the qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pIₙ ; _+ₚ_ ; +ₚ-group)
open import Examples.Groups.ProjectivePauli.Presentation p-2 p-prime using (Pauli-group)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Semantics
  using (CMS-extension ; CMS-group)

------------------------------------------------------------------------
-- The two shapes of the Pauli group
--
-- Pauli-group n — what Γ-H ⊕^ n presents — is the n-fold direct product
-- of H = ℤ/2 × ℤ/2 built by iterating the binary product, bottoming out
-- at the trivial group; its carrier is a nested tuple.  +ₚ-group n is the
-- same group with the coordinates laid out as a vector.

-- The carrier of the presented Pauli group.
Nested : ℕ → Set
Nested n = Group.Carrier (Pauli-group n)

-- Reassociate the nested tuple into a coordinate vector, and back.
vec : (n : ℕ) → Nested n → Pauli n
vec zero      _       = []
vec (₁₊ zero) x       = x ∷ []
vec (₂₊ n)    (x , r) = x ∷ vec (₁₊ n) r

nest : (n : ℕ) → Pauli n → Nested n
nest zero      _        = Group.ε (Pauli-group zero)
nest (₁₊ zero) (x ∷ []) = x
nest (₂₊ n)    (x ∷ ps) = x , nest (₁₊ n) ps

------------------------------------------------------------------------
-- vec is a group isomorphism Pauli-group n → +ₚ-group n
--
-- The target equality is _≡_, so the round trip vec ∘ nest is an
-- equality; the other round trip only holds up to the product's pointwise
-- equality, which at n = 0 is the trivial relation of the terminal group.

vec∘nest : (n : ℕ) (P : Pauli n) → vec n (nest n P) ≡ P
vec∘nest zero      []       = Eq.refl
vec∘nest (₁₊ zero) (x ∷ []) = Eq.refl
vec∘nest (₂₊ n)    (x ∷ ps) = Eq.cong (x ∷_) (vec∘nest (₁₊ n) ps)

nest∘vec : (n : ℕ) (x : Nested n) →
           Group._≈_ (Pauli-group n) (nest n (vec n x)) x
nest∘vec zero      x       = Group.refl (Pauli-group zero)
nest∘vec (₁₊ zero) x       = Group.refl (Pauli-group (₁₊ zero))
nest∘vec (₂₊ n)    (x , r) =
  Group.refl (Pauli-group (₁₊ zero)) , nest∘vec (₁₊ n) r

-- vec turns the pointwise equality of the nested product into _≡_.
vec-cong : (n : ℕ) {x y : Nested n} →
           Group._≈_ (Pauli-group n) x y → vec n x ≡ vec n y
vec-cong zero      _          = Eq.refl
vec-cong (₁₊ zero) eq         = Eq.cong (_∷ []) (≡×≡⇒≡ eq)
vec-cong (₂₊ n)    (xeq , req) =
  Eq.cong₂ _∷_ (≡×≡⇒≡ xeq) (vec-cong (₁₊ n) req)

-- The homomorphism laws: the nested product's operation is _+ₚ_ read
-- coordinate by coordinate.
vec-homo : (n : ℕ) (x y : Nested n) →
           vec n (Group._∙_ (Pauli-group n) x y) ≡ vec n x +ₚ vec n y
vec-homo zero      x       y       = Eq.refl
vec-homo (₁₊ zero) x       y       = Eq.refl
vec-homo (₂₊ n)    (x , r) (y , s) =
  Eq.cong (_ ∷_) (vec-homo (₁₊ n) r s)

vec-ε : (n : ℕ) → vec n (Group.ε (Pauli-group n)) ≡ pIₙ {n}
vec-ε zero      = Eq.refl
vec-ε (₁₊ zero) = Eq.refl
vec-ε (₂₊ n)    = Eq.cong (pI ∷_) (vec-ε (₁₊ n))

-- Injectivity, through the round trip.
vec-injective : (n : ℕ) {x y : Nested n} →
                vec n x ≡ vec n y → Group._≈_ (Pauli-group n) x y
vec-injective n {x} {y} eq = GP.trans (GP.sym (nest∘vec n x))
  (GP.trans (GP.reflexive (Eq.cong (nest n) eq)) (nest∘vec n y))
  where module GP = Group (Pauli-group n)

module Iso (n : ℕ) where

  private
    module MN = MonoidMorphisms (Group.rawMonoid (Pauli-group n))
                                (Group.rawMonoid (+ₚ-group n))
  open GroupMorphisms (Group.rawGroup (Pauli-group n))
                      (Group.rawGroup (+ₚ-group n))
    using (IsGroupIsomorphism)

  vec-mon : MN.IsMonoidHomomorphism (vec n)
  vec-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = vec-cong n }
      ; homo              = vec-homo n
      }
    ; ε-homo = vec-ε n
    }

  -- Pauli-group n ≅ +ₚ-group n.
  Pauli≅+ₚ : IsGroupIsomorphism (vec n)
  Pauli≅+ₚ = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
                                (Pauli-group n) (+ₚ-group n) vec-mon
      ; injective           = vec-injective n
      }
    ; surjective = λ P → nest n P , λ {z} z≈ →
                     Eq.trans (vec-cong n z≈) (vec∘nest n P)
    }

------------------------------------------------------------------------
-- The extension, with the presented Pauli group as its kernel
--
-- Only the inclusion changes: a nested Pauli is first read as a vector
-- and then conjugated with.  The projection, its surjectivity and the
-- exactness at CMS n are inherited unchanged.

module Transport (n : ℕ) where

  private
    E : Extension (+ₚ-group n) (Sp-group n)
    E = CMS-extension n

    module GP = Group (Pauli-group n)
    module GC = Group (CMS-group n)

    module ιV = GroupMorphisms (Group.rawGroup (+ₚ-group n))
                               (Group.rawGroup (CMS-group n))
    incl-cong = ιV.IsGroupHomomorphism.⟦⟧-cong (Extension.incl-homo E)
    incl-∙    = ιV.IsGroupHomomorphism.homo    (Extension.incl-homo E)
    incl-ε    = ιV.IsGroupHomomorphism.ε-homo  (Extension.incl-homo E)

    module MN = MonoidMorphisms (Group.rawMonoid (Pauli-group n))
                                (Group.rawMonoid (CMS-group n))

  -- Conjugation by a nested Pauli operator.
  inclᴾ : GP.Carrier → GC.Carrier
  inclᴾ x = Extension.incl E (vec n x)

  -- The laws are proved pointwise on P4: equality in CMS n is equal
  -- action, so its implicit endpoints are not inferable from a proof
  -- term, and transitivity is Eq.trans at a fixed point x instead.
  inclᴾ-mon : MN.IsMonoidHomomorphism inclᴾ
  inclᴾ-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ eq → incl-cong (vec-cong n eq) }
      ; homo              = λ x y z →
          Eq.trans (incl-cong (vec-homo n x y) z)
                   (incl-∙ (vec n x) (vec n y) z)
      }
    ; ε-homo = λ z → Eq.trans (incl-cong (vec-ε n) z) (incl-ε z)
    }

  -- Exactness at CMS n: a Clifford in the kernel of proj is conjugation
  -- by the nested reading of the Pauli the untransported extension gives.
  ker-nested : ∀ g → Group._≈_ (Sp-group n) (Extension.proj E g)
                                            (Group.ε (Sp-group n)) →
               ∃[ x ] GC._≈_ (inclᴾ x) g
  ker-nested g triv with Extension.ker⊆im-incl E g triv
  ... | P , eq =
    nest n P , λ z → Eq.trans (incl-cong (vec∘nest n P) z) (eq z)

  extension : Extension (Pauli-group n) (Sp-group n)
  extension = record
    { total           = CMS-group n
    ; incl            = inclᴾ
    ; proj            = Extension.proj E
    ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          (Pauli-group n) (CMS-group n) inclᴾ-mon
    ; proj-homo       = Extension.proj-homo E
    ; incl-injective  = λ eq → vec-injective n (Extension.incl-injective E eq)
    ; proj-surjective = Extension.proj-surjective E
    ; proj-kills-incl = λ x → Extension.proj-kills-incl E (vec n x)
    ; ker⊆im-incl     = ker-nested
    }

------------------------------------------------------------------------
-- The extension group presented by _Clifford,_===_

-- 1 → Pauli n → CMS n → Sp(2n, 2) → 1, with the Pauli group in the shape
-- that Γ-H ⊕^ n presents.
Clifford-extension : (n : ℕ) → Extension (Pauli-group n) (Sp-group n)
Clifford-extension n = Transport.extension n

-- The total group: the Clifford group modulo scalars (definitionally
-- CMS-group n — the transport changes only the inclusion).
Clifford-group : ℕ → Group 0ℓ 0ℓ
Clifford-group n = Extension.total (Clifford-extension n)

-- Conjugation by a Pauli operator, as a Clifford word: the inclusion of
-- the untransported extension, used to interpret the Pauli generators.
pauliIncl : (n : ℕ) → Pauli n → Group.Carrier (Clifford-group n)
pauliIncl n = Extension.incl (CMS-extension n)

-- The scalar layer above this one, 1 → ⟨ω⟩ → Exact n → CMS n → 1, with
-- Clifford-group n as its quotient, is outside the projective
-- development: see Examples.Groups.Clifford.Qubit.Semantics.
