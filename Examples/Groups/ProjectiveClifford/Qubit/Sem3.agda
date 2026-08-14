------------------------------------------------------------------------
-- Presentations of groups
--
-- The one-qubit Clifford extension as a twisted product (p = 2):
--
--     1 ─→ Pauli1 ─→ Pauli1 ×_f Sp(2, 2) ─→ Sp(2, 2) ─→ 1
--
-- This is the factor-set presentation, from
-- ForStdlib.Algebra.Construct.FactorSetExtension (Rotman, Theorem 9.8),
-- of the extension that Qubit.Semantics builds concretely at width 1:
--
--     1 ─→ Pauli n ─→ CMS n ─→ Sp(2n, 2) ─→ 1.
--
-- The two ingredients Theorem 9.8 asks for are
--
--   * K = the one-qubit phaseless Pauli group ℤ/2 × ℤ/2 (Pauli1, with
--     _+₁_), which is +₁-group of Examples.Groups.ProjectivePauli.
--     Semantics made into an AbelianGroup bundle;
--   * Q = Sp(2, 2) = Sp-group 1 of Examples.Groups.Symplectic.Semantics;
--   * φ = the linear action of a symplectic transformation on a Pauli,
--     read on Pauli1 rather than on the length-one vector Pauli 1 — this
--     is `ap`, transported along the (definitional) isomorphism
--     Pauli1 ≅ Pauli 1;
--   * γ = a factor set for φ.
--
-- φ is built here in full.  γ is left as a parameter — the named hole of
-- this development — because it is not determined by K, Q and φ: it is
-- the defect
--
--     f S T = ℓ S ∙ ℓ T ∙ ℓ (S ∘ˢ T) ⁻¹
--
-- of a lifting ℓ of Sp(2, 2) into the Clifford group, and the Clifford
-- group's own construction deliberately supplies no section of proj (see
-- the header of Qubit.CliffordGroup, "nothing here provides a section of
-- proj").  Given such an ℓ — together with the fact that conjugating a
-- Pauli by ℓ S acts by S — Theorem 9.8's necessity direction
-- (isFactorSet⇒isNormalisedCocycle) would produce γ from it, and the
-- twisted product below would then be the Clifford group.  The one entry
-- expected to be nontrivial is the one that S² = Z names: over the
-- transvection that the phase gate S projects to, the correction is pZ
-- (compare corr (order-S) = Z₀ in Qubit.Cocycle).
--
-- What is instantiated here is the factor set that *is* available, the
-- trivial one: it gives the affine group Pauli1 ⋊ Sp(2, 2), the split
-- extension, which is the semidirect product of
-- Examples.Construct.SemiDirectProduct.Clifford at width 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Sem3 where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Vec using ([] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pIₙ ; _+₁_ ; _+ₚ_ ; +₁-isAbelianGroup)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; εˢ ; _∘ˢ_ ; Sp-group)
open import Examples.Construct.SemiDirectProduct.Clifford p-2 p-prime
  using (ap-ε)
open Symplectic

------------------------------------------------------------------------
-- K: the one-qubit phaseless Pauli group ℤ/2 × ℤ/2

-- Examples.Groups.ProjectivePauli.Semantics exports the Group bundle
-- +₁-group; the factor-set construction needs the kernel as an
-- AbelianGroup, and the abelian structure is proved there already.

K : AbelianGroup 0ℓ 0ℓ
K = record { isAbelianGroup = +₁-isAbelianGroup }

------------------------------------------------------------------------
-- Q: the symplectic group Sp(2, 2)

Q : Group 0ℓ 0ℓ
Q = Sp-group 1

------------------------------------------------------------------------
-- Pauli1 ≅ Pauli 1
--
-- The kernel is the pair ℤ/2 × ℤ/2 while a symplectic transformation
-- acts on the length-one vector of such pairs.  The two carriers differ
-- only by the vector wrapper: both round-trips hold, and _+₁_ is _+ₚ_
-- read through the wrapper (all three by computation, once the vector is
-- exposed as a cons).

vec₁ : Pauli1 → Pauli 1
vec₁ x = x ∷ []

un₁ : Pauli 1 → Pauli1
un₁ (x ∷ []) = x

vec₁∘un₁ : ∀ (v : Pauli 1) → vec₁ (un₁ v) ≡ v
vec₁∘un₁ (x ∷ []) = Eq.refl

un₁-+ : ∀ (u v : Pauli 1) → un₁ (u +ₚ v) ≡ un₁ u +₁ un₁ v
un₁-+ (x ∷ []) (y ∷ []) = Eq.refl

------------------------------------------------------------------------
-- φ: the action of Sp(2, 2) on the one-qubit Pauli group
--
-- A symplectic transformation acts by its underlying linear map `ap`.
-- The action laws are exactly the fields of Symplectic, transported:
-- act-ε-homo is ap-ε (a linear map fixes the origin), act-∙-homo is
-- linear-+, and act-identity / act-compose hold on the nose because εˢ
-- and _∘ˢ_ are the identity and composition of the underlying maps —
-- act-compose needing only that un₁ has vec₁ for a section.

φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q)
φ = record
  { act          = act
  ; act-cong     = λ {S} {T} {x} {y} → act-cong {S} {T} {x} {y}
  ; act-ε-homo   = act-ε-homo
  ; act-∙-homo   = act-∙-homo
  ; act-identity = λ _ → Eq.refl
  ; act-compose  = act-compose
  }
  where
  act : Symplectic 1 → Pauli1 → Pauli1
  act S x = un₁ (ap S (vec₁ x))

  act-cong : ∀ {S T : Symplectic 1} {x y : Pauli1} →
             S ≈ˢ T → x ≡ y → act S x ≡ act T y
  act-cong {x = x} S≈T Eq.refl = Eq.cong un₁ (S≈T (vec₁ x))

  -- vec₁ pI is pIₙ, so this is ap-ε read through the wrapper.
  act-ε-homo : ∀ S → act S pI ≡ pI
  act-ε-homo S = Eq.cong un₁ (ap-ε S)

  act-∙-homo : ∀ S x y → act S (x +₁ y) ≡ act S x +₁ act S y
  act-∙-homo S x y =
    Eq.trans (Eq.cong un₁ (linear-+ S (vec₁ x) (vec₁ y)))
             (un₁-+ (ap S (vec₁ x)) (ap S (vec₁ y)))

  act-compose : ∀ S T x → act (S ∘ˢ T) x ≡ act S (act T x)
  act-compose S T x =
    Eq.cong (λ v → un₁ (ap S v)) (Eq.sym (vec₁∘un₁ (ap T (vec₁ x))))

------------------------------------------------------------------------
-- The twisted product Pauli1 ×_f Sp(2, 2)
--
-- For any factor set γ = (f , laws) this is the group on Pauli1 × Sp(2,2)
-- with
--
--     (a , S) ∙ (b , T) = ((a +₁ act S b) +₁ f S T , S ∘ˢ T),
--
-- an extension of Sp(2, 2) by Pauli1 realising φ.

Twisted : FactorSet K Q φ → Group 0ℓ 0ℓ
Twisted γ = FSE.group K Q φ γ

Twisted-extension : (γ : FactorSet K Q φ) → Extension (AbelianGroup.group K) Q
Twisted-extension γ = FSE.factorSetExtension K Q φ γ

------------------------------------------------------------------------
-- Where a factor set comes from
--
-- The route to the Clifford γ, made executable: any extension of Sp(2, 2)
-- by Pauli1 that realises φ and carries a unit-preserving lifting
-- determines its factor set, by Theorem 9.8's necessity direction.  So
-- filling the hole means building an IsFactorSet record over
-- Qubit.Semantics.CMS-extension 1 — the missing field is the lifting,
-- for which CliffordGroup.proj-surjective (= surj-nf, the normal form)
-- supplies a candidate.

γ-of-lifting : {f : Symplectic 1 → Symplectic 1 → Pauli1} →
               FSE.IsFactorSet K Q φ f → FactorSet K Q φ
γ-of-lifting {f} ifs = record
  { f                   = f
  ; isNormalisedCocycle = FSE.isFactorSet⇒isNormalisedCocycle K Q φ ifs
  }

------------------------------------------------------------------------
-- The split instance
--
-- f ≡ pI is a factor set for any action, and the twisted product it
-- names is the affine group Pauli1 ⋊ Sp(2, 2) — the extension in which
-- the lifting S ↦ (pI , S) is a homomorphism.  The Clifford group is the
-- same construction over the factor set discussed in the header.

γ-split : FactorSet K Q φ
γ-split = FSE.trivialFactorSet K Q φ

Affine-group : Group 0ℓ 0ℓ
Affine-group = Twisted γ-split

Affine-extension : Extension (AbelianGroup.group K) Q
Affine-extension = Twisted-extension γ-split
