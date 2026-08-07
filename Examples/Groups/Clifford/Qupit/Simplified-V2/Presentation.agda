------------------------------------------------------------------------
-- Presentations of groups
--
-- The V2 (simplified) Clifford rules present Pauli n ⋊ Sp(2n, ℤ/pℤ).
--
-- Again nothing new is proved: this is the V1 theorem transported along
-- the identity isomorphism between the two rule sets.
--
--   * Simplified-V1.Presentation gives that the V1 rules present
--     Pauli⋊Sp — itself the composite of Iso and
--     SemiDirect.Presentation.
--   * Iso gives that the two rule sets have isomorphic word groups,
--     with the identity as the underlying map: every V1 rule holds in
--     V2 and every V2 rule holds in V1.
--
-- Iso states its isomorphism V1 → V2, and the direction that composes
-- here is V2 → V1, so it is rebuilt from the same two well-definedness
-- proofs in the other order.  Since the map is the identity, the
-- composite's interpretation is P₁.⟦_⟧ unchanged: a V2 word is read by
-- reading it as a V1 word.
--
-- This is the same transport as Symplectic.Simplified.Presentation, one
-- level down.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Zp.Fermats-little-theorem
open import Zp.ModularArithmetic

module Examples.Groups.Clifford.Qupit.Simplified-V2.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Group)
open import Algebra.Bundles.Raw using (RawGroup)
import Algebra.Morphism.Construct.Composition as MC
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Function using (id)
open import Level using (0ℓ)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)

-- The V1 rules and their presentation theorem.
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar
  p-3 p-prime g* g-gen as Cli using (module Clifford-Relations)
import Examples.Groups.Clifford.Qupit.Simplified-V1.Presentation
  p-3 p-prime g* g-gen as V1Pres

-- The V2 rules, their grouplike witness, and the isomorphism with V1.
open import Examples.Groups.Clifford.Qupit.Simplified-V2.Syntactics
  p-3 p-prime g* g-gen as Sim using (module Simplified-Relations)
open import Examples.Groups.Clifford.Qupit.Simplified-V2.Lemmas
  p-3 p-prime g* g-gen as SimL using (module Simplified-GroupLike-S)
import Examples.Groups.Clifford.Qupit.Simplified-V2.Iso
  p-3 p-prime g* g-gen as ISO

-- The group being presented.
import Examples.Groups.Clifford.Qupit.SemiDirect.Presentation
  p-3 p-prime g* g-gen as SDPres

private
  module Build (n : ℕ) where

    private
      module P₁ = _IsPresentationOf_ (V1Pres.presentation {n})

    -- W₁ is the V1 word group — the presentation's own, whose grouplike
    -- witness is Clifford-GroupLike's, which is also the one Iso uses
    -- for its source.  W₂ is the V2 word group.
    module W₁ = P₁.GL
    module W₂ = Group-Lemmas (Sim.Simplified-Relations._QRel,_===_ n)
                             (Simplified-GroupLike-S.grouplike {n})

    G₃ : Group 0ℓ 0ℓ
    G₃ = SDPres.Semidirect.Pauli⋊Sp n

    ------------------------------------------------------------------
    -- The identity isomorphism, in the direction that composes

    private
      module M₂₁ = GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                                  (Group.rawGroup W₁.•-ε-group)
      module M₁₃ = GroupMorphisms (Group.rawGroup W₁.•-ε-group)
                                  (Group.rawGroup G₃)

      -- MorphismId instantiated the other way round from Iso: V2
      -- first, V1 second.
      open import Presentation.MorphismId
        (Sim.Simplified-Relations._QRel,_===_ n)
        (Cli.Clifford-Relations._QRel,_===_ n)
      open GroupMorphs (Simplified-GroupLike-S.grouplike {n}) P₁.gl

    -- The same two proofs Iso uses, in the other order: a V2 rule holds
    -- in V1, and a V1 rule holds in V2.
    iso₂₁ : M₂₁.IsGroupIsomorphism id
    iso₂₁ = StarGroupIsomorphism.isGroupIsomorphism
              ISO.g-well-defined ISO.f-well-defined

    iso₁₃ : M₁₃.IsGroupIsomorphism P₁.⟦_⟧
    iso₁₃ = P₁.iso

    ------------------------------------------------------------------
    -- The composite

    open GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                        (Group.rawGroup G₃)

    -- Transitivity of the target's equality, three implicits bound by
    -- hand: the semidirect product compares through projections, so
    -- unification never recovers them.
    ≈₃-trans : Transitive (RawGroup._≈_ (Group.rawGroup G₃))
    ≈₃-trans {x} {y} {z} eq₁ eq₂ =
      Setoid.trans (Group.setoid G₃) {x} {y} {z} eq₁ eq₂

    -- The underlying map is P₁.⟦_⟧ ∘ id, i.e. P₁.⟦_⟧ itself.
    iso : IsGroupIsomorphism P₁.⟦_⟧
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup W₂.•-ε-group}
                                {G₂ = Group.rawGroup W₁.•-ε-group}
                                {G₃ = Group.rawGroup G₃}
                                (λ {x} {y} {z} → ≈₃-trans {x} {y} {z})
                                {f = id} {g = P₁.⟦_⟧} iso₂₁ iso₁₃

    pres : (Sim.Simplified-Relations._QRel,_===_ n) IsPresentationOf G₃
    pres = record
      { gl  = Simplified-GroupLike-S.grouplike
      ; ⟦_⟧ = P₁.⟦_⟧
      ; iso = iso
      }

------------------------------------------------------------------------
-- The theorem

-- The simplified Clifford rules present the semidirect product of the
-- Pauli group by Sp(2n, ℤ/pℤ).
presentation : ∀ {n} →
               (Sim.Simplified-Relations._QRel,_===_ n)
                 IsPresentationOf (SDPres.Semidirect.Pauli⋊Sp n)
presentation {n} = Build.pres n
