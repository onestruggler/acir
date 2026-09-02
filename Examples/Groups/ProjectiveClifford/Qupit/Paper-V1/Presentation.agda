------------------------------------------------------------------------
-- Presentations of groups
--
-- The Paper-V1 Clifford rules present Pauli n ⋊ Sp(2n, ℤ/pℤ).
--
-- Nothing new is proved here: the theorem is the composite of two
-- results that already exist.
--
--   * Paper-V1.Iso gives a group isomorphism between the word group of
--     the Paper-V1 rules and the word group of the Simplified-V1 rules.
--     Both rule sets are relations over the same alphabet, so the
--     isomorphism is the identity on words and needs no transport of
--     the interpretation at all.
--   * Simplified-V1.Presentation gives that the V1 rules present
--     Pauli⋊Sp.
--
-- Composing, the Paper-V1 rules present the same group, with the same
-- interpretation: ⟦_⟧ ∘ id, where ⟦_⟧ is V1's.  Concretely a Paper-V1
-- word is read as a V1 word (itself), rewritten into the semidirect
-- generators by V1's h, and interpreted there.
--
-- This mirrors Simplified-V1.Presentation, which transports the
-- semidirect presentation the one step below.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Presentation
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
open import Function using (_∘_ ; id)
open import Level using (0ℓ)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)

-- The target group, from the semidirect-product presentation.
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  p-3 p-prime g* g-gen as SDPres

-- The Paper-V1 rules, their grouplike witness, and the identity
-- isomorphism onto the V1 rules.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Iso
  p-3 p-prime g* g-gen as PIso

-- The Paper-V0 presentation theorem: Iso now lands on Paper-V0, so the
-- composite runs through Paper-V0 rather than Simplified-V1.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
  p-3 p-prime g* g-gen as V0Pres

private
  module Build (n : ℕ) where

    private
      module T = PIso.Theorem
      module P = _IsPresentationOf_ (V0Pres.presentation n)

    -- The two word groups: W₀ over the Paper-V1 rules, W₁ over the V1
    -- rules.  W₁ must be the V1 presentation's own word group — it is
    -- the source of P.iso — and it is the target of the isomorphism
    -- exactly because Paper-V1.Iso builds it from the same grouplike
    -- witness, Simplified-V1.Lemmas' one.
    module W₀ = Group-Lemmas (Pap.Clifford-Relations._QRel,_===_ n)
                             (T.pap-grouplike {n})
    module W₁ = P.GL

    G₃ : Group 0ℓ 0ℓ
    G₃ = SDPres.Semidirect.Pauli⋊Sp n

    ------------------------------------------------------------------
    -- The two isomorphisms

    private
      module M₀₁ = GroupMorphisms (Group.rawGroup W₀.•-ε-group)
                                  (Group.rawGroup W₁.•-ε-group)

    iso₀₁ : M₀₁.IsGroupIsomorphism id
    iso₀₁ = PIso.Theorem.M.Theorem-PaperV1-iso-PaperV0 n

    ------------------------------------------------------------------
    -- The composite

    open GroupMorphisms (Group.rawGroup W₀.•-ε-group)
                        (Group.rawGroup G₃)

    -- Transitivity of the target's equality, with its three implicits
    -- bound by hand: the semidirect product's equality is Pointwise
    -- through projections, so unification never recovers them.
    ≈₃-trans : Transitive (RawGroup._≈_ (Group.rawGroup G₃))
    ≈₃-trans {x} {y} {z} eq₁ eq₂ =
      Setoid.trans (Group.setoid G₃) {x} {y} {z} eq₁ eq₂

    iso : IsGroupIsomorphism (P.⟦_⟧ ∘ id)
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup W₀.•-ε-group}
                                {G₂ = Group.rawGroup W₁.•-ε-group}
                                {G₃ = Group.rawGroup G₃}
                                (λ {x} {y} {z} → ≈₃-trans {x} {y} {z})
                                {f = id} {g = P.⟦_⟧} iso₀₁ P.iso

    pres : (Pap.Clifford-Relations._QRel,_===_ n) IsPresentationOf G₃
    pres = record
      { gl  = T.pap-grouplike
      ; ⟦_⟧ = P.⟦_⟧ ∘ id
      ; iso = iso
      }

open Pap using (module Clifford-Relations)
open SDPres using (module Semidirect)
open Clifford-Relations renaming (_QRel,_===_ to _CRel,_===_)
open Semidirect using (Pauli⋊Sp)

------------------------------------------------------------------------
-- The theorem

-- The Paper-V1 Clifford rules — the paper's Figure 1 mod scalars —
-- present the semidirect product of the Pauli group and Sp(2n, ℤ/pℤ).
presentation : ∀ (n : ℕ) → (n CRel,_===_) IsPresentationOf (Pauli⋊Sp n)
presentation = Build.pres
