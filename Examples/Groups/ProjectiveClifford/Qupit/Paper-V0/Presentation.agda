------------------------------------------------------------------------
-- Presentations of groups
--
-- The Paper-V0 Clifford rules present Pauli n ⋊ Sp(2n, ℤ/pℤ).
--
-- Nothing new is proved here: the theorem is the composite of two
-- results that already exist.
--
--   * Paper-V0.Iso gives a group isomorphism between the word group of
--     the Paper-V0 rules and the word group of the Simplified-V1 rules.
--     Both rule sets are relations over the same alphabet, so the
--     isomorphism is the identity on words and needs no transport of
--     the interpretation at all.
--   * Simplified-V1.Presentation gives that the V1 rules present
--     Pauli⋊Sp.
--
-- Composing, the Paper-V0 rules present the same group, with the same
-- interpretation: ⟦_⟧ ∘ id, where ⟦_⟧ is V1's.  Concretely a Paper-V0
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

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
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

-- The Paper-V0 rules, their grouplike witness, and the identity
-- isomorphism onto the V1 rules.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Iso
  p-3 p-prime g* g-gen as PIso

-- The V1 presentation theorem.
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Presentation
  p-3 p-prime g* g-gen as V1Pres

private
  module Build (n : ℕ) where

    private
      module T = PIso.Theorem
      module P = _IsPresentationOf_ (V1Pres.presentation {n})

    -- The two word groups: W₀ over the Paper-V0 rules, W₁ over the V1
    -- rules.  W₁ must be the V1 presentation's own word group — it is
    -- the source of P.iso — and it is the target of the isomorphism
    -- exactly because Paper-V0.Iso builds it from the same grouplike
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
    iso₀₁ = PIso.Theorem.M.Theorem-PaperV0-iso-V1 n

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

------------------------------------------------------------------------
-- The theorem

-- The Paper-V0 Clifford rules — the paper's Figure 1 — present the
-- semidirect product of the Pauli group by Sp(2n, ℤ/pℤ).
presentation : ∀ {n} →
               (Pap.Clifford-Relations._QRel,_===_ n)
                 IsPresentationOf (SDPres.Semidirect.Pauli⋊Sp n)
presentation {n} = Build.pres n
