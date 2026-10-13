------------------------------------------------------------------------
-- Presentations of groups
--
-- On up to three wires the rules present a subgroup of the unitary
-- group U_{2ⁿ}(ℤ[½,i])
--
-- Completeness compares circuits through their scaled operators
-- (Semantics).  Stated as Clifford+CS-3qubit.Presentation states its
-- theorem, against the group U N of Clifford+CS-TwoLevel: a circuit
-- denotes the unitary matrix of its encoding — a two-level word on 2ⁿ
-- indices for n ≤ 2 (ZeroQubit, OneQubit, TwoQubit), one of Bian and
-- Selinger's 3-qubit words, read through their two-level translation,
-- for n = 3 (ThreeQubit) — and ⟦_⟧ᵁ is a group monomorphism: sound
-- because the encoding preserves the scaled operators and Bridge.Φ
-- sends those to the matrices, injective because the auxiliary theory
-- is complete for the matrices and the decoding retracts the encoding
-- (Reidemeister–Schreier, as in BackAndForth).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Unitary where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Nat using (ℕ ; _^_)
import Data.Nat as ℕ
open import Data.Product using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Normalization.Reidemeister-Schreier using (module Star-Injective-Simplified)

open import Quantum.Synthesis.Matrix using (_·*·_)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Examples.Groups.Clifford+CS.Semantics using (Scaled ; _~_ ; ~-sym ; ~-trans)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; module Ext)
open import Examples.Groups.Clifford+CS.Soundness using (soundᴱ)
import Examples.Groups.Clifford+CS.Bridge as Bridge
import Examples.Groups.Clifford+CS.ZeroQubit as ZeroQubit
import Examples.Groups.Clifford+CS.OneQubit as OneQubit
import Examples.Groups.Clifford+CS.TwoQubit as TwoQubit
import Examples.Groups.Clifford+CS.TwoQubit.Decoding as Decoding
import Examples.Groups.Clifford+CS.ThreeQubit as ThreeQubit

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (UMat ; U ; ⟦_⟧ᵐ ; ⟦•⟧ᵐ ; 𝕀)
import Examples.Groups.Clifford+CS-TwoLevel.Presentation as TLP
import Examples.Groups.Clifford+CS-TwoLevel.MainLemma as TLM
import Examples.Groups.Clifford+CS-3qubit.Presentation as BSP

------------------------------------------------------------------------
-- From back-and-forth data with a unitary semantics

-- The auxiliary words have a scaled reading ⟦_⟧Y and unitary matrices
-- m, Φ taking the one to the other; e, d and the lemmas on them are
-- those of BackAndForth (eʷ-sem being its CompleteOn.eʷ-sem).
module Generic (n : ℕ) {Y : Set} (Δ : WRel Y)
  (⟦_⟧Y       : Word Y → Scaled n)
  (m          : Word Y → UMat (2 ^ n))
  (m-•        : ∀ u t → proj₁ (m (u • t)) ≡ proj₁ (m u) ·*· proj₁ (m t))
  (m-ε        : proj₁ (m ε) ≡ 𝕀)
  (m-Φ        : ∀ u → Bridge.Φ ⟦ u ⟧Y ≡ proj₁ (m u))
  (m-complete : ∀ {u t} → proj₁ (m u) ≡ proj₁ (m t) → PB._≈_ Δ u t)
  (e      : Gen n → Word Y)
  (eʷ-sem : ∀ w → ⟦ (e ʷ) w ⟧Y ~ Ext.⟦_⟧ᴱ n w)
  (d      : Y → Circuit n)
  (d-wd   : ∀ {u t} → Δ u t → n ⊢ (d ʷ) u ≈ (d ʷ) t)
  (d∘e    : ∀ g → n ⊢ [ g ]ʷ ≈ (d ʷ) (e g))
  where

  private
    module RS = Star-Injective-Simplified (n VRel,_===_) Δ
    module R  = RS.Reidemeister-Schreier-Simplified e d d-wd d∘e

  -- A circuit's matrix: the matrix of its encoding.
  ⟦_⟧ᵁ : Circuit n → UMat (2 ^ n)
  ⟦ w ⟧ᵁ = m ((e ʷ) w)

  sound : ∀ {w v} → n ⊢ w ≈ v → proj₁ ⟦ w ⟧ᵁ ≡ proj₁ ⟦ v ⟧ᵁ
  sound {w} {v} eq =
    Eq.trans (Eq.sym (m-Φ ((e ʷ) w)))
      (Eq.trans (Bridge.Φ-cong {s = ⟦ (e ʷ) w ⟧Y} {⟦ (e ʷ) v ⟧Y} same) (m-Φ ((e ʷ) v)))
    where
    same : ⟦ (e ʷ) w ⟧Y ~ ⟦ (e ʷ) v ⟧Y
    same = ~-trans {s = ⟦ (e ʷ) w ⟧Y} {t = Ext.⟦_⟧ᴱ n w} {u = ⟦ (e ʷ) v ⟧Y} (eʷ-sem w)
             (~-trans {s = Ext.⟦_⟧ᴱ n w} {t = Ext.⟦_⟧ᴱ n v} {u = ⟦ (e ʷ) v ⟧Y} (soundᴱ eq)
                (~-sym {s = ⟦ (e ʷ) v ⟧Y} {t = Ext.⟦_⟧ᴱ n v} (eʷ-sem v)))

  complete : ∀ {w v} → proj₁ ⟦ w ⟧ᵁ ≡ proj₁ ⟦ v ⟧ᵁ → n ⊢ w ≈ v
  complete eq = R.fʷ-inj (m-complete eq)

  -- The rules present the subgroup of U (2ⁿ) the gates generate.
  presentation : (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
  presentation = record
    { gl   = grouplike
    ; ⟦_⟧  = ⟦_⟧ᵁ
    ; mono = record
      { isGroupHomomorphism =
          isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (U (2 ^ n)) hom
      ; injective = complete
      }
    }
    where
    module GL = Group-Lemmas (n VRel,_===_) grouplike
    open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (U (2 ^ n)))
    hom : IsMonoidHomomorphism ⟦_⟧ᵁ
    hom = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound }
        ; homo = λ w v → m-• ((e ʷ) w) ((e ʷ) v)
        }
      ; ε-homo = m-ε
      }

------------------------------------------------------------------------
-- No wire, one and two: the two-level words on 2ⁿ indices
--
-- Each instance is read through the module's own copy of
-- Bridge.TwoLevel n (its T).  The groups are written U (2 ^ n), as
-- Generic states them, with n a constructor numeral (₀ = zero, …), as
-- presentation≤₃'s cases substitute it: the conversion checker compares
-- U 1 with U (2 ^ 0), or U (2 ^ 0) with U (2 ^ zero), by unfolding the
-- two group records field by field, proofs included, before it reduces
-- the width (more than five minutes and 4 GB each; written this way
-- the types agree syntactically and the module checks in seconds).

presentation₀ : (₀ VRel,_===_) IsSubPresentationOf U (2 ^ ₀)
presentation₀ = Q.presentation
  where
  open ZeroQubit
  module C = T.BF.Complete T.complete-Y e e-sem d d-wd d∘e
  module Q = Generic ₀ (TL._===_ {1}) T.⟦_⟧Y (TLP.⟦_⟧ᵘ {1}) ⟦•⟧ᵐ refl T.Φ-Y
               (TLM.relations-complete {1}) e C.eʷ-sem d d-wd d∘e

presentation₁ : (₁ VRel,_===_) IsSubPresentationOf U (2 ^ ₁)
presentation₁ = Q.presentation
  where
  open OneQubit
  module C = T.BF.Complete T.complete-Y e e-sem d d-wd d∘e
  module Q = Generic ₁ (TL._===_ {2}) T.⟦_⟧Y (TLP.⟦_⟧ᵘ {2}) ⟦•⟧ᵐ refl T.Φ-Y
               (TLM.relations-complete {2}) e C.eʷ-sem d d-wd d∘e

presentation₂ : (₂ VRel,_===_) IsSubPresentationOf U (2 ^ ₂)
presentation₂ = Q.presentation
  where
  open TwoQubit
  module C = T.BF.Complete T.complete-Y e e-sem d Decoding.lemma-7-5 Decoding.lemma-7-4
  module Q = Generic ₂ (TL._===_ {4}) T.⟦_⟧Y (TLP.⟦_⟧ᵘ {4}) ⟦•⟧ᵐ refl T.Φ-Y
               (TLM.relations-complete {4}) e C.eʷ-sem d Decoding.lemma-7-5 Decoding.lemma-7-4

------------------------------------------------------------------------
-- Three wires: Bian and Selinger's words

presentation₃ : (₃ VRel,_===_) IsSubPresentationOf U (2 ^ ₃)
presentation₃ = Q.presentation
  where
  open ThreeQubit
  module C = BF.Complete complete-Y e e-sem d d-wd d∘e
  module Q = Generic ₃ B.Rel BF.⟦_⟧Y BSP.⟦_⟧
               (λ u t → ⟦•⟧ᵐ ((BSP.tl ʷ) u) ((BSP.tl ʷ) t)) refl Φ-Y BSP.complete
               e C.eʷ-sem d d-wd d∘e

------------------------------------------------------------------------
-- Every width up to three

presentation≤₃ : ∀ {n} → n ℕ.≤ 3 → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation≤₃ ℕ.z≤n                         = presentation₀
presentation≤₃ (ℕ.s≤s ℕ.z≤n)                 = presentation₁
presentation≤₃ (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))         = presentation₂
presentation≤₃ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) = presentation₃
