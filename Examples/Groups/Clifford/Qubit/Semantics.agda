------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the n-qubit Clifford group (p = 2), semantic side:
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ CMS n ─→ 1
--
-- Exact n is the Clifford group itself; the layer below it, the
-- non-split extension 1 → Pauli n → CMS n → Sp(2n, 2) → 1 presenting the
-- Clifford group modulo scalars, is
-- Examples.Groups.ProjectiveClifford.Qubit.Semantics, from which CMS-group
-- is taken here.
--
-- ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω: ωʲ · ωᵏ = ω^{j+k}.
-- The extension is an ordinary one, assembled by hand exactly as the
-- layer below is: the total group is Clifford words modulo the *exact*
-- congruence — the one Selinger's Figure 8 presents, which unlike ≈ᶜ
-- still sees the global scalar — with incl k = ωᵏ and proj the identity
-- on words.  See Qubit.ExactExtension, and the note at the end of this
-- file for what it still takes as input and why the P4-action cannot
-- supply it.
--
-- The layer is stated twice, once for each shape of its kernel: `Exact`
-- with the +-0-group 6 that ExactExtension builds, and `Exact-extension`
-- with the Cn-group 8 that a cyclic presentation produces.  Unlike the
-- two shapes of the Pauli group one storey down, these are the same ℤ/8
-- and nothing has to be transported between them.
--
-- The scalar layer needs at least one qubit, ω living on the first wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)

open import Notations using (₁₊)

open import ForStdlib.Algebra.Construct.Extension using (Extension)

open import Presentation.Definitions using (_IsPresentationOf_)
open import Examples.Groups.Cyclic.Semantics using (Cn-group)
open import Examples.Groups.Cyclic.Normalization using (_Cn,_===_)
import Examples.Groups.Cyclic.Presentation as CyP

open import Examples.Groups.ProjectiveClifford.Qubit.Semantics
  using (CMS-group)
open import Examples.Groups.ProjectiveClifford.Qubit.CMS
  using (Clifford-group)

open import Examples.Groups.Clifford.Qubit.ExactExtension
  using (Scalar-group ; Exact-group ; ExactData)
  renaming (Exact to Exact-of)

------------------------------------------------------------------------
-- The scalars ⟨ω⟩, and the exact Clifford group

-- 1 → ⟨ω⟩ → Exact n → CMS n → 1.
Exact : ∀ {n} → ExactData n → Extension Scalar-group (CMS-group (₁₊ n))
Exact = Exact-of

------------------------------------------------------------------------
-- The same layer with the kernel in presented shape
--
-- As on the Pauli layer one storey down, the kernel can also be taken in
-- the shape a presentation produces: Scalars = Cn-group 8, the group
-- presented by the cyclic relation 8 Cn,_===_ (T⁸ = ε), rather than the
-- +-0-group 6 of ExactExtension.  The two are the same ℤ/8 — same
-- carrier, addition, unit and negation — so unlike the Pauli layer,
-- where CMS.vec has to reassociate a nested tuple into a vector, nothing
-- has to be transported here.
--
-- ω lives on the first wire, so this layer needs ₁₊ n qubits.
--
-- What this sets up: Proposition 2.55 applied to
--
--     S    = 8 Cn,_===_             (the scalars, presented by Scalars)
--     R̄    = ₁₊ n Clifford,_===_    (the quotient CMS n)
--
-- with the trivial conjugation (ω is central) and the cocycle recording
-- which Clifford relators lift to Figure 8 only up to a power of ω.  That
-- relation is built in Qubit.Exact-Presentation — which states the same
-- two definitions in its own alphabet, as Scalar-relation and
-- Scalar-presentation — and Qubit.Exact-Iso-CMS shows it equivalent to
-- the rule set of Qubit.Selinger.Figure8, exactly as Selinger.Iso does
-- one layer down for _Clifford,_===_ against Figure8-Mod-Scalar.

-- The scalars ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω.
Scalars : Group 0ℓ 0ℓ
Scalars = Cn-group 8

-- The cyclic relation T⁸ = ε presents them.
Scalars-presentation : (8 Cn,_===_) IsPresentationOf Scalars
Scalars-presentation = CyP.presentation

-- 1 → ⟨ω⟩ → Exact n → CMS n → 1, with the scalars in the shape that
-- 8 Cn,_===_ presents and the quotient the group of the layer below.
Exact-extension : {n : ℕ} → ExactData n →
                  Extension Scalars (Clifford-group (₁₊ n))
Exact-extension d = Exact-of d

-- The total group: Clifford words modulo the exact (Figure-8) congruence.
Exact-total : {n : ℕ} → ExactData n → Group 0ℓ 0ℓ
Exact-total {n} d = Extension.total (Exact-extension d)

------------------------------------------------------------------------
-- What Exact n still takes as input
--
-- The group structure of the Figure-8 words, that k ↦ ωᵏ is a
-- homomorphism ℤ/8 → Exact n, surjectivity of proj and that proj kills
-- the scalars are all proved in Qubit.ExactExtension.  So `Exact` is a
-- definition, not a hole; what remains is to supply one ExactData n, and
-- its three fields are Selinger's theorems rather than bookkeeping:
--
--   sound      — Figure-8-equal words act equally on P4;
--   scalars    — a word acting trivially on P4 is some ωᵏ;
--   ω-faithful — ω has order exactly 8 in the presented group.
--
-- `sound` is within reach: Selinger.Action already discharges C1, C2, C3,
-- C5-C9, C12 and C13, and C4 is an identity, leaving C10, C11, C14, C15.
--
-- The other two cannot come from the action, and ExactExtension.
-- action-blind makes that precise: ω acts trivially on P4
-- (Selinger.Action.cact-ω), so if ≈ᶜ implied the Figure-8 congruence then
-- ω = ω¹ and ε = ω⁰ would be identified and ω-faithful would force
-- ₁ ≡ ₀.  The scalar is exactly the datum cact discards, so ω-faithful
-- has to come from a faithful model of the exact Clifford group.  The two
-- candidates in reach are Selinger's exact normal form
-- (Qubit.Selinger.NormalForm, ExactNF n = NF n × Fin 8, uniqueness still
-- WIP) and matrices over ℤ[1/√2, i].
--
-- Group-theoretically the extension is the non-split 2^{1+2n}·Sp(2n,2);
-- in particular a direct product ℤ/8 × CMS n would be the wrong
-- group, which is why the scalar cannot simply be adjoined.
