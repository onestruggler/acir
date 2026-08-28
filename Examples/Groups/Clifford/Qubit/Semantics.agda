------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the n-qubit Clifford group (p = 2), semantic side:
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ VSp n ─→ 1
--
-- Exact n is the Clifford group itself; the layer below it, the
-- non-split extension 1 → Pauli n → VSp n → Sp(2n, 2) → 1 presenting the
-- Clifford group modulo scalars, is
-- Examples.Groups.ProjectiveClifford.Qubit.Semantics.VSp, from which VSp-group is
-- taken here.  VSp n is the structural model — pairs (S , φ) of a
-- symplectic map and a phase function refining it — and is isomorphic to
-- the syntactic CMS n by Qubit.Iso2.CMS≅VSp.
--
-- ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω: ωʲ · ωᵏ = ω^{j+k}.
-- The extension is an ordinary one, assembled by hand exactly as the
-- layer below is: the total group is Clifford words modulo the *exact*
-- congruence — the one Selinger's Figure 8 presents, which unlike ≈ᶜ
-- still sees the global scalar — with incl k = ωᵏ and proj the VSp
-- denotation of a word.  See Qubit.ExactExtension, and the note at the
-- end of this file for what it still takes as input and why the
-- P4-action cannot supply it.
--
-- The layer is stated twice, once for each shape of its kernel: `Exact`
-- with the +-0-group 6 that ExactExtension builds, and `Exact-extension`
-- with the Cn-group 8 that a cyclic presentation produces.  Unlike the
-- two shapes of the Pauli group one storey down, these are the same ℤ/8
-- and nothing has to be transported between them.
--
-- The layer is stated at every width n, width 0 included: ω is a 0-ary
-- generator of Figure 8, so it needs no wire to live on.  See the note
-- on `scalar` in ExactExtension for what width 0 amounts to.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)

open import Notations using (₁₊)

open import ForStdlib.Algebra.Construct.Extension using (Extension)

open import Examples.Groups.Cyclic.Semantics using (Cn-group)

open import Examples.Groups.ProjectiveClifford.Qubit.Semantics.VSp
  using (VSp-group)

open import Examples.Groups.Clifford.Qubit.ExactExtension
  using (Scalar-group ; Exact-group ; ExactData)
  renaming (Exact to Exact-of)

------------------------------------------------------------------------
-- The scalars ⟨ω⟩, and the exact Clifford group

-- 1 → ⟨ω⟩ → Exact n → VSp n → 1.
Exact : ∀ {n} → ExactData n → Extension Scalar-group (VSp-group n)
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
-- That the cyclic relation really does present Scalars, and what
-- Proposition 2.55 asks for on top of it, are in Qubit.Presentation.

-- The scalars ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω.
Scalars : Group 0ℓ 0ℓ
Scalars = Cn-group 8

-- 1 → ⟨ω⟩ → Exact n → VSp n → 1, with the scalars in the shape that
-- 8 Cn,_===_ presents.  The change of shape is definitional — Cn-group 8
-- is Scalar-group — so `Exact` itself already has this type.
Exact-extension : {n : ℕ} → ExactData n →
                  Extension Scalars (VSp-group n)
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
-- that record now has a SINGLE field.  Two of Selinger's three theorems
-- have been discharged: soundness — Figure-8-equal words act equally on
-- P4 — is Selinger.Soundness.sound, and `scalars` — a word acting
-- trivially on P4 is some ωᵏ — is ExactExtension.scalars, proved once
-- the projective presentation became unconditional.  What is left is
--
--   ω-faithful — ω has order exactly 8 in the presented group.
--
-- It cannot come from the action, and ExactExtension.
-- action-blind makes that precise: ω acts trivially on P4
-- (Selinger.Action.cact-ω), so if ≈ᶜ implied the Figure-8 congruence then
-- ω = ω¹ and ε = ω⁰ would be identified and ω-faithful would force
-- ₁ ≡ ₀.  The scalar is exactly the datum cact discards, so ω-faithful
-- has to come from a faithful model of the exact Clifford group.  The two
-- candidates in reach are Selinger's exact normal form
-- (Qubit.Selinger.NormalForm, ExactNF n = NF n × Fin 8, uniqueness still
-- WIP) and matrices over ℤ[1/√2, i].
--
-- The second is now built, over ℤ/17ℤ, where ω = 2 has order exactly 8
-- (Qubit.Model.Faithful): an n-qubit circuit is read as a 2ⁿ × 2ⁿ matrix,
-- the tensor structure coming from indexing by bit vectors.  So the
-- layer takes no input at all — ExactData n is a theorem at every width,
-- and Qubit.Presentation.presentation-n is unconditional.
--
-- Group-theoretically the extension is the non-split 2^{1+2n}·Sp(2n,2);
-- in particular a direct product ℤ/8 × VSp n would be the wrong
-- group, which is why the scalar cannot simply be adjoined.
