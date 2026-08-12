------------------------------------------------------------------------
-- Presentations of groups
--
-- The presentation theorem for the n-qubit Clifford group mod scalars
-- (p = 2): _Clifford,_===_ presents CMS n.
--
--     1 ─→ Pauli n ─→ CMS n ─→ Sp(2n, 2) ─→ 1
--
-- The relation is Proposition 2.55's extension presentation of the Pauli
-- rule set by the simplified symplectic one, along the conjugation
-- action conj and the cocycle corr; all four live in Qubit.Cocycle,
-- which this module re-exports, so the ten Selinger modules that read
-- conj / corr / _Clifford,_===_ from here are unaffected.
--
-- The proof is assembled in Qubit.ExtensionPresentation (interpretation
-- of the generators, the two bijective normal forms, soundness of conj
-- and corr against CMS n, and the realisation conditions).  Two of
-- Proposition 2.55's inputs are still open, and are the hypotheses of
-- `presentation` below:
--
--   Sec-trivial   the identity coset's representative is trivial in the
--                 EXTENSION: [ rep Iᶜ ]ᵣ ≈ ε.  What the coset tower gives
--                 for free is the weaker rep Iᶜ ≈ ε in the QUOTIENT;
--                 lifting that into the extension goes through corrOf
--                 and so picks up the Pauli correction accumulated by
--                 the reduction, which is exactly what has to vanish.
--                 (The still weaker rep Iᶜ ≡ ε on the nose is not an
--                 option: Symplectic.Simplified.NfEps refutes it at
--                 every positive width, since one level of the tower's
--                 inverse is a concatenation whatever its arguments.)
--   Conj-trivial  conjugating a Pauli generator by that representative
--                 does nothing.
--
-- Both would follow at once from a section sending the identity coset to
-- ε on the nose.  The tower's section does not, but it may be patched to
-- at a single point: BijectiveNormalForm's section is recovered from its
-- surjectivity field, and redefining that field at the one index nfˢ ε
-- to return ε costs only  ∀ {z} → z ≈ ε → nfˢ z ≡ nfˢ ε,  which is
-- nf-cong.  The patched witness still satisfies both round trips (at
-- that index nf ε ≡ nfˢ ε by construction, and inv-nf ∘ nf ≈ id follows
-- from injectivity of nfˢ), and it makes both hypotheses hold by
-- computation.  What it needs is a decision procedure for u ≡ nfˢ ε on
-- NF n; the data components are Fins and Vecs, and the one proof
-- component (A carries a ≢) is pinned by
-- Symplectic.Normalization.Uniqueness.⟦[]⟧-injective, which recovers the
-- full propositional equality from equal denotations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Presentation where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

open import Notations using (₁₊)
open import Word.Base using (_^_)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime ; g* ; g-gen)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (H)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (srel ; order-H ; M₋₁)

open import Examples.Groups.ProjectiveClifford.Qubit.Semantics using (CMS-group)
import Examples.Groups.ProjectiveClifford.Qubit.ExtensionPresentation as EP

-- The conjugation action, the cocycle, and the relation they generate.
open import Examples.Groups.ProjectiveClifford.Qubit.Cocycle public

------------------------------------------------------------------------
-- The two open inputs of Proposition 2.55, named at this width

-- The identity coset's representative is trivial in the extension.
Sec-trivial : ℕ → Set
Sec-trivial n = EP.Clifford.Sec-trivial n

-- Conjugating a Pauli generator by it does nothing.
Conj-trivial : ℕ → Set
Conj-trivial n = EP.Clifford.Conj-trivial n

-- Sec-trivial has an elementary sufficient condition, and at p = 2 it
-- is sharp enough to name the single obstruction.  Only one simplified
-- relator carries a correction — corr (srel order-S) = Z₀, everything
-- else falls in corr's catch-all — so Extension.Corr-free is the whole
-- rule set minus order-S, and Sec-reduction asks for the identity
-- coset's representative to reduce to ε without ever using S² = ε.
-- That is a statement about the SYMPLECTIC calculus alone: no
-- extension, no cocycle, no coset machinery.
Sec-reduction : ℕ → Set
Sec-reduction n = EP.Clifford.Sec-reduction n

sec-trivial : ∀ {n} → Sec-reduction n → Sec-trivial n
sec-trivial {n} = EP.Clifford.sec-trivial-from n

-- A relator is admitted into the correction-free calculus by pairing it
-- with the proof that it lifts exactly, and for anything but order-S
-- that proof is refl, since corr reduces to ε on the nose.  order-H is
-- the case that matters: at p = 2 it reads H² = M₋₁ = Mg = ω, and it is
-- the relator standing between the identity coset's A-box XM ₁ and ε.
corr-free-order-H : ∀ {n} → EP.Clifford.Corr-free (₁₊ n) (H ^ 2) M₋₁
corr-free-order-H = srel order-H , PB.refl

------------------------------------------------------------------------
-- The presentation theorem
--
-- Everything else Proposition 2.55 asks for is discharged in
-- Qubit.ExtensionPresentation: the interpretation ⟦_⟧₀ of the mixed
-- alphabet in CMS n, the Pauli factor's bijective normal form (its
-- presentation is already an isomorphism, composed with the coordinate
-- map vec), the quotient factor's (Simplified.Bijective's coset tower,
-- upgraded by uniqueness of the section), soundness of conj and corr
-- (Qubit.ExtensionSoundness), and the two realisation conditions.
--
-- Note CMS-group n is Qubit.CMS.Clifford-group n on the nose: the
-- transport that puts the Pauli factor in the shape Γ-H ⊕^ n presents
-- changes only the inclusion, never the total group.

presentation : ∀ {n} → Sec-trivial n → Conj-trivial n →
               (n Clifford,_===_) IsPresentationOf (CMS-group n)
presentation {n} = EP.Clifford.presentation n
