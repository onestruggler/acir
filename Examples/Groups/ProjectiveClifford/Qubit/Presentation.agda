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
-- Proposition 2.55's inputs were long open, and are still the hypotheses
-- of `presentation` below:
--
--   Sec-trivial   the identity coset's representative is trivial in the
--                 EXTENSION: [ rep Iᶜ ]ᵣ ≈ ε.  What the coset tower gives
--                 for free is the weaker rep Iᶜ ≈ ε in the QUOTIENT;
--                 lifting that into the extension goes through corrOf
--                 and so picks up the Pauli correction accumulated by
--                 the reduction, which is exactly what has to vanish.
--   Conj-trivial  conjugating a Pauli generator by that representative
--                 does nothing.
--
-- Both are now theorems at every width — sec-trivial-n / conj-trivial-n
-- below, whence presentation-n with nothing assumed.  Both come from a
-- section that sends the identity coset to ε ON THE NOSE, which the
-- coset tower's does not (Symplectic.Simplified.NfEps refutes rep Iᶜ ≡ ε
-- at every positive width, one level of the tower's inverse being a
-- concatenation whatever its arguments).  But the section is not part of
-- a BijectiveNormalForm's data: it is recovered from the surjectivity
-- field, and redefining that field at the one index nfˢ ε to return ε
-- costs only  ∀ {z} → z ≈ ε → nfˢ z ≡ nfˢ ε,  which is nf-cong.  That
-- patched witness is Simplified.Bijective.bijective₂ε, and ExtensionPre-
-- sentation takes its quotient normal form from there.
--
-- The price is a decision procedure for equality on NF n.  Its data
-- components are Fins and Vecs, but an A box also carries a ≢, and two
-- proofs of a negation cannot be compared without function extension-
-- ality; Bijective.NF-dec therefore decides through the section instead
-- — words over a finite gate set are decidable, and Symplectic.Normali-
-- zation.Uniqueness.⟦[]⟧-injective recovers the full propositional
-- equality, proof component included, from equal denotations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Presentation where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊)
open import Word.Base using (_^_ ; _•_ ; ε ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Setoid as SNF
open import Presentation.Construct.Base using ([_]ᵣ)
open import Presentation.Definitions using (_IsPresentationOf_)

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime ; g* ; g-gen)
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open import Notations using (₁₊ ; ₂₊ ; auto)
open Symplectic using (H ; S ; S⁻¹ ; S^ ; XM ; CZ ; Circuit ; _↑)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations
  using (srel ; cong↑ ; comm₁ ; order-H ; order-CZ ; M₋₁ ; M-power)

-- The identity coset's representative is the empty word, on the nose:
-- the ε-patched section that ExtensionPresentation now takes its
-- quotient normal form from.
open import Examples.Groups.Symplectic.Simplified.Bijective p-2 p-prime g* g-gen
  using (rep-ε ; bijective₂ε)

-- The two factors, and the machine that turns their normal forms into
-- one for the extension.
open import Data.Product using (_×_)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.Construction as Con
open import Presentation.Construct.Base using (_⊕^_)
open Simplified-Relations using (_QRel,_===_)
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen
  as SimP
open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime using (NF)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli)
open import Examples.Groups.ProjectivePauli.Presentation p-2 p-prime
  using (Γ-H ; Pauli-group ; Pauli-presentation)
open import Examples.Groups.ProjectiveClifford.Qubit.CMS
  using (Clifford-extension)

open import Examples.Groups.ProjectiveClifford.Qubit.Semantics.Semantics using (CMS-group)
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
corr-free-order-H = srel order-H , Eq.refl

------------------------------------------------------------------------
-- ... and both are discharged, at every width
--
-- Neither needs Sec-reduction, nor any derivation replayed: the quotient
-- factor's normal form is the ε-patched section (ExtensionPresentation's
-- nfpQ is bijective₂ε), whose identity coset's representative is the
-- empty word ON THE NOSE.  Rewriting by rep-ε leaves a reflexivity in
-- both cases.
--
-- Sec-trivial:  [ ε ]ᵣ ≈ₑ ε, and [_]ᵣ = wmap inj₂ sends the empty word
--               to the empty word.
-- Conj-trivial: conjugation by the empty word is the identity on the
--               nose — conj ʰ' has ε as its unit clause — so the Pauli
--               generator comes back unchanged.  This is the condition
--               that would carry the Pauli correction if the
--               representative were any other word.

sec-trivial-n : ∀ {n} → Sec-trivial n
sec-trivial-n {n} rewrite rep-ε {n} = PB.refl

conj-trivial-n : ∀ {n} → Conj-trivial n
conj-trivial-n {n} x rewrite rep-ε {n} = PB.refl

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

-- Hence the theorem with nothing assumed, at every width.
presentation-n : ∀ {n} → (n Clifford,_===_) IsPresentationOf (CMS-group n)
presentation-n = presentation sec-trivial-n conj-trivial-n

------------------------------------------------------------------------
-- A bijective normal form for the Clifford group mod scalars
--
-- The same four facts that make the presentation unconditional also make
-- Normalization.Construction.bijective apply, so the group has a normal
-- form on Pauli n × NF n: a Pauli vector paired with a symplectic normal
-- form.  This is what lets THIS extension be a factor of the next one —
-- the scalar layer asks its quotient for exactly such a witness.
--
-- Nothing here is new work.  The Reidemeister–Schreier engine inside
-- Proposition 2.55 already produced the normal form; the round trip that
-- upgrades it to a bijection is Transfer.Unique, whose two premises are
-- the two factors' own bijectivity — the Pauli factor's directly, the
-- symplectic factor's through the coset table's exactness on sections.

bijective-Cl : ∀ {n} →
               BijectiveNormalForm (n Clifford,_===_) (Pauli n × NF n)
bijective-Cl {n} =
  Con.bijective (Γ-H ⊕^ n) (n QRel,_===_) conj corr
    (Pauli-group n) (Sp-group n) (Clifford-extension n)
    (Pauli-presentation n) (SimP.presentation {n})
    EP.⟦_⟧₀ (EP.bijectiveᴾ n) (bijective₂ε n)
    (EP.Clifford.realises n) (EP.Clifford.sound-ax n)
    sec-trivial-n conj-trivial-n
