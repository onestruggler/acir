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
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊)
open import Word.Base using (_^_ ; ε)
import Presentation.Base as PB
import Normalization.NormalForm.Setoid as SNF
open import Presentation.Definitions using (_IsPresentationOf_)

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime ; g* ; g-gen)
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open import Notations using (₁₊ ; ₂₊)
open Symplectic using (H ; S^ ; XM ; CZ ; Circuit ; _↑)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations
  using (srel ; cong↑ ; order-H ; order-CZ ; M₋₁ ; M-power)

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
corr-free-order-H = srel order-H , Eq.refl

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

------------------------------------------------------------------------
-- Width 0, unconditionally
--
-- At width 0 the coset tower's section IS the empty word on the nose —
-- Simplified.NfEps.nf-ε-zero, the one width at which it is, since the
-- base level sends everything to ε — so rep Iᶜ reduces to ε and both
-- hypotheses hold by computation.  (Conj-trivial is doubly free here:
-- the Pauli alphabet (⊤ ⊎ ⊤) ⊎^ 0 is ⊥.)
--
-- This is Proposition 2.55 discharged in full at one width: the
-- interpretation, both bijective normal forms, soundness of conj and
-- corr, the realisation conditions and the Reidemeister–Schreier engine
-- all run with nothing assumed.  The group is trivial, so the content
-- is in the plumbing rather than the mathematics — but it is the first
-- instance to close end to end, and a width-n proof reuses every part
-- of it.
--
-- Above width 0 rep Iᶜ does not even reduce to a word: it is stuck on
-- CosetNF.SingleLevel.Transfer's section applied to the coset, so no
-- amount of computation will discharge these two.  That is what makes
-- the tower's own identity-section lemma the next thing needed.

sec-trivial-0 : Sec-trivial 0
sec-trivial-0 = PB.refl

conj-trivial-0 : Conj-trivial 0
conj-trivial-0 ()

presentation-0 : (0 Clifford,_===_) IsPresentationOf (CMS-group 0)
presentation-0 = presentation sec-trivial-0 conj-trivial-0

------------------------------------------------------------------------
-- Width 1: the identity section reduces without order-S
--
-- rep Iᶜ does compute here: it is ε • [ I₀ ]ᵐˡ on the nose, Tower01's
-- identity section with the coset-transfer's leading unit.  So the
-- reduction to ε is Tower01's [I]≈ε₀ chain, and the question is only
-- whether it can be replayed using correction-free axioms.
--
-- It can, and with room to spare — the chain needs exactly one axiom.
-- The M-part contributes nothing: [ ([] , ₀) ]ᵐ • [ [] ]ᵛᵇ is
-- S^ (- ₀) • ε, which right-unit and a ≡-congruence on -0#≈0# take to
-- S^ ₀ = ε.  What is left is the A-box XM ₁, and at p = 2 that is
-- literally the right-hand side of M-power at k = ₀: ℤ*₂ = {1} forces
-- g^ ₀ = ₁, so M (g^ ₀) and XM (₁ , _) are the same word, while the
-- left-hand side Mg^ ₀ = Mg ^ 0 is ε.  So the A-box collapses by the
-- single axiom M-power ₀ — which is not order-S, hence lifts exactly.
--
-- Note this is a different route from the original rule set's, which
-- reaches XM ₁ ≈ ε through order-SH (lemma-M1); the simplified set has
-- no order-SH, and M-power turns out to be the cleaner road anyway.

-- The identity A-box collapses correction-free, at EVERY width: nothing
-- in the argument is special to width 1.  This is Normalization's
-- [Ia]≈ε, done in the correction-free calculus and by a shorter route —
-- that file goes through XM≡ZM⁻¹, aux-MM and aux-mc1ε, where M-power ₀
-- is a single axiom.
a-box-free : ∀ {n} →
  PB._≈_ (EP.Clifford.Corr-free (₁₊ n)) (XM {n} (₁ , λ ())) ε
a-box-free = PB.sym (PB.axiom (srel (M-power ₀) , Eq.refl))

-- H² ≈ ε, correction-free, at every width.  The simplified rule set
-- only gives H² = M₋₁, and at p = 2 that scalar is Mg = XM ₁, which
-- a-box-free kills.  This is the fact the ORIGINAL rule set has as an
-- axiom (order-H there reads H⁴ = ε), so it is the bridge every
-- H-manipulation in Normalization's identity-section chain needs when
-- replayed here — [₀]ᵇ≈Ex in particular.
H²-free : ∀ {n} → PB._≈_ (EP.Clifford.Corr-free (₁₊ n)) (H ^ 2) ε
H²-free = PB.trans (PB.axiom (srel order-H , Eq.refl)) a-box-free

-- Wire-shifting preserves correction-freeness.  Structurally this is the
-- same seven-case induction as rights₀ — _↑ is a wmap, so it takes ε to
-- ε and • to • on the nose — and the axiom case is where the tightened
-- side condition pays: cong↑ is a rule of the lifted relation, and
-- corr (cong↑ r) is shiftPauli (corr r), so a correction that is ε
-- literally stays ε literally under the shift.
↑-free : ∀ {n} {w v : Circuit n} →
  PB._≈_ (EP.Clifford.Corr-free n) w v →
  PB._≈_ (EP.Clifford.Corr-free (₁₊ n)) (w ↑) (v ↑)
↑-free PB.refl              = PB.refl
↑-free (PB.sym p)           = PB.sym (↑-free p)
↑-free (PB.trans p q)       = PB.trans (↑-free p) (↑-free q)
↑-free (PB.cong p q)        = PB.cong (↑-free p) (↑-free q)
↑-free PB.assoc             = PB.assoc
↑-free PB.left-unit         = PB.left-unit
↑-free PB.right-unit        = PB.right-unit
↑-free (PB.axiom (r , triv)) =
  PB.axiom (cong↑ r , Eq.cong shiftPauli triv)

-- The involution kit for Ex = (CZ • H • H ↑)³.  At p = 2 all three of
-- its letters square to ε in the correction-free calculus: H by H²-free,
-- H ↑ by shifting that, and CZ by order-CZ, whose p is 2.
H↑²-free : ∀ {n} →
  PB._≈_ (EP.Clifford.Corr-free (₂₊ n)) ((H ↑) ^ 2) ε
H↑²-free = ↑-free H²-free

CZ²-free : ∀ {n} →
  PB._≈_ (EP.Clifford.Corr-free (₂₊ n)) (CZ ^ 2) ε
CZ²-free = PB.axiom (srel order-CZ , Eq.refl)

sec-reduction-1 : Sec-reduction 1
sec-reduction-1 =
  trans left-unit
    (trans (sym assoc)
      (trans (cleft (trans right-unit (refl' (Eq.cong S^ -0#≈0#))))
        (trans left-unit a-box-free)))
  where
  open PB (EP.Clifford.Corr-free 1)

sec-trivial-1 : Sec-trivial 1
sec-trivial-1 = sec-trivial sec-reduction-1

------------------------------------------------------------------------
-- Towards width n
--
-- Normalization.[I]≈ε' already proves the identity section trivial at
-- every width, and with the same chain as width 1 — sym assoc, cleft
-- aux-MB, left-unit, [Ia]≈ε — so the general case is that chain replayed
-- in Corr-free, plus the tower step.  What each part costs, in the
-- SIMPLIFIED rule set:
--
--   [Ia]≈ε      a-box-free above, at every width.  Done.
--   [₀]ᵉ≈ε      refl' on -0#≈0#: no axiom, so it ports verbatim.
--   [₀]ᵈ≈Ex     refl' and right-unit: likewise.
--   [₀]ᵇ≈Ex     needs H⁴ ≈ ε, which the original rule set has as its
--               order-H axiom and this one does not.  H²-free supplies
--               it: H⁴ = H² • H², twice H²-free.
--   aux-MB      induction on the width.  The ↑-congruence it needs is
--               ↑-free above.  What is left is lemma-order-Ex-n
--               (Ex • Ex ≈ ε), and that one is not a leaf: it is
--               by-emb n lemma-order-Ex, and lemma-order-Ex sits on the
--               Ex-Sym1/2/2n/3n/4/4n family together with Ex-Rewriting
--               and XEX-Rewriting.  Porting the identity-section chain
--               therefore means auditing that whole family for order-S,
--               not discharging one lemma — which is the main reason to
--               weigh the alternative route below.
--
-- The alternative.  Patch the quotient section to send the identity
-- coset to ε on the nose, and Sec-trivial and Conj-trivial both become
-- refl at EVERY width, with no reduction to replay and no Ex lemmas
-- involved.  A BijectiveNormalForm's section comes from its surjectivity
-- field, and redefining that field at the single index nfˢ ε costs only
-- nf-cong; the round trips survive (nf ε ≡ nfˢ ε there by construction,
-- and inv-nf ∘ nf ≈ id by injectivity of nfˢ).  Its price is a decision
-- procedure for u ≡ nfˢ ε on NF n: the data components are Fins and
-- Vecs, and the ≢-proof that A carries — the one part not decidable on
-- its own — is pinned by Normalization.Uniqueness.⟦[]⟧-injective, which
-- recovers the full propositional equality from equal denotations.
-- Bounded, mechanical, and it closes all widths at once.
--   the tower   at width 1, rep Iᶜ is ε • [ I₀ ]ᵐˡ definitionally.  At
--               width n it is a nest of levels, so this becomes an
--               induction: nfˢ ε is the identity NF at each level, and
--               the transfer's section of a pair is (f ʷ) of the level
--               below concatenated with that level's coset section.
--
-- One design note for the ↑-congruence.  Corr-free asks corr r̄ ≈s ε; if
-- it asked for corr r̄ ≡ ε instead, lifting an axiom through cong↑ would
-- be free, since corr (cong↑ r) is shiftPauli (corr r) and shiftPauli ε
-- reduces to ε.  Every witness built so far proves its side condition by
-- refl, so nothing would be lost by tightening it.

-- Conj-trivial 1 is still open, and it is a different kind of problem.
-- Conjugating a Pauli generator by that representative rebuilds it
-- letterwise: (SH)³ is the identity symplectic map, so the vector comes
-- back unchanged, but conj is applied one gate at a time and each step
-- re-expands through vecToWord, so after the six letters of XM ₁ the
-- word is a tree of X/Z leaves rather than the generator it started as.
--
-- Two routes are closed.  Structural reasoning is hopeless by hand (the
-- tree roughly doubles per step).  Comparing the two sides through the
-- Pauli normal form — nf-injective (bijectiveᴾ 1) Eq.refl — fails
-- because nfᴾ is vec ∘ ⟦_⟧N, and ⟦_⟧N is the direct-product
-- presentation's interpretation: a Group-bundle term that does not
-- reduce to a vector by computation.
--
-- What is wanted is the lemma that conj computes the action, at the
-- level of the PAULI group rather than of CMS:
--
--     ⟦ conjss w u ⟧N  ≈  actg-of w applied to ⟦ u ⟧N
--
-- with which Conj-trivial follows from rep Iᶜ ≈q ε and soundness of the
-- symplectic presentation, uniformly in n rather than width by width.
-- Qubit.ExtensionSoundness.conj-sound is the same statement read in
-- CMS n; this is its Pauli-side twin.
