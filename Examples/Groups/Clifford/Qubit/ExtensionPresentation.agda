------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 2.55 applied to the qubit Clifford extension (p = 2):
-- _Clifford,_===_ presents CMS n.
--
-- Everything the proposition needs about the group is already built:
--
--   * the extension  1 → Pauli n → CMS n → Sp(2n,2) → 1  is
--     CMS.Clifford-extension (the Vec-based extension of
--     Qubit.CliffordGroup, transported to the nested Pauli-group that a
--     presentation produces);
--   * the kernel is presented by Γ-H ⊕^ n   (Pauli.Presentation), and
--   * the quotient by the simplified symplectic rule set
--     (Symplectic.Simplified.Presentation);
--   * conj and corr are Qubit.Presentation's, and the extension relation
--     _Clifford,_===_ is by definition extension-presentation of exactly
--     these four.
--
-- What is assembled here is the instantiation, and the interpretation
-- ⟦_⟧₀ of the generators in CMS n: a gate is itself, a Pauli generator is
-- conjugation by the corresponding Pauli operator (CMS.pauliIncl).
--
-- The proposition's four remaining inputs are left as arguments of
-- `presentation`, and its two normal-form witnesses as parameters of
-- this module.  They are, in the order the work is likely to be done:
--
--   nfpS, nfpQ  bijective normal forms for the two factors.  Both
--               factors have a NormalForm in the library already; a
--               BIJECTIVE one needs additionally nf ∘ inv-nf ≡ id, which
--               follows from the corresponding uniqueness theorem
--               (⟦ inv-nf a ⟧ ≈ ⟦ inv-nf b ⟧ → a ≡ b) applied to
--               inv-nf∘nf=id — see Symplectic.Normalization.Uniqueness.
--   sound-ax    the substance: conj records conjugation in CMS n, and
--               each twisted relator's correction word is the Pauli that
--               lifting it accumulates.  This is the semantic twin of
--               Selinger.Conjugation / Selinger.Relators, which prove the
--               same two families inside Figure 8 mod scalars.
--   nf-ε        the quotient normal form sends ε to ε.
--   real-Q      a gate projects to its symplectic value.
--
-- Why this module exists: with `presentation` in hand, completeness of
-- _Clifford,_===_ for CMS n is one projection away, and composing it
-- with Selinger.Iso gives Selinger.Scalars.Complete-mod-scalars — the
-- single input still missing from ExactData.scalars.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.ExtensionPresentation where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Level using (0ℓ)

open import Word.Base using (Word ; [_]ʷ ; ε)
open import Presentation.Construct.Base using (_⊕^_)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.NormalForm.Setoid as SNF
open import Relation.Binary.PropositionalEquality using (_≡_)
import Presentation.Construct.Properties.Extension as Ext

open import Examples.Groups.Clifford.Qubit.Presentation
  using (p-2 ; p-prime ; PauliGen ; genToVec ; conj ; corr ; _Clifford,_===_)

open import Examples.Groups.Pauli.Presentation p-2 p-prime
  using (Γ-H ; Pauli-group ; Pauli-presentation)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (g* ; g-gen)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (_QRel,_===_)
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen
  as SimP

open import Examples.Groups.Clifford.Qubit.CMS
  using (Clifford-extension ; Clifford-group ; pauliIncl)

------------------------------------------------------------------------
-- The interpretation of the generators in CMS n
--
-- A gate generator is the one-letter Clifford word; a Pauli generator is
-- conjugation by the Pauli operator it names, which is exactly the
-- inclusion of the extension (CMS.pauliIncl, i.e. the pauliWord circuit).

⟦_⟧₀ : {n : ℕ} → (PauliGen n ⊎ Gen n) → Group.Carrier (Clifford-group n)
⟦_⟧₀ {n} (inj₁ y) = pauliIncl n (genToVec y)
⟦_⟧₀     (inj₂ g) = [ g ]ʷ

------------------------------------------------------------------------
-- Proposition 2.55, instantiated

module Clifford (n : ℕ)
  {NFS NFQ : Set}
  (nfpS : BijectiveNormalForm (Γ-H ⊕^ n) NFS)
  (nfpQ : BijectiveNormalForm (n QRel,_===_) NFQ)
  where

  -- (The proposition's own module is opened publicly; it internally
  -- names a module E, so this one is EP.)
  open module EP = Ext.Presentation
    (Γ-H ⊕^ n) (n QRel,_===_) conj corr
    (Pauli-group n) (Sp-group n) (Clifford-extension n)
    (Pauli-presentation n) (SimP.presentation {n})
    ⟦_⟧₀ nfpS nfpQ
    public

  -- The headline, once the four compatibility inputs are supplied.
  presentation :
    Realises →
    (∀ {w v} → Ext.extp (Γ-H ⊕^ n) (n QRel,_===_) conj corr w v →
               Group._≈_ (Clifford-group n) ⟦ w ⟧ ⟦ v ⟧) →
    SNF.BijectiveNormalForm.inv-nf nfpQ (SNF.BijectiveNormalForm.nf nfpQ ε) ≡ ε →
    (∀ x → Group._≈_ (Sp-group n) (proj ⟦ inj₂ x ⟧₀) ⟦ [ x ]ʷ ⟧Q) →
    (n Clifford,_===_) IsPresentationOf (Clifford-group n)
  presentation = dpres
