------------------------------------------------------------------------
-- Presentations of groups
--
-- Surjectivity of the Clifford action onto the symplectic group:
-- every symplectic transformation S : Sp(2n, ℤ/pℤ) is the action of
-- some Clifford circuit w ∈ Word (Gen n).
--
-- The hard content is NF.lemma-invnf (any linear sform-preserving map
-- has a normal form that inverts it); here we package it against the
-- bundled group Sp-group (Examples.Groups.Symplectic.Semantics).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=2 #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.ExtendedGate.Surjectivity (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_ ; [] ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≗_)

open import Function.Definitions using (Surjective)

open import Word.Base using (Word ; _•_ ; ε ; [_]ʷ)
open import Notations
import Presentation.Base as PB
open import Presentation.GroupLike

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli ; Pauli1)
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open Symplectic-Derived-Gen      using (Gen ; _↑ ; _QRel,_===_)
open Symplectic-Derived-GroupLike using (grouplike)
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.ActionLemmas p-2 p-prime using (NF ; [_]ˡᵐ)
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime using (act ; act1)
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime using (act-sound-ax)
open import Examples.Groups.Symplectic.ExtendedGate.NF p-2 p-prime
  using (act-nf ; lemma-invnf ; sform-preserving ; lemma-actw-linear)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
open Symplectic

------------------------------------------------------------------------
-- Turning a normal form into a word with the same action

-- act (w ↑) fixes the head qupit and acts by w on the tail.
act-↑ : ∀ {n} (w : Word (Gen n)) (p : Pauli1) (ps : Pauli n)
      → act (w ↑) (p ∷ ps) ≡ p ∷ act w ps
act-↑ [ g ]ʷ   p ps = Eq.refl
act-↑ ε        p ps = Eq.refl
act-↑ (w • w') p ps =
  Eq.trans (Eq.cong (act (w ↑)) (act-↑ w' p ps)) (act-↑ w p (act w' ps))

-- The word realising a normal form.
nf→word : ∀ {n} → NF n → Word (Gen n)
nf→word {₀}    _        = ε
nf→word {₁₊ n} (ih , lm) = nf→word ih ↑ • [ lm ]ˡᵐ

-- It has the same action as the normal form.
act-nf→word : ∀ {n} (nf : NF n) → act (nf→word nf) ≗ act-nf nf
act-nf→word {₀}    _        []       = Eq.refl
act-nf→word {₁₊ n} (ih , lm) ps with act [ lm ]ˡᵐ ps
... | (x ∷ xs) =
  Eq.trans (act-↑ (nf→word ih) x xs)
           (Eq.cong (x ∷_) (act-nf→word ih xs))

------------------------------------------------------------------------
-- The Clifford action as a map into the symplectic group, and its
-- surjectivity.

module _ {n : ℕ} where

  open Group-Lemmas (n QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)
  open Group-Action (Pauli n) (Gen n) (n QRel,_===_) grouplike act1
    (act-sound-ax {n} _ _) using (act-cong)
  open PB (n QRel,_===_) using (_≈_)

  -- Every circuit is a symplectic transformation.
  ⟦_⟧ : Word (Gen n) → Symplectic n
  ⟦ w ⟧ = record
    { ap        = act w
    ; ap⁻¹      = act (w ⁻¹ʷ)
    ; invˡ      = λ p → act-cong (w ⁻¹ʷ • w) ε p inverseˡ
    ; invʳ      = λ p → act-cong (w • w ⁻¹ʷ) ε p inverseʳ
    ; linear-+  = proj₁ (lemma-actw-linear w)
    ; linear-*  = proj₂ (lemma-actw-linear w)
    ; preserves = sform-preserving w
    }

  -- Surjectivity: every symplectic transformation is realised by a
  -- circuit.
  surjective : ∀ (S : Symplectic n) → ∃ λ w → ⟦ w ⟧ ≈ˢ S
  surjective S = nf→word nf , claim
    where
    open Eq.≡-Reasoning
    -- lemma-invnf applied to the (linear, symplectic) inverse of S.
    invnf = lemma-invnf (ap⁻¹ S)
              (linear-+ (S ⁻¹ˢ) , linear-* (S ⁻¹ˢ)) (preserves (S ⁻¹ˢ))
    nf = proj₁ invnf

    claim : act (nf→word nf) ≗ ap S
    claim p = begin
      act (nf→word nf) p               ≡⟨ act-nf→word nf p ⟩
      act-nf nf p                      ≡⟨ Eq.cong (act-nf nf) (Eq.sym (invˡ S p)) ⟩
      act-nf nf (ap⁻¹ S (ap S p))      ≡⟨ proj₂ invnf (ap S p) ⟩
      ap S p                           ∎

  -- The same fact as stdlib's setoid surjectivity of ⟦_⟧, from the word
  -- setoid (Word / ≈) onto (Symplectic / ≈ˢ): ⟦_⟧ respects the congruence,
  -- so any z ≈ (the witness) also realises S.
  surjective-fn : Surjective _≈_ _≈ˢ_ ⟦_⟧
  surjective-fn S = w , λ {z} z≈w p → Eq.trans (act-cong z w p z≈w) (w≈S p)
    where
    w   = proj₁ (surjective S)
    w≈S = proj₂ (surjective S)
