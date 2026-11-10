------------------------------------------------------------------------
-- Presentations of groups
--
-- Block normal forms and certified equations for four-bit reversible
-- circuits: the main theorem
--
-- The theory T of Figure 1 (rules (1)–(7)) with the symmetric monoidal
-- laws is sound and complete for circuits over X, CX and CCX on four
-- wires, and on one, two and three (Theorem 1.1, Propositions
-- B.1–B.3); the four-wire circuits present Alt(16), and those on one,
-- two and three wires Sym(2), Sym(4), Sym(8) (Corollary 5.2); every
-- four-wire circuit rewrites to a unique block normal form NF(E, B, S),
-- the normal forms are in bijection with Alt(16) (Proposition 3.3), and
-- a gate followed by a normal form rewrites to the normal form with the
-- updated coordinates (Theorem 5.1).  This module collects the
-- statements behind one import: the circuits, the rules at each width
-- (_CRel,_===_), a circuit's function ⟦_⟧ and pointwise equality _≐_,
-- derivability ⊢_≈_, and the theorems.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.MainTheorem where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Product.Base using (Σ ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Presentation.Base as PB
open import Word.Base using (_•_)
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)
open import Examples.Groups.Alternating.Semantics using (Alt ; Alt-group)

open import Examples.Groups.XCXCCX-4bit.Syntactics public
  using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.XCXCCX-4bit.Semantics public using (Bits ; _≐_)
import Examples.Groups.XCXCCX-4bit.Semantics as Sem
import Examples.Groups.XCXCCX-4bit.Width1 as W1
import Examples.Groups.XCXCCX-4bit.Width2 as W2
import Examples.Groups.XCXCCX-4bit.Width3 as W3
import Examples.Groups.XCXCCX-4bit.Completeness as C
import Examples.Groups.XCXCCX-4bit.Groups as G
open import Examples.Groups.XCXCCX-4bit.NormalForm public
  using (Coords ; E ; B ; S ; S8 ; NF ; coords ; absorb)
import Examples.Groups.XCXCCX-4bit.NormalForm as N
-- The numbering of the sixteen states (Four's, lower half first).
open N.F public using (enc)

-- Equality by the rules.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

-- A circuit's function on the states of its wires.
⟦_⟧ : ∀ {n} → Circuit n → Bits n → Bits n
⟦_⟧ = Sem.⟦_⟧

------------------------------------------------------------------------
-- Soundness and completeness (Theorem 1.1, Propositions B.1–B.3)

sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound = Sem.sound

complete : {w v : Circuit 4} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⊢ w ≈ v
complete = C.complete₄

complete₁ : {w v : Circuit 1} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⊢ w ≈ v
complete₁ = W1.complete₁

complete₂ : {w v : Circuit 2} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⊢ w ≈ v
complete₂ = W2.complete₂

complete₃ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⊢ w ≈ v
complete₃ = W3.complete₃

------------------------------------------------------------------------
-- The groups of circuits (Corollary 5.2, Propositions B.1–B.3)

presentation₁ : (1 CRel,_===_) IsPresentationOf Permutation′-group 2
presentation₁ = G.presentation₁

presentation₂ : (2 CRel,_===_) IsPresentationOf Permutation′-group 4
presentation₂ = G.presentation₂

presentation₃ : (3 CRel,_===_) IsPresentationOf Permutation′-group 8
presentation₃ = G.presentation₃

presentation₄ : (4 CRel,_===_) IsPresentationOf Alt-group 16
presentation₄ = G.presentation₄

------------------------------------------------------------------------
-- The block normal form (Theorem 1.1, Proposition 3.3, Theorem 5.1)

-- Every circuit rewrites to the normal form of its coordinates ...
normal-form : (u : Circuit 4) → ⊢ u ≈ NF (coords u)
normal-form = N.normal-form

-- ... which are determined by its function.
unique : (c c′ : Coords) → ⟦ NF c ⟧ ≐ ⟦ NF c′ ⟧ →
         (∀ i → S c i ≡ S c′ i) × (∀ p → B c ⟨$⟩ʳ p ≡ B c′ ⟨$⟩ʳ p) ×
         (∀ p → Alt.perm (E c) ⟨$⟩ʳ p ≡ Alt.perm (E c′) ⟨$⟩ʳ p)
unique = N.NF-unique

-- Every even permutation of the sixteen states is a normal form's.
onto : (a : Alt 16) → Σ Coords (λ c → ∀ i → ⟦ NF c ⟧ (enc i) ≡ enc (Alt.perm a ⟨$⟩ʳ i))
onto = N.NF-onto

-- A circuit w (a gate, say) followed by a normal form rewrites to the
-- normal form with the updated coordinates (NormalForm.Absorb gives
-- them: S′ = w⁻¹ S, B′ = B A₀, E′ B′ = E B A₁).
absorption : (c : Coords) (w : Circuit 4) → ⊢ w • NF c ≈ NF (absorb c w)
absorption = N.absorption
