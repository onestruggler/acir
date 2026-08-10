------------------------------------------------------------------------
-- Presentations of groups
--
-- The dictionary between the two generating sets compared in
-- Qubit.Selinger.Iso.
--
-- The extension presentation _Clifford,_===_ names the Paulis as
-- generators, over PauliGen n ⊎ Gen n; Selinger's Figure 8 derives them
-- as the words X = HS²H and Z = S² over Gen n.  Translating between the
-- two therefore needs a map in each direction,
--
--     f : PauliGen n ⊎ Gen n → Word (Gen n)     (Paulis to gate words)
--     g : Gen n → Word (PauliGen n ⊎ Gen n)     (gates to themselves)
--
-- together with the small lemmas saying how their word extensions relate
-- to the embeddings [_]ₗ and [_]ᵣ.  Nothing here mentions either rule
-- set: this module is pure translation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Translation where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap ; WRel)

import Presentation.Base as PB
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; _↑)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; vecToWord)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (pIₙ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The two translations

-- A Pauli generator names a single-qubit X or Z at one position; send it
-- to the corresponding derived word X = HS²H or Z = S² on that wire.
-- The clause structure matches genToVec in Qubit.Presentation.
pauliGen→word : PauliGen n → Word (Gen n)
pauliGen→word {₁₊ zero} (inj₁ tt)        = X
pauliGen→word {₁₊ zero} (inj₂ tt)        = Z
pauliGen→word {₂₊ n}    (inj₁ (inj₁ tt)) = X
pauliGen→word {₂₊ n}    (inj₁ (inj₂ tt)) = Z
pauliGen→word {₂₊ n}    (inj₂ y)         = (pauliGen→word {₁₊ n} y) ↑

-- Paulis become their gate words; gates stay put.
f : PauliGen n ⊎ Gen n → Word (Gen n)
f (inj₁ y)  = pauliGen→word y
f (inj₂ gg) = [ gg ]ʷ

-- Gates embed on the right.
g : Gen n → Word (PauliGen n ⊎ Gen n)
g gg = [ inj₂ gg ]ʷ

------------------------------------------------------------------------
-- The distinguished wire-0 Pauli generators
--
-- Both match the shape of Presentation.Z₀, which is defined by cases on
-- the wire count.

Z-gen : PauliGen (₁₊ n)
Z-gen {zero} = inj₂ tt
Z-gen {₁₊ m} = inj₁ (inj₂ tt)

X-gen : PauliGen (₁₊ n)
X-gen {zero} = inj₁ tt
X-gen {₁₊ m} = inj₁ (inj₁ tt)

------------------------------------------------------------------------
-- How the word extensions relate to the embeddings

-- (g ʷ) is the right embedding.
gʷ≡ᵣ : (w : Word (Gen n)) → (g ʷ) w ≡ [ w ]ᵣ
gʷ≡ᵣ [ x ]ʷ  = Eq.refl
gʷ≡ᵣ ε       = Eq.refl
gʷ≡ᵣ (u • v) rewrite gʷ≡ᵣ u | gʷ≡ᵣ v = Eq.refl

-- Pw translates a whole Pauli word; it is what (f ʷ) does to a
-- left-embedded word.
Pw : Word (PauliGen n) → Word (Gen n)
Pw = pauliGen→word ʷ

fₗ≡Pw : (u : Word (PauliGen n)) → (f ʷ) [ u ]ₗ ≡ Pw u
fₗ≡Pw [ y ]ʷ  = Eq.refl
fₗ≡Pw ε       = Eq.refl
fₗ≡Pw (u • v) rewrite fₗ≡Pw u | fₗ≡Pw v = Eq.refl

-- Translating a shifted Pauli word shifts its translation.
Pw-↑ : (m : ℕ) (u : Word (PauliGen (₁₊ m))) →
       Pw {₂₊ m} (wmap inj₂ u) ≡ (Pw {₁₊ m} u) ↑
Pw-↑ m [ y ]ʷ  = Eq.refl
Pw-↑ m ε       = Eq.refl
Pw-↑ m (u • v) rewrite Pw-↑ m u | Pw-↑ m v = Eq.refl

------------------------------------------------------------------------
-- Relabelling the identity Pauli

wmap-∘ : ∀ {A B C : Set} (fn : B → C) (h : A → B) (w : Word A) →
         wmap fn (wmap h w) ≡ wmap (λ x → fn (h x)) w
wmap-∘ fn h [ x ]ʷ  = Eq.refl
wmap-∘ fn h ε       = Eq.refl
wmap-∘ fn h (u • v) rewrite wmap-∘ fn h u | wmap-∘ fn h v = Eq.refl

-- vecToWord of the identity Pauli is a nest of ε's (one per zero
-- exponent), so any relabelling of it collapses.  Stated for an
-- arbitrary relation, since only the monoid laws are used.
pIw-ε : ∀ {A : Set} (Γ : WRel A) (m : ℕ) (fn : PauliGen m → A) →
        PB._≈_ Γ (wmap fn (vecToWord (pIₙ {m}))) ε
pIw-ε Γ zero      fn = PB.refl
pIw-ε Γ (₁₊ zero) fn = PB.left-unit
pIw-ε Γ (₂₊ k)    fn =
  PB.trans (PB.cong PB.left-unit
              (Eq.subst (λ □ → PB._≈_ Γ □ ε)
                        (Eq.sym (wmap-∘ fn inj₂ (vecToWord (pIₙ {₁₊ k}))))
                        (pIw-ε Γ (₁₊ k) (λ x → fn (inj₂ x)))))
           PB.left-unit
