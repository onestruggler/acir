------------------------------------------------------------------------
-- Presentations of groups
--
-- The coordinate identity behind Proposition 2.55's `Realises` for the
-- qubit Clifford extension (p = 2).
--
-- Realises asks that ⟦_⟧₀ send a Pauli generator to the inclusion of its
-- value in the kernel.  Both sides are conjugation by a Pauli operator —
-- the transported inclusion is pauliIncl ∘ vec — so everything reduces to
--
--     vec n ⟦ [ y ]ʷ ⟧N  ≡  genToVec y,
--
-- i.e. that the Pauli presentation's reading of a generator is the basis
-- vector genToVec names.
--
-- At width 1 the two sides are the same pair, so those cases are refl.
-- At width ≥ 2 the interpretation is the direct-product one: a
-- left-injected generator goes to (⟦ a ⟧ , ε), and the goal left on the
-- tail is vec (₁₊ m) ε ≡ pIₙ — which is CMS.vec-ε.  The inj₂ case
-- recurses into the tail.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Realises where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ)

open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.Construct.Base using (_⊕^_ ; _⊎^_)

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.ProjectiveClifford.Qubit.Presentation
  using (PauliGen ; genToVec)
open import Examples.Groups.ProjectivePauli.Presentation p-2 p-prime
  using (Γ-H ; Pauli-group ; Pauli-presentation)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; pI ; pX ; pZ)
open import Examples.Groups.ProjectiveClifford.Qubit.CMS using (vec ; vec-ε)

-- The Pauli presentation's reading of a Pauli word.
⟦_⟧N : {n : ℕ} → Word (PauliGen n) → Group.Carrier (Pauli-group n)
⟦_⟧N {n} = _IsPresentationOf_.⟦_⟧ (Pauli-presentation n)

vec-gen : (n : ℕ) (y : PauliGen n) → vec n ⟦ [ y ]ʷ ⟧N ≡ genToVec y
vec-gen (₁₊ zero) (inj₁ tt)        = Eq.refl
vec-gen (₁₊ zero) (inj₂ tt)        = Eq.refl
vec-gen (₂₊ m)    (inj₁ (inj₁ tt)) = Eq.cong (pX ∷_) (vec-ε (₁₊ m))
vec-gen (₂₊ m)    (inj₁ (inj₂ tt)) = Eq.cong (pZ ∷_) (vec-ε (₁₊ m))
vec-gen (₂₊ m)    (inj₂ y)         = Eq.cong (pI ∷_) (vec-gen (₁₊ m) y)
