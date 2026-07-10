------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group (p = 2), presented as a group extension
-- (Selinger, arXiv:1310.6813).
--
--     1 ─→ Pauli n ─→ Clifford n ─→ Sp(2n, 2) ─→ 1
--
-- The (phaseless) Pauli group is normal and the quotient is the
-- symplectic group.  Using Presentation.Construct.Properties.Extension
-- (Proposition 2.55), a presentation of the extension is
--
--     extension-presentation S R̄ conj corr
--
-- where
--   * S    = the Pauli presentation      (Examples.Groups.Pauli.Presentation),
--   * R̄    = the symplectic relations     (Symplectic._QRel,_===_),
--   * conj = the symplectic action of a quotient generator on a Pauli
--            generator (the word-valued form of Symplectic.Action.act1),
--   * corr = the cocycle: the Pauli correction word carried by each
--            symplectic relator when it is lifted to Clifford.
--
-- The p = 2 cocycle.  Working in the *phaseless* Pauli group (Pauli1 =
-- ℤ/2 × ℤ/2, no phase), the only symplectic relator that fails to lift
-- exactly is order-S: over the qubit phase gate S = diag(1, i) one has
-- S² = Z, so corr(order-S) = Z on the acted qubit.  Every other relator
-- lifts either exactly or up to a global phase (e.g. (SH)³ = e^{iπ/4}·I,
-- the two-qubit selinger relators up to e^{-iπ/4}), and a global phase is
-- trivial in the phaseless Pauli group.  cong↑ shifts a correction up one
-- qubit.  This was verified numerically against the exact 2×2/4×4/8×8
-- Clifford matrices under the act1 conventions.
--
-- (For odd p the extension splits — every correction is ε; that case is
-- the odd-prime development under Examples.Groups.Symplectic.Clifford.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.Presentation where

open import Data.Nat using (ℕ ; zero)
open import Data.Nat.Primality using (Prime ; prime?)
open import Relation.Nullary.Decidable using (from-yes)

-- This module is the qubit case: fix the prime to 2.
p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Fin using (toℕ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^'_ ; wmap)
open import Notations using (₁₊ ; ₂₊)

open import Presentation.Construct.Base using (_⊕^_ ; _⊎^_)
open import Presentation.Construct.Properties.Extension using (extension-presentation)

-- S : the Pauli presentation, over the generators (⊤ ⊎ ⊤) ⊎^ n
-- (an X- and a Z-generator per qubit).
open import Examples.Groups.Pauli.Presentation p-2 p-prime using (Γ-H)

-- The Pauli group as vectors, and the symplectic action act1.
open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pX ; pZ ; pI ; pIₙ)
open import Examples.Groups.Symplectic.Action p-2 p-prime using (act1)

-- R̄ : the symplectic relations, over the Clifford generators Gen n.
open import Examples.Groups.Symplectic.Symplectic-Derived p-2 p-prime
open Symplectic-Derived-Gen using (Gen ; _QRel,_===_ ; order-S ; cong↑)

------------------------------------------------------------------------
-- Generator sets

-- The Pauli generators of n qubits: X_i and Z_i for each i.
PauliGen : ℕ → Set
PauliGen n = (⊤ ⊎ ⊤) ⊎^ n

------------------------------------------------------------------------
-- conj : the word-valued symplectic action
--
-- conj g y :   the word over Pauli generators equal, inside Clifford, to
--              the conjugate g · y · g⁻¹ of the Pauli generator y by the
--              quotient generator g.  Determined by Symplectic.Action.act1.

-- A Pauli generator names a single-qubit X or Z at one position; read it
-- back as a basis vector of the Pauli group.
genToVec : ∀ {n} → PauliGen n → Pauli n
genToVec {₁₊ zero}  (inj₁ tt)        = pX ∷ []
genToVec {₁₊ zero}  (inj₂ tt)        = pZ ∷ []
genToVec {₂₊ n} (inj₁ (inj₁ tt)) = pX ∷ pIₙ
genToVec {₂₊ n} (inj₁ (inj₂ tt)) = pZ ∷ pIₙ
genToVec {₂₊ n} (inj₂ y)         = pI ∷ genToVec {₁₊ n} y

-- Delog a Pauli vector to a word: position i with exponents (a , b) becomes
-- X_i^a • Z_i^b, positions laid out left to right.
vecToWord : ∀ {n} → Pauli n → Word (PauliGen n)
vecToWord {zero}     []              = ε
vecToWord {₁₊ zero}  ((a , b) ∷ []) =
  [ inj₁ tt ]ʷ ^' toℕ a • [ inj₂ tt ]ʷ ^' toℕ b
vecToWord {₂₊ n} ((a , b) ∷ ps) =
  ([ inj₁ (inj₁ tt) ]ʷ ^' toℕ a • [ inj₁ (inj₂ tt) ]ʷ ^' toℕ b)
  • wmap inj₂ (vecToWord {₁₊ n} ps)

conj : ∀ {n} → Gen n → PauliGen n → Word (PauliGen n)
conj g y = vecToWord (act1 g (genToVec y))

------------------------------------------------------------------------
-- corr : the p = 2 cocycle
--
-- corr r :     the Pauli correction word carried by the quotient relator r,
--              i.e. [ lhs ]ᵣ ≈ [ corr r ]ₗ • [ rhs ]ᵣ.

-- The Z-generator on qubit 0.
Z₀ : ∀ {n} → Word (PauliGen (₁₊ n))
Z₀ {zero}  = [ inj₂ tt ]ʷ
Z₀ {₁₊ m}  = [ inj₁ (inj₂ tt) ]ʷ

-- Shift a Pauli word up one qubit (position i ↦ i+1); used by cong↑.
shift-gen : ∀ {n} → PauliGen n → PauliGen (₁₊ n)
shift-gen {zero}  ()
shift-gen {₁₊ m}  y = inj₂ y

shiftPauli : ∀ {n} → Word (PauliGen n) → Word (PauliGen (₁₊ n))
shiftPauli = wmap shift-gen

-- The only nontrivial correction is S² = Z (order-S); cong↑ shifts a
-- correction up one qubit; every other relator lifts with no Pauli.
corr : ∀ {n} {u v} → (n QRel,_===_) u v → Word (PauliGen n)
corr order-S    = Z₀
corr (cong↑ r)  = shiftPauli (corr r)
corr _          = ε

------------------------------------------------------------------------
-- The Clifford presentation, as an extension of Pauli by the symplectic
-- group.

infix 4 _Clifford,_===_

_Clifford,_===_ : (n : ℕ) → WRel (PauliGen n ⊎ Gen n)
_Clifford,_===_ n = extension-presentation (Γ-H ⊕^ n) (n QRel,_===_) conj corr


import Presentation.Properties as PP
import Presentation.Base as PB
open import Presentation.Definitions
open import Normalization.NormalForm.Propositional
open import Normalization.StarPresentation
open import Examples.Groups.Clifford.Qubit.Semantics

subpresentation : ∀ {n} -> 
  (n Clifford,_===_) IsSubPresentationOf Clifford-group n
subpresentation {n} =
  GS.GetSubPresentation.groupSubPres {!!} {!!} {!!} {!!}
  where
  module GS = GroupSem (n Clifford,_===_) {!!} {!!} {!!}


presentation : ∀ {n} -> let open PP (n Clifford,_===_) in
  (n Clifford,_===_) IsPresentationOf {!!}
presentation {n} = isPresentationOf subpresentation claim
  where
  open PB (n Clifford,_===_)
  open import Function.Definitions using (Surjective)

  claim : Surjective {!!} {!!} {!!}
  claim y = {!!}

