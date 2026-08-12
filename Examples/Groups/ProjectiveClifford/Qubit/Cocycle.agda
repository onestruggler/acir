------------------------------------------------------------------------
-- Presentations of groups
--
-- The syntactic data of the n-qubit Clifford extension (p = 2): the
-- conjugation action conj, the cocycle corr, and the extension relation
-- _Clifford,_===_ they generate (Selinger, arXiv:1310.6813).
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
--   * S    = the Pauli presentation      (Examples.Groups.ProjectivePauli.Presentation),
--   * R̄    = the symplectic relations, taken from the SIMPLIFIED rule set
--            (Symplectic.Simplified.Syntactics.Simplified-Relations),
--   * conj = the symplectic action of a quotient generator on a Pauli
--            generator (the word-valued form of
--            Symplectic.Semantics.Interpretation.actg),
--   * corr = the cocycle: the Pauli correction word carried by each
--            symplectic relator when it is lifted to Clifford.
--
-- The p = 2 cocycle.  Working in the *phaseless* Pauli group (Pauli1 =
-- ℤ/2 × ℤ/2, no phase), the only symplectic relator that fails to lift
-- exactly is order-S: over the qubit phase gate S = diag(1, i) one has
-- S² = Z, so corr(order-S) = Z on the acted qubit.  Every other relator
-- lifts either exactly or up to a global phase, and a global phase is
-- trivial in the phaseless Pauli group.  cong↑ shifts a correction up one
-- qubit.  This was verified numerically against the exact 2×2/4×4/8×8
-- Clifford matrices under the actg conventions.
--
-- On the simplified rule set the global-phase relators are worth naming,
-- because at p = 2 the M-generators degenerate: ℤ*₂ = {1}, so
--
--     Mg = M₋₁ = M 1 = S·H·S·H·S·H = (SH)³ = ω,
--
-- the order-8 scalar.  Hence order-H reads H² = ω, and M-power, semi-MS
-- and semi-M↑CZ / semi-M↓CZ all say that ω is central — each a global
-- phase, so each has corr = ε.  The two-qubit selinger relators lift up
-- to e^{-iπ/4}, likewise ε.
--
-- (For odd p the extension splits — every correction is ε; that case is
-- the odd-prime development under Examples.Groups.ProjectiveClifford.Qupit.)
--
-- This module carries only the data.  That the relation it builds really
-- presents the Clifford group is Qubit.Presentation, which sits on top of
-- the whole assembly (Qubit.ExtensionSoundness, Qubit.Realises and
-- Qubit.ExtensionPresentation all read their conj / corr from here).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Cocycle where

open import Data.Nat using (ℕ ; zero)

-- This module is the qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime ; g* ; g-gen)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Fin using (toℕ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^'_ ; wmap)
open import Notations using (₁₊ ; ₂₊)

open import Presentation.Construct.Base using (_⊕^_ ; _⊎^_ ; _⋄_⋄_ ; ConjRelʷ)
open import Presentation.Construct.Properties.Extension using (extension-presentation)

-- S : the Pauli presentation, over the generators (⊤ ⊎ ⊤) ⊎^ n
-- (an X- and a Z-generator per qubit).
open import Examples.Groups.ProjectivePauli.Presentation p-2 p-prime using (Γ-H)

-- The Pauli group as vectors, and the symplectic action actg.
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pX ; pZ ; pI ; pIₙ)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)

-- R̄ : the symplectic relations, over the Clifford generators Gen n.
--
-- The rule set is the SIMPLIFIED one (Symplectic.Simplified).  Its
-- syntax — Gen, the gates, and the derived words — is shared with
-- Symplectic.Syntactics, which Simplified.Syntactics itself re-exports;
-- only the relation differs.
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime using (module Symplectic)
open Symplectic using (Gen)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (_QRel,_===_ ; srel ; cong↑ ; order-S)

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
--              quotient generator g.  Determined by
--              Symplectic.Semantics.Interpretation.actg.

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
conj g y = vecToWord (actg g (genToVec y))

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
corr (srel order-S) = Z₀
corr (cong↑ r)      = shiftPauli (corr r)
corr _              = ε

------------------------------------------------------------------------
-- The Clifford presentation, as an extension of Pauli by the symplectic
-- group.

infix 4 _Clifford,_===_

_Clifford,_===_ : (n : ℕ) → WRel (PauliGen n ⊎ Gen n)
_Clifford,_===_ n = extension-presentation (Γ-H ⊕^ n) (n QRel,_===_) conj corr
