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
-- the odd-prime development under Examples.Groups.Clifford.Qupit.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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

open import Presentation.Construct.Base using (_⊕^_ ; _⊎^_ ; _⋄_⋄_ ; ConjRelʷ)
open import Presentation.Construct.Properties.Extension using (extension-presentation)

-- S : the Pauli presentation, over the generators (⊤ ⊎ ⊤) ⊎^ n
-- (an X- and a Z-generator per qubit).
open import Examples.Groups.Pauli.Presentation p-2 p-prime using (Γ-H)

-- The Pauli group as vectors, and the symplectic action actg.
open import Examples.Groups.Pauli.Semantics p-2 p-prime
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

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (g* ; g-gen)
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


open import Algebra.Bundles using (Group)
open import Function.Definitions using (Surjective)
open import Presentation.Definitions
open import Normalization.StarPresentation


------------------------------------------------------------------------
-- The split case: a presentation of Pauli n ⋊ Sp(2n, 2)
--
-- Dropping the cocycle (corr ≡ ε) turns the extension relation into
-- Γ ⋄ Δ ⋄ ConjRelʷ conj, which is exactly the relation
-- Presentation.Construct.Properties.SemiDirectProduct2 presents.  Both
-- factor presentations are already available:
--
--   * Pauli.Pauli-presentation n : (Γ-H ⊕^ n) IsPresentationOf Pauli-group n
--   * Simplified.Presentation.presentation : QRel IsPresentationOf Sp-group n
--
-- so the semidirect product needs only the two action-congruence
-- hypotheses below.  Note the resulting group is SDP.group with the
-- action TRANSPORTED from conj through the two presentation
-- isomorphisms; it is the Pauli ⋊ Sp group, but not the same Agda value
-- as Examples.Construct.SemiDirectProduct.Clifford.Pauli⋊Sp-group, whose
-- action is ap and whose Pauli factor is the Vec-based +ₚ-group.

import Presentation.Base as PB
open import Word.Base using (_ⁿ' ; _ʰ')
open import Presentation.Construct.Properties.SemiDirectProduct2 as SD2

open import Examples.Groups.Pauli.Presentation p-2 p-prime
  using (Pauli-group ; Pauli-presentation)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen
  as SimP using ()

-- conj respects the symplectic axioms in its acting argument: related
-- symplectic words conjugate every Pauli word alike.
ConjHypH : (n : ℕ) → Set
ConjHypH n = ∀ {c d : Word (Gen n)} (w : Word (PauliGen n)) →
             (n QRel,_===_) c d →
             PB._≈_ (Γ-H ⊕^ n) ((conj ʰ') c w) ((conj ʰ') d w)

-- conj respects the Pauli axioms in its acted argument: conjugating both
-- sides of a Pauli relation by one gate keeps them related.
ConjHypN : (n : ℕ) → Set
ConjHypN n = ∀ (c : Gen n) {u v : Word (PauliGen n)} →
             (Γ-H ⊕^ n) u v →
             PB._≈_ (Γ-H ⊕^ n) ((conj ⁿ') c u) ((conj ⁿ') c v)

module SemiDirect (n : ℕ) (hyph : ConjHypH n) (hypn : ConjHypN n) where

  private
    module SD = SD2 (Γ-H ⊕^ n) (n QRel,_===_) (conj {n})
    module P  = SD.Presentation hyph hypn
                  (Pauli-group n) (Sp-group n)
                  (Pauli-presentation n) (SimP.presentation {n})

  -- Pauli n ⋊ Sp(2n, 2), with the action transported from conj.
  Pauli⋊Sp : Group _ _
  Pauli⋊Sp = P.G1⋊G2

  -- The headline: the semidirect relation presents it.
  presentation :
    ((Γ-H ⊕^ n) ⋄ (n QRel,_===_) ⋄ ConjRelʷ (conj {n}))
      IsPresentationOf Pauli⋊Sp
  presentation = P.dpres
