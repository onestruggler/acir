------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qupit Clifford group *with* its scalar, presented as a group
-- extension, for an odd prime p = 3 + p-3.
--
--     1 ─→ ⟨ω⟩ ≅ ℤ/pℤ ─→ Exact n ─→ Clifford n / ⟨ω⟩ ─→ 1
--
-- This is the qupit copy of Clifford.Qubit.Presentation: the scalar
-- layer one storey above the projective rule set of
-- ProjectiveClifford.Qupit.Paper-V0.Syntactics, whose quotient it takes
-- for granted.  What is built here is
--
--     extension-presentation Scalar-relation R̄ conj corr
--
-- (Presentation.Construct.Properties.Extension, Proposition 2.55), where
--
--   * Scalar-relation = ⟨ ω ∣ ωᵖ = 1 ⟩, the cyclic presentation of order
--     p (Cyclic.Syntactics, whose single generator is renamed ω on
--     import — in this presentation the scalar IS a generator),
--   * R̄    = the Paper-V0 rule set, which is stated modulo scalars,
--   * conj = the action of a gate on the scalar: trivial, ω being
--            central,
--   * corr = the cocycle: the power of ω that a mod-scalar relator picks
--            up when it is lifted back to the unitary group.
--
-- The cocycle.  Reading the generators as the matrices of the paper —
-- ω = e^(2πi/p), and, with δ_p = 1, -i, -1, i for p ≡ 1, 3, 5, 7 mod 8
-- (convention B, eq. 3.5-3.6),
--
--     H  = δ_p · p^(-1/2) · Σ_{j,k} ω^(jk) |j⟩⟨k|
--     S  = |j⟩ ↦ ω^(j(j-1)/2) |j⟩        (/2 = the inverse of 2 in ℤ/p)
--     CZ = |j⟩|l⟩ ↦ ω^(jl) |j⟩|l⟩
--
-- — exactly ONE of the sixteen group-specific rules of Paper-V0 fails to
-- hold on the nose, namely
--
--     order-SH   (S • H)³ = ε   picks up   ω^((p²-1)/8)
--
-- and the other fifteen, together with the structural rules cong↑,
-- comm₁ and comm₂, lift with no correction at all:
--
--     order-S, order-H, M-power k (every k), semi-MR, comm-HHSHHS,
--     order-CZ, order-Ex, comm-CZ-S↑, semi-M↑CZ, semi-Ex-S↑,
--     semi-Ex-H↑, blake-c12, yang-baxter, cz-slide, semi-CX↑-CZ↓
--
-- This is what makes the qupit cocycle simpler than Selinger's qubit one
-- (three exceptional relators there): δ_p is chosen precisely so that
-- H⁴ = 1 and H² = M(-1) hold exactly, and the multiplier calculus that
-- carries M-power, semi-MR and semi-M↑CZ is phase-free.  The three
-- corrections that could depend on the chosen primitive root g —
-- M-power, semi-MR, semi-M↑CZ — are trivial for *every* primitive root,
-- so `corr` does not mention g.
--
-- The exponent.  (p² - 1)/8 is an integer because p is odd, and modulo p
-- it is -1/8; it is never ≡ 0, so the correction is a primitive p-th
-- root of unity at every odd prime.  For p = 3, 5, 7, 11, 13, 17, 19,
-- 23, 29, 31, 37, 41, 43, 47 it reduces to
--
--     1, 3, 6, 4, 8, 2, 7, 20, 18, 27, 23, 5, 16, 41.
--
-- cong↑ recurses with the SAME word.  As in the qubit case this is where
-- the scalar cocycle is easier than a Pauli one, which has to shift its
-- correction up a wire: the scalar alphabet does not depend on the
-- width, one generator ω naming the scalar on every wire.
--
-- Width.  The relation is stated at every width n, which is possible
-- precisely because the scalar has become a generator: nothing here
-- mentions the word (S • H)³, so nothing needs a wire to write it on.
--
-- The corrections are not all trivial, so this instance is not the split
-- one that Presentation.Construct.Properties.SemiDirectProduct covers;
-- the twisted relator for order-SH is what the extension recipe adds.
--
-- This module is the syntax only.  That these correction words are the
-- right ones — soundness of conj and corr in the central extension of
-- Clifford.Qupit.Semantics — and Proposition 2.55 instantiated at it,
-- belong to the presentation layer above.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.Syntactics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

import Data.Nat as Nat
import Data.Nat.DivMod as DM
open import Data.Sum using (_⊎_)

open import Word.Base using (Word ; WRel ; ε ; _^_)

open import Presentation.Construct.Properties.Extension
  using (extension-presentation ; tw)

-- The cyclic generator is the scalar, so it is imported under the name
-- the matrix model gives it.  Re-exported: the scalar alphabet and its
-- generator are part of this module's interface, since _Exact,_===_ is a
-- relation over them.
open import Examples.Groups.Cyclic.Syntactics
  using (_Cn,_===_) renaming (X to ScalarGen ; T to ω) public

-- The quotient: the Paper-V0 rule set, which is stated modulo scalars.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as PV
open PV using (Gen ; Circuit) public

module CR = PV.Clifford-Relations
module CB = CR.Base

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- S : the scalars ⟨ω⟩ ≅ ℤ/pℤ
--
-- One generator (Cyclic.Syntactics.X is a singleton), one relation
-- ωᵖ = 1.  Cyclic.Presentation shows this is a presentation of ℤ/pℤ, so
-- the normal factor needs no work of its own here.

Scalar-relation : WRel ScalarGen
Scalar-relation = p Cn,_===_

------------------------------------------------------------------------
-- conj : the scalar is central
--
-- A gate conjugates the scalar to itself.  That single clause is all the
-- action there is, and it is what makes ⟨ω⟩ normal in the Clifford
-- group.

conj : Gen n → ScalarGen → Word ScalarGen
conj _ _ = ω

------------------------------------------------------------------------
-- corr : the scalar cocycle
--
-- corr r is the word w_r of Proposition 2.55: lifting the mod-scalar
-- relator r back to the unitary group leaves the discrepancy
--
--     [ lhs ]ᵣ  ≈  [ corr r ]ₗ • [ rhs ]ᵣ.
--
-- Only order-SH has one.  Its exponent is (p² - 1)/8, which is exact
-- division: p is odd, so 8 divides p² - 1.

sh-exponent : ℕ
sh-exponent = (p Nat.* p Nat.∸ 1) DM./ 8

-- The one correction word of the whole rule set, named so that clients
-- can state facts about it without respelling the power.
ω^SH : Word ScalarGen
ω^SH = ω ^ sh-exponent

srel-corr : ∀ {u v} → (n CB.SRel, u === v) → Word ScalarGen
srel-corr CB.order-SH = ω^SH
srel-corr _           = ε

corr : ∀ {u v} → (n CR.QRel, u === v) → Word ScalarGen
corr (CR.srel r)    = srel-corr r
corr (CR.cong↑ r)   = corr r
corr (CR.comm₁ h x) = ε
corr (CR.comm₂ h x) = ε

------------------------------------------------------------------------
-- The exact qupit Clifford presentation
--
-- The alphabet is ScalarGen ⊎ Gen n: the scalar ω, and the gates.
-- Unfolding extension-presentation, the relations are
--
--   S    ωᵖ = 1                                     (on the scalar)
--   T    g⁻¹ ω g = ω     for every gate g           (conj, centrality)
--   R    the Paper-V0 relations, each corrected by its power of ω
--                                                   (corr, twisted)
--
-- and nothing else: the gate side contributes EmptyRel, every mod-scalar
-- relation having been twisted into the mixed part.

infix 4 _Exact,_===_

_Exact,_===_ : (n : ℕ) → WRel (ScalarGen ⊎ Gen n)
_Exact,_===_ n =
  extension-presentation Scalar-relation (n CR.QRel,_===_) conj corr
