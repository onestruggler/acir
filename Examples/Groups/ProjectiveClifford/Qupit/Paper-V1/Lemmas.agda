{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- What the Paper-V1 rules give, on one wire.
--
-- Paper-V1's job is to be Paper-V0 with the multiplier respelled, and
-- Iso proves exactly that.  So this library only has to reach the four
-- facts Iso needs — order-SH as a theorem, and the bridge between the R-
-- and S-spellings of the multiplier at -1, at g and at g ^ k — and every
-- rule Paper-V0 derives is then a Paper-V1 theorem by transport.
--
-- That is why there is no Ex-conjugation or three-wire layer here.  An
-- earlier version carried one, ported wholesale from Paper-V0: 4255 lines
-- deriving the swap calculus, the lower-wire rules and Selinger's
-- c10–c15 natively.  None of it was reachable from Presentation, because
-- the isomorphism already transports all of it, so it is gone.  Look in
-- Paper-V0.Lemmas for those derivations; they are live there, since
-- Paper-V0.Iso proves Simplified-V1 ⟺ Paper-V0 the long way round and
-- genuinely consumes them.
--
-- The lemmas themselves live in Lemmas/, stated over any relation with
-- the rules they use, and in dependency order:
--
--   OneWire     multiplier arithmetic on one wire, and lemma-order-SH
--   GroupLike   group-likeness, powers modulo p, and induction on powers
--   XZ          Pauli conjugation past H and past S, the ℤₚ
--               half-exponent arithmetic (where X • Z ≈ Z • X lives),
--               and the bridge between the two spellings
--   SemiMR      semi-MR, derived from the other four one-wire rules
--
-- This module instantiates the first three at Paper-V1's relation, under
-- the names Iso.agda uses.  It does not instantiate SemiMR: Paper-V1 has
-- semi-MR as an axiom, and One-Wire-Group's lemma-semi-MR-R below reads
-- it off that.  SemiMR is for the rule set that does without it,
-- Reduced.
------------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
import Presentation.Base as PB
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (_•_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen
open Clifford-Relations

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  p-3 p-prime g* g-gen as OW
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  p-3 p-prime g* g-gen as GL
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  p-3 p-prime g* g-gen as XZ

open GL public using (lemma-pow-mod ; lemma-Induction ; lemma-Inductionˡ)

------------------------------------------------------------------------
-- The one-wire layer at Paper-V1's relation
--
-- Each rule is passed as the axiom it is.  Only four of the five one-wire
-- axioms are passed: semi-MR is not a parameter of any of these modules.

module One-Wire (n : ℕ) =
  OW.One-Wire n ((₁₊ n) QRel,_===_)
    (PB.axiom order-S) (PB.axiom order-H) (λ k → PB.axiom (M-power k))
    (PB.axiom comm-HHSHHS)

module Paper-GroupLike =
  GL.Paper-GroupLike _QRel,_===_
    (PB.axiom order-S) (PB.axiom order-H) (λ k → PB.axiom (M-power k))
    (PB.axiom comm-HHSHHS) (PB.axiom order-CZ) lemma-cong↑

module One-Wire-Group (n : ℕ) where

  open XZ.One-Wire-Group n ((₁₊ n) QRel,_===_)
    (PB.axiom order-S) (PB.axiom order-H) (λ k → PB.axiom (M-power k))
    (PB.axiom comm-HHSHHS) (Paper-GroupLike.grouplike {₁₊ n}) public

  open PB ((₁₊ n) QRel,_===_) using (_≈_ ; axiom)

  -- semi-MR, back in the R-spelling.
  --
  -- Paper-V1 states semi-MR over S, with the Pauli that the change of
  -- spelling leaves behind written out on the left.  Paper-V0 states it
  -- over R.  The two are the same rule: R^(g·g) splits as S^(g·g) • Z^(½g²),
  -- and the Z^½ that R contributes on the right crosses the multiplier by
  -- Z-XM, picking up the factor g.  What is left over on each side is
  -- Z^(½g), and cancelling it is the difference between the two
  -- statements.
  --
  -- This is the one place the lemma layer uses Paper-V1's fifth one-wire
  -- axiom.  Lemmas.SemiMR proves the same statement without it.
  lemma-semi-MR-R : XMg {n} • R^ (g * g) ≈ R • XMg
  lemma-semi-MR-R = SB.SemiMR.S⇒R g′ (axiom semi-MR)
