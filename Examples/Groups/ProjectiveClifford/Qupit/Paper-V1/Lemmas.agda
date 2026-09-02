{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Ex-conjugation algebra of the Paper-V1 rules.
--
-- Paper-V1 axiomatises the swap directly: order-Ex says Ex is an
-- involution, and semi-Ex-S↑ / semi-Ex-H↑ say conjugating by it carries
-- a gate on the upper wire down to the lower one,
--
--     Ex • S ↑ === S • Ex        Ex • H ↑ === H • Ex.
--
-- Everything below is the bookkeeping that turns those three axioms into
-- a usable calculus: the opposite direction (a lower-wire gate goes up),
-- the two-sided conjugation forms, and the extension of all of it from
-- single gates to powers and to whole words.  These are the steps that
-- the corresponding symplectic lemmas get for free from Ex's definition
-- as a CZ/H word — a route that is NOT available here, since the
-- symplectic proofs of lemma-comm-Ex-H' and lemma-comm-Ex-H↑' run
-- through lemma-eqn16 / lemma-eqn17 / lemma-CZH↓CZCZ, i.e. through the
-- CZ-H-CZ relations c10 and c11 that Paper-V1 does not have.
--
-- This file is now a façade.  The development was one 5000-line module;
-- it is split across Lemmas/, in dependency order:
--
--   OneWire     multiplier arithmetic on one wire
--   GroupLike   group-likeness, and powers modulo p
--   XZ          Pauli conjugation past H and past S, and the ℤₚ
--               half-exponent arithmetic (where X • Z ≈ Z • X lives)
--   ExConjA/B/C the Ex-conjugation calculus, in three parts
--   ExConj      the three parts reassembled as Ex-Conjugation
--   DownRules   the two lower-wire rules
--   ThreeWireA  the remote CZ at three wires
--   ThreeWireB  …and Selinger's c12-c15
--
-- Ex-Conjugation and Three-Wire are each split mid-module, so the later
-- part opens the earlier one publicly.  A handful of helpers that were
-- `private` in the monolith are exported for that reason; they are
-- marked where they occur.
--
-- Clients should keep importing this module: the names below are the
-- ones Iso.agda and Presentation.agda use, and they are unchanged.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ< ; toℕ-injective)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  p-3 p-prime g* g-gen public
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  p-3 p-prime g* g-gen public
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  p-3 p-prime g* g-gen public
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ExConj
  p-3 p-prime g* g-gen public
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.DownRules
  p-3 p-prime g* g-gen public

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ThreeWireB
  p-3 p-prime g* g-gen as TB

-- Three-Wire, reassembled: ThreeWireB already re-exports ThreeWireA.
module Three-Wire (n : ℕ) where

  open TB.Three-Wire-B n public
