------------------------------------------------------------------------
-- Presentations of groups
--
-- The projective Pauli relations of Presentation-Alt: the rules on
-- their own wires, padded by Circuit.TopPad, give the same congruence
-- as Syntactics' rules at every width, lifted by Circuit.Base's
-- Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence, as Symmetric.TopPad is:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and SameRules says, rule by rule, that the two
-- relations have the same rules. Powers whose exponent is not a numeral
-- (S ^ p, S^ k) do not compute under ⇓, so the padded rules and the
-- rules ⇓'d go through Circuit.TopPad.Closed's ⇓-same.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.ProjectivePauli.TopPad-Alt (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime
open XZ-GroupLike using (grouplike)

open import Circuit.Base XZGate using (Circuit)
open Circuit.TopPad XZGate using (_⇓)
open import Circuit.TopPad.Closed XZGate using (⇓-same)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order-Xᴮ : 1 Base, X ^ p === ε
  order-Zᴮ : 1 Base, Z ^ p === ε
  comm-Z-Xᴮ : 1 Base, Z • X === X • Z

module TP = Circuit.TopPad.Top-Pad XZGate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad XZGate Base._SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: one wire wider
-- its words are the same words, up to the powers ⇓ does not compute
-- through (⇓-same).

order-X↓ : (₁₊ n) TRel, X ^ p === ε
order-X↓ {0}    = TP.srel order-Xᴮ
order-X↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-X↓

order-Z↓ : (₁₊ n) TRel, Z ^ p === ε
order-Z↓ {0}    = TP.srel order-Zᴮ
order-Z↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-Z↓

comm-Z-X↓ : (₁₊ n) TRel, Z • X === X • Z
comm-Z-X↓ {0}    = TP.srel comm-Z-Xᴮ
comm-Z-X↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-Z-X↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : Base._SRel,_===_ n w v → n ⊢ᵀ w ≈ v
  pad Base.order-X = PB.axiom order-X↓
  pad Base.order-Z = PB.axiom order-Z↓
  pad Base.comm-Z-X = PB.axiom comm-Z-X↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad order-Xᴮ = PB.axiom (srel Base.order-X)
  unpad order-Zᴮ = PB.axiom (srel Base.order-Z)
  unpad comm-Z-Xᴮ = PB.axiom (srel Base.comm-Z-X)

  srel-⇓ : Base._SRel,_===_ n w v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ Base.order-X = E.axiom≡ ⇓-same ⇓-same (srel Base.order-X)
  srel-⇓ Base.order-Z = E.axiom≡ ⇓-same ⇓-same (srel Base.order-Z)
  srel-⇓ Base.comm-Z-X = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-Z-X)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
