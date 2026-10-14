------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Clifford relations (C1–C15): the rules on their own wires, padded by
-- Circuit.TopPad, give the same congruence as Syntactics' rules at every
-- width, lifted by Circuit.Base's Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence, as Symmetric.TopPad is:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and SameRules says, rule by rule, that the two
-- relations have the same rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qubit-Clifford.TopPad where

open import Data.Nat using (ℕ)
open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import Examples.Groups.Qubit-Clifford.Syntactics

open Circuit.TopPad Gate using (_⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  C₁ᴮ : 0 Base, ω ^ 8 === ε
  C₂ᴮ : 1 Base, H • H === ε
  C₃ᴮ : 1 Base, S • S • S • S === ε
  C₄ᴮ : 1 Base, S • H • S • H • S • H === ω
  C₅ᴮ : 2 Base, CZ • CZ === ε
  C₆ᴮ : 2 Base, CZ • S ↑ === S ↑ • CZ
  C₇ᴮ : 2 Base, CZ • S === S • CZ
  C₈ᴮ : 2 Base, CZ • H ↑ • S ↑ • S ↑ • H ↑ === H ↑ • S ↑ • S ↑ • H ↑ • S • S • CZ
  C₉ᴮ : 2 Base, CZ • H • S • S • H === H • S • S • H • S ↑ • S ↑ • CZ
  C₁₀ᴮ : 2 Base, CZ • H ↑ • CZ === ω ^ 7 • S ↑ • H ↑ • S ↑ • S • CZ • H ↑ • S ↑
  C₁₁ᴮ : 2 Base, CZ • H • CZ === ω ^ 7 • S • H • S • S ↑ • CZ • H • S
  C₁₂ᴮ : 3 Base, CZ • CZ ↑ === CZ ↑ • CZ
  C₁₃ᴮ : 3 Base,
        CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • H • H ↑ • CZ • H • H ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ ===
        CZ • H ↑ • H • CZ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ ↑ • H ↑ • CZ • H ↑ • H • CZ
  C₁₄ᴮ : 3 Base,
        CZ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • CZ • H ↑ • H ↑ ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • CZ • H ↑ • H ↑ ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ ===
        ε
  C₁₅ᴮ : 3 Base,
        CZ ↑ • H • H ↑ • CZ • H ↑ • H • CZ • CZ ↑ • H ↑ • H • CZ • H ↑ • H • CZ • CZ ↑ • H ↑ • H • CZ • H ↑ • H • CZ ===
        ε

module TP = Circuit.TopPad.Top-Pad Gate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad Gate _SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: its words are
-- closed, so one wire wider they are the same words.

C₁↓ : n TRel, ω ^ 8 === ε
C₁↓ {0}    = TP.srel C₁ᴮ
C₁↓ {₁₊ n} = TP.cong↓ C₁↓

C₂↓ : (₁₊ n) TRel, H • H === ε
C₂↓ {0}    = TP.srel C₂ᴮ
C₂↓ {₁₊ n} = TP.cong↓ C₂↓

C₃↓ : (₁₊ n) TRel, S • S • S • S === ε
C₃↓ {0}    = TP.srel C₃ᴮ
C₃↓ {₁₊ n} = TP.cong↓ C₃↓

C₄↓ : (₁₊ n) TRel, S • H • S • H • S • H === ω
C₄↓ {0}    = TP.srel C₄ᴮ
C₄↓ {₁₊ n} = TP.cong↓ C₄↓

C₅↓ : (₂₊ n) TRel, CZ • CZ === ε
C₅↓ {0}    = TP.srel C₅ᴮ
C₅↓ {₁₊ n} = TP.cong↓ C₅↓

C₆↓ : (₂₊ n) TRel, CZ • S ↑ === S ↑ • CZ
C₆↓ {0}    = TP.srel C₆ᴮ
C₆↓ {₁₊ n} = TP.cong↓ C₆↓

C₇↓ : (₂₊ n) TRel, CZ • S === S • CZ
C₇↓ {0}    = TP.srel C₇ᴮ
C₇↓ {₁₊ n} = TP.cong↓ C₇↓

C₈↓ : (₂₊ n) TRel, CZ • H ↑ • S ↑ • S ↑ • H ↑ === H ↑ • S ↑ • S ↑ • H ↑ • S • S • CZ
C₈↓ {0}    = TP.srel C₈ᴮ
C₈↓ {₁₊ n} = TP.cong↓ C₈↓

C₉↓ : (₂₊ n) TRel, CZ • H • S • S • H === H • S • S • H • S ↑ • S ↑ • CZ
C₉↓ {0}    = TP.srel C₉ᴮ
C₉↓ {₁₊ n} = TP.cong↓ C₉↓

C₁₀↓ : (₂₊ n) TRel, CZ • H ↑ • CZ === ω ^ 7 • S ↑ • H ↑ • S ↑ • S • CZ • H ↑ • S ↑
C₁₀↓ {0}    = TP.srel C₁₀ᴮ
C₁₀↓ {₁₊ n} = TP.cong↓ C₁₀↓

C₁₁↓ : (₂₊ n) TRel, CZ • H • CZ === ω ^ 7 • S • H • S • S ↑ • CZ • H • S
C₁₁↓ {0}    = TP.srel C₁₁ᴮ
C₁₁↓ {₁₊ n} = TP.cong↓ C₁₁↓

C₁₂↓ : (₃₊ n) TRel, CZ • CZ ↑ === CZ ↑ • CZ
C₁₂↓ {0}    = TP.srel C₁₂ᴮ
C₁₂↓ {₁₊ n} = TP.cong↓ C₁₂↓

C₁₃↓ : (₃₊ n) TRel,
      CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • H • H ↑ • CZ • H • H ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ ===
      CZ • H ↑ • H • CZ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ ↑ • H ↑ • CZ • H ↑ • H • CZ
C₁₃↓ {0}    = TP.srel C₁₃ᴮ
C₁₃↓ {₁₊ n} = TP.cong↓ C₁₃↓

C₁₄↓ : (₃₊ n) TRel,
      CZ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • CZ • H ↑ • H ↑ ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • CZ • H ↑ • H ↑ ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ ===
      ε
C₁₄↓ {0}    = TP.srel C₁₄ᴮ
C₁₄↓ {₁₊ n} = TP.cong↓ C₁₄↓

C₁₅↓ : (₃₊ n) TRel,
      CZ ↑ • H • H ↑ • CZ • H ↑ • H • CZ • CZ ↑ • H ↑ • H • CZ • H ↑ • H • CZ • CZ ↑ • H ↑ • H • CZ • H ↑ • H • CZ ===
      ε
C₁₅↓ {0}    = TP.srel C₁₅ᴮ
C₁₅↓ {₁₊ n} = TP.cong↓ C₁₅↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n SRel, w === v → n ⊢ᵀ w ≈ v
  pad C₁ = PB.axiom C₁↓
  pad C₂ = PB.axiom C₂↓
  pad C₃ = PB.axiom C₃↓
  pad C₄ = PB.axiom C₄↓
  pad C₅ = PB.axiom C₅↓
  pad C₆ = PB.axiom C₆↓
  pad C₇ = PB.axiom C₇↓
  pad C₈ = PB.axiom C₈↓
  pad C₉ = PB.axiom C₉↓
  pad C₁₀ = PB.axiom C₁₀↓
  pad C₁₁ = PB.axiom C₁₁↓
  pad C₁₂ = PB.axiom C₁₂↓
  pad C₁₃ = PB.axiom C₁₃↓
  pad C₁₄ = PB.axiom C₁₄↓
  pad C₁₅ = PB.axiom C₁₅↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad C₁ᴮ = PB.axiom (srel C₁)
  unpad C₂ᴮ = PB.axiom (srel C₂)
  unpad C₃ᴮ = PB.axiom (srel C₃)
  unpad C₄ᴮ = PB.axiom (srel C₄)
  unpad C₅ᴮ = PB.axiom (srel C₅)
  unpad C₆ᴮ = PB.axiom (srel C₆)
  unpad C₇ᴮ = PB.axiom (srel C₇)
  unpad C₈ᴮ = PB.axiom (srel C₈)
  unpad C₉ᴮ = PB.axiom (srel C₉)
  unpad C₁₀ᴮ = PB.axiom (srel C₁₀)
  unpad C₁₁ᴮ = PB.axiom (srel C₁₁)
  unpad C₁₂ᴮ = PB.axiom (srel C₁₂)
  unpad C₁₃ᴮ = PB.axiom (srel C₁₃)
  unpad C₁₄ᴮ = PB.axiom (srel C₁₄)
  unpad C₁₅ᴮ = PB.axiom (srel C₁₅)

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ C₁ = PB.axiom (srel C₁)
  srel-⇓ C₂ = PB.axiom (srel C₂)
  srel-⇓ C₃ = PB.axiom (srel C₃)
  srel-⇓ C₄ = PB.axiom (srel C₄)
  srel-⇓ C₅ = PB.axiom (srel C₅)
  srel-⇓ C₆ = PB.axiom (srel C₆)
  srel-⇓ C₇ = PB.axiom (srel C₇)
  srel-⇓ C₈ = PB.axiom (srel C₈)
  srel-⇓ C₉ = PB.axiom (srel C₉)
  srel-⇓ C₁₀ = PB.axiom (srel C₁₀)
  srel-⇓ C₁₁ = PB.axiom (srel C₁₁)
  srel-⇓ C₁₂ = PB.axiom (srel C₁₂)
  srel-⇓ C₁₃ = PB.axiom (srel C₁₃)
  srel-⇓ C₁₄ = PB.axiom (srel C₁₄)
  srel-⇓ C₁₅ = PB.axiom (srel C₁₅)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
