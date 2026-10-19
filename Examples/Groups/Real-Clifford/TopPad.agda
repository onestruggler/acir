------------------------------------------------------------------------
-- Presentations of groups
--
-- Makary, Ross and Selinger's real Clifford relations (R1–R16): the
-- rules on their own wires, padded by Circuit.TopPad, give the same
-- congruence as Syntactics' rules at every width, lifted by
-- Circuit.Base's Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence, as Symmetric.TopPad is:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and SameRules says, rule by rule, that the two
-- relations have the same rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford.TopPad where

open import Data.Nat using (ℕ)
open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import Examples.Groups.Real-Clifford.Syntactics

open Circuit.TopPad Gate using (_⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  R₁ᴮ : 0 Base, neg • neg === ε
  R₂ᴮ : 1 Base, Z • Z === ε
  R₃ᴮ : 1 Base, H • H === ε
  R₄ᴮ : 1 Base, (H • Z) ^ 4 === neg
  R₅ᴮ : 2 Base, CZ • CZ === ε
  R₆ᴮ : 2 Base, CZ • Z ↑ === Z ↑ • CZ
  R₇ᴮ : 2 Base, CZ • Z === Z • CZ
  R₈ᴮ : 2 Base, CZ • H ↑ • Z ↑ • H ↑ === H ↑ • Z • Z ↑ • H ↑ • CZ
  R₉ᴮ : 2 Base, CZ • H • Z • H === H • Z • Z ↑ • H • CZ
  R₁₀ᴮ : 2 Base, CZ • H ↑ • CZ • H ↑ === Z • H ↑ • CZ • H ↑ • CZ
  R₁₁ᴮ : 2 Base, CZ • H • CZ • H === H • Z ↑ • CZ • H • CZ
  R₁₂ᴮ : 2 Base, CZ • HH • CZ • HH • CZ • H === H ↑ • CZ • HH • CZ • HH • CZ
  R₁₃ᴮ : 3 Base, CZ • CZ ↑ === CZ ↑ • CZ
  R₁₄ᴮ : 3 Base,
        H • CZ • HH • CZ • H ↑ • CZ ↑ • H ↑ • CZ • HH • CZ • H ===
        H ↑ ↑ • CZ ↑ • HH ↑ • CZ ↑ • H ↑ • CZ • H ↑ • CZ ↑ • HH ↑ • CZ ↑ •
        H ↑ ↑
  R₁₅ᴮ : 3 Base,
        CZ • HH ↑ • CZ ↑ • HH ↑ • CZ ↑ • CZ • HH ↑ • CZ ↑ • HH ↑ • CZ ↑ ===
        CZ ↑ • HH ↑ • CZ ↑ • HH ↑ • CZ
  R₁₆ᴮ : 3 Base, CZ ↑ • HH • CZ • HH • CZ • CZ ↑ • HH • CZ • HH • CZ ===
        CZ • HH • CZ • HH • CZ ↑

module TP = Circuit.TopPad.Top-Pad Gate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad Gate _SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: its words are
-- closed, so one wire wider they are the same words.

R₁↓ : n TRel, neg • neg === ε
R₁↓ {0}    = TP.srel R₁ᴮ
R₁↓ {₁₊ n} = TP.cong↓ R₁↓

R₂↓ : (₁₊ n) TRel, Z • Z === ε
R₂↓ {0}    = TP.srel R₂ᴮ
R₂↓ {₁₊ n} = TP.cong↓ R₂↓

R₃↓ : (₁₊ n) TRel, H • H === ε
R₃↓ {0}    = TP.srel R₃ᴮ
R₃↓ {₁₊ n} = TP.cong↓ R₃↓

R₄↓ : (₁₊ n) TRel, (H • Z) ^ 4 === neg
R₄↓ {0}    = TP.srel R₄ᴮ
R₄↓ {₁₊ n} = TP.cong↓ R₄↓

R₅↓ : (₂₊ n) TRel, CZ • CZ === ε
R₅↓ {0}    = TP.srel R₅ᴮ
R₅↓ {₁₊ n} = TP.cong↓ R₅↓

R₆↓ : (₂₊ n) TRel, CZ • Z ↑ === Z ↑ • CZ
R₆↓ {0}    = TP.srel R₆ᴮ
R₆↓ {₁₊ n} = TP.cong↓ R₆↓

R₇↓ : (₂₊ n) TRel, CZ • Z === Z • CZ
R₇↓ {0}    = TP.srel R₇ᴮ
R₇↓ {₁₊ n} = TP.cong↓ R₇↓

R₈↓ : (₂₊ n) TRel, CZ • H ↑ • Z ↑ • H ↑ === H ↑ • Z • Z ↑ • H ↑ • CZ
R₈↓ {0}    = TP.srel R₈ᴮ
R₈↓ {₁₊ n} = TP.cong↓ R₈↓

R₉↓ : (₂₊ n) TRel, CZ • H • Z • H === H • Z • Z ↑ • H • CZ
R₉↓ {0}    = TP.srel R₉ᴮ
R₉↓ {₁₊ n} = TP.cong↓ R₉↓

R₁₀↓ : (₂₊ n) TRel, CZ • H ↑ • CZ • H ↑ === Z • H ↑ • CZ • H ↑ • CZ
R₁₀↓ {0}    = TP.srel R₁₀ᴮ
R₁₀↓ {₁₊ n} = TP.cong↓ R₁₀↓

R₁₁↓ : (₂₊ n) TRel, CZ • H • CZ • H === H • Z ↑ • CZ • H • CZ
R₁₁↓ {0}    = TP.srel R₁₁ᴮ
R₁₁↓ {₁₊ n} = TP.cong↓ R₁₁↓

R₁₂↓ : (₂₊ n) TRel, CZ • HH • CZ • HH • CZ • H ===
      H ↑ • CZ • HH • CZ • HH • CZ
R₁₂↓ {0}    = TP.srel R₁₂ᴮ
R₁₂↓ {₁₊ n} = TP.cong↓ R₁₂↓

R₁₃↓ : (₃₊ n) TRel, CZ • CZ ↑ === CZ ↑ • CZ
R₁₃↓ {0}    = TP.srel R₁₃ᴮ
R₁₃↓ {₁₊ n} = TP.cong↓ R₁₃↓

R₁₄↓ : (₃₊ n) TRel,
      H • CZ • HH • CZ • H ↑ • CZ ↑ • H ↑ • CZ • HH • CZ • H ===
      H ↑ ↑ • CZ ↑ • HH ↑ • CZ ↑ • H ↑ • CZ • H ↑ • CZ ↑ • HH ↑ • CZ ↑ •
      H ↑ ↑
R₁₄↓ {0}    = TP.srel R₁₄ᴮ
R₁₄↓ {₁₊ n} = TP.cong↓ R₁₄↓

R₁₅↓ : (₃₊ n) TRel,
      CZ • HH ↑ • CZ ↑ • HH ↑ • CZ ↑ • CZ • HH ↑ • CZ ↑ • HH ↑ • CZ ↑ ===
      CZ ↑ • HH ↑ • CZ ↑ • HH ↑ • CZ
R₁₅↓ {0}    = TP.srel R₁₅ᴮ
R₁₅↓ {₁₊ n} = TP.cong↓ R₁₅↓

R₁₆↓ : (₃₊ n) TRel, CZ ↑ • HH • CZ • HH • CZ • CZ ↑ • HH • CZ • HH • CZ ===
      CZ • HH • CZ • HH • CZ ↑
R₁₆↓ {0}    = TP.srel R₁₆ᴮ
R₁₆↓ {₁₊ n} = TP.cong↓ R₁₆↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n SRel, w === v → n ⊢ᵀ w ≈ v
  pad R₁ = PB.axiom R₁↓
  pad R₂ = PB.axiom R₂↓
  pad R₃ = PB.axiom R₃↓
  pad R₄ = PB.axiom R₄↓
  pad R₅ = PB.axiom R₅↓
  pad R₆ = PB.axiom R₆↓
  pad R₇ = PB.axiom R₇↓
  pad R₈ = PB.axiom R₈↓
  pad R₉ = PB.axiom R₉↓
  pad R₁₀ = PB.axiom R₁₀↓
  pad R₁₁ = PB.axiom R₁₁↓
  pad R₁₂ = PB.axiom R₁₂↓
  pad R₁₃ = PB.axiom R₁₃↓
  pad R₁₄ = PB.axiom R₁₄↓
  pad R₁₅ = PB.axiom R₁₅↓
  pad R₁₆ = PB.axiom R₁₆↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad R₁ᴮ = PB.axiom (srel R₁)
  unpad R₂ᴮ = PB.axiom (srel R₂)
  unpad R₃ᴮ = PB.axiom (srel R₃)
  unpad R₄ᴮ = PB.axiom (srel R₄)
  unpad R₅ᴮ = PB.axiom (srel R₅)
  unpad R₆ᴮ = PB.axiom (srel R₆)
  unpad R₇ᴮ = PB.axiom (srel R₇)
  unpad R₈ᴮ = PB.axiom (srel R₈)
  unpad R₉ᴮ = PB.axiom (srel R₉)
  unpad R₁₀ᴮ = PB.axiom (srel R₁₀)
  unpad R₁₁ᴮ = PB.axiom (srel R₁₁)
  unpad R₁₂ᴮ = PB.axiom (srel R₁₂)
  unpad R₁₃ᴮ = PB.axiom (srel R₁₃)
  unpad R₁₄ᴮ = PB.axiom (srel R₁₄)
  unpad R₁₅ᴮ = PB.axiom (srel R₁₅)
  unpad R₁₆ᴮ = PB.axiom (srel R₁₆)

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ R₁ = PB.axiom (srel R₁)
  srel-⇓ R₂ = PB.axiom (srel R₂)
  srel-⇓ R₃ = PB.axiom (srel R₃)
  srel-⇓ R₄ = PB.axiom (srel R₄)
  srel-⇓ R₅ = PB.axiom (srel R₅)
  srel-⇓ R₆ = PB.axiom (srel R₆)
  srel-⇓ R₇ = PB.axiom (srel R₇)
  srel-⇓ R₈ = PB.axiom (srel R₈)
  srel-⇓ R₉ = PB.axiom (srel R₉)
  srel-⇓ R₁₀ = PB.axiom (srel R₁₀)
  srel-⇓ R₁₁ = PB.axiom (srel R₁₁)
  srel-⇓ R₁₂ = PB.axiom (srel R₁₂)
  srel-⇓ R₁₃ = PB.axiom (srel R₁₃)
  srel-⇓ R₁₄ = PB.axiom (srel R₁₄)
  srel-⇓ R₁₅ = PB.axiom (srel R₁₅)
  srel-⇓ R₁₆ = PB.axiom (srel R₁₆)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
