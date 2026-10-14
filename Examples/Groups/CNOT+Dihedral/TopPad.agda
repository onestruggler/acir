------------------------------------------------------------------------
-- Presentations of groups
--
-- Amy, Chen and Ross's CNOT-dihedral relations (R₁–R₁₃): the rules on
-- their own wires, padded by Circuit.TopPad, give the same congruence
-- as Syntactics' rules at every width, lifted by Circuit.Prop's
-- Lift-To-Prop
--
-- An instance of Circuit.Prop.TopPad, which has the swap rules already:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and FamilyRules says, rule by rule, that the
-- two relations have the same rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.TopPad where

open import Data.Nat using (ℕ)
open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.Prop.TopPad
import Presentation.Base as PB

open import Examples.Groups.CNOT+Dihedral.Syntactics

open Circuit.TopPad Gate using (_⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  R₁ᴮ : 1 Base, X • X === ε
  R₂ᴮ : 2 Base, CNOT • X • CNOT === X
  R₃ᴮ : 2 Base, CNOT • X ↑ • CNOT === X ↑ • X
  R₄ᴮ : 2 Base, CNOT • CNOT === ε
  R₅ᴮ : 2 Base, SWAP === CNOT • SWAP • CNOT • SWAP • CNOT
  R₆ᴮ : 3 Base, CNOT₂₀ === CNOT • CNOT ↑ • CNOT • CNOT ↑
  R₇ᴮ : 1 Base, T ^ 8 === ε
  R₈ᴮ : 2 Base, U ^ 4 === T ^ 4 • (T ↑) ^ 4
  R₉ᴮ : 3 Base, V ^ 2 ===
        T ^ 6 • (T ↑) ^ 6 • (T ↑ ↑) ^ 6 • (U ↑) ^ 2 • U₀₂ ^ 2 • U ^ 2
  R₁₀ᴮ : 0 Base, ω ^ 8 === ε
  R₁₁ᴮ : 1 Base, X • T • X === ω • T ^ 7
  R₁₂ᴮ : 2 Base, CNOT • T ↑ • CNOT === T ↑
  R₁₃ᴮ : 4 Base,
        CNOT ↑ ↑ • V • CNOT ↑ ↑ ===
        T ^ 5 • (T ↑) ^ 5 • (T ↑ ↑) ^ 5 • (T ↑ ↑ ↑) ^ 5 • (U ↑ ↑) ^ 3 •
        U₁₃ ^ 3 • U₀₃ ^ 3 • (U ↑) ^ 3 • U₀₂ ^ 3 • U ^ 3 • V ↑ • V₀₂₃ •
        V₀₁₃ • V

module P  = Circuit.Prop.TopPad Gate SWAP-gate
module E  = P.Lift≅Top-Pad-Prop _SRel,_===_ _Base,_===_
module TP = E.TP

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: its words are
-- closed, so one wire wider they are the same words.

R₁↓ : (₁₊ n) TRel, X • X === ε
R₁↓ {0}    = TP.srel (E.sbase R₁ᴮ)
R₁↓ {₁₊ n} = TP.cong↓ R₁↓

R₂↓ : (₂₊ n) TRel, CNOT • X • CNOT === X
R₂↓ {0}    = TP.srel (E.sbase R₂ᴮ)
R₂↓ {₁₊ n} = TP.cong↓ R₂↓

R₃↓ : (₂₊ n) TRel, CNOT • X ↑ • CNOT === X ↑ • X
R₃↓ {0}    = TP.srel (E.sbase R₃ᴮ)
R₃↓ {₁₊ n} = TP.cong↓ R₃↓

R₄↓ : (₂₊ n) TRel, CNOT • CNOT === ε
R₄↓ {0}    = TP.srel (E.sbase R₄ᴮ)
R₄↓ {₁₊ n} = TP.cong↓ R₄↓

R₅↓ : (₂₊ n) TRel, SWAP === CNOT • SWAP • CNOT • SWAP • CNOT
R₅↓ {0}    = TP.srel (E.sbase R₅ᴮ)
R₅↓ {₁₊ n} = TP.cong↓ R₅↓

R₆↓ : (₃₊ n) TRel, CNOT₂₀ === CNOT • CNOT ↑ • CNOT • CNOT ↑
R₆↓ {0}    = TP.srel (E.sbase R₆ᴮ)
R₆↓ {₁₊ n} = TP.cong↓ R₆↓

R₇↓ : (₁₊ n) TRel, T ^ 8 === ε
R₇↓ {0}    = TP.srel (E.sbase R₇ᴮ)
R₇↓ {₁₊ n} = TP.cong↓ R₇↓

R₈↓ : (₂₊ n) TRel, U ^ 4 === T ^ 4 • (T ↑) ^ 4
R₈↓ {0}    = TP.srel (E.sbase R₈ᴮ)
R₈↓ {₁₊ n} = TP.cong↓ R₈↓

R₉↓ : (₃₊ n) TRel, V ^ 2 ===
      T ^ 6 • (T ↑) ^ 6 • (T ↑ ↑) ^ 6 • (U ↑) ^ 2 • U₀₂ ^ 2 • U ^ 2
R₉↓ {0}    = TP.srel (E.sbase R₉ᴮ)
R₉↓ {₁₊ n} = TP.cong↓ R₉↓

R₁₀↓ : n TRel, ω ^ 8 === ε
R₁₀↓ {0}    = TP.srel (E.sbase R₁₀ᴮ)
R₁₀↓ {₁₊ n} = TP.cong↓ R₁₀↓

R₁₁↓ : (₁₊ n) TRel, X • T • X === ω • T ^ 7
R₁₁↓ {0}    = TP.srel (E.sbase R₁₁ᴮ)
R₁₁↓ {₁₊ n} = TP.cong↓ R₁₁↓

R₁₂↓ : (₂₊ n) TRel, CNOT • T ↑ • CNOT === T ↑
R₁₂↓ {0}    = TP.srel (E.sbase R₁₂ᴮ)
R₁₂↓ {₁₊ n} = TP.cong↓ R₁₂↓

R₁₃↓ : (₄₊ n) TRel,
      CNOT ↑ ↑ • V • CNOT ↑ ↑ ===
      T ^ 5 • (T ↑) ^ 5 • (T ↑ ↑) ^ 5 • (T ↑ ↑ ↑) ^ 5 • (U ↑ ↑) ^ 3 •
      U₁₃ ^ 3 • U₀₃ ^ 3 • (U ↑) ^ 3 • U₀₂ ^ 3 • U ^ 3 • V ↑ • V₀₂₃ • V₀₁₃ •
      V
R₁₃↓ {0}    = TP.srel (E.sbase R₁₃ᴮ)
R₁₃↓ {₁₊ n} = TP.cong↓ R₁₃↓

------------------------------------------------------------------------
-- The two have the same rules

fam : E.FamilyRules
fam = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
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

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad R₁ᴮ = PB.axiom (srel (srel R₁))
  unpad R₂ᴮ = PB.axiom (srel (srel R₂))
  unpad R₃ᴮ = PB.axiom (srel (srel R₃))
  unpad R₄ᴮ = PB.axiom (srel (srel R₄))
  unpad R₅ᴮ = PB.axiom (srel (srel R₅))
  unpad R₆ᴮ = PB.axiom (srel (srel R₆))
  unpad R₇ᴮ = PB.axiom (srel (srel R₇))
  unpad R₈ᴮ = PB.axiom (srel (srel R₈))
  unpad R₉ᴮ = PB.axiom (srel (srel R₉))
  unpad R₁₀ᴮ = PB.axiom (srel (srel R₁₀))
  unpad R₁₁ᴮ = PB.axiom (srel (srel R₁₁))
  unpad R₁₂ᴮ = PB.axiom (srel (srel R₁₂))
  unpad R₁₃ᴮ = PB.axiom (srel (srel R₁₃))

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ R₁ = PB.axiom (srel (srel R₁))
  srel-⇓ R₂ = PB.axiom (srel (srel R₂))
  srel-⇓ R₃ = PB.axiom (srel (srel R₃))
  srel-⇓ R₄ = PB.axiom (srel (srel R₄))
  srel-⇓ R₅ = PB.axiom (srel (srel R₅))
  srel-⇓ R₆ = PB.axiom (srel (srel R₆))
  srel-⇓ R₇ = PB.axiom (srel (srel R₇))
  srel-⇓ R₈ = PB.axiom (srel (srel R₈))
  srel-⇓ R₉ = PB.axiom (srel (srel R₉))
  srel-⇓ R₁₀ = PB.axiom (srel (srel R₁₀))
  srel-⇓ R₁₁ = PB.axiom (srel (srel R₁₁))
  srel-⇓ R₁₂ = PB.axiom (srel (srel R₁₂))
  srel-⇓ R₁₃ = PB.axiom (srel (srel R₁₃))

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

same : E.E.SameRules
same = E.same fam

open E.E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
