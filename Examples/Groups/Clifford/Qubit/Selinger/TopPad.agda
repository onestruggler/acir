------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure 8, C1–C15: the rules on their own wires, padded by
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

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.TopPad (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import Data.Nat using (2+)
open import Data.Nat.Primality using (Prime)

open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime

open Circuit.TopPad ExactGate using (_⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  c1ᴮ : 0 Base, ω ^ 8 === ε
  c2ᴮ : 1 Base, H ^ 2 === ε
  c3ᴮ : 1 Base, S ^ 4 === ε
  c4ᴮ : 1 Base, SH ^ 3 === ω
  c5ᴮ : 2 Base, CZ ^ 2 === ε
  c6ᴮ : 2 Base, S ↓ • CZ === CZ • S ↓
  c7ᴮ : 2 Base, S ↑ • CZ === CZ • S ↑
  c8ᴮ : 2 Base, X ↓ • CZ === CZ • X ↓ • Z ↑
  c9ᴮ : 2 Base, X ↑ • CZ === CZ • X ↑ • Z ↓
  c10ᴮ : 2 Base, CZ • H ↑ • CZ === SH ↑ • CZ • (S • H • S) ↑ • S ↓ • ω⁻¹
  c11ᴮ : 2 Base, CZ • H ↓ • CZ === SH ↓ • CZ • (S • H • S) ↓ • S ↑ • ω⁻¹
  c12ᴮ : 3 Base, CZ ↑ • CZ === CZ • CZ ↑
  c13ᴮ : 3 Base, ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  c14ᴮ : 3 Base, (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  c15ᴮ : 3 Base, (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

module TP = Circuit.TopPad.Top-Pad ExactGate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad ExactGate _Sel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: its words are
-- closed, so one wire wider they are the same words.

c1↓ : n TRel, ω ^ 8 === ε
c1↓ {0}    = TP.srel c1ᴮ
c1↓ {₁₊ n} = TP.cong↓ c1↓

c2↓ : (₁₊ n) TRel, H ^ 2 === ε
c2↓ {0}    = TP.srel c2ᴮ
c2↓ {₁₊ n} = TP.cong↓ c2↓

c3↓ : (₁₊ n) TRel, S ^ 4 === ε
c3↓ {0}    = TP.srel c3ᴮ
c3↓ {₁₊ n} = TP.cong↓ c3↓

c4↓ : (₁₊ n) TRel, SH ^ 3 === ω
c4↓ {0}    = TP.srel c4ᴮ
c4↓ {₁₊ n} = TP.cong↓ c4↓

c5↓ : (₂₊ n) TRel, CZ ^ 2 === ε
c5↓ {0}    = TP.srel c5ᴮ
c5↓ {₁₊ n} = TP.cong↓ c5↓

c6↓ : (₂₊ n) TRel, S ↓ • CZ === CZ • S ↓
c6↓ {0}    = TP.srel c6ᴮ
c6↓ {₁₊ n} = TP.cong↓ c6↓

c7↓ : (₂₊ n) TRel, S ↑ • CZ === CZ • S ↑
c7↓ {0}    = TP.srel c7ᴮ
c7↓ {₁₊ n} = TP.cong↓ c7↓

c8↓ : (₂₊ n) TRel, X ↓ • CZ === CZ • X ↓ • Z ↑
c8↓ {0}    = TP.srel c8ᴮ
c8↓ {₁₊ n} = TP.cong↓ c8↓

c9↓ : (₂₊ n) TRel, X ↑ • CZ === CZ • X ↑ • Z ↓
c9↓ {0}    = TP.srel c9ᴮ
c9↓ {₁₊ n} = TP.cong↓ c9↓

c10↓ : (₂₊ n) TRel, CZ • H ↑ • CZ === SH ↑ • CZ • (S • H • S) ↑ • S ↓ • ω⁻¹
c10↓ {0}    = TP.srel c10ᴮ
c10↓ {₁₊ n} = TP.cong↓ c10↓

c11↓ : (₂₊ n) TRel, CZ • H ↓ • CZ === SH ↓ • CZ • (S • H • S) ↓ • S ↑ • ω⁻¹
c11↓ {0}    = TP.srel c11ᴮ
c11↓ {₁₊ n} = TP.cong↓ c11↓

c12↓ : (₃₊ n) TRel, CZ ↑ • CZ === CZ • CZ ↑
c12↓ {0}    = TP.srel c12ᴮ
c12↓ {₁₊ n} = TP.cong↓ c12↓

c13↓ : (₃₊ n) TRel, ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
c13↓ {0}    = TP.srel c13ᴮ
c13↓ {₁₊ n} = TP.cong↓ c13↓

c14↓ : (₃₊ n) TRel, (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
c14↓ {0}    = TP.srel c14ᴮ
c14↓ {₁₊ n} = TP.cong↓ c14↓

c15↓ : (₃₊ n) TRel, (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
c15↓ {0}    = TP.srel c15ᴮ
c15↓ {₁₊ n} = TP.cong↓ c15↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n Sel, w === v → n ⊢ᵀ w ≈ v
  pad c1 = PB.axiom c1↓
  pad c2 = PB.axiom c2↓
  pad c3 = PB.axiom c3↓
  pad c4 = PB.axiom c4↓
  pad c5 = PB.axiom c5↓
  pad c6 = PB.axiom c6↓
  pad c7 = PB.axiom c7↓
  pad c8 = PB.axiom c8↓
  pad c9 = PB.axiom c9↓
  pad c10 = PB.axiom c10↓
  pad c11 = PB.axiom c11↓
  pad c12 = PB.axiom c12↓
  pad c13 = PB.axiom c13↓
  pad c14 = PB.axiom c14↓
  pad c15 = PB.axiom c15↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad c1ᴮ = PB.axiom (srel c1)
  unpad c2ᴮ = PB.axiom (srel c2)
  unpad c3ᴮ = PB.axiom (srel c3)
  unpad c4ᴮ = PB.axiom (srel c4)
  unpad c5ᴮ = PB.axiom (srel c5)
  unpad c6ᴮ = PB.axiom (srel c6)
  unpad c7ᴮ = PB.axiom (srel c7)
  unpad c8ᴮ = PB.axiom (srel c8)
  unpad c9ᴮ = PB.axiom (srel c9)
  unpad c10ᴮ = PB.axiom (srel c10)
  unpad c11ᴮ = PB.axiom (srel c11)
  unpad c12ᴮ = PB.axiom (srel c12)
  unpad c13ᴮ = PB.axiom (srel c13)
  unpad c14ᴮ = PB.axiom (srel c14)
  unpad c15ᴮ = PB.axiom (srel c15)

  srel-⇓ : n Sel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ c1 = PB.axiom (srel c1)
  srel-⇓ c2 = PB.axiom (srel c2)
  srel-⇓ c3 = PB.axiom (srel c3)
  srel-⇓ c4 = PB.axiom (srel c4)
  srel-⇓ c5 = PB.axiom (srel c5)
  srel-⇓ c6 = PB.axiom (srel c6)
  srel-⇓ c7 = PB.axiom (srel c7)
  srel-⇓ c8 = PB.axiom (srel c8)
  srel-⇓ c9 = PB.axiom (srel c9)
  srel-⇓ c10 = PB.axiom (srel c10)
  srel-⇓ c11 = PB.axiom (srel c11)
  srel-⇓ c12 = PB.axiom (srel c12)
  srel-⇓ c13 = PB.axiom (srel c13)
  srel-⇓ c14 = PB.axiom (srel c14)
  srel-⇓ c15 = PB.axiom (srel c15)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
