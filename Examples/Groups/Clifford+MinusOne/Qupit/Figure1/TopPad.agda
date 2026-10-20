------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1 with its scalar -ω (c0–c15): the rules on their own wires,
-- padded by Circuit.TopPad, give the same congruence as Syntactics'
-- rules at every width, lifted by Circuit.Base's Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence, as Symmetric.TopPad is:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and SameRules says, rule by rule, that the two
-- relations have the same rules. Powers whose exponent is not a numeral
-- (S ^ p, S^ k) do not compute under ⇓, so the padded rules and the
-- rules ⇓'d go through Circuit.TopPad.Closed's ⇓-same. The Legendre
-- symbol, chosen by a case split, goes through by cases
-- (legendre-by-⇓).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_×_ ; _,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.TopPad
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import Data.List using (List ; [] ; _∷_)
import Data.Nat as Nat
open import Reflection using (Name)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.PropositionalEquality as Eq

open Primitive-Root-Modp' g* g-gen
open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics p-3 p-prime g* g-gen
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics as Figure1
open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.FF-Iso p-3 p-prime g* g-gen
  using (grouplike-F)

open Circuit.TopPad Fig1Gate using (_⇓)
open import Circuit.TopPad.Closed Fig1Gate using (⇓-same ; ⇓-same-by)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

-- The Legendre symbol is a word chosen by a case split on a label,
-- stuck for good: ⇓ goes through it by cases.
legendre-by-⇓ : ∀ {n} {y : ℤ ₚ} (d : Dec (toℕ y ≡ 1)) →
                _⇓ {n} (legendre-by d) ≡ legendre-by d
legendre-by-⇓ (yes _) = Eq.refl
legendre-by-⇓ (no _)  = ⇓-same

-- (Quoted from the module itself: a goal shows the original, not the
-- copy an applied import makes.)
lemmas₀ : List (Name × Name × ℕ)
lemmas₀ = (quote Figure1.legendre-by , quote legendre-by-⇓ , 1) ∷ []

-- The multipliers and the swap, which many rules share, ⇓'d once each:
-- the traversal of a rule stops at them rather than going through
-- their definitions again.
M-⇓ : ∀ {n} (a* : ℤ* ₚ) → _⇓ {₁₊ n} (M a*) ≡ M a*
M-⇓ a* = ⇓-same-by lemmas₀

SWAP-⇓ : ∀ {n} → _⇓ {₂₊ n} SWAP ≡ SWAP
SWAP-⇓ = ⇓-same

lemmas : List (Name × Name × ℕ)
lemmas = (quote Figure1.M , quote M-⇓ , 1) ∷ (quote Figure1.SWAP , quote SWAP-⇓ , 0) ∷ lemmas₀

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  c0ᴮ : 0 Base, ν ^ (p Nat.+ p) === ε
  c1ᴮ : 1 Base, S ^ p === ε
  c2ᴮ : 1 Base, H ^ 2 === M₋₁ • -1ˢ ^ p-1/2
  c3ᴮ : ∀ (k : ℤ ₚ) → 1 Base, Mg ^ toℕ k === M (g^ k)
  c4ᴮ : 1 Base, Mg • S ===
        Z^ ((₁ + - g) * 1/2 * (g⁻¹ * g⁻¹)) • S^ (g⁻¹ * g⁻¹) • Mg
  c5ᴮ : 1 Base, S • H • H • S • H • H === H • H • S • H • H • S
  c6ᴮ : 2 Base, CZ ^ p === ε
  c7ᴮ : 2 Base, SWAP • SWAP === ε
  c8ᴮ : 2 Base, CZ • S ↑ === S ↑ • CZ
  c9ᴮ : 2 Base, CZ • Mg ↑ === Mg ↑ • CZ^ g
  c10ᴮ : 2 Base, SWAP • S ↑ === S ↓ • SWAP
  c11ᴮ : 2 Base, SWAP • H ↑ === H ↓ • SWAP
  c12ᴮ : 2 Base, (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ
  c13ᴮ : 3 Base, SWAP ↑ • SWAP ↓ • SWAP ↑ === SWAP ↓ • SWAP ↑ • SWAP ↓
  c14ᴮ : 3 Base, SWAP ↓ • SWAP ↑ • CZ ↓ === CZ ↑ • SWAP ↓ • SWAP ↑
  c15ᴮ : 3 Base, CZ ↓ • CX ↑ === CIZ • CX ↑ • CZ ↓

module TP = Circuit.TopPad.Top-Pad Fig1Gate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad Fig1Gate _Fig1,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- The equations ⇓-same proves for a rule: each side ⇓'d is that side
-- one wire wider.  Proved once per rule, for its padded form and for
-- srel-⇓ below, which would otherwise each prove them.

import Relation.Binary.PropositionalEquality as TopPad-≡

⇓ˡ ⇓ʳ : ∀ {n w v w′ v′} → n Fig1, w === v → (₁₊ n) Fig1, w′ === v′ → Set
⇓ˡ {w = w} {w′ = w′} _ _ = TopPad-≡._≡_ (w ⇓) w′
⇓ʳ {v = v} {v′ = v′} _ _ = TopPad-≡._≡_ (v ⇓) v′

c0⇓ˡ : ⇓ˡ {n} c0 c0
c0⇓ˡ = (⇓-same-by lemmas)

c0⇓ʳ : ⇓ʳ {n} c0 c0
c0⇓ʳ = (⇓-same-by lemmas)

c1⇓ˡ : ⇓ˡ {(₁₊ n)} c1 c1
c1⇓ˡ = (⇓-same-by lemmas)

c1⇓ʳ : ⇓ʳ {(₁₊ n)} c1 c1
c1⇓ʳ = (⇓-same-by lemmas)

c2⇓ˡ : ⇓ˡ {(₁₊ n)} c2 c2
c2⇓ˡ = (⇓-same-by lemmas)

c2⇓ʳ : ⇓ʳ {(₁₊ n)} c2 c2
c2⇓ʳ = (⇓-same-by lemmas)

c3⇓ˡ : ∀ (k : ℤ ₚ) → ⇓ˡ {(₁₊ n)} (c3 k) (c3 k)
c3⇓ˡ k = (⇓-same-by lemmas)

c3⇓ʳ : ∀ (k : ℤ ₚ) → ⇓ʳ {(₁₊ n)} (c3 k) (c3 k)
c3⇓ʳ k = (⇓-same-by lemmas)

c4⇓ˡ : ⇓ˡ {(₁₊ n)} c4 c4
c4⇓ˡ = (⇓-same-by lemmas)

c4⇓ʳ : ⇓ʳ {(₁₊ n)} c4 c4
c4⇓ʳ = (⇓-same-by lemmas)

c5⇓ˡ : ⇓ˡ {(₁₊ n)} c5 c5
c5⇓ˡ = (⇓-same-by lemmas)

c5⇓ʳ : ⇓ʳ {(₁₊ n)} c5 c5
c5⇓ʳ = (⇓-same-by lemmas)

c6⇓ˡ : ⇓ˡ {(₂₊ n)} c6 c6
c6⇓ˡ = (⇓-same-by lemmas)

c6⇓ʳ : ⇓ʳ {(₂₊ n)} c6 c6
c6⇓ʳ = (⇓-same-by lemmas)

c7⇓ˡ : ⇓ˡ {(₂₊ n)} c7 c7
c7⇓ˡ = (⇓-same-by lemmas)

c7⇓ʳ : ⇓ʳ {(₂₊ n)} c7 c7
c7⇓ʳ = (⇓-same-by lemmas)

c8⇓ˡ : ⇓ˡ {(₂₊ n)} c8 c8
c8⇓ˡ = (⇓-same-by lemmas)

c8⇓ʳ : ⇓ʳ {(₂₊ n)} c8 c8
c8⇓ʳ = (⇓-same-by lemmas)

c9⇓ˡ : ⇓ˡ {(₂₊ n)} c9 c9
c9⇓ˡ = (⇓-same-by lemmas)

c9⇓ʳ : ⇓ʳ {(₂₊ n)} c9 c9
c9⇓ʳ = (⇓-same-by lemmas)

c10⇓ˡ : ⇓ˡ {(₂₊ n)} c10 c10
c10⇓ˡ = (⇓-same-by lemmas)

c10⇓ʳ : ⇓ʳ {(₂₊ n)} c10 c10
c10⇓ʳ = (⇓-same-by lemmas)

c11⇓ˡ : ⇓ˡ {(₂₊ n)} c11 c11
c11⇓ˡ = (⇓-same-by lemmas)

c11⇓ʳ : ⇓ʳ {(₂₊ n)} c11 c11
c11⇓ʳ = (⇓-same-by lemmas)

c12⇓ˡ : ⇓ˡ {(₂₊ n)} c12 c12
c12⇓ˡ = (⇓-same-by lemmas)

c12⇓ʳ : ⇓ʳ {(₂₊ n)} c12 c12
c12⇓ʳ = (⇓-same-by lemmas)

c13⇓ˡ : ⇓ˡ {(₃₊ n)} c13 c13
c13⇓ˡ = (⇓-same-by lemmas)

c13⇓ʳ : ⇓ʳ {(₃₊ n)} c13 c13
c13⇓ʳ = (⇓-same-by lemmas)

c14⇓ˡ : ⇓ˡ {(₃₊ n)} c14 c14
c14⇓ˡ = (⇓-same-by lemmas)

c14⇓ʳ : ⇓ʳ {(₃₊ n)} c14 c14
c14⇓ʳ = (⇓-same-by lemmas)

c15⇓ˡ : ⇓ˡ {(₃₊ n)} c15 c15
c15⇓ˡ = (⇓-same-by lemmas)

c15⇓ʳ : ⇓ʳ {(₃₊ n)} c15 c15
c15⇓ʳ = (⇓-same-by lemmas)

-- Each rule on the bottom wires of every wider circuit: one wire wider
-- its words are the same words, up to the powers ⇓ does not compute
-- through (⇓-same).

c0↓ : n TRel, ν ^ (p Nat.+ p) === ε
c0↓ {0}    = TP.srel c0ᴮ
c0↓ {₁₊ n} = E.cong↓≡ c0⇓ˡ c0⇓ʳ c0↓

c1↓ : (₁₊ n) TRel, S ^ p === ε
c1↓ {0}    = TP.srel c1ᴮ
c1↓ {₁₊ n} = E.cong↓≡ c1⇓ˡ c1⇓ʳ c1↓

c2↓ : (₁₊ n) TRel, H ^ 2 === M₋₁ • -1ˢ ^ p-1/2
c2↓ {0}    = TP.srel c2ᴮ
c2↓ {₁₊ n} = E.cong↓≡ c2⇓ˡ c2⇓ʳ c2↓

c3↓ : ∀ (k : ℤ ₚ) → (₁₊ n) TRel, Mg ^ toℕ k === M (g^ k)
c3↓ {0}    k = TP.srel (c3ᴮ k)
c3↓ {₁₊ n} k = E.cong↓≡ (c3⇓ˡ k) (c3⇓ʳ k) (c3↓ k)

c4↓ : (₁₊ n) TRel, Mg • S ===
      Z^ ((₁ + - g) * 1/2 * (g⁻¹ * g⁻¹)) • S^ (g⁻¹ * g⁻¹) • Mg
c4↓ {0}    = TP.srel c4ᴮ
c4↓ {₁₊ n} = E.cong↓≡ c4⇓ˡ c4⇓ʳ c4↓

c5↓ : (₁₊ n) TRel, S • H • H • S • H • H === H • H • S • H • H • S
c5↓ {0}    = TP.srel c5ᴮ
c5↓ {₁₊ n} = E.cong↓≡ c5⇓ˡ c5⇓ʳ c5↓

c6↓ : (₂₊ n) TRel, CZ ^ p === ε
c6↓ {0}    = TP.srel c6ᴮ
c6↓ {₁₊ n} = E.cong↓≡ c6⇓ˡ c6⇓ʳ c6↓

c7↓ : (₂₊ n) TRel, SWAP • SWAP === ε
c7↓ {0}    = TP.srel c7ᴮ
c7↓ {₁₊ n} = E.cong↓≡ c7⇓ˡ c7⇓ʳ c7↓

c8↓ : (₂₊ n) TRel, CZ • S ↑ === S ↑ • CZ
c8↓ {0}    = TP.srel c8ᴮ
c8↓ {₁₊ n} = E.cong↓≡ c8⇓ˡ c8⇓ʳ c8↓

c9↓ : (₂₊ n) TRel, CZ • Mg ↑ === Mg ↑ • CZ^ g
c9↓ {0}    = TP.srel c9ᴮ
c9↓ {₁₊ n} = E.cong↓≡ c9⇓ˡ c9⇓ʳ c9↓

c10↓ : (₂₊ n) TRel, SWAP • S ↑ === S ↓ • SWAP
c10↓ {0}    = TP.srel c10ᴮ
c10↓ {₁₊ n} = E.cong↓≡ c10⇓ˡ c10⇓ʳ c10↓

c11↓ : (₂₊ n) TRel, SWAP • H ↑ === H ↓ • SWAP
c11↓ {0}    = TP.srel c11ᴮ
c11↓ {₁₊ n} = E.cong↓≡ c11⇓ˡ c11⇓ʳ c11↓

c12↓ : (₂₊ n) TRel, (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ
c12↓ {0}    = TP.srel c12ᴮ
c12↓ {₁₊ n} = E.cong↓≡ c12⇓ˡ c12⇓ʳ c12↓

c13↓ : (₃₊ n) TRel, SWAP ↑ • SWAP ↓ • SWAP ↑ === SWAP ↓ • SWAP ↑ • SWAP ↓
c13↓ {0}    = TP.srel c13ᴮ
c13↓ {₁₊ n} = E.cong↓≡ c13⇓ˡ c13⇓ʳ c13↓

c14↓ : (₃₊ n) TRel, SWAP ↓ • SWAP ↑ • CZ ↓ === CZ ↑ • SWAP ↓ • SWAP ↑
c14↓ {0}    = TP.srel c14ᴮ
c14↓ {₁₊ n} = E.cong↓≡ c14⇓ˡ c14⇓ʳ c14↓

c15↓ : (₃₊ n) TRel, CZ ↓ • CX ↑ === CIZ • CX ↑ • CZ ↓
c15↓ {0}    = TP.srel c15ᴮ
c15↓ {₁₊ n} = E.cong↓≡ c15⇓ˡ c15⇓ʳ c15↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n Fig1, w === v → n ⊢ᵀ w ≈ v
  pad c0 = PB.axiom c0↓
  pad c1 = PB.axiom c1↓
  pad c2 = PB.axiom c2↓
  pad (c3 k) = PB.axiom (c3↓ k)
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
  unpad c0ᴮ = PB.axiom (srel c0)
  unpad c1ᴮ = PB.axiom (srel c1)
  unpad c2ᴮ = PB.axiom (srel c2)
  unpad (c3ᴮ k) = PB.axiom (srel (c3 k))
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

  srel-⇓ : n Fig1, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ c0 = E.axiom≡ c0⇓ˡ c0⇓ʳ (srel c0)
  srel-⇓ c1 = E.axiom≡ c1⇓ˡ c1⇓ʳ (srel c1)
  srel-⇓ c2 = E.axiom≡ c2⇓ˡ c2⇓ʳ (srel c2)
  srel-⇓ (c3 k) = E.axiom≡ (c3⇓ˡ k) (c3⇓ʳ k) (srel (c3 k))
  srel-⇓ c4 = E.axiom≡ c4⇓ˡ c4⇓ʳ (srel c4)
  srel-⇓ c5 = E.axiom≡ c5⇓ˡ c5⇓ʳ (srel c5)
  srel-⇓ c6 = E.axiom≡ c6⇓ˡ c6⇓ʳ (srel c6)
  srel-⇓ c7 = E.axiom≡ c7⇓ˡ c7⇓ʳ (srel c7)
  srel-⇓ c8 = E.axiom≡ c8⇓ˡ c8⇓ʳ (srel c8)
  srel-⇓ c9 = E.axiom≡ c9⇓ˡ c9⇓ʳ (srel c9)
  srel-⇓ c10 = E.axiom≡ c10⇓ˡ c10⇓ʳ (srel c10)
  srel-⇓ c11 = E.axiom≡ c11⇓ˡ c11⇓ʳ (srel c11)
  srel-⇓ c12 = E.axiom≡ c12⇓ˡ c12⇓ʳ (srel c12)
  srel-⇓ c13 = E.axiom≡ c13⇓ˡ c13⇓ʳ (srel c13)
  srel-⇓ c14 = E.axiom≡ c14⇓ˡ c14⇓ʳ (srel c14)
  srel-⇓ c15 = E.axiom≡ c15⇓ˡ c15⇓ʳ (srel c15)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike-F public using (glᵀ ; lr≅tp)
