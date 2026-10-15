------------------------------------------------------------------------
-- Presentations of groups
--
-- The symplectic relations of Syntactics.Gates: the rules on their own
-- wires, padded by Circuit.TopPad, give the same congruence as
-- Syntactics' rules at every width, lifted by Circuit.Base's
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

module Examples.Groups.Symplectic.Syntactics.TopPad (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics.Gates p-2 p-prime
open Symplectic
open Symplectic-GroupLike using (grouplike)

open Circuit.TopPad SympGate using (_⇓)
open import Circuit.TopPad.Closed SympGate using (⇓-same)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order-Sᴮ : 1 Base, S ^ p === ε
  order-Hᴮ : 1 Base, H ^ 4 === ε
  order-SHᴮ : 1 Base, (S • H) ^ 3 === ε
  comm-HHSᴮ : 1 Base, H • H • S === S • H • H
  M-mulᴮ : ∀ x y → 1 Base, M x • M y === M (x *' y)
  semi-MSᴮ : ∀ x → 1 Base, M x • S === S^ (x ^2) • M x
  semi-M↑CZᴮ : ∀ x → 2 Base, M x ↑ • CZ === CZ^ (x ^1) • M x ↑
  semi-M↓CZᴮ : ∀ x → 2 Base, M x ↓ • CZ === CZ^ (x ^1) • M x ↓
  order-CZᴮ : 2 Base, CZ ^ p === ε
  comm-CZ-S↓ᴮ : 2 Base, CZ • S ↓ === S ↓ • CZ
  comm-CZ-S↑ᴮ : 2 Base, CZ • S ↑ === S ↑ • CZ
  selinger-c10ᴮ : 2 Base, CZ • H ↑ • CZ ===
        S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
  selinger-c11ᴮ : 2 Base, CZ • H ↓ • CZ ===
        S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
  selinger-c12ᴮ : 3 Base, CZ ↑ • CZ === CZ • CZ ↑
  selinger-c13ᴮ : 3 Base, ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  selinger-c14ᴮ : 3 Base, (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  selinger-c15ᴮ : 3 Base, (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

module TP = Circuit.TopPad.Top-Pad SympGate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad SympGate Base._SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: one wire wider
-- its words are the same words, up to the powers ⇓ does not compute
-- through (⇓-same).

order-S↓ : (₁₊ n) TRel, S ^ p === ε
order-S↓ {0}    = TP.srel order-Sᴮ
order-S↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-S↓

order-H↓ : (₁₊ n) TRel, H ^ 4 === ε
order-H↓ {0}    = TP.srel order-Hᴮ
order-H↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-H↓

order-SH↓ : (₁₊ n) TRel, (S • H) ^ 3 === ε
order-SH↓ {0}    = TP.srel order-SHᴮ
order-SH↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-SH↓

comm-HHS↓ : (₁₊ n) TRel, H • H • S === S • H • H
comm-HHS↓ {0}    = TP.srel comm-HHSᴮ
comm-HHS↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-HHS↓

M-mul↓ : ∀ x y → (₁₊ n) TRel, M x • M y === M (x *' y)
M-mul↓ {0}    x y = TP.srel (M-mulᴮ x y)
M-mul↓ {₁₊ n} x y = E.cong↓≡ ⇓-same ⇓-same (M-mul↓ x y)

semi-MS↓ : ∀ x → (₁₊ n) TRel, M x • S === S^ (x ^2) • M x
semi-MS↓ {0}    x = TP.srel (semi-MSᴮ x)
semi-MS↓ {₁₊ n} x = E.cong↓≡ ⇓-same ⇓-same (semi-MS↓ x)

semi-M↑CZ↓ : ∀ x → (₂₊ n) TRel, M x ↑ • CZ === CZ^ (x ^1) • M x ↑
semi-M↑CZ↓ {0}    x = TP.srel (semi-M↑CZᴮ x)
semi-M↑CZ↓ {₁₊ n} x = E.cong↓≡ ⇓-same ⇓-same (semi-M↑CZ↓ x)

semi-M↓CZ↓ : ∀ x → (₂₊ n) TRel, M x ↓ • CZ === CZ^ (x ^1) • M x ↓
semi-M↓CZ↓ {0}    x = TP.srel (semi-M↓CZᴮ x)
semi-M↓CZ↓ {₁₊ n} x = E.cong↓≡ ⇓-same ⇓-same (semi-M↓CZ↓ x)

order-CZ↓ : (₂₊ n) TRel, CZ ^ p === ε
order-CZ↓ {0}    = TP.srel order-CZᴮ
order-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-CZ↓

comm-CZ-S↓↓ : (₂₊ n) TRel, CZ • S ↓ === S ↓ • CZ
comm-CZ-S↓↓ {0}    = TP.srel comm-CZ-S↓ᴮ
comm-CZ-S↓↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-CZ-S↓↓

comm-CZ-S↑↓ : (₂₊ n) TRel, CZ • S ↑ === S ↑ • CZ
comm-CZ-S↑↓ {0}    = TP.srel comm-CZ-S↑ᴮ
comm-CZ-S↑↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-CZ-S↑↓

selinger-c10↓ : (₂₊ n) TRel, CZ • H ↑ • CZ ===
      S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
selinger-c10↓ {0}    = TP.srel selinger-c10ᴮ
selinger-c10↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c10↓

selinger-c11↓ : (₂₊ n) TRel, CZ • H ↓ • CZ ===
      S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
selinger-c11↓ {0}    = TP.srel selinger-c11ᴮ
selinger-c11↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c11↓

selinger-c12↓ : (₃₊ n) TRel, CZ ↑ • CZ === CZ • CZ ↑
selinger-c12↓ {0}    = TP.srel selinger-c12ᴮ
selinger-c12↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c12↓

selinger-c13↓ : (₃₊ n) TRel, ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
selinger-c13↓ {0}    = TP.srel selinger-c13ᴮ
selinger-c13↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c13↓

selinger-c14↓ : (₃₊ n) TRel, (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
selinger-c14↓ {0}    = TP.srel selinger-c14ᴮ
selinger-c14↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c14↓

selinger-c15↓ : (₃₊ n) TRel, (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
selinger-c15↓ {0}    = TP.srel selinger-c15ᴮ
selinger-c15↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c15↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : Base._SRel,_===_ n w v → n ⊢ᵀ w ≈ v
  pad Base.order-S = PB.axiom order-S↓
  pad Base.order-H = PB.axiom order-H↓
  pad Base.order-SH = PB.axiom order-SH↓
  pad Base.comm-HHS = PB.axiom comm-HHS↓
  pad (Base.M-mul x y) = PB.axiom (M-mul↓ x y)
  pad (Base.semi-MS x) = PB.axiom (semi-MS↓ x)
  pad (Base.semi-M↑CZ x) = PB.axiom (semi-M↑CZ↓ x)
  pad (Base.semi-M↓CZ x) = PB.axiom (semi-M↓CZ↓ x)
  pad Base.order-CZ = PB.axiom order-CZ↓
  pad Base.comm-CZ-S↓ = PB.axiom comm-CZ-S↓↓
  pad Base.comm-CZ-S↑ = PB.axiom comm-CZ-S↑↓
  pad Base.selinger-c10 = PB.axiom selinger-c10↓
  pad Base.selinger-c11 = PB.axiom selinger-c11↓
  pad Base.selinger-c12 = PB.axiom selinger-c12↓
  pad Base.selinger-c13 = PB.axiom selinger-c13↓
  pad Base.selinger-c14 = PB.axiom selinger-c14↓
  pad Base.selinger-c15 = PB.axiom selinger-c15↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad order-Sᴮ = PB.axiom (srel Base.order-S)
  unpad order-Hᴮ = PB.axiom (srel Base.order-H)
  unpad order-SHᴮ = PB.axiom (srel Base.order-SH)
  unpad comm-HHSᴮ = PB.axiom (srel Base.comm-HHS)
  unpad (M-mulᴮ x y) = PB.axiom (srel (Base.M-mul x y))
  unpad (semi-MSᴮ x) = PB.axiom (srel (Base.semi-MS x))
  unpad (semi-M↑CZᴮ x) = PB.axiom (srel (Base.semi-M↑CZ x))
  unpad (semi-M↓CZᴮ x) = PB.axiom (srel (Base.semi-M↓CZ x))
  unpad order-CZᴮ = PB.axiom (srel Base.order-CZ)
  unpad comm-CZ-S↓ᴮ = PB.axiom (srel Base.comm-CZ-S↓)
  unpad comm-CZ-S↑ᴮ = PB.axiom (srel Base.comm-CZ-S↑)
  unpad selinger-c10ᴮ = PB.axiom (srel Base.selinger-c10)
  unpad selinger-c11ᴮ = PB.axiom (srel Base.selinger-c11)
  unpad selinger-c12ᴮ = PB.axiom (srel Base.selinger-c12)
  unpad selinger-c13ᴮ = PB.axiom (srel Base.selinger-c13)
  unpad selinger-c14ᴮ = PB.axiom (srel Base.selinger-c14)
  unpad selinger-c15ᴮ = PB.axiom (srel Base.selinger-c15)

  srel-⇓ : Base._SRel,_===_ n w v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ Base.order-S = E.axiom≡ ⇓-same ⇓-same (srel Base.order-S)
  srel-⇓ Base.order-H = E.axiom≡ ⇓-same ⇓-same (srel Base.order-H)
  srel-⇓ Base.order-SH = E.axiom≡ ⇓-same ⇓-same (srel Base.order-SH)
  srel-⇓ Base.comm-HHS = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-HHS)
  srel-⇓ (Base.M-mul x y) = E.axiom≡ ⇓-same ⇓-same (srel (Base.M-mul x y))
  srel-⇓ (Base.semi-MS x) = E.axiom≡ ⇓-same ⇓-same (srel (Base.semi-MS x))
  srel-⇓ (Base.semi-M↑CZ x) = E.axiom≡ ⇓-same ⇓-same (srel (Base.semi-M↑CZ x))
  srel-⇓ (Base.semi-M↓CZ x) = E.axiom≡ ⇓-same ⇓-same (srel (Base.semi-M↓CZ x))
  srel-⇓ Base.order-CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.order-CZ)
  srel-⇓ Base.comm-CZ-S↓ = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-CZ-S↓)
  srel-⇓ Base.comm-CZ-S↑ = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-CZ-S↑)
  srel-⇓ Base.selinger-c10 = E.axiom≡ ⇓-same ⇓-same (srel Base.selinger-c10)
  srel-⇓ Base.selinger-c11 = E.axiom≡ ⇓-same ⇓-same (srel Base.selinger-c11)
  srel-⇓ Base.selinger-c12 = E.axiom≡ ⇓-same ⇓-same (srel Base.selinger-c12)
  srel-⇓ Base.selinger-c13 = E.axiom≡ ⇓-same ⇓-same (srel Base.selinger-c13)
  srel-⇓ Base.selinger-c14 = E.axiom≡ ⇓-same ⇓-same (srel Base.selinger-c14)
  srel-⇓ Base.selinger-c15 = E.axiom≡ ⇓-same ⇓-same (srel Base.selinger-c15)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
