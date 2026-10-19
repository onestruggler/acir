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

-- The equations ⇓-same proves for a rule: each side ⇓'d is that side
-- one wire wider.  Proved once per rule, for its padded form and for
-- srel-⇓ below, which would otherwise each prove them.

import Relation.Binary.PropositionalEquality as TopPad-≡

⇓ˡ ⇓ʳ : ∀ {n w v w′ v′} → Base._SRel,_===_ n w v → Base._SRel,_===_ (₁₊ n) w′ v′ → Set
⇓ˡ {w = w} {w′ = w′} _ _ = TopPad-≡._≡_ (w ⇓) w′
⇓ʳ {v = v} {v′ = v′} _ _ = TopPad-≡._≡_ (v ⇓) v′

order-S⇓ˡ : ⇓ˡ {(₁₊ n)} Base.order-S Base.order-S
order-S⇓ˡ = ⇓-same

order-S⇓ʳ : ⇓ʳ {(₁₊ n)} Base.order-S Base.order-S
order-S⇓ʳ = ⇓-same

order-H⇓ˡ : ⇓ˡ {(₁₊ n)} Base.order-H Base.order-H
order-H⇓ˡ = ⇓-same

order-H⇓ʳ : ⇓ʳ {(₁₊ n)} Base.order-H Base.order-H
order-H⇓ʳ = ⇓-same

order-SH⇓ˡ : ⇓ˡ {(₁₊ n)} Base.order-SH Base.order-SH
order-SH⇓ˡ = ⇓-same

order-SH⇓ʳ : ⇓ʳ {(₁₊ n)} Base.order-SH Base.order-SH
order-SH⇓ʳ = ⇓-same

comm-HHS⇓ˡ : ⇓ˡ {(₁₊ n)} Base.comm-HHS Base.comm-HHS
comm-HHS⇓ˡ = ⇓-same

comm-HHS⇓ʳ : ⇓ʳ {(₁₊ n)} Base.comm-HHS Base.comm-HHS
comm-HHS⇓ʳ = ⇓-same

M-mul⇓ˡ : ∀ x y → ⇓ˡ {(₁₊ n)} (Base.M-mul x y) (Base.M-mul x y)
M-mul⇓ˡ x y = ⇓-same

M-mul⇓ʳ : ∀ x y → ⇓ʳ {(₁₊ n)} (Base.M-mul x y) (Base.M-mul x y)
M-mul⇓ʳ x y = ⇓-same

semi-MS⇓ˡ : ∀ x → ⇓ˡ {(₁₊ n)} (Base.semi-MS x) (Base.semi-MS x)
semi-MS⇓ˡ x = ⇓-same

semi-MS⇓ʳ : ∀ x → ⇓ʳ {(₁₊ n)} (Base.semi-MS x) (Base.semi-MS x)
semi-MS⇓ʳ x = ⇓-same

semi-M↑CZ⇓ˡ : ∀ x → ⇓ˡ {(₂₊ n)} (Base.semi-M↑CZ x) (Base.semi-M↑CZ x)
semi-M↑CZ⇓ˡ x = ⇓-same

semi-M↑CZ⇓ʳ : ∀ x → ⇓ʳ {(₂₊ n)} (Base.semi-M↑CZ x) (Base.semi-M↑CZ x)
semi-M↑CZ⇓ʳ x = ⇓-same

semi-M↓CZ⇓ˡ : ∀ x → ⇓ˡ {(₂₊ n)} (Base.semi-M↓CZ x) (Base.semi-M↓CZ x)
semi-M↓CZ⇓ˡ x = ⇓-same

semi-M↓CZ⇓ʳ : ∀ x → ⇓ʳ {(₂₊ n)} (Base.semi-M↓CZ x) (Base.semi-M↓CZ x)
semi-M↓CZ⇓ʳ x = ⇓-same

order-CZ⇓ˡ : ⇓ˡ {(₂₊ n)} Base.order-CZ Base.order-CZ
order-CZ⇓ˡ = ⇓-same

order-CZ⇓ʳ : ⇓ʳ {(₂₊ n)} Base.order-CZ Base.order-CZ
order-CZ⇓ʳ = ⇓-same

comm-CZ-S↓⇓ˡ : ⇓ˡ {(₂₊ n)} Base.comm-CZ-S↓ Base.comm-CZ-S↓
comm-CZ-S↓⇓ˡ = ⇓-same

comm-CZ-S↓⇓ʳ : ⇓ʳ {(₂₊ n)} Base.comm-CZ-S↓ Base.comm-CZ-S↓
comm-CZ-S↓⇓ʳ = ⇓-same

comm-CZ-S↑⇓ˡ : ⇓ˡ {(₂₊ n)} Base.comm-CZ-S↑ Base.comm-CZ-S↑
comm-CZ-S↑⇓ˡ = ⇓-same

comm-CZ-S↑⇓ʳ : ⇓ʳ {(₂₊ n)} Base.comm-CZ-S↑ Base.comm-CZ-S↑
comm-CZ-S↑⇓ʳ = ⇓-same

selinger-c10⇓ˡ : ⇓ˡ {(₂₊ n)} Base.selinger-c10 Base.selinger-c10
selinger-c10⇓ˡ = ⇓-same

selinger-c10⇓ʳ : ⇓ʳ {(₂₊ n)} Base.selinger-c10 Base.selinger-c10
selinger-c10⇓ʳ = ⇓-same

selinger-c11⇓ˡ : ⇓ˡ {(₂₊ n)} Base.selinger-c11 Base.selinger-c11
selinger-c11⇓ˡ = ⇓-same

selinger-c11⇓ʳ : ⇓ʳ {(₂₊ n)} Base.selinger-c11 Base.selinger-c11
selinger-c11⇓ʳ = ⇓-same

selinger-c12⇓ˡ : ⇓ˡ {(₃₊ n)} Base.selinger-c12 Base.selinger-c12
selinger-c12⇓ˡ = ⇓-same

selinger-c12⇓ʳ : ⇓ʳ {(₃₊ n)} Base.selinger-c12 Base.selinger-c12
selinger-c12⇓ʳ = ⇓-same

selinger-c13⇓ˡ : ⇓ˡ {(₃₊ n)} Base.selinger-c13 Base.selinger-c13
selinger-c13⇓ˡ = ⇓-same

selinger-c13⇓ʳ : ⇓ʳ {(₃₊ n)} Base.selinger-c13 Base.selinger-c13
selinger-c13⇓ʳ = ⇓-same

selinger-c14⇓ˡ : ⇓ˡ {(₃₊ n)} Base.selinger-c14 Base.selinger-c14
selinger-c14⇓ˡ = ⇓-same

selinger-c14⇓ʳ : ⇓ʳ {(₃₊ n)} Base.selinger-c14 Base.selinger-c14
selinger-c14⇓ʳ = ⇓-same

selinger-c15⇓ˡ : ⇓ˡ {(₃₊ n)} Base.selinger-c15 Base.selinger-c15
selinger-c15⇓ˡ = ⇓-same

selinger-c15⇓ʳ : ⇓ʳ {(₃₊ n)} Base.selinger-c15 Base.selinger-c15
selinger-c15⇓ʳ = ⇓-same

-- Each rule on the bottom wires of every wider circuit: one wire wider
-- its words are the same words, up to the powers ⇓ does not compute
-- through (⇓-same).

order-S↓ : (₁₊ n) TRel, S ^ p === ε
order-S↓ {0}    = TP.srel order-Sᴮ
order-S↓ {₁₊ n} = E.cong↓≡ order-S⇓ˡ order-S⇓ʳ order-S↓

order-H↓ : (₁₊ n) TRel, H ^ 4 === ε
order-H↓ {0}    = TP.srel order-Hᴮ
order-H↓ {₁₊ n} = E.cong↓≡ order-H⇓ˡ order-H⇓ʳ order-H↓

order-SH↓ : (₁₊ n) TRel, (S • H) ^ 3 === ε
order-SH↓ {0}    = TP.srel order-SHᴮ
order-SH↓ {₁₊ n} = E.cong↓≡ order-SH⇓ˡ order-SH⇓ʳ order-SH↓

comm-HHS↓ : (₁₊ n) TRel, H • H • S === S • H • H
comm-HHS↓ {0}    = TP.srel comm-HHSᴮ
comm-HHS↓ {₁₊ n} = E.cong↓≡ comm-HHS⇓ˡ comm-HHS⇓ʳ comm-HHS↓

M-mul↓ : ∀ x y → (₁₊ n) TRel, M x • M y === M (x *' y)
M-mul↓ {0}    x y = TP.srel (M-mulᴮ x y)
M-mul↓ {₁₊ n} x y = E.cong↓≡ (M-mul⇓ˡ x y) (M-mul⇓ʳ x y) (M-mul↓ x y)

semi-MS↓ : ∀ x → (₁₊ n) TRel, M x • S === S^ (x ^2) • M x
semi-MS↓ {0}    x = TP.srel (semi-MSᴮ x)
semi-MS↓ {₁₊ n} x = E.cong↓≡ (semi-MS⇓ˡ x) (semi-MS⇓ʳ x) (semi-MS↓ x)

semi-M↑CZ↓ : ∀ x → (₂₊ n) TRel, M x ↑ • CZ === CZ^ (x ^1) • M x ↑
semi-M↑CZ↓ {0}    x = TP.srel (semi-M↑CZᴮ x)
semi-M↑CZ↓ {₁₊ n} x = E.cong↓≡ (semi-M↑CZ⇓ˡ x) (semi-M↑CZ⇓ʳ x) (semi-M↑CZ↓ x)

semi-M↓CZ↓ : ∀ x → (₂₊ n) TRel, M x ↓ • CZ === CZ^ (x ^1) • M x ↓
semi-M↓CZ↓ {0}    x = TP.srel (semi-M↓CZᴮ x)
semi-M↓CZ↓ {₁₊ n} x = E.cong↓≡ (semi-M↓CZ⇓ˡ x) (semi-M↓CZ⇓ʳ x) (semi-M↓CZ↓ x)

order-CZ↓ : (₂₊ n) TRel, CZ ^ p === ε
order-CZ↓ {0}    = TP.srel order-CZᴮ
order-CZ↓ {₁₊ n} = E.cong↓≡ order-CZ⇓ˡ order-CZ⇓ʳ order-CZ↓

comm-CZ-S↓↓ : (₂₊ n) TRel, CZ • S ↓ === S ↓ • CZ
comm-CZ-S↓↓ {0}    = TP.srel comm-CZ-S↓ᴮ
comm-CZ-S↓↓ {₁₊ n} = E.cong↓≡ comm-CZ-S↓⇓ˡ comm-CZ-S↓⇓ʳ comm-CZ-S↓↓

comm-CZ-S↑↓ : (₂₊ n) TRel, CZ • S ↑ === S ↑ • CZ
comm-CZ-S↑↓ {0}    = TP.srel comm-CZ-S↑ᴮ
comm-CZ-S↑↓ {₁₊ n} = E.cong↓≡ comm-CZ-S↑⇓ˡ comm-CZ-S↑⇓ʳ comm-CZ-S↑↓

selinger-c10↓ : (₂₊ n) TRel, CZ • H ↑ • CZ ===
      S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
selinger-c10↓ {0}    = TP.srel selinger-c10ᴮ
selinger-c10↓ {₁₊ n} = E.cong↓≡ selinger-c10⇓ˡ selinger-c10⇓ʳ selinger-c10↓

selinger-c11↓ : (₂₊ n) TRel, CZ • H ↓ • CZ ===
      S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
selinger-c11↓ {0}    = TP.srel selinger-c11ᴮ
selinger-c11↓ {₁₊ n} = E.cong↓≡ selinger-c11⇓ˡ selinger-c11⇓ʳ selinger-c11↓

selinger-c12↓ : (₃₊ n) TRel, CZ ↑ • CZ === CZ • CZ ↑
selinger-c12↓ {0}    = TP.srel selinger-c12ᴮ
selinger-c12↓ {₁₊ n} = E.cong↓≡ selinger-c12⇓ˡ selinger-c12⇓ʳ selinger-c12↓

selinger-c13↓ : (₃₊ n) TRel, ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
selinger-c13↓ {0}    = TP.srel selinger-c13ᴮ
selinger-c13↓ {₁₊ n} = E.cong↓≡ selinger-c13⇓ˡ selinger-c13⇓ʳ selinger-c13↓

selinger-c14↓ : (₃₊ n) TRel, (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
selinger-c14↓ {0}    = TP.srel selinger-c14ᴮ
selinger-c14↓ {₁₊ n} = E.cong↓≡ selinger-c14⇓ˡ selinger-c14⇓ʳ selinger-c14↓

selinger-c15↓ : (₃₊ n) TRel, (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
selinger-c15↓ {0}    = TP.srel selinger-c15ᴮ
selinger-c15↓ {₁₊ n} = E.cong↓≡ selinger-c15⇓ˡ selinger-c15⇓ʳ selinger-c15↓

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
  srel-⇓ Base.order-S = E.axiom≡ order-S⇓ˡ order-S⇓ʳ (srel Base.order-S)
  srel-⇓ Base.order-H = E.axiom≡ order-H⇓ˡ order-H⇓ʳ (srel Base.order-H)
  srel-⇓ Base.order-SH = E.axiom≡ order-SH⇓ˡ order-SH⇓ʳ (srel Base.order-SH)
  srel-⇓ Base.comm-HHS = E.axiom≡ comm-HHS⇓ˡ comm-HHS⇓ʳ (srel Base.comm-HHS)
  srel-⇓ (Base.M-mul x y) = E.axiom≡ (M-mul⇓ˡ x y) (M-mul⇓ʳ x y) (srel (Base.M-mul x y))
  srel-⇓ (Base.semi-MS x) = E.axiom≡ (semi-MS⇓ˡ x) (semi-MS⇓ʳ x) (srel (Base.semi-MS x))
  srel-⇓ (Base.semi-M↑CZ x) = E.axiom≡ (semi-M↑CZ⇓ˡ x) (semi-M↑CZ⇓ʳ x) (srel (Base.semi-M↑CZ x))
  srel-⇓ (Base.semi-M↓CZ x) = E.axiom≡ (semi-M↓CZ⇓ˡ x) (semi-M↓CZ⇓ʳ x) (srel (Base.semi-M↓CZ x))
  srel-⇓ Base.order-CZ = E.axiom≡ order-CZ⇓ˡ order-CZ⇓ʳ (srel Base.order-CZ)
  srel-⇓ Base.comm-CZ-S↓ = E.axiom≡ comm-CZ-S↓⇓ˡ comm-CZ-S↓⇓ʳ (srel Base.comm-CZ-S↓)
  srel-⇓ Base.comm-CZ-S↑ = E.axiom≡ comm-CZ-S↑⇓ˡ comm-CZ-S↑⇓ʳ (srel Base.comm-CZ-S↑)
  srel-⇓ Base.selinger-c10 = E.axiom≡ selinger-c10⇓ˡ selinger-c10⇓ʳ (srel Base.selinger-c10)
  srel-⇓ Base.selinger-c11 = E.axiom≡ selinger-c11⇓ˡ selinger-c11⇓ʳ (srel Base.selinger-c11)
  srel-⇓ Base.selinger-c12 = E.axiom≡ selinger-c12⇓ˡ selinger-c12⇓ʳ (srel Base.selinger-c12)
  srel-⇓ Base.selinger-c13 = E.axiom≡ selinger-c13⇓ˡ selinger-c13⇓ʳ (srel Base.selinger-c13)
  srel-⇓ Base.selinger-c14 = E.axiom≡ selinger-c14⇓ˡ selinger-c14⇓ʳ (srel Base.selinger-c14)
  srel-⇓ Base.selinger-c15 = E.axiom≡ selinger-c15⇓ˡ selinger-c15⇓ʳ (srel Base.selinger-c15)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
