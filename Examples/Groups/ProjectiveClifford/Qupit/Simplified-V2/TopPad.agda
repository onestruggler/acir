------------------------------------------------------------------------
-- Presentations of groups
--
-- The simplified qupit Clifford relations (Simplified-V2): the rules on
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

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃ ; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations

module Examples.Groups.ProjectiveClifford.Qupit.Simplified-V2.TopPad
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

open Primitive-Root-Modp' g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics p-3 p-prime g* g-gen
open Clifford-Relations hiding
  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-MR ; order-SH
  ; comm-HHSHHS ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ
  ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11
  ; selinger-c12 ; selinger-c13 ; selinger-c14 ; selinger-c15
  ; comm-H ; comm-S ; comm-CZ ; cong↑ ; lemma-cong↑ ; srel ; comm₁
  ; comm₂ ; module Base )
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V2.Syntactics p-3 p-prime g* g-gen
open Simplified-Relations
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V2.Structural p-3 p-prime g* g-gen
  using (module Simplified-GroupLike-S)
open Simplified-GroupLike-S using (grouplike)

open Circuit.TopPad SympGate using (_⇓)
open import Circuit.TopPad.Closed SympGate using (⇓-same)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

-- Simplified-Relations' own two words, which it keeps private.
Wg : ∀ {n} → Word (Gen (₁₊ n))
Wg = S ^ toℕ (g* .proj₁) • H • S ^ toℕ ((g* ⁻¹) .proj₁) • H •
     S ^ toℕ (g* .proj₁) • H

zX : ℕ
zX = toℕ ((g* .proj₁ + (- 1ₚ)) * 1/2)

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order-Sᴮ : 1 Base, S ^ p === ε
  order-SHᴮ : 1 Base, (S • H) ^ 3 === ε
  comm-HHSHHSᴮ : 1 Base, H • H • S • H • H • S === S • H • H • S • H • H
  order-Hᴮ : 1 Base, H ^ 2 === M₋₁
  M-powerᴮ : ∀ (k : ℤ ₚ) → 1 Base, Mg^ k === M (g^ k)
  semi-MRᴮ : 1 Base, Wg • S === S ^ toℕ (g * g) • Wg • Z ^ toℕ (g + (- 1ₚ))
  semi-M↑CZᴮ : 2 Base, Wg ↑ • CZ === CZ^ g • Wg ↑ • (Z ↓) ^ zX
  semi-M↓CZᴮ : 2 Base, Wg • CZ === CZ^ g • Wg • (Z ↑) ^ zX
  comm-X-Zᴮ : 1 Base, X • Z === Z • X
  rel-X↑-CZᴮ : 2 Base, CZ • X ↑ === X ↑ • Z ↓ • CZ
  rel-X↓-CZᴮ : 2 Base, CZ • X ↓ === X ↓ • Z ↑ • CZ
  comm-Z-CZᴮ : 2 Base, Z • CZ === CZ • Z
  comm-Z↑-CZᴮ : 2 Base, Z ↑ • CZ === CZ • Z ↑
  order-CZᴮ : 2 Base, CZ ^ p === ε
  comm-CZ-S↓ᴮ : 2 Base, CZ • S ↓ === S ↓ • CZ
  comm-CZ-S↑ᴮ : 2 Base, CZ • S ↑ === S ↑ • CZ
  selinger-c10ᴮ : 2 Base, CZ • H ↑ • CZ • X ↑ • Z ↑ ===
        S ↑ ^ p-1 • H ↑ • S ↑ ^ p-1 • CZ • H ↑ • S ↑ ^ p-1 • S ↓ ^ p-1
  selinger-c11ᴮ : 2 Base, CZ • H ↓ • CZ • X ↓ • Z ↓ ===
        S ↓ ^ p-1 • H ↓ • S ↓ ^ p-1 • CZ • H ↓ • S ↓ ^ p-1 • S ↑ ^ p-1
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

order-SH↓ : (₁₊ n) TRel, (S • H) ^ 3 === ε
order-SH↓ {0}    = TP.srel order-SHᴮ
order-SH↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-SH↓

comm-HHSHHS↓ : (₁₊ n) TRel, H • H • S • H • H • S === S • H • H • S • H • H
comm-HHSHHS↓ {0}    = TP.srel comm-HHSHHSᴮ
comm-HHSHHS↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-HHSHHS↓

order-H↓ : (₁₊ n) TRel, H ^ 2 === M₋₁
order-H↓ {0}    = TP.srel order-Hᴮ
order-H↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-H↓

M-power↓ : ∀ (k : ℤ ₚ) → (₁₊ n) TRel, Mg^ k === M (g^ k)
M-power↓ {0}    k = TP.srel (M-powerᴮ k)
M-power↓ {₁₊ n} k = E.cong↓≡ ⇓-same ⇓-same (M-power↓ k)

semi-MR↓ : (₁₊ n) TRel, Wg • S === S ^ toℕ (g * g) • Wg • Z ^ toℕ (g + (- 1ₚ))
semi-MR↓ {0}    = TP.srel semi-MRᴮ
semi-MR↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-MR↓

semi-M↑CZ↓ : (₂₊ n) TRel, Wg ↑ • CZ === CZ^ g • Wg ↑ • (Z ↓) ^ zX
semi-M↑CZ↓ {0}    = TP.srel semi-M↑CZᴮ
semi-M↑CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-M↑CZ↓

semi-M↓CZ↓ : (₂₊ n) TRel, Wg • CZ === CZ^ g • Wg • (Z ↑) ^ zX
semi-M↓CZ↓ {0}    = TP.srel semi-M↓CZᴮ
semi-M↓CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-M↓CZ↓

comm-X-Z↓ : (₁₊ n) TRel, X • Z === Z • X
comm-X-Z↓ {0}    = TP.srel comm-X-Zᴮ
comm-X-Z↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-X-Z↓

rel-X↑-CZ↓ : (₂₊ n) TRel, CZ • X ↑ === X ↑ • Z ↓ • CZ
rel-X↑-CZ↓ {0}    = TP.srel rel-X↑-CZᴮ
rel-X↑-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same rel-X↑-CZ↓

rel-X↓-CZ↓ : (₂₊ n) TRel, CZ • X ↓ === X ↓ • Z ↑ • CZ
rel-X↓-CZ↓ {0}    = TP.srel rel-X↓-CZᴮ
rel-X↓-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same rel-X↓-CZ↓

comm-Z-CZ↓ : (₂₊ n) TRel, Z • CZ === CZ • Z
comm-Z-CZ↓ {0}    = TP.srel comm-Z-CZᴮ
comm-Z-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-Z-CZ↓

comm-Z↑-CZ↓ : (₂₊ n) TRel, Z ↑ • CZ === CZ • Z ↑
comm-Z↑-CZ↓ {0}    = TP.srel comm-Z↑-CZᴮ
comm-Z↑-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-Z↑-CZ↓

order-CZ↓ : (₂₊ n) TRel, CZ ^ p === ε
order-CZ↓ {0}    = TP.srel order-CZᴮ
order-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-CZ↓

comm-CZ-S↓↓ : (₂₊ n) TRel, CZ • S ↓ === S ↓ • CZ
comm-CZ-S↓↓ {0}    = TP.srel comm-CZ-S↓ᴮ
comm-CZ-S↓↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-CZ-S↓↓

comm-CZ-S↑↓ : (₂₊ n) TRel, CZ • S ↑ === S ↑ • CZ
comm-CZ-S↑↓ {0}    = TP.srel comm-CZ-S↑ᴮ
comm-CZ-S↑↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-CZ-S↑↓

selinger-c10↓ : (₂₊ n) TRel, CZ • H ↑ • CZ • X ↑ • Z ↑ ===
      S ↑ ^ p-1 • H ↑ • S ↑ ^ p-1 • CZ • H ↑ • S ↑ ^ p-1 • S ↓ ^ p-1
selinger-c10↓ {0}    = TP.srel selinger-c10ᴮ
selinger-c10↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same selinger-c10↓

selinger-c11↓ : (₂₊ n) TRel, CZ • H ↓ • CZ • X ↓ • Z ↓ ===
      S ↓ ^ p-1 • H ↓ • S ↓ ^ p-1 • CZ • H ↓ • S ↓ ^ p-1 • S ↑ ^ p-1
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
  pad Base.order-SH = PB.axiom order-SH↓
  pad Base.comm-HHSHHS = PB.axiom comm-HHSHHS↓
  pad Base.order-H = PB.axiom order-H↓
  pad (Base.M-power k) = PB.axiom (M-power↓ k)
  pad Base.semi-MR = PB.axiom semi-MR↓
  pad Base.semi-M↑CZ = PB.axiom semi-M↑CZ↓
  pad Base.semi-M↓CZ = PB.axiom semi-M↓CZ↓
  pad Base.comm-X-Z = PB.axiom comm-X-Z↓
  pad Base.rel-X↑-CZ = PB.axiom rel-X↑-CZ↓
  pad Base.rel-X↓-CZ = PB.axiom rel-X↓-CZ↓
  pad Base.comm-Z-CZ = PB.axiom comm-Z-CZ↓
  pad Base.comm-Z↑-CZ = PB.axiom comm-Z↑-CZ↓
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
  unpad order-SHᴮ = PB.axiom (srel Base.order-SH)
  unpad comm-HHSHHSᴮ = PB.axiom (srel Base.comm-HHSHHS)
  unpad order-Hᴮ = PB.axiom (srel Base.order-H)
  unpad (M-powerᴮ k) = PB.axiom (srel (Base.M-power k))
  unpad semi-MRᴮ = PB.axiom (srel Base.semi-MR)
  unpad semi-M↑CZᴮ = PB.axiom (srel Base.semi-M↑CZ)
  unpad semi-M↓CZᴮ = PB.axiom (srel Base.semi-M↓CZ)
  unpad comm-X-Zᴮ = PB.axiom (srel Base.comm-X-Z)
  unpad rel-X↑-CZᴮ = PB.axiom (srel Base.rel-X↑-CZ)
  unpad rel-X↓-CZᴮ = PB.axiom (srel Base.rel-X↓-CZ)
  unpad comm-Z-CZᴮ = PB.axiom (srel Base.comm-Z-CZ)
  unpad comm-Z↑-CZᴮ = PB.axiom (srel Base.comm-Z↑-CZ)
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
  srel-⇓ Base.order-SH = E.axiom≡ ⇓-same ⇓-same (srel Base.order-SH)
  srel-⇓ Base.comm-HHSHHS = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-HHSHHS)
  srel-⇓ Base.order-H = E.axiom≡ ⇓-same ⇓-same (srel Base.order-H)
  srel-⇓ (Base.M-power k) = E.axiom≡ ⇓-same ⇓-same (srel (Base.M-power k))
  srel-⇓ Base.semi-MR = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-MR)
  srel-⇓ Base.semi-M↑CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-M↑CZ)
  srel-⇓ Base.semi-M↓CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-M↓CZ)
  srel-⇓ Base.comm-X-Z = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-X-Z)
  srel-⇓ Base.rel-X↑-CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.rel-X↑-CZ)
  srel-⇓ Base.rel-X↓-CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.rel-X↓-CZ)
  srel-⇓ Base.comm-Z-CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-Z-CZ)
  srel-⇓ Base.comm-Z↑-CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-Z↑-CZ)
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
