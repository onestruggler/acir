------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 1 with its scalars erased: the rules on their own wires,
-- padded by Circuit.TopPad, give the same congruence as Syntactics'
-- rules at every width, lifted by Circuit.Base's Lift-Relation
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
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.TopPad
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
open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Syntactics p-3 p-prime g* g-gen
open Clifford-Relations
open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.ModScalar.Lemmas.GroupLike p-3 p-prime g* g-gen using (module Paper-GroupLike)
open Paper-GroupLike using (grouplike)

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
  order-Hᴮ : 1 Base, H ^ 2 === XM₋₁
  M-powerᴮ : ∀ k → 1 Base, XMg^ k === XM (g^ k)
  semi-MSᴮ : 1 Base, XMg • S ===
        Z^ ((₁ + - g) * 1/2 * (g⁻¹ * g⁻¹)) • S^ (g⁻¹ * g⁻¹) • XMg
  comm-HHSHHSᴮ : 1 Base, H • H • S • H • H • S === S • H • H • S • H • H
  order-CZᴮ : 2 Base, CZ ^ p === ε
  order-Exᴮ : 2 Base, Ex ^ 2 === ε
  comm-CZ-S↑ᴮ : 2 Base, CZ • S ↑ === S ↑ • CZ
  semi-M↑CZᴮ : 2 Base, XMg ↑ • CZ^ g === CZ • XMg ↑
  semi-Ex-S↑ᴮ : 2 Base, Ex • S ↑ === S ↓ • Ex
  semi-Ex-H↑ᴮ : 2 Base, Ex • H ↑ === H ↓ • Ex
  blake-c12ᴮ : 2 Base, (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ
  yang-baxterᴮ : 3 Base, Ex ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • Ex ↓
  cz-slideᴮ : 3 Base, Ex ↓ • Ex ↑ • CZ === CZ ↑ • Ex ↓ • Ex ↑
  semi-CX↑-CZ↓ᴮ : 3 Base, CZ ↓ • CX ↑ === CZ02 • CX ↑ • CZ ↓

module TP = Circuit.TopPad.Top-Pad SympGate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad SympGate Base._SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: one wire wider
-- its words are the same words, up to the powers ⇓ does not compute
-- through (⇓-same).

order-S↓ : (₁₊ n) TRel, S ^ p === ε
order-S↓ {0}    = TP.srel order-Sᴮ
order-S↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-S↓

order-H↓ : (₁₊ n) TRel, H ^ 2 === XM₋₁
order-H↓ {0}    = TP.srel order-Hᴮ
order-H↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-H↓

M-power↓ : ∀ k → (₁₊ n) TRel, XMg^ k === XM (g^ k)
M-power↓ {0}    k = TP.srel (M-powerᴮ k)
M-power↓ {₁₊ n} k = E.cong↓≡ ⇓-same ⇓-same (M-power↓ k)

semi-MS↓ : (₁₊ n) TRel, XMg • S ===
      Z^ ((₁ + - g) * 1/2 * (g⁻¹ * g⁻¹)) • S^ (g⁻¹ * g⁻¹) • XMg
semi-MS↓ {0}    = TP.srel semi-MSᴮ
semi-MS↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-MS↓

comm-HHSHHS↓ : (₁₊ n) TRel, H • H • S • H • H • S === S • H • H • S • H • H
comm-HHSHHS↓ {0}    = TP.srel comm-HHSHHSᴮ
comm-HHSHHS↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-HHSHHS↓

order-CZ↓ : (₂₊ n) TRel, CZ ^ p === ε
order-CZ↓ {0}    = TP.srel order-CZᴮ
order-CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-CZ↓

order-Ex↓ : (₂₊ n) TRel, Ex ^ 2 === ε
order-Ex↓ {0}    = TP.srel order-Exᴮ
order-Ex↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same order-Ex↓

comm-CZ-S↑↓ : (₂₊ n) TRel, CZ • S ↑ === S ↑ • CZ
comm-CZ-S↑↓ {0}    = TP.srel comm-CZ-S↑ᴮ
comm-CZ-S↑↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same comm-CZ-S↑↓

semi-M↑CZ↓ : (₂₊ n) TRel, XMg ↑ • CZ^ g === CZ • XMg ↑
semi-M↑CZ↓ {0}    = TP.srel semi-M↑CZᴮ
semi-M↑CZ↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-M↑CZ↓

semi-Ex-S↑↓ : (₂₊ n) TRel, Ex • S ↑ === S ↓ • Ex
semi-Ex-S↑↓ {0}    = TP.srel semi-Ex-S↑ᴮ
semi-Ex-S↑↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-Ex-S↑↓

semi-Ex-H↑↓ : (₂₊ n) TRel, Ex • H ↑ === H ↓ • Ex
semi-Ex-H↑↓ {0}    = TP.srel semi-Ex-H↑ᴮ
semi-Ex-H↑↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-Ex-H↑↓

blake-c12↓ : (₂₊ n) TRel, (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ===
      CZ
blake-c12↓ {0}    = TP.srel blake-c12ᴮ
blake-c12↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same blake-c12↓

yang-baxter↓ : (₃₊ n) TRel, Ex ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • Ex ↓
yang-baxter↓ {0}    = TP.srel yang-baxterᴮ
yang-baxter↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same yang-baxter↓

cz-slide↓ : (₃₊ n) TRel, Ex ↓ • Ex ↑ • CZ === CZ ↑ • Ex ↓ • Ex ↑
cz-slide↓ {0}    = TP.srel cz-slideᴮ
cz-slide↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same cz-slide↓

semi-CX↑-CZ↓↓ : (₃₊ n) TRel, CZ ↓ • CX ↑ === CZ02 • CX ↑ • CZ ↓
semi-CX↑-CZ↓↓ {0}    = TP.srel semi-CX↑-CZ↓ᴮ
semi-CX↑-CZ↓↓ {₁₊ n} = E.cong↓≡ ⇓-same ⇓-same semi-CX↑-CZ↓↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : Base._SRel,_===_ n w v → n ⊢ᵀ w ≈ v
  pad Base.order-S = PB.axiom order-S↓
  pad Base.order-H = PB.axiom order-H↓
  pad (Base.M-power k) = PB.axiom (M-power↓ k)
  pad Base.semi-MS = PB.axiom semi-MS↓
  pad Base.comm-HHSHHS = PB.axiom comm-HHSHHS↓
  pad Base.order-CZ = PB.axiom order-CZ↓
  pad Base.order-Ex = PB.axiom order-Ex↓
  pad Base.comm-CZ-S↑ = PB.axiom comm-CZ-S↑↓
  pad Base.semi-M↑CZ = PB.axiom semi-M↑CZ↓
  pad Base.semi-Ex-S↑ = PB.axiom semi-Ex-S↑↓
  pad Base.semi-Ex-H↑ = PB.axiom semi-Ex-H↑↓
  pad Base.blake-c12 = PB.axiom blake-c12↓
  pad Base.yang-baxter = PB.axiom yang-baxter↓
  pad Base.cz-slide = PB.axiom cz-slide↓
  pad Base.semi-CX↑-CZ↓ = PB.axiom semi-CX↑-CZ↓↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad order-Sᴮ = PB.axiom (srel Base.order-S)
  unpad order-Hᴮ = PB.axiom (srel Base.order-H)
  unpad (M-powerᴮ k) = PB.axiom (srel (Base.M-power k))
  unpad semi-MSᴮ = PB.axiom (srel Base.semi-MS)
  unpad comm-HHSHHSᴮ = PB.axiom (srel Base.comm-HHSHHS)
  unpad order-CZᴮ = PB.axiom (srel Base.order-CZ)
  unpad order-Exᴮ = PB.axiom (srel Base.order-Ex)
  unpad comm-CZ-S↑ᴮ = PB.axiom (srel Base.comm-CZ-S↑)
  unpad semi-M↑CZᴮ = PB.axiom (srel Base.semi-M↑CZ)
  unpad semi-Ex-S↑ᴮ = PB.axiom (srel Base.semi-Ex-S↑)
  unpad semi-Ex-H↑ᴮ = PB.axiom (srel Base.semi-Ex-H↑)
  unpad blake-c12ᴮ = PB.axiom (srel Base.blake-c12)
  unpad yang-baxterᴮ = PB.axiom (srel Base.yang-baxter)
  unpad cz-slideᴮ = PB.axiom (srel Base.cz-slide)
  unpad semi-CX↑-CZ↓ᴮ = PB.axiom (srel Base.semi-CX↑-CZ↓)

  srel-⇓ : Base._SRel,_===_ n w v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ Base.order-S = E.axiom≡ ⇓-same ⇓-same (srel Base.order-S)
  srel-⇓ Base.order-H = E.axiom≡ ⇓-same ⇓-same (srel Base.order-H)
  srel-⇓ (Base.M-power k) = E.axiom≡ ⇓-same ⇓-same (srel (Base.M-power k))
  srel-⇓ Base.semi-MS = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-MS)
  srel-⇓ Base.comm-HHSHHS = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-HHSHHS)
  srel-⇓ Base.order-CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.order-CZ)
  srel-⇓ Base.order-Ex = E.axiom≡ ⇓-same ⇓-same (srel Base.order-Ex)
  srel-⇓ Base.comm-CZ-S↑ = E.axiom≡ ⇓-same ⇓-same (srel Base.comm-CZ-S↑)
  srel-⇓ Base.semi-M↑CZ = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-M↑CZ)
  srel-⇓ Base.semi-Ex-S↑ = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-Ex-S↑)
  srel-⇓ Base.semi-Ex-H↑ = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-Ex-H↑)
  srel-⇓ Base.blake-c12 = E.axiom≡ ⇓-same ⇓-same (srel Base.blake-c12)
  srel-⇓ Base.yang-baxter = E.axiom≡ ⇓-same ⇓-same (srel Base.yang-baxter)
  srel-⇓ Base.cz-slide = E.axiom≡ ⇓-same ⇓-same (srel Base.cz-slide)
  srel-⇓ Base.semi-CX↑-CZ↓ = E.axiom≡ ⇓-same ⇓-same (srel Base.semi-CX↑-CZ↓)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
