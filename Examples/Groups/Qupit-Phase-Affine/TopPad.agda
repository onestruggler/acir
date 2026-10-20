------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake's phase-affine relations at every level: the rules on their own
-- wires, padded by Circuit.TopPad, give the same congruence as
-- Syntactics' rules at every width, lifted by Circuit.Prop's
-- Lift-To-Prop
--
-- An instance of Circuit.Prop.TopPad, which has the swap rules already:
-- each rule that Syntactics states at every width is here stated on its
-- own wires only (its name with ᴮ), its padded form is that rule with
-- idle wires on top (↓), and FamilyRules says, rule by rule, that the
-- two relations have the same rules. Powers whose exponent is not a
-- numeral (S ^ p, S^ k) do not compute under ⇓, so the padded rules and
-- the rules ⇓'d go through Circuit.TopPad.Closed's ⇓-same.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.TopPad (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Notations
open import Word.Base

import Circuit.TopPad
import Circuit.Prop.TopPad
import Presentation.Base as PB

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Product.Base using (proj₁ ; _×_ ; _,_)
open import Reflection using (Name)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Examples.Groups.Qupit-Phase-Affine.Field p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; 2F ; half ; binom2 ; binom3 ; _+_ ; _*_
        ; -_ ; _-_ ; 1* ; -1* ; _⊛_)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
import Examples.Groups.Qupit-Phase-Affine.Syntactics as QS
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (grouplike)

open Circuit.TopPad Gate using (_⇓)
open import Circuit.TopPad.Closed Gate using (⇓-same ; ⇓-same-by)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

-- The derived diagonals, which several rules share, ⇓'d once each: the
-- traversal of a rule stops at them rather than going through their
-- definitions again (CCZ has seventeen factors, most of them stuck
-- powers).
CZ-⇓ : ∀ {n} .(h : 2 ≤ lv) → _⇓ {₂₊ n} (CZ h) ≡ CZ h
CZ-⇓ h = ⇓-same

CCZ-⇓ : ∀ {n} .(h : 3 ≤ lv) → _⇓ {₃₊ n} (CCZ h) ≡ CCZ h
CCZ-⇓ h = ⇓-same

-- (Quoted from the module itself: a goal shows the original, not the
-- copy an applied import makes.)
lemmas₀ : List (Name × Name × ℕ)
lemmas₀ = (quote QS.CZ , quote CZ-⇓ , 1) ∷ (quote QS.CCZ , quote CCZ-⇓ , 1) ∷ []

CS-⇓ : ∀ {n} .(h : 3 ≤ lv) → _⇓ {₂₊ n} (CS h) ≡ CS h
CS-⇓ h = ⇓-same-by lemmas₀

lemmas : List (Name × Name × ℕ)
lemmas = (quote QS.CS , quote CS-⇓ , 1) ∷ lemmas₀

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  ax1ᴮ : 1 Base, M⟨ 1* ⟩ === ε
  ax2ᴮ : (x y : F*) → 1 Base, M⟨ y ⟩ • M⟨ x ⟩ === M⟨ x ⊛ y ⟩
  ax3ᴮ : (x : F*) → 1 Base, X ^ᶠ proj₁ x • M⟨ x ⟩ • X ^ᶠ (- 1F) === M⟨ x ⟩
  ax4ᴮ : (x : F*) → 2 Base, CX • M⟨ x ⟩ ↑ === M⟨ x ⟩ ↑ • CX ^ᶠ proj₁ x
  ax5ᴮ : (x : F*) → 2 Base, CX ^ᶠ (- proj₁ x) • M⟨ x ⟩ • CX === M⟨ x ⟩
  ax6ᴮ : 2 Base, CX • X ↑ === X • X ↑ • CX
  ax7ᴮ : 2 Base,
        SWAP ===
        M⟨ -1* ⟩ ↑ • (SWAP • CX ^ᶠ (- 1F) • SWAP) • CX • (SWAP •
        CX ^ᶠ (- 1F) • SWAP)
  ax8ᴮ : 3 Base, CX ↑ • CX • CX₂₀ === CX • CX ↑
  ax19ᴮ : .(h : 1 ≤ lv) → 0 Base, ω h ^ p === ε
  ax20ᴮ : .(h : 1 ≤ lv) → 1 Base, Z h ^ p === ε
  ax21ᴮ : .(h : 1 ≤ lv) → 2 Base, CX • Z h • Z h ↑ === Z h • CX
  ax22ᴮ : .(h : 1 ≤ lv) (x : F*) → 1 Base, Z h • M⟨ x ⟩ ===
        M⟨ x ⟩ • Z h ^ᶠ proj₁ x
  ax23ᴮ : .(h : 1 ≤ lv) → 1 Base, Z h • X === ω h • X • Z h
  ax24ᴮ : .(h : 2 ≤ lv) → 1 Base, S h ^ p === ε
  ax25ᴮ : .(h : 2 ≤ lv) → 1 Base, S h • X === X • Z (lin₂ h) • S h
  ax26ᴮ : .(h : 2 ≤ lv) → 1 Base, S h • Z (lin₂ h) === Z (lin₂ h) • S h
  ax27ᴮ : .(h : 2 ≤ lv) (x : F*) → 1 Base, S h • M⟨ x ⟩ ===
        M⟨ x ⟩ • Z (lin₂ h) ^ᶠ binom2 (proj₁ x) • S h ^ᶠ (proj₁ x * proj₁ x)
  ax28ᴮ : .(h : 2 ≤ lv) → 2 Base,
        M⟨ -1* ⟩ ↑ • CZ h ^ᶠ (- 1F) • M⟨ -1* ⟩ ↑ ===
        CZ h
  ax29ᴮ : .(h : 2 ≤ lv) → 2 Base, CX • S h ↑ === S h ↑ • CX
  ax30ᴮ : .(h : 2 ≤ lv) → 3 Base, CZ h • CX ↑ === CX ↑ • CZ h • CZ₂₀ h
  ax31ᴮ : .(h : 3 ≤ lv) → 1 Base, T h ^ p === ε
  ax32ᴮ : .(h : 3 ≤ lv) (x : F*) → 1 Base,
        M⟨ x ⟩ • S (quad₃ h) ^ᶠ (2F * proj₁ x * binom2 (proj₁ x)) •
        Z (lin₃ h) ^ᶠ binom3 (proj₁ x) •
        T h ^ᶠ (proj₁ x * proj₁ x * proj₁ x) ===
        T h • M⟨ x ⟩
  ax33ᴮ : .(h : 3 ≤ lv) → 1 Base, T h • S (quad₃ h) === S (quad₃ h) • T h
  ax34ᴮ : .(h : 3 ≤ lv) → 1 Base, T h • X === X • T h • S (quad₃ h)
  ax35ᴮ : .(h : 3 ≤ lv) (a : F*) → 2 Base,
        M⟨ a ⟩ • CZ (quad₃ h) ^ᶠ binom2 (proj₁ a) •
        CS h ^ᶠ (proj₁ a * proj₁ a) ===
        CS h • M⟨ a ⟩
  ax36ᴮ : .(h : 3 ≤ lv) → 1 Base, T h • Z (lin₃ h) === Z (lin₃ h) • T h
  ax37ᴮ : .(h : 3 ≤ lv) (x : F*) → 2 Base, M⟨ x ⟩ ↑ • CS h ^ᶠ proj₁ x ===
        CS h • M⟨ x ⟩ ↑
  ax38ᴮ : .(h : 3 ≤ lv) → 3 Base, CX • CS₂₀ h • CS h ↑ • CCZ h === CS₂₀ h • CX
  ax39ᴮ : .(h : 3 ≤ lv) → 2 Base, CX • T h ↑ === T h ↑ • CX
  ax40ᴮ : .(h : 3 ≤ lv) (x : F*) → 3 Base, M⟨ x ⟩ ↑ ↑ • CCZ h ^ᶠ proj₁ x ===
        CCZ h • M⟨ x ⟩ ↑ ↑
  ax41ᴮ : .(h : 3 ≤ lv) → 4 Base, CX ↑ ↑ • CCZ₃₁₀ h • CCZ h === CCZ h • CX ↑ ↑
  ax42ᴮ : .(h : 3 ≤ lv) → 3 Base, CX ↑ • CS h • CS₂₀ h === CS h • CX ↑

module P  = Circuit.Prop.TopPad Gate SWAP-gate
module E  = P.Lift≅Top-Pad-Prop _SRel,_===_ _Base,_===_
module TP = E.TP

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- The equations ⇓-same proves for a rule: each side ⇓'d is that side
-- one wire wider.  Proved once per rule, for its padded form and for
-- srel-⇓ below, which would otherwise each prove them.

import Relation.Binary.PropositionalEquality as TopPad-≡

⇓ˡ ⇓ʳ : ∀ {n w v w′ v′} → n SRel, w === v → (₁₊ n) SRel, w′ === v′ → Set
⇓ˡ {w = w} {w′ = w′} _ _ = TopPad-≡._≡_ (w ⇓) w′
⇓ʳ {v = v} {v′ = v′} _ _ = TopPad-≡._≡_ (v ⇓) v′

ax1⇓ˡ : ⇓ˡ {(₁₊ n)} ax1 ax1
ax1⇓ˡ = (⇓-same-by lemmas)

ax1⇓ʳ : ⇓ʳ {(₁₊ n)} ax1 ax1
ax1⇓ʳ = (⇓-same-by lemmas)

ax2⇓ˡ : (x y : F*) → ⇓ˡ {(₁₊ n)} (ax2 x y) (ax2 x y)
ax2⇓ˡ x y = (⇓-same-by lemmas)

ax2⇓ʳ : (x y : F*) → ⇓ʳ {(₁₊ n)} (ax2 x y) (ax2 x y)
ax2⇓ʳ x y = (⇓-same-by lemmas)

ax3⇓ˡ : (x : F*) → ⇓ˡ {(₁₊ n)} (ax3 x) (ax3 x)
ax3⇓ˡ x = (⇓-same-by lemmas)

ax3⇓ʳ : (x : F*) → ⇓ʳ {(₁₊ n)} (ax3 x) (ax3 x)
ax3⇓ʳ x = (⇓-same-by lemmas)

ax4⇓ˡ : (x : F*) → ⇓ˡ {(₂₊ n)} (ax4 x) (ax4 x)
ax4⇓ˡ x = (⇓-same-by lemmas)

ax4⇓ʳ : (x : F*) → ⇓ʳ {(₂₊ n)} (ax4 x) (ax4 x)
ax4⇓ʳ x = (⇓-same-by lemmas)

ax5⇓ˡ : (x : F*) → ⇓ˡ {(₂₊ n)} (ax5 x) (ax5 x)
ax5⇓ˡ x = (⇓-same-by lemmas)

ax5⇓ʳ : (x : F*) → ⇓ʳ {(₂₊ n)} (ax5 x) (ax5 x)
ax5⇓ʳ x = (⇓-same-by lemmas)

ax6⇓ˡ : ⇓ˡ {(₂₊ n)} ax6 ax6
ax6⇓ˡ = (⇓-same-by lemmas)

ax6⇓ʳ : ⇓ʳ {(₂₊ n)} ax6 ax6
ax6⇓ʳ = (⇓-same-by lemmas)

ax7⇓ˡ : ⇓ˡ {(₂₊ n)} ax7 ax7
ax7⇓ˡ = (⇓-same-by lemmas)

ax7⇓ʳ : ⇓ʳ {(₂₊ n)} ax7 ax7
ax7⇓ʳ = (⇓-same-by lemmas)

ax8⇓ˡ : ⇓ˡ {(₃₊ n)} ax8 ax8
ax8⇓ˡ = (⇓-same-by lemmas)

ax8⇓ʳ : ⇓ʳ {(₃₊ n)} ax8 ax8
ax8⇓ʳ = (⇓-same-by lemmas)

ax19⇓ˡ : .(h : 1 ≤ lv) → ⇓ˡ {n} (ax19 h) (ax19 h)
ax19⇓ˡ h = (⇓-same-by lemmas)

ax19⇓ʳ : .(h : 1 ≤ lv) → ⇓ʳ {n} (ax19 h) (ax19 h)
ax19⇓ʳ h = (⇓-same-by lemmas)

ax20⇓ˡ : .(h : 1 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax20 h) (ax20 h)
ax20⇓ˡ h = (⇓-same-by lemmas)

ax20⇓ʳ : .(h : 1 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax20 h) (ax20 h)
ax20⇓ʳ h = (⇓-same-by lemmas)

ax21⇓ˡ : .(h : 1 ≤ lv) → ⇓ˡ {(₂₊ n)} (ax21 h) (ax21 h)
ax21⇓ˡ h = (⇓-same-by lemmas)

ax21⇓ʳ : .(h : 1 ≤ lv) → ⇓ʳ {(₂₊ n)} (ax21 h) (ax21 h)
ax21⇓ʳ h = (⇓-same-by lemmas)

ax22⇓ˡ : .(h : 1 ≤ lv) (x : F*) → ⇓ˡ {(₁₊ n)} (ax22 h x) (ax22 h x)
ax22⇓ˡ h x = (⇓-same-by lemmas)

ax22⇓ʳ : .(h : 1 ≤ lv) (x : F*) → ⇓ʳ {(₁₊ n)} (ax22 h x) (ax22 h x)
ax22⇓ʳ h x = (⇓-same-by lemmas)

ax23⇓ˡ : .(h : 1 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax23 h) (ax23 h)
ax23⇓ˡ h = (⇓-same-by lemmas)

ax23⇓ʳ : .(h : 1 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax23 h) (ax23 h)
ax23⇓ʳ h = (⇓-same-by lemmas)

ax24⇓ˡ : .(h : 2 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax24 h) (ax24 h)
ax24⇓ˡ h = (⇓-same-by lemmas)

ax24⇓ʳ : .(h : 2 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax24 h) (ax24 h)
ax24⇓ʳ h = (⇓-same-by lemmas)

ax25⇓ˡ : .(h : 2 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax25 h) (ax25 h)
ax25⇓ˡ h = (⇓-same-by lemmas)

ax25⇓ʳ : .(h : 2 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax25 h) (ax25 h)
ax25⇓ʳ h = (⇓-same-by lemmas)

ax26⇓ˡ : .(h : 2 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax26 h) (ax26 h)
ax26⇓ˡ h = (⇓-same-by lemmas)

ax26⇓ʳ : .(h : 2 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax26 h) (ax26 h)
ax26⇓ʳ h = (⇓-same-by lemmas)

ax27⇓ˡ : .(h : 2 ≤ lv) (x : F*) → ⇓ˡ {(₁₊ n)} (ax27 h x) (ax27 h x)
ax27⇓ˡ h x = (⇓-same-by lemmas)

ax27⇓ʳ : .(h : 2 ≤ lv) (x : F*) → ⇓ʳ {(₁₊ n)} (ax27 h x) (ax27 h x)
ax27⇓ʳ h x = (⇓-same-by lemmas)

ax28⇓ˡ : .(h : 2 ≤ lv) → ⇓ˡ {(₂₊ n)} (ax28 h) (ax28 h)
ax28⇓ˡ h = (⇓-same-by lemmas)

ax28⇓ʳ : .(h : 2 ≤ lv) → ⇓ʳ {(₂₊ n)} (ax28 h) (ax28 h)
ax28⇓ʳ h = (⇓-same-by lemmas)

ax29⇓ˡ : .(h : 2 ≤ lv) → ⇓ˡ {(₂₊ n)} (ax29 h) (ax29 h)
ax29⇓ˡ h = (⇓-same-by lemmas)

ax29⇓ʳ : .(h : 2 ≤ lv) → ⇓ʳ {(₂₊ n)} (ax29 h) (ax29 h)
ax29⇓ʳ h = (⇓-same-by lemmas)

ax30⇓ˡ : .(h : 2 ≤ lv) → ⇓ˡ {(₃₊ n)} (ax30 h) (ax30 h)
ax30⇓ˡ h = (⇓-same-by lemmas)

ax30⇓ʳ : .(h : 2 ≤ lv) → ⇓ʳ {(₃₊ n)} (ax30 h) (ax30 h)
ax30⇓ʳ h = (⇓-same-by lemmas)

ax31⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax31 h) (ax31 h)
ax31⇓ˡ h = (⇓-same-by lemmas)

ax31⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax31 h) (ax31 h)
ax31⇓ʳ h = (⇓-same-by lemmas)

ax32⇓ˡ : .(h : 3 ≤ lv) (x : F*) → ⇓ˡ {(₁₊ n)} (ax32 h x) (ax32 h x)
ax32⇓ˡ h x = (⇓-same-by lemmas)

ax32⇓ʳ : .(h : 3 ≤ lv) (x : F*) → ⇓ʳ {(₁₊ n)} (ax32 h x) (ax32 h x)
ax32⇓ʳ h x = (⇓-same-by lemmas)

ax33⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax33 h) (ax33 h)
ax33⇓ˡ h = (⇓-same-by lemmas)

ax33⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax33 h) (ax33 h)
ax33⇓ʳ h = (⇓-same-by lemmas)

ax34⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax34 h) (ax34 h)
ax34⇓ˡ h = (⇓-same-by lemmas)

ax34⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax34 h) (ax34 h)
ax34⇓ʳ h = (⇓-same-by lemmas)

ax35⇓ˡ : .(h : 3 ≤ lv) (a : F*) → ⇓ˡ {(₂₊ n)} (ax35 h a) (ax35 h a)
ax35⇓ˡ h a = (⇓-same-by lemmas)

ax35⇓ʳ : .(h : 3 ≤ lv) (a : F*) → ⇓ʳ {(₂₊ n)} (ax35 h a) (ax35 h a)
ax35⇓ʳ h a = (⇓-same-by lemmas)

ax36⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₁₊ n)} (ax36 h) (ax36 h)
ax36⇓ˡ h = (⇓-same-by lemmas)

ax36⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₁₊ n)} (ax36 h) (ax36 h)
ax36⇓ʳ h = (⇓-same-by lemmas)

ax37⇓ˡ : .(h : 3 ≤ lv) (x : F*) → ⇓ˡ {(₂₊ n)} (ax37 h x) (ax37 h x)
ax37⇓ˡ h x = (⇓-same-by lemmas)

ax37⇓ʳ : .(h : 3 ≤ lv) (x : F*) → ⇓ʳ {(₂₊ n)} (ax37 h x) (ax37 h x)
ax37⇓ʳ h x = (⇓-same-by lemmas)

ax38⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₃₊ n)} (ax38 h) (ax38 h)
ax38⇓ˡ h = (⇓-same-by lemmas)

ax38⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₃₊ n)} (ax38 h) (ax38 h)
ax38⇓ʳ h = (⇓-same-by lemmas)

ax39⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₂₊ n)} (ax39 h) (ax39 h)
ax39⇓ˡ h = (⇓-same-by lemmas)

ax39⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₂₊ n)} (ax39 h) (ax39 h)
ax39⇓ʳ h = (⇓-same-by lemmas)

ax40⇓ˡ : .(h : 3 ≤ lv) (x : F*) → ⇓ˡ {(₃₊ n)} (ax40 h x) (ax40 h x)
ax40⇓ˡ h x = (⇓-same-by lemmas)

ax40⇓ʳ : .(h : 3 ≤ lv) (x : F*) → ⇓ʳ {(₃₊ n)} (ax40 h x) (ax40 h x)
ax40⇓ʳ h x = (⇓-same-by lemmas)

ax41⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₄₊ n)} (ax41 h) (ax41 h)
ax41⇓ˡ h = (⇓-same-by lemmas)

ax41⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₄₊ n)} (ax41 h) (ax41 h)
ax41⇓ʳ h = (⇓-same-by lemmas)

ax42⇓ˡ : .(h : 3 ≤ lv) → ⇓ˡ {(₃₊ n)} (ax42 h) (ax42 h)
ax42⇓ˡ h = (⇓-same-by lemmas)

ax42⇓ʳ : .(h : 3 ≤ lv) → ⇓ʳ {(₃₊ n)} (ax42 h) (ax42 h)
ax42⇓ʳ h = (⇓-same-by lemmas)

-- Each rule on the bottom wires of every wider circuit: one wire wider
-- its words are the same words, up to the powers ⇓ does not compute
-- through (⇓-same).

ax1↓ : (₁₊ n) TRel, M⟨ 1* ⟩ === ε
ax1↓ {0}    = TP.srel (E.sbase ax1ᴮ)
ax1↓ {₁₊ n} = E.E.cong↓≡ ax1⇓ˡ ax1⇓ʳ ax1↓

ax2↓ : (x y : F*) → (₁₊ n) TRel, M⟨ y ⟩ • M⟨ x ⟩ === M⟨ x ⊛ y ⟩
ax2↓ {0}    x y = TP.srel (E.sbase (ax2ᴮ x y))
ax2↓ {₁₊ n} x y = E.E.cong↓≡ (ax2⇓ˡ x y) (ax2⇓ʳ x y) (ax2↓ x y)

ax3↓ : (x : F*) → (₁₊ n) TRel, X ^ᶠ proj₁ x • M⟨ x ⟩ • X ^ᶠ (- 1F) === M⟨ x ⟩
ax3↓ {0}    x = TP.srel (E.sbase (ax3ᴮ x))
ax3↓ {₁₊ n} x = E.E.cong↓≡ (ax3⇓ˡ x) (ax3⇓ʳ x) (ax3↓ x)

ax4↓ : (x : F*) → (₂₊ n) TRel, CX • M⟨ x ⟩ ↑ === M⟨ x ⟩ ↑ • CX ^ᶠ proj₁ x
ax4↓ {0}    x = TP.srel (E.sbase (ax4ᴮ x))
ax4↓ {₁₊ n} x = E.E.cong↓≡ (ax4⇓ˡ x) (ax4⇓ʳ x) (ax4↓ x)

ax5↓ : (x : F*) → (₂₊ n) TRel, CX ^ᶠ (- proj₁ x) • M⟨ x ⟩ • CX === M⟨ x ⟩
ax5↓ {0}    x = TP.srel (E.sbase (ax5ᴮ x))
ax5↓ {₁₊ n} x = E.E.cong↓≡ (ax5⇓ˡ x) (ax5⇓ʳ x) (ax5↓ x)

ax6↓ : (₂₊ n) TRel, CX • X ↑ === X • X ↑ • CX
ax6↓ {0}    = TP.srel (E.sbase ax6ᴮ)
ax6↓ {₁₊ n} = E.E.cong↓≡ ax6⇓ˡ ax6⇓ʳ ax6↓

ax7↓ : (₂₊ n) TRel,
      SWAP ===
      M⟨ -1* ⟩ ↑ • (SWAP • CX ^ᶠ (- 1F) • SWAP) • CX • (SWAP •
      CX ^ᶠ (- 1F) • SWAP)
ax7↓ {0}    = TP.srel (E.sbase ax7ᴮ)
ax7↓ {₁₊ n} = E.E.cong↓≡ ax7⇓ˡ ax7⇓ʳ ax7↓

ax8↓ : (₃₊ n) TRel, CX ↑ • CX • CX₂₀ === CX • CX ↑
ax8↓ {0}    = TP.srel (E.sbase ax8ᴮ)
ax8↓ {₁₊ n} = E.E.cong↓≡ ax8⇓ˡ ax8⇓ʳ ax8↓

ax19↓ : .(h : 1 ≤ lv) → n TRel, ω h ^ p === ε
ax19↓ {0}    h = TP.srel (E.sbase (ax19ᴮ h))
ax19↓ {₁₊ n} h = E.E.cong↓≡ (ax19⇓ˡ h) (ax19⇓ʳ h) (ax19↓ h)

ax20↓ : .(h : 1 ≤ lv) → (₁₊ n) TRel, Z h ^ p === ε
ax20↓ {0}    h = TP.srel (E.sbase (ax20ᴮ h))
ax20↓ {₁₊ n} h = E.E.cong↓≡ (ax20⇓ˡ h) (ax20⇓ʳ h) (ax20↓ h)

ax21↓ : .(h : 1 ≤ lv) → (₂₊ n) TRel, CX • Z h • Z h ↑ === Z h • CX
ax21↓ {0}    h = TP.srel (E.sbase (ax21ᴮ h))
ax21↓ {₁₊ n} h = E.E.cong↓≡ (ax21⇓ˡ h) (ax21⇓ʳ h) (ax21↓ h)

ax22↓ : .(h : 1 ≤ lv) (x : F*) → (₁₊ n) TRel, Z h • M⟨ x ⟩ ===
      M⟨ x ⟩ • Z h ^ᶠ proj₁ x
ax22↓ {0}    h x = TP.srel (E.sbase (ax22ᴮ h x))
ax22↓ {₁₊ n} h x = E.E.cong↓≡ (ax22⇓ˡ h x) (ax22⇓ʳ h x) (ax22↓ h x)

ax23↓ : .(h : 1 ≤ lv) → (₁₊ n) TRel, Z h • X === ω h • X • Z h
ax23↓ {0}    h = TP.srel (E.sbase (ax23ᴮ h))
ax23↓ {₁₊ n} h = E.E.cong↓≡ (ax23⇓ˡ h) (ax23⇓ʳ h) (ax23↓ h)

ax24↓ : .(h : 2 ≤ lv) → (₁₊ n) TRel, S h ^ p === ε
ax24↓ {0}    h = TP.srel (E.sbase (ax24ᴮ h))
ax24↓ {₁₊ n} h = E.E.cong↓≡ (ax24⇓ˡ h) (ax24⇓ʳ h) (ax24↓ h)

ax25↓ : .(h : 2 ≤ lv) → (₁₊ n) TRel, S h • X === X • Z (lin₂ h) • S h
ax25↓ {0}    h = TP.srel (E.sbase (ax25ᴮ h))
ax25↓ {₁₊ n} h = E.E.cong↓≡ (ax25⇓ˡ h) (ax25⇓ʳ h) (ax25↓ h)

ax26↓ : .(h : 2 ≤ lv) → (₁₊ n) TRel, S h • Z (lin₂ h) === Z (lin₂ h) • S h
ax26↓ {0}    h = TP.srel (E.sbase (ax26ᴮ h))
ax26↓ {₁₊ n} h = E.E.cong↓≡ (ax26⇓ˡ h) (ax26⇓ʳ h) (ax26↓ h)

ax27↓ : .(h : 2 ≤ lv) (x : F*) → (₁₊ n) TRel, S h • M⟨ x ⟩ ===
      M⟨ x ⟩ • Z (lin₂ h) ^ᶠ binom2 (proj₁ x) • S h ^ᶠ (proj₁ x * proj₁ x)
ax27↓ {0}    h x = TP.srel (E.sbase (ax27ᴮ h x))
ax27↓ {₁₊ n} h x = E.E.cong↓≡ (ax27⇓ˡ h x) (ax27⇓ʳ h x) (ax27↓ h x)

ax28↓ : .(h : 2 ≤ lv) → (₂₊ n) TRel,
      M⟨ -1* ⟩ ↑ • CZ h ^ᶠ (- 1F) • M⟨ -1* ⟩ ↑ ===
      CZ h
ax28↓ {0}    h = TP.srel (E.sbase (ax28ᴮ h))
ax28↓ {₁₊ n} h = E.E.cong↓≡ (ax28⇓ˡ h) (ax28⇓ʳ h) (ax28↓ h)

ax29↓ : .(h : 2 ≤ lv) → (₂₊ n) TRel, CX • S h ↑ === S h ↑ • CX
ax29↓ {0}    h = TP.srel (E.sbase (ax29ᴮ h))
ax29↓ {₁₊ n} h = E.E.cong↓≡ (ax29⇓ˡ h) (ax29⇓ʳ h) (ax29↓ h)

ax30↓ : .(h : 2 ≤ lv) → (₃₊ n) TRel, CZ h • CX ↑ === CX ↑ • CZ h • CZ₂₀ h
ax30↓ {0}    h = TP.srel (E.sbase (ax30ᴮ h))
ax30↓ {₁₊ n} h = E.E.cong↓≡ (ax30⇓ˡ h) (ax30⇓ʳ h) (ax30↓ h)

ax31↓ : .(h : 3 ≤ lv) → (₁₊ n) TRel, T h ^ p === ε
ax31↓ {0}    h = TP.srel (E.sbase (ax31ᴮ h))
ax31↓ {₁₊ n} h = E.E.cong↓≡ (ax31⇓ˡ h) (ax31⇓ʳ h) (ax31↓ h)

ax32↓ : .(h : 3 ≤ lv) (x : F*) → (₁₊ n) TRel,
      M⟨ x ⟩ • S (quad₃ h) ^ᶠ (2F * proj₁ x * binom2 (proj₁ x)) •
      Z (lin₃ h) ^ᶠ binom3 (proj₁ x) •
      T h ^ᶠ (proj₁ x * proj₁ x * proj₁ x) ===
      T h • M⟨ x ⟩
ax32↓ {0}    h x = TP.srel (E.sbase (ax32ᴮ h x))
ax32↓ {₁₊ n} h x = E.E.cong↓≡ (ax32⇓ˡ h x) (ax32⇓ʳ h x) (ax32↓ h x)

ax33↓ : .(h : 3 ≤ lv) → (₁₊ n) TRel, T h • S (quad₃ h) === S (quad₃ h) • T h
ax33↓ {0}    h = TP.srel (E.sbase (ax33ᴮ h))
ax33↓ {₁₊ n} h = E.E.cong↓≡ (ax33⇓ˡ h) (ax33⇓ʳ h) (ax33↓ h)

ax34↓ : .(h : 3 ≤ lv) → (₁₊ n) TRel, T h • X === X • T h • S (quad₃ h)
ax34↓ {0}    h = TP.srel (E.sbase (ax34ᴮ h))
ax34↓ {₁₊ n} h = E.E.cong↓≡ (ax34⇓ˡ h) (ax34⇓ʳ h) (ax34↓ h)

ax35↓ : .(h : 3 ≤ lv) (a : F*) → (₂₊ n) TRel,
      M⟨ a ⟩ • CZ (quad₃ h) ^ᶠ binom2 (proj₁ a) •
      CS h ^ᶠ (proj₁ a * proj₁ a) ===
      CS h • M⟨ a ⟩
ax35↓ {0}    h a = TP.srel (E.sbase (ax35ᴮ h a))
ax35↓ {₁₊ n} h a = E.E.cong↓≡ (ax35⇓ˡ h a) (ax35⇓ʳ h a) (ax35↓ h a)

ax36↓ : .(h : 3 ≤ lv) → (₁₊ n) TRel, T h • Z (lin₃ h) === Z (lin₃ h) • T h
ax36↓ {0}    h = TP.srel (E.sbase (ax36ᴮ h))
ax36↓ {₁₊ n} h = E.E.cong↓≡ (ax36⇓ˡ h) (ax36⇓ʳ h) (ax36↓ h)

ax37↓ : .(h : 3 ≤ lv) (x : F*) → (₂₊ n) TRel, M⟨ x ⟩ ↑ • CS h ^ᶠ proj₁ x ===
      CS h • M⟨ x ⟩ ↑
ax37↓ {0}    h x = TP.srel (E.sbase (ax37ᴮ h x))
ax37↓ {₁₊ n} h x = E.E.cong↓≡ (ax37⇓ˡ h x) (ax37⇓ʳ h x) (ax37↓ h x)

ax38↓ : .(h : 3 ≤ lv) → (₃₊ n) TRel, CX • CS₂₀ h • CS h ↑ • CCZ h ===
      CS₂₀ h • CX
ax38↓ {0}    h = TP.srel (E.sbase (ax38ᴮ h))
ax38↓ {₁₊ n} h = E.E.cong↓≡ (ax38⇓ˡ h) (ax38⇓ʳ h) (ax38↓ h)

ax39↓ : .(h : 3 ≤ lv) → (₂₊ n) TRel, CX • T h ↑ === T h ↑ • CX
ax39↓ {0}    h = TP.srel (E.sbase (ax39ᴮ h))
ax39↓ {₁₊ n} h = E.E.cong↓≡ (ax39⇓ˡ h) (ax39⇓ʳ h) (ax39↓ h)

ax40↓ : .(h : 3 ≤ lv) (x : F*) → (₃₊ n) TRel,
      M⟨ x ⟩ ↑ ↑ • CCZ h ^ᶠ proj₁ x ===
      CCZ h • M⟨ x ⟩ ↑ ↑
ax40↓ {0}    h x = TP.srel (E.sbase (ax40ᴮ h x))
ax40↓ {₁₊ n} h x = E.E.cong↓≡ (ax40⇓ˡ h x) (ax40⇓ʳ h x) (ax40↓ h x)

ax41↓ : .(h : 3 ≤ lv) → (₄₊ n) TRel, CX ↑ ↑ • CCZ₃₁₀ h • CCZ h ===
      CCZ h • CX ↑ ↑
ax41↓ {0}    h = TP.srel (E.sbase (ax41ᴮ h))
ax41↓ {₁₊ n} h = E.E.cong↓≡ (ax41⇓ˡ h) (ax41⇓ʳ h) (ax41↓ h)

ax42↓ : .(h : 3 ≤ lv) → (₃₊ n) TRel, CX ↑ • CS h • CS₂₀ h === CS h • CX ↑
ax42↓ {0}    h = TP.srel (E.sbase (ax42ᴮ h))
ax42↓ {₁₊ n} h = E.E.cong↓≡ (ax42⇓ˡ h) (ax42⇓ʳ h) (ax42↓ h)

------------------------------------------------------------------------
-- The two have the same rules

fam : E.FamilyRules
fam = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n SRel, w === v → n ⊢ᵀ w ≈ v
  pad ax1 = PB.axiom ax1↓
  pad (ax2 x y) = PB.axiom (ax2↓ x y)
  pad (ax3 x) = PB.axiom (ax3↓ x)
  pad (ax4 x) = PB.axiom (ax4↓ x)
  pad (ax5 x) = PB.axiom (ax5↓ x)
  pad ax6 = PB.axiom ax6↓
  pad ax7 = PB.axiom ax7↓
  pad ax8 = PB.axiom ax8↓
  pad (ax19 h) = PB.axiom (ax19↓ h)
  pad (ax20 h) = PB.axiom (ax20↓ h)
  pad (ax21 h) = PB.axiom (ax21↓ h)
  pad (ax22 h x) = PB.axiom (ax22↓ h x)
  pad (ax23 h) = PB.axiom (ax23↓ h)
  pad (ax24 h) = PB.axiom (ax24↓ h)
  pad (ax25 h) = PB.axiom (ax25↓ h)
  pad (ax26 h) = PB.axiom (ax26↓ h)
  pad (ax27 h x) = PB.axiom (ax27↓ h x)
  pad (ax28 h) = PB.axiom (ax28↓ h)
  pad (ax29 h) = PB.axiom (ax29↓ h)
  pad (ax30 h) = PB.axiom (ax30↓ h)
  pad (ax31 h) = PB.axiom (ax31↓ h)
  pad (ax32 h x) = PB.axiom (ax32↓ h x)
  pad (ax33 h) = PB.axiom (ax33↓ h)
  pad (ax34 h) = PB.axiom (ax34↓ h)
  pad (ax35 h a) = PB.axiom (ax35↓ h a)
  pad (ax36 h) = PB.axiom (ax36↓ h)
  pad (ax37 h x) = PB.axiom (ax37↓ h x)
  pad (ax38 h) = PB.axiom (ax38↓ h)
  pad (ax39 h) = PB.axiom (ax39↓ h)
  pad (ax40 h x) = PB.axiom (ax40↓ h x)
  pad (ax41 h) = PB.axiom (ax41↓ h)
  pad (ax42 h) = PB.axiom (ax42↓ h)

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad ax1ᴮ = PB.axiom (srel (srel ax1))
  unpad (ax2ᴮ x y) = PB.axiom (srel (srel (ax2 x y)))
  unpad (ax3ᴮ x) = PB.axiom (srel (srel (ax3 x)))
  unpad (ax4ᴮ x) = PB.axiom (srel (srel (ax4 x)))
  unpad (ax5ᴮ x) = PB.axiom (srel (srel (ax5 x)))
  unpad ax6ᴮ = PB.axiom (srel (srel ax6))
  unpad ax7ᴮ = PB.axiom (srel (srel ax7))
  unpad ax8ᴮ = PB.axiom (srel (srel ax8))
  unpad (ax19ᴮ h) = PB.axiom (srel (srel (ax19 h)))
  unpad (ax20ᴮ h) = PB.axiom (srel (srel (ax20 h)))
  unpad (ax21ᴮ h) = PB.axiom (srel (srel (ax21 h)))
  unpad (ax22ᴮ h x) = PB.axiom (srel (srel (ax22 h x)))
  unpad (ax23ᴮ h) = PB.axiom (srel (srel (ax23 h)))
  unpad (ax24ᴮ h) = PB.axiom (srel (srel (ax24 h)))
  unpad (ax25ᴮ h) = PB.axiom (srel (srel (ax25 h)))
  unpad (ax26ᴮ h) = PB.axiom (srel (srel (ax26 h)))
  unpad (ax27ᴮ h x) = PB.axiom (srel (srel (ax27 h x)))
  unpad (ax28ᴮ h) = PB.axiom (srel (srel (ax28 h)))
  unpad (ax29ᴮ h) = PB.axiom (srel (srel (ax29 h)))
  unpad (ax30ᴮ h) = PB.axiom (srel (srel (ax30 h)))
  unpad (ax31ᴮ h) = PB.axiom (srel (srel (ax31 h)))
  unpad (ax32ᴮ h x) = PB.axiom (srel (srel (ax32 h x)))
  unpad (ax33ᴮ h) = PB.axiom (srel (srel (ax33 h)))
  unpad (ax34ᴮ h) = PB.axiom (srel (srel (ax34 h)))
  unpad (ax35ᴮ h a) = PB.axiom (srel (srel (ax35 h a)))
  unpad (ax36ᴮ h) = PB.axiom (srel (srel (ax36 h)))
  unpad (ax37ᴮ h x) = PB.axiom (srel (srel (ax37 h x)))
  unpad (ax38ᴮ h) = PB.axiom (srel (srel (ax38 h)))
  unpad (ax39ᴮ h) = PB.axiom (srel (srel (ax39 h)))
  unpad (ax40ᴮ h x) = PB.axiom (srel (srel (ax40 h x)))
  unpad (ax41ᴮ h) = PB.axiom (srel (srel (ax41 h)))
  unpad (ax42ᴮ h) = PB.axiom (srel (srel (ax42 h)))

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ ax1 = E.E.axiom≡ ax1⇓ˡ ax1⇓ʳ (srel (srel ax1))
  srel-⇓ (ax2 x y) = E.E.axiom≡ (ax2⇓ˡ x y) (ax2⇓ʳ x y) (srel (srel (ax2 x y)))
  srel-⇓ (ax3 x) = E.E.axiom≡ (ax3⇓ˡ x) (ax3⇓ʳ x) (srel (srel (ax3 x)))
  srel-⇓ (ax4 x) = E.E.axiom≡ (ax4⇓ˡ x) (ax4⇓ʳ x) (srel (srel (ax4 x)))
  srel-⇓ (ax5 x) = E.E.axiom≡ (ax5⇓ˡ x) (ax5⇓ʳ x) (srel (srel (ax5 x)))
  srel-⇓ ax6 = E.E.axiom≡ ax6⇓ˡ ax6⇓ʳ (srel (srel ax6))
  srel-⇓ ax7 = E.E.axiom≡ ax7⇓ˡ ax7⇓ʳ (srel (srel ax7))
  srel-⇓ ax8 = E.E.axiom≡ ax8⇓ˡ ax8⇓ʳ (srel (srel ax8))
  srel-⇓ (ax19 h) = E.E.axiom≡ (ax19⇓ˡ h) (ax19⇓ʳ h) (srel (srel (ax19 h)))
  srel-⇓ (ax20 h) = E.E.axiom≡ (ax20⇓ˡ h) (ax20⇓ʳ h) (srel (srel (ax20 h)))
  srel-⇓ (ax21 h) = E.E.axiom≡ (ax21⇓ˡ h) (ax21⇓ʳ h) (srel (srel (ax21 h)))
  srel-⇓ (ax22 h x) = E.E.axiom≡ (ax22⇓ˡ h x) (ax22⇓ʳ h x) (srel (srel (ax22 h x)))
  srel-⇓ (ax23 h) = E.E.axiom≡ (ax23⇓ˡ h) (ax23⇓ʳ h) (srel (srel (ax23 h)))
  srel-⇓ (ax24 h) = E.E.axiom≡ (ax24⇓ˡ h) (ax24⇓ʳ h) (srel (srel (ax24 h)))
  srel-⇓ (ax25 h) = E.E.axiom≡ (ax25⇓ˡ h) (ax25⇓ʳ h) (srel (srel (ax25 h)))
  srel-⇓ (ax26 h) = E.E.axiom≡ (ax26⇓ˡ h) (ax26⇓ʳ h) (srel (srel (ax26 h)))
  srel-⇓ (ax27 h x) = E.E.axiom≡ (ax27⇓ˡ h x) (ax27⇓ʳ h x) (srel (srel (ax27 h x)))
  srel-⇓ (ax28 h) = E.E.axiom≡ (ax28⇓ˡ h) (ax28⇓ʳ h) (srel (srel (ax28 h)))
  srel-⇓ (ax29 h) = E.E.axiom≡ (ax29⇓ˡ h) (ax29⇓ʳ h) (srel (srel (ax29 h)))
  srel-⇓ (ax30 h) = E.E.axiom≡ (ax30⇓ˡ h) (ax30⇓ʳ h) (srel (srel (ax30 h)))
  srel-⇓ (ax31 h) = E.E.axiom≡ (ax31⇓ˡ h) (ax31⇓ʳ h) (srel (srel (ax31 h)))
  srel-⇓ (ax32 h x) = E.E.axiom≡ (ax32⇓ˡ h x) (ax32⇓ʳ h x) (srel (srel (ax32 h x)))
  srel-⇓ (ax33 h) = E.E.axiom≡ (ax33⇓ˡ h) (ax33⇓ʳ h) (srel (srel (ax33 h)))
  srel-⇓ (ax34 h) = E.E.axiom≡ (ax34⇓ˡ h) (ax34⇓ʳ h) (srel (srel (ax34 h)))
  srel-⇓ (ax35 h a) = E.E.axiom≡ (ax35⇓ˡ h a) (ax35⇓ʳ h a) (srel (srel (ax35 h a)))
  srel-⇓ (ax36 h) = E.E.axiom≡ (ax36⇓ˡ h) (ax36⇓ʳ h) (srel (srel (ax36 h)))
  srel-⇓ (ax37 h x) = E.E.axiom≡ (ax37⇓ˡ h x) (ax37⇓ʳ h x) (srel (srel (ax37 h x)))
  srel-⇓ (ax38 h) = E.E.axiom≡ (ax38⇓ˡ h) (ax38⇓ʳ h) (srel (srel (ax38 h)))
  srel-⇓ (ax39 h) = E.E.axiom≡ (ax39⇓ˡ h) (ax39⇓ʳ h) (srel (srel (ax39 h)))
  srel-⇓ (ax40 h x) = E.E.axiom≡ (ax40⇓ˡ h x) (ax40⇓ʳ h x) (srel (srel (ax40 h x)))
  srel-⇓ (ax41 h) = E.E.axiom≡ (ax41⇓ˡ h) (ax41⇓ʳ h) (srel (srel (ax41 h)))
  srel-⇓ (ax42 h) = E.E.axiom≡ (ax42⇓ˡ h) (ax42⇓ʳ h) (srel (srel (ax42 h)))

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

same : E.E.SameRules
same = E.same fam

open E.E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)
