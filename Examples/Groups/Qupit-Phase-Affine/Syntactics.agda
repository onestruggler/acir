------------------------------------------------------------------------
-- Presentations of groups
--
-- The syntax of phase-affine circuits (Blake, "Completeness for
-- prime-dimensional phase-affine circuits", arXiv:2603.06466): the
-- affine generators X, M_a, CX and the symmetry, the phases ω, Z, S, T,
-- and the rulesets Aff_d (Figure 1), LinPhase_d (Figure 3), QuadPhase_d
-- (Figure 4) and CubicPhase_d (Figure 5).
--
-- The four fragments share one alphabet, indexed by a level lv: the
-- affine fragment is lv = 0, and the phases of degree k (ω and Z for
-- k = 1, S for 2, T for 3) are generators when k ≤ lv.  A phase gate
-- carries its level evidence irrelevantly, so a lemma about S is stated
-- for every level with 2 ≤ lv and holds in each fragment that has S.
-- The relations of the paper are included at the levels where their
-- gates exist.
--
-- Wires are numbered from the bottom: wire 0 is the paper's bottom
-- wire and the first label.  CX adds wire 1 to wire 0 (the paper's
-- controlled addition, control on top).  A word is read in operator
-- order, so a drawing "A then B" is the word B • A.  A label k ∈ F_p on
-- a gate is the iterate by its representative, w ^ᶠ k = w ^ toℕ k; the
-- negative labels are the iterates by the negatives in F_p.
--
-- The symmetry is a generator, SWAP, with the laws of a symmetric
-- monoidal category: an involution, coherent (braid), and natural for
-- every generator.  A gate drawn on non-adjacent or reordered wires is
-- its placement by swaps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_ ; _<_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Syntactics
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Properties using (<⇒≤)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Word.Base

open import Notations using (₀ ; ₁ ; ₁₊ ; ₃₊ ; ₄₊)

import Circuit.Base
import Presentation.Base as PB

open import ForStdlib.Data.Fin.Mod using (_+_ ; _*_ ; -_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat using (module PrimeModulus')

open import Examples.Groups.Qupit-Phase-Affine.Field p-2 p-prime
  using (F ; F* ; p ; 1F ; 2F ; half ; binom2 ; binom3 ; _-_)

private
  module PM = PrimeModulus' p-2 p-prime
  variable
    n : ℕ

------------------------------------------------------------------------
-- Levels

-- A level with S has Z, and a level with T has S.
lin₂ : 2 ≤ lv → 1 ≤ lv
lin₂ = <⇒≤

quad₃ : 3 ≤ lv → 2 ≤ lv
quad₃ = <⇒≤

lin₃ : 3 ≤ lv → 1 ≤ lv
lin₃ h = lin₂ (quad₃ h)

------------------------------------------------------------------------
-- Gates

-- M_a carries the proof a ≢ 0 irrelevantly, so M_a depends on a alone.
data Gate : ℕ → Set where
  ω-gate    : .(1 ≤ lv) → Gate 0
  X-gate    : Gate 1
  M-gate    : (a : F) → .(a ≢ ₀) → Gate 1
  Z-gate    : .(1 ≤ lv) → Gate 1
  S-gate    : .(2 ≤ lv) → Gate 1
  T-gate    : .(3 ≤ lv) → Gate 1
  CX-gate   : Gate 2
  SWAP-gate : Gate 2

private module C = Circuit.Base Gate

open C public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_ )

------------------------------------------------------------------------
-- The generators as circuits

X : Circuit (₁₊ n)
X = [ gate₁ X-gate ]ʷ

M : (a : F) → .(a ≢ ₀) → Circuit (₁₊ n)
M a nz = [ gate₁ (M-gate a nz) ]ʷ

-- M at a unit.
M⟨_⟩ : F* → Circuit (₁₊ n)
M⟨ a ⟩ = M (proj₁ a) (proj₂ a)

CX SWAP : Circuit (₂₊ n)
CX   = [ gate₂ CX-gate ]ʷ
SWAP = [ gate₂ SWAP-gate ]ʷ

ω : .(1 ≤ lv) → Circuit n
ω h = [ gate₀ (ω-gate h) ]ʷ

Z : .(1 ≤ lv) → Circuit (₁₊ n)
Z h = [ gate₁ (Z-gate h) ]ʷ

S : .(2 ≤ lv) → Circuit (₁₊ n)
S h = [ gate₁ (S-gate h) ]ʷ

T : .(3 ≤ lv) → Circuit (₁₊ n)
T h = [ gate₁ (T-gate h) ]ʷ

-- An iterate labelled by k ∈ F_p.
infixr 8 _^ᶠ_
_^ᶠ_ : Circuit n → F → Circuit n
w ^ᶠ k = w ^ toℕ k

-- The units 1 and -1.
1* -1* : F*
1*  = ₁ , λ ()
-1* = PM.-' 1*

-- The product of units.
infixl 7 _⊛_
_⊛_ : F* → F* → F*
_⊛_ = PM._*'_

------------------------------------------------------------------------
-- Placed gates (Section 2: placements by the symmetry)

-- CX with control on the bottom wire and target on the top: the
-- reversed controlled addition (x₀ , x₁) ↦ (x₀ , x₁ + x₀).
CXʳ : Circuit (₂₊ n)
CXʳ = SWAP • CX • SWAP

-- CX from wire 2 to wire 0.
CX₂₀ : Circuit (₃₊ n)
CX₂₀ = SWAP ↑ • CX • SWAP ↑

------------------------------------------------------------------------
-- Derived diagonals (Definitions 16, 17, 18)
--
-- In the paper's drawings the top wire is wire 1 (wire 2 for CCZ).

-- The bilinear quadratic diagonal: phase x₀ x₁.
CZ : .(2 ≤ lv) → Circuit (₂₊ n)
CZ h = S h ^ᶠ (- 1F) • (S h ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F) • S h • CX

-- The controlled square, dot on wire 1 and square on wire 0: phase
-- x₁ (x₀ choose 2).  Here t = 2⁻¹.
CS : .(3 ≤ lv) → Circuit (₂₊ n)
CS h =
  CX • T h ^ᶠ (- half) • CX ^ᶠ (- 1F) • CX ^ᶠ (- 1F) • T h ^ᶠ half • CX •
  (S (quad₃ h) ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • (Z (lin₃ h) ^ᶠ (- half)) ↑ •
  CZ (quad₃ h) ^ᶠ half

-- The trilinear cubic diagonal on wires 2, 1, 0: phase x₀ x₁ x₂.
CCZ : .(3 ≤ lv) → Circuit (₃₊ n)
CCZ h =
  T h • T h ↑ • T h ↑ ↑ •
  CX₂₀ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX₂₀ •
  CX ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX •
  (CX ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • CX ↑ • (CX ^ᶠ (- 1F)) ↑ •
  CX ^ᶠ (- 1F) • T h • CX • CX ↑

-- Placements used by the rules: CZ on wires 2 and 0; CS with dot on
-- wire 2 and square on wire 0; CCZ on wires 3, 1, 0.
CZ₂₀ : .(2 ≤ lv) → Circuit (₃₊ n)
CZ₂₀ h = SWAP ↑ • CZ h • SWAP ↑

CS₂₀ : .(3 ≤ lv) → Circuit (₃₊ n)
CS₂₀ h = SWAP ↑ • CS h • SWAP ↑

CCZ₃₁₀ : .(3 ≤ lv) → Circuit (₄₊ n)
CCZ₃₁₀ h = SWAP ↑ ↑ • CCZ h • SWAP ↑ ↑

------------------------------------------------------------------------
-- The relations
--
-- Each rule is stated at the width it is drawn on; the structural
-- rules of Circuit.Base lift it to every width.  Numbers are the
-- paper's equation numbers.

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- Aff_d (Figure 1).
  ax1 : (₁₊ n) SRel, M⟨ 1* ⟩ === ε
  ax2 : (x y : F*) → (₁₊ n) SRel, M⟨ y ⟩ • M⟨ x ⟩ === M⟨ x ⊛ y ⟩
  ax3 : (x : F*) → (₁₊ n) SRel, X ^ᶠ proj₁ x • M⟨ x ⟩ • X ^ᶠ (- 1F) === M⟨ x ⟩
  ax4 : (x : F*) → (₂₊ n) SRel, CX • M⟨ x ⟩ ↑ === M⟨ x ⟩ ↑ • CX ^ᶠ proj₁ x
  ax5 : (x : F*) → (₂₊ n) SRel, CX ^ᶠ (- proj₁ x) • M⟨ x ⟩ • CX === M⟨ x ⟩
  ax6 : (₂₊ n) SRel, CX • X ↑ === X • X ↑ • CX
  ax7 : (₂₊ n) SRel,
        SWAP === M⟨ -1* ⟩ ↑ • (SWAP • CX ^ᶠ (- 1F) • SWAP) • CX • (SWAP • CX ^ᶠ (- 1F) • SWAP)
  ax8 : (₃₊ n) SRel, CX ↑ • CX • CX₂₀ === CX • CX ↑

  -- The symmetry: an involution, coherent, and natural.
  swap-order : (₂₊ n) SRel, SWAP • SWAP === ε
  swap-braid : (₃₊ n) SRel, SWAP • SWAP ↑ • SWAP === SWAP ↑ • SWAP • SWAP ↑
  swap-X     : (₂₊ n) SRel, X • SWAP === SWAP • X ↑
  swap-M     : (a : F) .(nz : a ≢ ₀) → (₂₊ n) SRel, M a nz • SWAP === SWAP • M a nz ↑
  swap-Z     : .(h : 1 ≤ lv) → (₂₊ n) SRel, Z h • SWAP === SWAP • Z h ↑
  swap-S     : .(h : 2 ≤ lv) → (₂₊ n) SRel, S h • SWAP === SWAP • S h ↑
  swap-T     : .(h : 3 ≤ lv) → (₂₊ n) SRel, T h • SWAP === SWAP • T h ↑
  swap-CX    : (₃₊ n) SRel, CX • SWAP ↑ • SWAP === SWAP ↑ • SWAP • CX ↑

  -- LinPhase_d (Figure 3).
  ax19 : .(h : 1 ≤ lv) → n SRel, ω h ^ p === ε
  ax20 : .(h : 1 ≤ lv) → (₁₊ n) SRel, Z h ^ p === ε
  ax21 : .(h : 1 ≤ lv) → (₂₊ n) SRel, CX • Z h • Z h ↑ === Z h • CX
  ax22 : .(h : 1 ≤ lv) (x : F*) → (₁₊ n) SRel, Z h • M⟨ x ⟩ === M⟨ x ⟩ • Z h ^ᶠ proj₁ x
  ax23 : .(h : 1 ≤ lv) → (₁₊ n) SRel, Z h • X === ω h • X • Z h

  -- QuadPhase_d (Figure 4).
  ax24 : .(h : 2 ≤ lv) → (₁₊ n) SRel, S h ^ p === ε
  ax25 : .(h : 2 ≤ lv) → (₁₊ n) SRel, S h • X === X • Z (lin₂ h) • S h
  ax26 : .(h : 2 ≤ lv) → (₁₊ n) SRel, S h • Z (lin₂ h) === Z (lin₂ h) • S h
  ax27 : .(h : 2 ≤ lv) (x : F*) → (₁₊ n) SRel,
         S h • M⟨ x ⟩ === M⟨ x ⟩ • Z (lin₂ h) ^ᶠ binom2 (proj₁ x) • S h ^ᶠ (proj₁ x * proj₁ x)
  ax28 : .(h : 2 ≤ lv) → (₂₊ n) SRel, M⟨ -1* ⟩ ↑ • CZ h ^ᶠ (- 1F) • M⟨ -1* ⟩ ↑ === CZ h
  ax29 : .(h : 2 ≤ lv) → (₂₊ n) SRel, CX • S h ↑ === S h ↑ • CX
  ax30 : .(h : 2 ≤ lv) → (₃₊ n) SRel, CZ h • CX ↑ === CX ↑ • CZ h • CZ₂₀ h

  -- CubicPhase_d (Figure 5).  In (35), μ = (a choose 2).
  ax31 : .(h : 3 ≤ lv) → (₁₊ n) SRel, T h ^ p === ε
  ax32 : .(h : 3 ≤ lv) (x : F*) → (₁₊ n) SRel,
         M⟨ x ⟩ • S (quad₃ h) ^ᶠ (2F * proj₁ x * binom2 (proj₁ x)) •
         Z (lin₃ h) ^ᶠ binom3 (proj₁ x) • T h ^ᶠ (proj₁ x * proj₁ x * proj₁ x) === T h • M⟨ x ⟩
  ax33 : .(h : 3 ≤ lv) → (₁₊ n) SRel, T h • S (quad₃ h) === S (quad₃ h) • T h
  ax34 : .(h : 3 ≤ lv) → (₁₊ n) SRel, T h • X === X • T h • S (quad₃ h)
  ax35 : .(h : 3 ≤ lv) (a : F*) → (₂₊ n) SRel,
         M⟨ a ⟩ • CZ (quad₃ h) ^ᶠ binom2 (proj₁ a) • CS h ^ᶠ (proj₁ a * proj₁ a) === CS h • M⟨ a ⟩
  ax36 : .(h : 3 ≤ lv) → (₁₊ n) SRel, T h • Z (lin₃ h) === Z (lin₃ h) • T h
  ax37 : .(h : 3 ≤ lv) (x : F*) → (₂₊ n) SRel, M⟨ x ⟩ ↑ • CS h ^ᶠ proj₁ x === CS h • M⟨ x ⟩ ↑
  ax38 : .(h : 3 ≤ lv) → (₃₊ n) SRel, CX • CS₂₀ h • CS h ↑ • CCZ h === CS₂₀ h • CX
  ax39 : .(h : 3 ≤ lv) → (₂₊ n) SRel, CX • T h ↑ === T h ↑ • CX
  ax40 : .(h : 3 ≤ lv) (x : F*) → (₃₊ n) SRel, M⟨ x ⟩ ↑ ↑ • CCZ h ^ᶠ proj₁ x === CCZ h • M⟨ x ⟩ ↑ ↑
  ax41 : .(h : 3 ≤ lv) → (₄₊ n) SRel, CX ↑ ↑ • CCZ₃₁₀ h • CCZ h === CCZ h • CX ↑ ↑
  ax42 : .(h : 3 ≤ lv) → (₃₊ n) SRel, CX ↑ • CS h • CS₂₀ h === CS h • CX ↑

------------------------------------------------------------------------
-- The full relation: the structural rules of Circuit.Base on top

private module LR = C.Lift-Relation _SRel,_===_

open LR public
  using ( srel ; cong↑ ; comm₀ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₀-w ; comm-gate₁-w↑ ; comm-gate₂-w↑↑ ; _VRel,_===_ )

-- The monoid congruence the relations generate at width n: the
-- equality of circuits of the fragment.
infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (n VRel,_===_) w v
