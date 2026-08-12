------------------------------------------------------------------------
-- Presentations of groups
--
-- The symplectic gate set and its relations.
--
-- Generators, circuits and the defining relation set, together with
-- group-likeness and the commutation data the rewriting tactics use.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_)

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃ ; Σ-syntax)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality

open import Notations
import Circuit.Base

module Examples.Groups.Symplectic.Syntactics.Gates (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

module Symplectic where

  
  -- p-1 : ℕ
  -- p-1 = ₁₊ p-2
  -- p : ℕ
  -- p = ₁₊ p-1
  -- ₚ = p
  
  -- Gate types for the symplectic group generators.
  data SympGate : ℕ → Set where
    H-gate  : SympGate 1
    S-gate  : SympGate 1
    CZ-gate : SympGate 2

  -- Open the Syntactics framework: provides Gen, gate₁, gate₂, _↥, _↑, _↓, _↥ᵏ_, _↑ᵏ_, Lift-Relation.
  private module SC = Circuit.Base SympGate
  -- gate₀ is exported so that clients can discharge it: SympGate has no
  -- 0-ary gate, so every gate₀ case in this development is `gate₀ ()`.
  open SC using (Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; Circuit ; _↓ᵏ_) public

  -- Backward-compatible pattern synonyms for the three basic generators.
  -- These let CommData and Rewriting-Sym0 use the old constructor-style names.
  pattern H-gen  = gate₁ H-gate
  pattern S-gen  = gate₁ S-gate
  pattern CZ-gen = gate₂ CZ-gate

  [_⇑] : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
  [_⇑] {n} = ([_]ʷ ∘ _↥) WB.ʷ

  [_⇑]' : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
  [_⇑]' {n} = wmap _↥


  lemma-[⇑]=[⇑]' : ∀ {n} (w : Word (Gen n)) → [ w ⇑] ≡ [ w ⇑]'
  lemma-[⇑]=[⇑]' {n} [ x ]ʷ = Eq.refl
  lemma-[⇑]=[⇑]' {n} ε = Eq.refl
  lemma-[⇑]=[⇑]' {n} (w • w₁) = Eq.cong₂ _•_ (lemma-[⇑]=[⇑]' w) (lemma-[⇑]=[⇑]' w₁)

  S : ∀ {n} → Word (Gen (₁₊ n))
  S = [ gate₁ S-gate ]ʷ

  S⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  S⁻¹ = S ^ p-1

  H : ∀ {n} → Word (Gen (₁₊ n))
  H = [ gate₁ H-gate ]ʷ

  HH : ∀ {n} → Word (Gen (₁₊ n))
  HH = H ^ 2

  H⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  H⁻¹ = H ^ 3

  CZ : ∀ {n} → Word (Gen (₂₊ n))
  CZ = [ gate₂ CZ-gate ]ʷ

  CZ⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  CZ⁻¹ = CZ ^ p-1

  CX : ∀ {n} → Word (Gen (₂₊ n))
  CX = H ↓ ^ 3 • CZ • H ↓ 

  XC : ∀ {n} → Word (Gen (₂₊ n))
  XC = H ↑ ^ 3 • CZ • H ↑ 

  CX' : ∀ {n} → Word (Gen (₂₊ n))
  CX' = H ↓ • CZ • H ↓ ^ 3

  XC' : ∀ {n} → Word (Gen (₂₊ n))
  XC' = H ↑ • CZ • H ↑ ^ 3

  Ex : ∀ {n} → Word (Gen (₂₊ n))
  Ex = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑

  -- EX : ∀ {n} → Word (Gen (₂₊ n))
  -- EX = [ EX-gen ]ʷ

  ₕ|ₕ : ∀ {n} → Word (Gen (₂₊ n))
  ₕ|ₕ = H ↓ • CZ • H ↓

  ʰ|ʰ : ∀ {n} → Word (Gen (₂₊ n))
  ʰ|ʰ = H ↑ • CZ • H ↑

  ⊥⊤ : ∀ {n} → Word (Gen (₂₊ n))
  ⊥⊤ = ₕ|ₕ • ʰ|ʰ

  ⊤⊥ : ∀ {n} → Word (Gen (₂₊ n))
  ⊤⊥ = ʰ|ʰ • ₕ|ₕ

  H^ : ∀ {n} → ℤ ₄ → Word (Gen (₁₊ n))
  H^ k = H ^ toℕ k

  S^ : ∀ {n} → ℤ ₚ → Word (Gen (₁₊ n))
  S^ k = S ^ toℕ k

  CZ^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CZ^ k = CZ ^ toℕ k
  
  CX^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CX^ k = CX ^ toℕ k

  -- The shape both multiplier words have: S-powers and H alternating,
  -- with the outer two exponents equal.  ZM and XM are the two ways of
  -- filling it from a unit and its inverse, so every lemma that only
  -- uses the shape can be stated once, over a and b (see
  -- Lemmas/Lemma-Comm.aux-comm-shs-* and Lemmas4-Sym.aux-comm-shs-w↑).
  SHS : ∀ {n} → ℤ ₚ → ℤ ₚ → Word (Gen (₁₊ n))
  SHS a b = S^ a • H • S^ b • H • S^ a • H

  ZM : ∀ {n} → ℤ* ₚ → Word (Gen (₁₊ n))
  ZM x' = SHS x x⁻¹
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  XM : ∀ {n} → ℤ* ₚ → Word (Gen (₁₊ n))
  XM x' = SHS x⁻¹ x
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  -- The two fillings are exchanged by inversion.  Over SHS this is one
  -- congruence in the second exponent, since (x ⁻¹) ⁻¹ is x; proofs
  -- that state a box in ZM form but read it off a definition in XM form
  -- go through here.
  XM≡ZM⁻¹ : ∀ {n} (x : ℤ* ₚ) → XM {n} x ≡ ZM (x ⁻¹)
  XM≡ZM⁻¹ x = Eq.cong (SHS ((x ⁻¹) .proj₁)) (Eq.sym (inv-involutive x))

  -- The historical name for ZM, kept so that existing uses of M do not
  -- have to change.
  M : ∀ {n} → ℤ* ₚ → Word (Gen (₁₊ n))
  M = ZM

  M₁ : ∀ {n} → Word (Gen (₁₊ n))
  M₁ = M ₁ₚ

  CX⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  CX⁻¹ = H ^ 3 • CZ^ (- ₁) • H

  XC⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  XC⁻¹ = H ↑ ^ 3 • CZ^ (- ₁) • H ↑


  CZ02 : ∀ {n} → Word (Gen (₃₊ n))
  CZ02 = Ex • CZ ↑ • Ex

  CZ02' : ∀ {n} → Word (Gen (₃₊ n))
  CZ02' = Ex ↑ • CZ • Ex ↑

  CZ02⁻¹ : ∀ {n} → Word (Gen (₃₊ n))
  CZ02⁻¹ = Ex • CZ⁻¹ ↑ • Ex

  CZ02k : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02k k = Ex • CZ ↑ ^ k • Ex

  CZ02'k : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02'k k = Ex ↑ • CZ ^ k • Ex ↑

  CZ02⁻ᵏ : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02⁻ᵏ k = Ex • CZ⁻¹ ↑ ^ k • Ex

  CZ02'⁻ᵏ : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02'⁻ᵏ k = Ex ↑ • CZ⁻¹ ^ k • Ex ↑

  CZ02'⁻¹ : ∀ {n} → Word (Gen (₃₊ n))
  CZ02'⁻¹ = Ex ↑ • CZ⁻¹ • Ex ↑

  XC02 : ∀ {n} → Word (Gen (₃₊ n))
  XC02 = H ↑ ↑ ^ 3 • CZ02 • H ↑ ↑

  CZ02^ : ∀ {n} (k : ℤ ₚ) → Word (Gen (₃₊ n))
  CZ02^ k = Ex • CZ^ k ↑ • Ex

  CZ02'^ : ∀ {n} (k : ℤ ₚ) → Word (Gen (₃₊ n))
  CZ02'^ k = CZ02 ^ toℕ k

  CX'^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CX'^ k = H ^ 3 • CZ^ k • H

  XC^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  XC^ k = XC ^ toℕ k

  XC'^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  XC'^ k = H ↑ ^ 3 • CZ^ k • H ↑

  XC02^ : ∀ {n} → ℤ ₚ → Word (Gen (₃₊ n))
  XC02^ k = H ↑ ↑ ^ 3 • CZ02^ k • H ↑ ↑

  CX02^ : ∀ {n} → ℤ ₚ → Word (Gen (₃₊ n))
  CX02^ k = H ^ 3 • CZ02^ k • H

  infixr 9 _^2
  _^2 : ℤ* ₚ → ℤ ₚ
  _^2 x' = let x = x' .proj₁ in x * x 

  infixr 9 _^1
  _^1 : ℤ* ₚ → ℤ ₚ
  _^1 x' = let x = x' .proj₁ in x

  -- Group-specific axioms only (no structural rules).
  module Base where
      infix 4 _SRel,_===_
      data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where
        order-S    : ∀ {n} → (₁₊ n) SRel,  S ^ p === ε
        order-H    : ∀ {n} → (₁₊ n) SRel,  H ^ 4 === ε
        order-SH   : ∀ {n} → (₁₊ n) SRel,  (S • H) ^ 3 === ε
        comm-HHS   : ∀ {n} → (₁₊ n) SRel,  H • H • S === S • H • H
        M-mul      : ∀ {n} x y → (₁₊ n) SRel,  M x • M y === M (x *' y)
        semi-MS    : ∀ {n} x → (₁₊ n) SRel,  M x • S === S^ (x ^2) • M x
        semi-M↑CZ  : ∀ {n} x → (₂₊ n) SRel,  M x ↑ • CZ === CZ^ (x ^1) • M x ↑
        semi-M↓CZ  : ∀ {n} x → (₂₊ n) SRel,  M x ↓ • CZ === CZ^ (x ^1) • M x ↓
        order-CZ   : ∀ {n} → (₂₊ n) SRel,  CZ ^ p === ε
        comm-CZ-S↓ : ∀ {n} → (₂₊ n) SRel,  CZ • S ↓ === S ↓ • CZ
        comm-CZ-S↑ : ∀ {n} → (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
        selinger-c10 : ∀ {n} → (₂₊ n) SRel,  CZ • H ↑ • CZ === S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
        selinger-c11 : ∀ {n} → (₂₊ n) SRel,  CZ • H ↓ • CZ === S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
        selinger-c12 : ∀ {n} → (₃₊ n) SRel,  CZ ↑ • CZ === CZ • CZ ↑
        selinger-c13 : ∀ {n} → (₃₊ n) SRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
        selinger-c14 : ∀ {n} → (₃₊ n) SRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
        selinger-c15 : ∀ {n} → (₃₊ n) SRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

  -- Full relation: group-specific rules + structural rules (cong↑, comm).
  private module LR = SC.Lift-Relation Base._SRel,_===_

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → WRel (Gen n)
  _QRel,_===_ = LR._VRel,_===_

  -- Structural rules, exported directly.
  open LR public using (srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑)

  -- Group-specific axioms lifted to the full relation (preserves call-site names).
  order-S    : ∀ {n} → (₁₊ n) QRel, S ^ p === ε
  order-S    = LR.srel Base.order-S
  order-H    : ∀ {n} → (₁₊ n) QRel, H ^ 4 === ε
  order-H    = LR.srel Base.order-H
  order-SH   : ∀ {n} → (₁₊ n) QRel, (S • H) ^ 3 === ε
  order-SH   = LR.srel Base.order-SH
  comm-HHS   : ∀ {n} → (₁₊ n) QRel, H • H • S === S • H • H
  comm-HHS   = LR.srel Base.comm-HHS
  M-mul      : ∀ {n} x y → (₁₊ n) QRel, M x • M y === M (x *' y)
  M-mul x y  = LR.srel (Base.M-mul x y)
  semi-MS    : ∀ {n} x → (₁₊ n) QRel, M x • S === S^ (x ^2) • M x
  semi-MS x  = LR.srel (Base.semi-MS x)
  semi-M↑CZ  : ∀ {n} x → (₂₊ n) QRel, M x ↑ • CZ === CZ^ (x ^1) • M x ↑
  semi-M↑CZ x = LR.srel (Base.semi-M↑CZ x)
  semi-M↓CZ  : ∀ {n} x → (₂₊ n) QRel, M x ↓ • CZ === CZ^ (x ^1) • M x ↓
  semi-M↓CZ x = LR.srel (Base.semi-M↓CZ x)
  order-CZ   : ∀ {n} → (₂₊ n) QRel, CZ ^ p === ε
  order-CZ   = LR.srel Base.order-CZ
  comm-CZ-S↓ : ∀ {n} → (₂₊ n) QRel, CZ • S ↓ === S ↓ • CZ
  comm-CZ-S↓ = LR.srel Base.comm-CZ-S↓
  comm-CZ-S↑ : ∀ {n} → (₂₊ n) QRel, CZ • S ↑ === S ↑ • CZ
  comm-CZ-S↑ = LR.srel Base.comm-CZ-S↑
  selinger-c10 : ∀ {n} → (₂₊ n) QRel, CZ • H ↑ • CZ === S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
  selinger-c10 = LR.srel Base.selinger-c10
  selinger-c11 : ∀ {n} → (₂₊ n) QRel, CZ • H ↓ • CZ === S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
  selinger-c11 = LR.srel Base.selinger-c11
  selinger-c12 : ∀ {n} → (₃₊ n) QRel, CZ ↑ • CZ === CZ • CZ ↑
  selinger-c12 = LR.srel Base.selinger-c12
  selinger-c13 : ∀ {n} → (₃₊ n) QRel, ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  selinger-c13 = LR.srel Base.selinger-c13
  selinger-c14 : ∀ {n} → (₃₊ n) QRel, (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  selinger-c14 = LR.srel Base.selinger-c14
  selinger-c15 : ∀ {n} → (₃₊ n) QRel, (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
  selinger-c15 = LR.srel Base.selinger-c15

  -- Structural commutativity lifted from Lift-Relation.comm₁/comm₂ (preserves old names).
  comm-H  : ∀ {n} {g : Gen (₁₊ n)} → (₂₊ n) QRel, [ g ↥ ]ʷ • H === H • [ g ↥ ]ʷ
  comm-H  {g = g} = LR.comm₁ H-gate g
  comm-S  : ∀ {n} {g : Gen (₁₊ n)} → (₂₊ n) QRel, [ g ↥ ]ʷ • S === S • [ g ↥ ]ʷ
  comm-S  {g = g} = LR.comm₁ S-gate g
  comm-CZ : ∀ {n} {g : Gen (₁₊ n)} → (₃₊ n) QRel, [ g ↥ ↥ ]ʷ • CZ === CZ • [ g ↥ ↥ ]ʷ
  comm-CZ {g = g} = LR.comm₂ CZ-gate g

module Lemmas-Sym where
  open Symplectic


  import Data.Nat.Literals as NL
  open import Agda.Builtin.FromNat
  open import Data.Unit.Base using (⊤)
  open import Data.Fin.Literals
  import Data.Nat.Literals as NL


  lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  lemma-^-↑ w ₀ = auto
  lemma-^-↑ w ₁ = auto
  lemma-^-↑ w (₂₊ k) = begin
    (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (₁₊ k)) ⟩
    (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
    ((w • w ^ ₁₊ k) ↑) ∎
    where open ≡-Reasoning


  lemma-cong↓-S^ : ∀ {n} k → let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ≈↓ S ^ k
  lemma-cong↓-S^ {n} ₀ = PB.refl
  lemma-cong↓-S^ {n} ₁ = PB.refl
  lemma-cong↓-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^ {n} (₁₊ k))

  lemma-cong↑-S^ : ∀ {n} k → let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
    (S ^ k) ↑ ≈↑ S ↑ ^ k
  lemma-cong↑-S^ {n} ₀ = PB.refl
  lemma-cong↑-S^ {n} ₁ = PB.refl
  lemma-cong↑-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↑-S^ {n} (₁₊ k))


  lemma-cong↓-S↓^ : ∀ {n} k → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ↓ ^ k) ↓ ≈↓ S ↓ ^ k
  lemma-cong↓-S↓^ {n} ₀ = PB.refl
  lemma-cong↓-S↓^ {n} ₁ = PB.refl
  lemma-cong↓-S↓^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↓^ {n} (₁₊ k))

  lemma-cong↓-S↑^ : ∀ {n} k → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    ((S ↑) ^ k) ↓ ≈↓ (S ↑) ^ k
  lemma-cong↓-S↑^ {n} ₀ = PB.refl
  lemma-cong↓-S↑^ {n} ₁ = PB.refl
  lemma-cong↓-S↑^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↑^ {n} (₁₊ k))


  lemma-cong↓-S^↓ : ∀ {n} k → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ↓ ≈↓ (S ^ k) ↓
  lemma-cong↓-S^↓ {n} ₀ = PB.refl
  lemma-cong↓-S^↓ {n} ₁ = PB.refl
  lemma-cong↓-S^↓ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↓ {n} (₁₊ k))

  lemma-cong↓-S^↑ : ∀ {n} k → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↑ ↓ ≈↓ (S ^ k) ↑
  lemma-cong↓-S^↑ {n} ₀ = PB.refl
  lemma-cong↓-S^↑ {n} ₁ = PB.refl
  lemma-cong↓-S^↑ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↑ {n} (₁₊ k))

  lemma-cong↓-H^ : ∀ {n} k → let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (H ^ k) ↓ ≈↓ H ^ k
  lemma-cong↓-H^ {n} ₀ = PB.refl
  lemma-cong↓-H^ {n} ₁ = PB.refl
  lemma-cong↓-H^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-H^ {n} (₁₊ k))

  lemma-cong↓-CZ^ : ∀ {n} k → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (CZ ^ k) ↓ ≈↓ CZ ^ k
  lemma-cong↓-CZ^ {n} ₀ = PB.refl
  lemma-cong↓-CZ^ {n} ₁ = PB.refl
  lemma-cong↓-CZ^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-CZ^ {n} (₁₊ k))

  lemma-↑↓ : ∀ {n} (w : Word (Gen n)) → w ↑ ↓ ≡ w ↓ ↑
  lemma-↑↓ [ x ]ʷ = auto
  lemma-↑↓ ε = auto
  lemma-↑↓ (w • w₁) = Eq.cong₂ _•_ (lemma-↑↓ w) (lemma-↑↓ w₁)

  lemma-↓^ : ∀ {n} k (w : Word (Gen n)) → (w ^ k) ↓ ≡ w ↓ ^ k
  lemma-↓^ {n} ₀ w = auto
  lemma-↓^ {n} ₁ w = auto
  lemma-↓^ {n} (₂₊ k) w = Eq.cong₂ _•_ auto (lemma-↓^ {n} (₁₊ k) w)

  lemma-M↓ : ∀ {n} x → let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    M x ↓ ≈↓ M x
  lemma-M↓ {n} x' = begin
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↓ ≈⟨ cong (refl' (lemma-↓^ (toℕ x) S)) (cright cong (refl' (lemma-↓^ (toℕ x⁻¹) S)) (cright (cleft refl' (lemma-↓^ (toℕ x) S)))) ⟩
    M x' ∎
    where
    open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    
  lemma-M↑↓ : ∀ {n} x → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    M x ↑ ↓ ≈↓ M x ↑
  lemma-M↑↓ {n} x' = begin
    ((M x' ↑) ↓) ≡⟨ lemma-↑↓ (M x') ⟩
    ((M x' ↓) ↑) ≈⟨ lemma-cong↑ _ _ (lemma-M↓ x') ⟩
    (M x' ↑) ∎
    where
    open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid


  lemma-M↓↓ : ∀ {n} x → let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    M x ↓ ↓ ≈↓ M x ↓
  lemma-M↓↓ {n} x' = begin
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↓ ↓ ≡⟨ auto ⟩
    (S^ x ↓ • H • S^ x⁻¹ ↓ • H • S^ x ↓ • H) ↓ ≡⟨ Eq.cong₂ (\ xx yy → (xx • H • yy • H • S^ x ↓ • H) ↓) (lemma-↓^ (toℕ x) S) (lemma-↓^ (toℕ x⁻¹) S) ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x ↓ • H) ↓ ≡⟨ Eq.cong (\ xx → (S^ x • H • S^ x⁻¹ • H • xx • H) ↓) (lemma-↓^ (toℕ x) S) ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↓ ≡⟨ auto ⟩
    M x' ↓ ∎
    where
    open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  instance
    Numℕ' : Number ℕ
    Numℕ' = NL.number 

  instance
    NumFin' : Number (Fin p)
    NumFin' = number p

  lemma-comm-S-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    S • w ↑ ≈ w ↑ • S
    
  lemma-comm-S-w↑ {n} [ x ]ʷ = sym (axiom comm-S)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} (w • w₁) = begin
    S • ((w • w₁) ↑) ≈⟨ refl ⟩
    S • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (S • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • S • w₁ ↑ ≈⟨ cong refl (lemma-comm-S-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • S ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-comm-Sᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    S ^ k • w ↑ ≈ w ↑ • S ^ k
    
  lemma-comm-Sᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} ₁ w = lemma-comm-S-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} (₂₊ k) w = begin
    (S • S ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    S • S ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑ (₁₊ k) w) ⟩
    S • (w ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (S • w ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • S • S ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-H-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    H • w ↑ ≈ w ↑ • H
    
  lemma-comm-H-w↑ {n} [ x ]ʷ = sym (axiom comm-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} (w • w₁) = begin
    H • ((w • w₁) ↑) ≈⟨ refl ⟩
    H • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (H • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • H • w₁ ↑ ≈⟨ cong refl (lemma-comm-H-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • H ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-Hᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    H ^ k • w ↑ ≈ w ↑ • H ^ k
    
  lemma-comm-Hᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} ₁ w = lemma-comm-H-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} (₂₊ k) w = begin
    (H • H ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    H • H ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑ (₁₊ k) w) ⟩
    H • (w ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H • w ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • H • H ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-CZ-w↑ : ∀ {n} w → let open PB ((₃₊ n) QRel,_===_) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑ {n} [ x ]ʷ = sym (axiom comm-CZ)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} (w • w₁) = begin
    CZ • ((w • w₁) ↑ ↑) ≈⟨ refl ⟩
    CZ • (w ↑ ↑ • w₁ ↑ ↑) ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • w₁ ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑ w) refl ⟩
    (w ↑ ↑ • CZ) • w₁ ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • CZ • w₁ ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑ w₁) ⟩
    w ↑ ↑ • w₁ ↑ ↑ • CZ ≈⟨ sym assoc ⟩
    ((w • w₁) ↑ ↑) • CZ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid


module Symplectic-GroupLike where

  private
    variable
      n : ℕ
    
  open Symplectic
  open Lemmas-Sym

  grouplike : Grouplike (n QRel,_===_)
  grouplike {n} (gate₁ H-gate) = H ^ 3 , claim
    where
    open PB (n QRel,_===_)
    open PP (n QRel,_===_)
    open SR word-setoid
    claim : H ^ 3 • H ≈ ε
    claim = begin
      H ^ 3 • H ≈⟨ by-assoc auto ⟩
      H ^ 4 ≈⟨ axiom order-H ⟩
      ε ∎
  grouplike {n} (gate₁ S-gate) = S ^ p-1 , claim
    where
    open PB (n QRel,_===_)
    open PP (n QRel,_===_)
    open SR word-setoid
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p ≈⟨ axiom order-S ⟩
      ε ∎
  grouplike {n} (gate₂ CZ-gate) = CZ ^ p-1 , claim
    where
    open PB (n QRel,_===_)
    open PP (n QRel,_===_)
    open SR word-setoid
    claim : CZ ^ p-1 • CZ ≈ ε
    claim = begin
      CZ ^ p-1 • CZ ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p ≈⟨ axiom order-CZ ⟩
      ε ∎
  grouplike {n} (g ↥) with grouplike g
  ... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB (n QRel,_===_)
    open PP (n QRel,_===_)


{-
  sform1-antisym' : ∀ (p q : Pauli1) → sform1 p q ≡ - sform1 q p
  sform1-antisym' p@(a , b) q@(c , d) = begin
    sform1 (a , b) (c , d) ≡⟨ solve p-2 {!4!} {!!} {!!} ⟩
    (- a) * d + c * b ≡⟨ {!\ a b c d → (solve p-2 4 ? ?)!} ⟩
    - ((- c) * b + a * d) ≡⟨ solve p-2 {!4!} {!!} {!!} ⟩
    - sform1 (c , d) (a , b) ∎
    where
    open ≡-Reasoning
    aux2 : ∀ a b c d e → - e * ((a) * d + c * b) ≡ - e * (c * b + (a) * d)
    aux2 = solve p-2 5 (\ a b c d e → (⊝ e) ⊗ ((a) ⊗ d ⊕ c ⊗ b) , (⊝ e) ⊗ (c ⊗ b ⊕ (a) ⊗ d)) λ {x} {x = x₁} {x = x₂} {x = x₃} {x = x₄} → Eq.refl

    aux3 : ∀ a b → a * b ≡ b * a
    aux3 = solve p-2 2 (\ a b → a ⊗ b , b ⊗ a) λ {x} {x = x₁} → Eq.refl

-}

  module Two-Qupit-Completeness where

{-
    aux1 : ∀ (p : Pauli 1) → sform pIₙ p ≡ 0
    aux1 p = {!!}

    Theorem-NF :
    
      ∀ (p q : Pauli 1) →
      sform p q ≡ 1 →
      -------------------------------
      ∃ \ nf → act ⟦ nf ⟧ p ≡ pZ₀ ×
                act ⟦ nf ⟧ q ≡ pX₀
      
    Theorem-NF p@((₀ , ₀) ∷ []) q@(q1 ∷ []) eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (aux1 q)) eq)
    ... | ()
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₀ , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₀ , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₁₊ c , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₁₊ c , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₀ , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₀ , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₁₊ c , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₁₊ c , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₀ , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₀ , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₁₊ c , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₁₊ c , ₁₊ d) ∷ []) eq = {!!}
  -}


-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData where
  variable
    n : ℕ

  open Symplectic
  open Lemmas-Sym
  
  
  -- Commutativity.
  commute : (x y : Gen (₂₊ n)) → let open PB ((₂₊ n) QRel,_===_) in Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  commute {n} H-gen (y ↥) = just (PB.sym (PB.axiom comm-H))
  commute {n} (x ↥) H-gen = just (PB.axiom comm-H)
  commute {n} S-gen (y ↥) = just (PB.sym (PB.axiom comm-S))
  commute {n} (x ↥) S-gen = just (PB.axiom comm-S)
  commute {n} S-gen CZ-gen = just (PB.sym (PB.axiom comm-CZ-S↓))
  commute {n} CZ-gen S-gen = just (PB.axiom comm-CZ-S↓)
  commute {n} (S-gen ↥) CZ-gen = just (PB.sym (PB.axiom comm-CZ-S↑))
  commute {n} CZ-gen (S-gen ↥) = just (PB.axiom comm-CZ-S↑)
  
  commute {n@(₁₊ n')} CZ-gen (CZ-gen ↥) = just (PB.sym (PB.axiom selinger-c12))
  commute {n} (CZ-gen ↥) CZ-gen = just (PB.axiom selinger-c12)
  
  commute {n@(₁₊ n')} CZ-gen ((y ↥) ↥) = just (PB.sym (PB.axiom comm-CZ))
  commute {n@(₁₊ n')} ((x ↥) ↥) CZ-gen = just (PB.axiom comm-CZ)
  
  commute {n@(₁₊ n')} (x ↥) (y ↥) with commute x y
  ... | nothing = nothing
  ... | just eq = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) eq)

  commute {n} _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen (₁₊ n) → ℕ
  ord {n}(S-gen) = 0
  ord {n} (H-gen) = 1
  ord {₁₊ n} (CZ-gen) = 2
--  ord {₁₊ n} (EX-gen) = 3
  ord {₁₊ n} (g ↥) = 4 Nat.+ ord g
  -- Gen 0 is inhabited only by gate₀, and SympGate has no 0-ary gate.
  ord {₀} ((gate₀ ()) ↥)


  -- Ordering of generators.
  les : Gen (₂₊ n) → Gen (₂₊ n) → Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic (n : ℕ) where
  open Symplectic
  open CommData hiding (n)
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public

module Lemmas00 where

  variable
    n : ℕ

  -- open Lemmas hiding (n)
  -- open Lemmas2 hiding (n)
  -- open Lemmas3 hiding (n)
  open Symplectic
  open import ForStdlib.Data.Fin.Mod
  open Rewriting

  -- lemma-semi-CZ-HH↓ : let open PB ((₂₊ n) QRel,_===_) in

  --   CZ • H ↓ ^ 2 ≈ H ↓ ^ 2 • CZ^ ₋₁
    
  -- lemma-semi-CZ-HH↓ = {!!}
