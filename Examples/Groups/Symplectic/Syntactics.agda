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

module Examples.Groups.Symplectic.Syntactics (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
    

module Rewriting-Sym0 where

  -- This module provides a complete rewrite system for 1-qubit
  -- Swap operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  
  
  step-sym0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  -- step-sym0 ((S-gen) ∷ (S-gen) ∷ (S-gen) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  -- step-sym0 ((S-gen ↥) ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  -- step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-sym0 ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-sym0 ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  -- step-sym0 ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  -- step-sym0 ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-sym0 ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-sym0 ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

--  step-sym0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (PB.axiom order-Ex))
--  step-sym0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-Ex)))

  -- Commuting of generators.
  step-sym0 ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↓)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↓))))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↑))))

  step-sym0 ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))

  -- step-sym0 ((EX-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  -- step-sym0 ((EX-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (EX-gen ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-sym0 ((EX-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (EX-gen ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (EX-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (EX-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  -- step-sym0 ((EX-gen ↥ ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (EX-gen ↥ ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-CZ))))
  -- step-sym0 ((H-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))
  -- step-sym0 ((S-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))
  -- step-sym0 ((CZ-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))

  step-sym0 ((S-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  step-sym0 ((S-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((H-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-sym0 ((H-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom comm-CZ)))
  step-sym0 ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom selinger-c12)))

  step-sym0 ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-HHS)))
  step-sym0 ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-HHS))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (cong↑ comm-HHS)))))

  -- Others.
--  step-sym0 ((CZ-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↓))
--  step-sym0 ((CZ-gen) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↑))

  -- step-sym0 ((CZ-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ xs) = just ((S-gen) ∷ (S-gen) ∷ H-gen ∷ (S-gen) ∷ (S-gen) ∷ CZ-gen ∷ H-gen ∷ S-gen ∷ S-gen ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom selinger-c11 ))
  -- step-sym0 ((CZ-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c11 )))
  -- step-sym0 ((CZ-gen) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ∷ S-gen ∷ xs , at-head (PB.axiom selinger-c10 ))
  -- step-sym0 ((CZ-gen ↥) ∷ (H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ H-gen ↥ ↥ ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c10 )))

  -- Catch-all
  step-sym0 _ = nothing

module Sym0-Rewriting (n : ℕ) where
  open Symplectic
  open Rewriting
  open Rewriting-Sym0 hiding (n)
  open Rewriting.Step (step-cong (step-sym0 {n})) renaming (general-rewrite to rewrite-sym0) public


module Lemmas0 (n : ℕ) where

  open Symplectic
--  open Symplectic-GroupLike
  open import ForStdlib.Data.Fin.Mod

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-S^k+l : ∀ k l → S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ refl ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ ^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (^^ S p (k+l Nat./ p))) ⟩
    S^ (k + l) • (S ^ p) ^ (k+l Nat./ p) ≈⟨ cright (^-cong (S ^ p) ε (k+l Nat./ p) (axiom order-S)) ⟩
    S^ (k + l) • ε ^ (k+l Nat./ p) ≈⟨ cright ε^k=ε (k+l Nat./ p) ⟩
    S^ (k + l) • ε ≈⟨ right-unit ⟩
    S^ (k + l) ∎
    where
    k+l = toℕ k Nat.+ toℕ l
    open SR word-setoid


  lemma-S^k-k : ∀ k → S^ k • S^ (- k) ≈ ε
  lemma-S^k-k k = begin
    S^ k • S^ (- k) ≈⟨ lemma-S^k+l k (- k) ⟩
    S^ (k + - k) ≡⟨ Eq.cong S^ (+-inverseʳ k) ⟩
    S^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k → S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ refl ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ comm⇒pow-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ refl ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  
  lemma-M1 : ε ≈ M (₁ , λ ())
  lemma-M1 = begin
    ε ≈⟨ _≈_.sym (axiom order-SH) ⟩
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≡⟨ auto ⟩
    S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx → S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
    S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
    M (₁ , λ ()) ∎
    where
    open SR word-setoid


  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ sym left-unit ⟩
    ε • (H⁻¹ • S⁻¹) ^ 3 ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (S • H) ^ 3 • (H⁻¹ • S⁻¹) ^ 3 ≈⟨ rewrite-sym0 100 auto ⟩
    ((S • H • S • H • S) • (H • H⁻¹)) • S⁻¹ • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ ( cleft trans (cright axiom order-H) (by-assoc auto)) ⟩
    ((S • H • S • H) • S) • S⁻¹ • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • (S • S⁻¹) • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ (cright cleft axiom order-S) ⟩
    (S • H • S • H) • ε • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • H • H⁻¹) • S⁻¹ • (H⁻¹ • S⁻¹) ≈⟨ (cleft cright cright cright axiom order-H) ⟩
    (S • H • S • ε) • S⁻¹ • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ (cleft cright cright axiom order-S) ⟩
    (S • H • ε) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • H⁻¹) • S⁻¹ ≈⟨ (cleft cright axiom order-H) ⟩
    (S • ε) • S⁻¹ ≈⟨ by-assoc auto ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
    open SR word-setoid
    open Sym0-Rewriting n


  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright trans (comm⇒pow-comm p-1 1 refl) (axiom order-S)) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ by-passoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
--    open Group-Lemmas _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≡⟨ Eq.refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid

  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright ^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (by-passoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft comm⇒pow-comm 1 p-1 (trans assoc (axiom comm-HHS)))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft comm⇒pow-comm p-1 1 (sym (trans assoc (axiom comm-HHS)))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright rewrite-sym0 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ by-passoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ by-passoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright cong lemma-S⁻¹ refl)) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx → S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy → S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx → S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where
    open Sym0-Rewriting n


    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁
    open SR word-setoid


  aux-M≡M : ∀ y y' → y .proj₁ ≡ y' .proj₁ → M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy → S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx → S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
    M y' ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )
    aux-eq : x⁻¹ ≡ x'⁻¹
    aux-eq  = begin
      x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
      x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
      x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx → (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎


  lemma-M-power : ∀ (x : ℤ* ₚ) k → let x' = x .proj₁ in  M x ^ k ≈ M (x ^' k)
  lemma-M-power x k@0 = lemma-M1 
  lemma-M-power x k@1 = begin
    M x ^ 1 ≡⟨ aux-M≡M x (x ^' 1) (Eq.sym (lemma-x^′1=x (x .proj₁))) ⟩
    M (x ^' 1) ∎
    where
    open SR word-setoid
  lemma-M-power x k@(₂₊ k') = begin
    M x • M x ^ ₁₊ k' ≈⟨ (cright lemma-M-power x (₁₊ k')) ⟩
    M x • M (x ^' ₁₊ k') ≈⟨ axiom (M-mul x (x ^' ₁₊ k')) ⟩
    M (x *' (x ^' ₁₊ k')) ≡⟨ aux-M≡M (x *' (x ^' ₁₊ k')) (x ^' ₂₊ k') auto ⟩
    M (x ^' ₂₊ k') ∎
    where
    open SR word-setoid


  derived-D : ∀ x → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (axiom order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright by-passoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid

  derived-5 : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ axiom (semi-MS (x , nz)) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
  derived-5 x k@(₂₊ k') nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) • S) • S ^ ₁₊ k' ≈⟨ (cleft derived-5 x 1 nz) ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • M (x , nz)) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (x * x)) • M (x , nz) • S ^ ₁₊ k' ≈⟨ (cright derived-5 x (₁₊ k') nz) ⟩
    S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x))) • M (x , nz) ≈⟨ (cleft sym (^-+ S ((1 Nat.* toℕ (x * x))) ((₁₊ k' Nat.* toℕ (x * x))))) ⟩
    (S ^ ((1 Nat.* toℕ (x * x)) Nat.+ (₁₊ k' Nat.* toℕ (x * x)))) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x * x)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x * x) ) • M (x , nz) ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid

  lemma-S^k-% : ∀ k → S ^ k ≈ S ^ (k % p)
  lemma-S^k-% k = begin
    S ^ k ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k p) ⟩
    S ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ ^-+ S (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    S ^ (k Nat.% p) • S ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    S ^ (k Nat.% p) • S ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright ^^ S p (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • (S ^ p) ^ (k Nat./ p) ≈⟨ (cright ^-cong (S ^ p) ε (k Nat./ p) (axiom order-S)) ⟩
    S ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright ε^k=ε (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    S ^ (k % p) ∎
    where
    open SR word-setoid


  lemma-MS^k : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ refl ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-MS^k' : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ (k * (x⁻¹ * x⁻¹)) ≈ S^ k • M (x , nz)
  lemma-MS^k' x k nz = begin 
    M (x , nz) • S^ (k * (x⁻¹ * x⁻¹)) ≈⟨ lemma-MS^k x (k * (x⁻¹ * x⁻¹)) nz ⟩
    S^ (k * (x⁻¹ * x⁻¹) * (x * x)) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong S^ (Eq.trans (*-assoc k (x⁻¹ * x⁻¹)  (x * x)) (Eq.cong (k *_) (aux-xxxx (x , nz)))))) ⟩
    S^ (k * ₁) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong S^ (*-identityʳ k))) ⟩
    S^ k • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-S^ab : ∀ (a b : ℤ ₚ) → S ^ toℕ (a * b) ≈ S ^ (toℕ a Nat.* toℕ b)
  lemma-S^ab a b = begin
    S ^ toℕ (a * b) ≡⟨ auto ⟩
    S ^ toℕ (fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ≡⟨ Eq.cong (S ^_) (toℕ-fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ⟩
    S ^ ((toℕ a Nat.* toℕ b) % p) ≈⟨ sym right-unit ⟩
    S ^ (ab Nat.% p) • ε ≈⟨ (cright sym (ε^k=ε (ab Nat./ p))) ⟩
    S ^ (ab Nat.% p) • (ε) ^ (ab Nat./ p) ≈⟨ (cright sym (^-cong (S ^ p) ε (ab Nat./ p) (axiom order-S))) ⟩
    S ^ (ab Nat.% p) • (S ^ p) ^ (ab Nat./ p) ≈⟨ (cright ^^ S p (ab Nat./ p)) ⟩
    S ^ (ab Nat.% p) • S ^ (p Nat.* (ab Nat./ p)) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm p (ab Nat./ p)))) ⟩
    S ^ (ab Nat.% p) • S ^ (ab Nat./ p Nat.* p) ≈⟨ sym (^-+ S (ab Nat.% p) (ab Nat./ p Nat.* p)) ⟩
    S ^ (ab Nat.% p Nat.+ ab Nat./ p Nat.* p) ≡⟨ Eq.cong (S ^_) (Eq.sym (m≡m%n+[m/n]*n ab p)) ⟩
    S ^ (toℕ a Nat.* toℕ b) ∎
    where
    ab = toℕ a Nat.* toℕ b
    open SR word-setoid


  derived-7 : ∀ x y → (nz : x ≢ ₀) → (nzy : y ≢ ₀) → let -'₁ = -' ((₁ , λ ())) in let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in let -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) in let -y/x = -y/x' .proj₁ in
  
    M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    
  derived-7 x y nzx nzy = begin
    M (y , nzy) • H • S^ x • H ≈⟨ (cright derived-D x nzx) ⟩
    M (y , nzy) • H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright by-passoc (□ • □ • □ • □ • □ • □ • □) (□ ^ 5 • □ • □) auto) ⟩
    M (y , nzy) • (H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft sym left-unit) ⟩
    M (y , nzy) • (ε • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft cleft sym (lemma-S^-k+k x⁻¹)) ⟩
    M (y , nzy) • ((S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ by-passoc (□ • (□ ^ 2 • □ ^ 5) • □) (□ ^ 2 • □ ^ 6 • □) auto ⟩
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ refl ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright by-passoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ refl ⟩
    S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ∎
    where
    open SR word-setoid
    nz = nzx
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

  aux-MM : ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) → x ≡ y → M (x , nzx) ≈ M (y , nzy)
  aux-MM {x} {y} nz1 nz2 eq rewrite eq = refl


  aux-M-mul : ∀ m → M m • M (m ⁻¹) ≈ ε
  aux-M-mul m = begin
    M m • M (m ⁻¹) ≈⟨ axiom (M-mul m ( m ⁻¹)) ⟩
    M (m *' m ⁻¹) ≈⟨ aux-MM ((m *' m ⁻¹) .proj₂) (λ ()) (lemma-⁻¹ʳ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ sym lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid

  aux-M-mulˡ : ∀ m → M (m ⁻¹) • M m ≈ ε
  aux-M-mulˡ m = begin
    M (m ⁻¹) • M m ≈⟨ axiom (M-mul ( m ⁻¹) m) ⟩
    M (m ⁻¹ *' m) ≈⟨ aux-MM ((m ⁻¹ *' m) .proj₂) (λ ()) (lemma-⁻¹ˡ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ sym lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid


  semi-HM : ∀ (x : ℤ* ₚ) → H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ by-passoc (□ • □ ^ 6) (□ ^ 3 • □ ^ 4) auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong lemma-M1 refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-passoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright by-passoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft axiom (M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ -x⁻¹ • S^ x⁻¹) • M (x' ⁻¹) • H ≈⟨ (cleft lemma-S^-k+k x⁻¹) ⟩
    ε • M (x' ⁻¹) • H ≈⟨ left-unit ⟩
    M (x' ⁻¹) • H ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    open Pattern-Assoc
    -x = - x
    -x⁻¹ = - x⁻¹
    aux-a1 : ₁ * x⁻¹ * (-'₁ .proj₁) ≡ -x⁻¹
    aux-a1 = begin
      ₁ * x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (\ xx → xx * (-'₁ .proj₁)) (*-identityˡ x⁻¹) ⟩
      x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym p-1=-1ₚ) ⟩
      x⁻¹ * ₋₁ ≡⟨ *-comm x⁻¹ ₋₁ ⟩
      ₋₁ * x⁻¹ ≡⟨ auto ⟩
      -x⁻¹ ∎
      where open ≡-Reasoning

    aux-a2 : -x⁻¹ * - ₁ ≡ x⁻¹
    aux-a2 = begin
      -x⁻¹ * - ₁ ≡⟨ *-comm -x⁻¹ (- ₁) ⟩
      - ₁ * -x⁻¹ ≡⟨ -1*x≈-x -x⁻¹ ⟩
      - -x⁻¹ ≡⟨ -‿involutive x⁻¹ ⟩
      x⁻¹ ∎
      where
      open ≡-Reasoning
      open import Algebra.Properties.Ring (+-*-ring p-2)


    aux-a3 : x * (x⁻¹ * x⁻¹) ≡ x⁻¹
    aux-a3 = begin
      x * (x⁻¹ * x⁻¹) ≡⟨ Eq.sym (*-assoc x x⁻¹ x⁻¹) ⟩
      x * x⁻¹ * x⁻¹ ≡⟨ Eq.cong (_* x⁻¹) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) ⟩
      ₁ * x⁻¹ ≡⟨ *-identityˡ x⁻¹ ⟩
      x⁻¹ ∎
      where open ≡-Reasoning

    open SR word-setoid

  aux-comm-MM' : ∀ m m' → M m • M m' ≈ M m' • M m
  aux-comm-MM' m m' = begin
    M m • M m' ≈⟨ axiom (M-mul m m') ⟩
    M (m *' m') ≈⟨ aux-MM ((m *' m') .proj₂) ((m' *' m) .proj₂) (*-comm (m .proj₁) (m' .proj₁)) ⟩
    M (m' *' m) ≈⟨ sym (axiom (M-mul m' m)) ⟩
    M m' • M m ∎
    where
    open SR word-setoid
    
  aux-comm-HHM : ∀ m → HH • M m ≈ M m • HH
  aux-comm-HHM m = begin
    HH • M m ≈⟨ (cleft lemma-HH-M-1) ⟩
    M -'₁ • M m ≈⟨ aux-comm-MM' -'₁ m ⟩
    M m • M -'₁ ≈⟨ (cright sym lemma-HH-M-1) ⟩
    M m • HH ∎
    where
    open SR word-setoid

  lemma-S^kM : ∀ x k → (nz : x ≢ ₀) →
    let
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    x⁻² = x⁻¹ * x⁻¹
    in
    S^ k • M (x , nz) ≈ M (x , nz) • S^ (k * x⁻²)
  lemma-S^kM x k nz = begin
    S^ k • M (x , nz) ≈⟨ sym (trans left-unit (cong refl right-unit)) ⟩
    ε • S^ k • M (x , nz) • ε ≈⟨ cong (sym (aux-M-mul (x , nz))) (cright cright sym (aux-M-mulˡ (x , nz))) ⟩
    (M ((x , nz)) • M ((x , nz) ⁻¹) ) • S^ k • M (x , nz) • (M ((x , nz) ⁻¹) • M ((x , nz)))  ≈⟨ by-passoc (□ ^ 2 • □ • □ • □ ^ 2) (□ • (□ • □ ^ 2 • □) • □) auto ⟩
    M ((x , nz)) • (M ((x , nz) ⁻¹)  • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹)) • M ((x , nz))  ≈⟨ (cright cleft aux) ⟩
    M ((x , nz)) • (M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹)) • M ((x , nz))  ≈⟨ sym (by-passoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • (□ • □ ^ 2 • □) • □) auto) ⟩
    (M ((x , nz)) • M ((x , nz) ⁻¹)) • (M (x , nz) • S^ (k * x⁻²)) • (M ((x , nz) ⁻¹) • M ((x , nz)))  ≈⟨ cong (aux-M-mul (x , nz)) (cright aux-M-mulˡ (x , nz)) ⟩
    ε • (M (x , nz) • S^ (k * x⁻²)) • ε  ≈⟨ trans left-unit right-unit ⟩
    M (x , nz) • S^ (k * x⁻²) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    x⁻² = x⁻¹ * x⁻¹
    aux : M ((x , nz) ⁻¹) • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹) ≈ M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹)
    aux = begin
      M ((x , nz) ⁻¹) • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹) ≈⟨ cong refl assoc ⟩
      M ((x , nz) ⁻¹) • S^ k • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ sym assoc ⟩
      (M ((x , nz) ⁻¹) • S^ k) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ (cleft lemma-MS^k x⁻¹ k (((x , nz) ⁻¹) .proj₂)) ⟩
      (S^ (k * x⁻²) • M ((x , nz) ⁻¹)) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ assoc ⟩
      S^ (k * x⁻²) • M ((x , nz) ⁻¹) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ (cright sym assoc) ⟩
      S^ (k * x⁻²) • (M ((x , nz) ⁻¹) • M (x , nz)) • M ((x , nz) ⁻¹) ≈⟨  (cright cleft (aux-M-mulˡ (x , nz))) ⟩
      S^ (k * x⁻²) • ε • M ((x , nz) ⁻¹) ≈⟨ cong refl left-unit ⟩
      S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ sym left-unit ⟩
      ε • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ (cleft sym ((aux-M-mulˡ (x , nz)))) ⟩
      (M ((x , nz) ⁻¹) • M (x , nz)) • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ assoc ⟩
      M ((x , nz) ⁻¹) • M (x , nz) • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ sym (cong refl assoc) ⟩
      M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹) ∎


  aux-H³M : ∀ m* → H ^ 3 • M m* ≈ M (m* ⁻¹) • H ^ 3
  aux-H³M m*  = begin
    H ^ 3 • M m* ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2 ) auto ⟩
    H ^ 2 • H • M m* ≈⟨ cright semi-HM m* ⟩
    H ^ 2 • M (m* ⁻¹) • H ≈⟨ sym assoc ⟩
    (H ^ 2 • M (m* ⁻¹)) • H ≈⟨ cleft aux-comm-HHM (m* ⁻¹) ⟩
    (M (m* ⁻¹) • H ^ 2) • H ≈⟨ trans assoc (cong refl assoc) ⟩
    M (m* ⁻¹) • H ^ 3 ∎
    where
    open SR word-setoid

  aux-H³M' : ∀ m'* → H ^ 3 • M (m'* ⁻¹) ≈ M m'* • H ^ 3
  aux-H³M' m'* = begin
    H ^ 3 • M (m'* ⁻¹) ≈⟨ aux-H³M (m'* ⁻¹) ⟩
    M (m'* ⁻¹ ⁻¹) • H ^ 3 ≈⟨ cleft aux-MM ((m'* ⁻¹ ⁻¹).proj₂) (m'* .proj₂) (inv-involutive m'* ) ⟩
    M (m'*) • H ^ 3 ∎
    where
    open SR word-setoid


module Lemmas3 where
  variable
    n : ℕ

  open Symplectic
  open import ForStdlib.Data.Fin.Mod
--  open Rewriting-Symplectic
  open Rewriting


  lemma-comm-Ex-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    Ex • w ↑ ↑ ≈ w ↑ ↑ • Ex
    
  lemma-comm-Ex-w↑↑ {n} [ H-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
    
  -- lemma-comm-Ex-w↑↑ {n} [ EX-gen ]ʷ = general-comm auto
  --   where
  --   open Commuting-Symplectic n
    
  lemma-comm-Ex-w↑↑ {n} [ S-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
  lemma-comm-Ex-w↑↑ {n} [ CZ-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
  lemma-comm-Ex-w↑↑ {n} [ x ↥ ]ʷ = begin
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (([ x ↥ ]ʷ ↑) ↑) ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑ ≈⟨ cong refl (sym (axiom (cong↑ comm-H))) ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑ ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • H ↑ ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • H ↑ ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
    ((CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
    ((CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    (CZ • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    (CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong ( (sym (axiom comm-CZ))) refl ⟩
    ([ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    [ x ↥ ]ʷ ↑ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ refl ⟩
    (([ x ↥ ]ʷ ↑) ↑) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-comm-Ex-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-comm-Ex-w↑↑ {n} (w • v) = begin
    Ex • (((w • v) ↑) ↑) ≈⟨ refl ⟩
    Ex • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
    (Ex • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-Ex-w↑↑ w) refl ⟩
    (w ↑ ↑ • Ex) • v ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • Ex • v ↑ ↑ ≈⟨ cong refl (lemma-comm-Ex-w↑↑ v) ⟩
    w ↑ ↑ • v ↑ ↑ • Ex ≈⟨ sym assoc ⟩
    (((w • v) ↑) ↑) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


-- ----------------------------------------------------------------------
-- * Duality

module Duality where

  open Symplectic
  open Commuting-Symplectic
  open Rewriting
  open Symplectic

  private
    variable
      n : ℕ

  -- Here, we provide a proof principle for duality (an equation is
  -- provable iff its dual is provable).


  -- Each generator has a dual, obtained by swapping the two qubits.
  dual-gen : Gen 2 → Gen 2
  dual-gen (gate₁ H-gate)        = gate₁ H-gate ↥
  dual-gen (gate₁ S-gate)        = gate₁ S-gate ↥
  dual-gen (gate₂ CZ-gate)       = gate₂ CZ-gate
--  dual-gen EX-gen = EX-gen
  dual-gen (gate₁ H-gate ↥)      = gate₁ H-gate
  dual-gen (gate₁ S-gate ↥)      = gate₁ S-gate
  dual-gen (((gate₀ ()) ↥) ↥)
  

  -- Compute the dual of a word.
  dual : Word (Gen 2) → Word (Gen 2)
  dual [ x ]ʷ = [ (dual-gen x) ]ʷ
  dual ε = ε
  dual (w • u) = dual w • dual u

  -- Lemma: duality is an involution.
  lemma-double-dual : ∀ w → w ≡ dual (dual w)
  lemma-double-dual ([ gate₁ H-gate ]ʷ)       = Eq.refl
  lemma-double-dual ([ gate₁ H-gate ↥ ]ʷ)     = Eq.refl
  lemma-double-dual ([ gate₁ S-gate ]ʷ)       = Eq.refl
  lemma-double-dual ([ gate₁ S-gate ↥ ]ʷ)     = Eq.refl
  lemma-double-dual ([ gate₂ CZ-gate ]ʷ)      = Eq.refl
  lemma-double-dual ([ ((gate₀ ()) ↥) ↥ ]ʷ)
--  lemma-double-dual ([ EX-gen ]ʷ) = Eq.refl
  lemma-double-dual ε = Eq.refl
  lemma-double-dual (w • v) = Eq.cong₂ _•_ (lemma-double-dual w) (lemma-double-dual v)


  aux-dual : ∀ w k → dual (w ^ k) ≡ dual w ^ k
  aux-dual w k@0 = auto
  aux-dual w k@1 = auto
  aux-dual w k@(₂₊ k') = begin
    dual (w ^ k) ≡⟨ auto ⟩
    dual w • dual (w ^ ₁₊ k') ≡⟨ (Eq.cong (dual w •_) (aux-dual w (₁₊ k'))) ⟩
    dual w • dual w ^ ₁₊ k' ≡⟨ auto ⟩
    dual w ^ k ∎
    where
    open ≡-Reasoning

  aux-↑ : ∀ (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  aux-↑ w k@0 = auto
  aux-↑ w k@1 = auto
  aux-↑ w k@(₂₊ k') = begin
    w ↑ ^ k ≡⟨ auto ⟩
    w ↑ • w ↑ ^ (₁₊ k') ≡⟨ (Eq.cong (w ↑ •_)  (aux-↑ w (₁₊ k'))) ⟩
    w ↑ • (w ^ (₁₊ k')) ↑ ≡⟨ auto ⟩
    (w ^ k) ↑ ∎
    where
    open ≡-Reasoning

  aux-dual-S⁻¹↑ : dual (S⁻¹ ↑) ≡ S⁻¹
  aux-dual-S⁻¹↑ = begin
    dual (S⁻¹ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S p-1)) ⟩
    dual (S ↑ ^ p-1) ≡⟨ aux-dual (S ↑) p-1 ⟩
    S⁻¹ ∎
    where
    open ≡-Reasoning

  aux-dual-S^k↑ : ∀ k → dual ((S ^ k) ↑) ≡ S ^ k
  aux-dual-S^k↑ k = begin
    dual ((S ^ k) ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S k)) ⟩
    dual (S ↑ ^ k) ≡⟨ aux-dual (S ↑) k ⟩
    S ^ k ∎
    where
    open ≡-Reasoning

  aux-dual-S⁻¹ : dual (S⁻¹ ↓) ≡ (S⁻¹ ↑)
  aux-dual-S⁻¹ = begin
    dual (S⁻¹ ↓) ≡⟨ aux-dual S p-1 ⟩
    S ↑ ^ p-1 ≡⟨ aux-↑ S p-1 ⟩
    (S⁻¹ ↑) ∎
    where
    open ≡-Reasoning

  aux-dual-S^k : ∀ k → dual ((S ^ k) ↓) ≡ (S ^ k) ↑
  aux-dual-S^k k = begin
    dual ((S ^ k) ↓) ≡⟨ aux-dual S k ⟩
    S ↑ ^ k ≡⟨ aux-↑ S k ⟩
    (S ^ k) ↑ ∎
    where
    open ≡-Reasoning


  aux-dual-CZ^k : ∀ k → dual ((CZ ^ k)) ≡ (CZ ^ k)
  aux-dual-CZ^k k = begin
    dual ((CZ ^ k)) ≡⟨ aux-dual CZ k ⟩
    CZ ^ k ≡⟨ auto ⟩
    (CZ ^ k) ∎
    where
    open ≡-Reasoning


  aux-dual-Mx : ∀ x → dual (M x) ≡ M x ↑
  aux-dual-Mx x' = begin
    dual (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≡⟨ Eq.cong₂ (\ xx yy → xx • H ↑ • yy • dual(H • S^ x • H)) (aux-dual-S^k (toℕ x)) (aux-dual-S^k (toℕ x⁻¹)) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • dual (H • S^ x • H) ≡⟨ Eq.cong (\ xx → S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • xx • H ↑)) (aux-dual-S^k (toℕ x)) ⟩
    M x' ↑ ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  aux-dual-Mx↑ : ∀ x → dual (M x ↑) ≡ M x
  aux-dual-Mx↑ x' = begin
    dual (S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong₂ (\ xx yy → xx • H • yy • dual(H ↑ • S^ x ↑ • H ↑)) (aux-dual-S^k↑ (toℕ x)) (aux-dual-S^k↑ (toℕ x⁻¹)) ⟩
    S^ x • H • S^ x⁻¹ • dual (H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong (\ xx → S^ x • H • S^ x⁻¹ • (H • xx • H)) (aux-dual-S^k↑ (toℕ x)) ⟩
    M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  -- Dualize a proof. Duality is useful early on. However, we will not
  -- prove the duals of axioms rel-A, rel-B, and rel-C until much
  -- later. Therefore, we work only with Clifford relations for the
  -- time being.
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid


  lemma-dual : ∀ {w u} → w === u → dual w ≈ dual u
  -- lemma-dual def-EX = begin
  --   EX ≈⟨ axiom def-EX ⟩
  --   Ex ≈⟨ general-comm 0 auto ⟩
  --   dual Ex ∎
  -- lemma-dual order-EX = axiom order-EX
  lemma-dual (srel Base.order-S) = begin
    S ↑ • dual (S ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual S p-1))) ⟩
    S ↑ • dual S ^ ₁₊ p-2 ≈⟨ refl ⟩
    S ↑ • (S ↑) ^ ₁₊ p-2 ≈⟨ (cright (refl' (aux-↑ S p-1))) ⟩
    (S ^ p) ↑ ≈⟨ axiom (cong↑ order-S) ⟩
    ε ∎
  lemma-dual (srel Base.order-H) = axiom (cong↑ order-H)
  lemma-dual (srel Base.order-SH) = axiom (cong↑ order-SH)
  lemma-dual (srel Base.comm-HHS) = axiom (cong↑ comm-HHS)
  lemma-dual (srel (Base.M-mul x y)) = begin
    dual (M x • M y) ≈⟨ cong (refl' (aux-dual-Mx x)) (refl' (aux-dual-Mx y)) ⟩
    (M x • M y) ↑ ≈⟨ axiom (cong↑ (M-mul x y)) ⟩
    M (x *' y) ↑ ≈⟨ refl' ((Eq.sym  (aux-dual-Mx (x *' y)))) ⟩
    dual (M (x *' y)) ∎
  lemma-dual (srel (Base.semi-MS x)) = begin
    dual (M x • S) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x • S) ↑ ≈⟨ axiom (cong↑ (semi-MS x)) ⟩
    (S^ (x ^2) • M x) ↑ ≈⟨ cong (refl' (Eq.sym (aux-dual-S^k (toℕ (fromℕ< _))))) (refl' (Eq.sym (aux-dual-Mx x))) ⟩
    dual (S^ (x ^2) • M x) ∎
  lemma-dual (srel (Base.semi-M↑CZ x)) = begin
    dual (M x ↑ • CZ) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    (M x • CZ) ≈⟨ axiom (semi-M↓CZ x) ⟩
    (CZ^ (x ^1) • M x) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx↑ x))) ⟩
    dual (CZ^ (x ^1) • M x ↑) ∎
  lemma-dual (srel (Base.semi-M↓CZ x)) = begin
    dual (M x • CZ) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x ↑ • CZ) ≈⟨ axiom (semi-M↑CZ x) ⟩
    (CZ^ (x ^1) • M x ↑) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx x))) ⟩
    dual (CZ^ (x ^1) • M x) ∎
  lemma-dual (srel Base.order-CZ) = begin
    CZ • dual (CZ ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual CZ p-1))) ⟩
    CZ • dual CZ ^ ₁₊ p-2 ≈⟨ refl ⟩
    (CZ ^ p) ≈⟨ axiom (order-CZ) ⟩
    ε ∎
  lemma-dual (srel Base.comm-CZ-S↓) = axiom comm-CZ-S↑
  lemma-dual (srel Base.comm-CZ-S↑) = axiom comm-CZ-S↓
  lemma-dual (srel Base.selinger-c10) = begin
    dual (CZ • H ↑ • CZ) ≈⟨ refl ⟩
    (CZ • H • CZ) ≈⟨ axiom selinger-c11 ⟩
    S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ sym (cong (refl' aux-dual-S⁻¹↑) (cright cong (refl' aux-dual-S⁻¹↑) (cright (cright cong (refl' aux-dual-S⁻¹↑) (refl' aux-dual-S⁻¹))))) ⟩
    dual (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) ∎
  lemma-dual (srel Base.selinger-c11) = begin
    dual (CZ • H ↓ • CZ) ≈⟨ refl ⟩
    (CZ • H ↑ • CZ) ≈⟨ axiom selinger-c10 ⟩
    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ≈⟨ sym (cong (refl' aux-dual-S⁻¹) (cright cong (refl' aux-dual-S⁻¹) (cright (cright cong (refl' aux-dual-S⁻¹) (refl' aux-dual-S⁻¹↑))))) ⟩
    dual (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) ∎
  lemma-dual (comm₁ H-gate (gate₁ S-gate)) = sym (axiom comm-S)
  lemma-dual (comm₁ H-gate (gate₁ H-gate)) = sym (axiom comm-H)
  lemma-dual (comm₁ S-gate (gate₁ S-gate)) = sym (axiom comm-S)
  lemma-dual (comm₁ S-gate (gate₁ H-gate)) = sym (axiom comm-H)
  -- The shifted generator can now sit at width 0, where only gate₀ lives.
  lemma-dual (comm₁ h (gate₀ ()))
  lemma-dual (comm₁ h ((gate₀ ()) ↥))
  lemma-dual (comm₂ h (gate₀ ()))
  lemma-dual (cong↑ (comm₁ h (gate₀ ())))
  lemma-dual (cong↑ (srel Base.order-S)) = begin
     S • dual ((S ^ p-1) ↑) ≈⟨ (cright refl' (Eq.cong dual (Eq.sym (aux-↑ S p-1)))) ⟩
     S • dual ((S ↑ ^ p-1)) ≈⟨ (cright refl' ( aux-dual (S ↑) p-1)) ⟩
     S • dual (S ↑) ^ p-1 ≈⟨ axiom order-S ⟩
     ε ∎
  lemma-dual (cong↑ (srel Base.order-H)) = axiom order-H
  lemma-dual (cong↑ (srel Base.order-SH)) = axiom order-SH
  lemma-dual (cong↑ (srel Base.comm-HHS)) = axiom comm-HHS
  lemma-dual (cong↑ (srel (Base.M-mul x y))) = begin
    dual ((M x • M y) ↑) ≈⟨ cong (refl' (aux-dual-Mx↑ x)) (refl' (aux-dual-Mx↑ y)) ⟩
    M x • M y ≈⟨ axiom (M-mul x y) ⟩
    M (x *' y) ≈⟨ sym (refl' (aux-dual-Mx↑ (x *' y))) ⟩
    dual (M (x *' y) ↑) ∎
  lemma-dual (cong↑ (srel (Base.semi-MS x))) = begin
    dual ((M x • S) ↑) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    M x • S ≈⟨ axiom (semi-MS x) ⟩
    S^ (x ^2) • M x ≈⟨ sym (cong (refl' (aux-dual-S^k↑ (toℕ (fromℕ< _)))) (refl' (aux-dual-Mx↑ x))) ⟩
    dual ((S^ (x ^2) • M x) ↑) ∎
  lemma-dual (cong↑ (cong↑ (srel ())))

  -- A proof principle for duality.
  by-duality : ∀ {w u} → w ≈ u → dual w ≈ dual u
  by-duality PB.refl = refl
  by-duality (PB.sym eq) = sym (by-duality eq)
  by-duality (PB.trans eq eq₁) = trans (by-duality eq) (by-duality eq₁)
  by-duality (PB.cong eq eq₁) = cong (by-duality eq) (by-duality eq₁)
  by-duality PB.assoc = assoc
  by-duality PB.left-unit = left-unit
  by-duality PB.right-unit = right-unit
  by-duality (PB.axiom x) = lemma-dual x


  -- A proof principle for duality.
  by-duality' : ∀ {w u w' u'} → w ≈ u → dual w ≈ w' → dual u ≈ u' → w' ≈ u'
  by-duality' eq eqw equ = trans (sym eqw) (trans (by-duality eq) equ)
