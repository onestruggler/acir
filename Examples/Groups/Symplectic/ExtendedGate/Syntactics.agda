{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (_∘_)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃ ; Σ-syntax)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality


module Examples.Groups.Symplectic.ExtendedGate.Syntactics (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where


open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

module Symplectic-Derived-Gen where

  
  -- The gate alphabet: single-qupit gates H (order 4, ℤ₄-indexed) and
  -- S (ℤₚ-indexed), and the two-qupit gate CZ (ℤₚ-indexed).  The
  -- wire-indexed generators Gen, circuits, the shifts _↑/_↓/_↥ᵏ_ and the
  -- Lift-Relation machinery are all inherited from Circuit.Base; a
  -- generator here is gate₁ (H-gen k), gate₁ (S-gen k) or gate₂ (CZ-gen k).
  data Gate : ℕ → Set where
    H-gen  : ℤ ₄ → Gate 1
    S-gen  : ℤ ₚ → Gate 1
    CZ-gen : ℤ ₚ → Gate 2

  open import Circuit.Base Gate public

  [_⇑] : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
  [_⇑] {n} = ([_]ʷ ∘ _↥) WB.ʷ

  [_⇑]' : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
  [_⇑]' {n} = wmap _↥

  _↓-gen : ∀ {n} → Gen n → Gen (₁₊ n)
  _↓-gen {zero} (gate₀ ())
  _↓-gen {₁₊ n} (gate₁ h) = gate₁ h
  _↓-gen {₁₊ .(₁₊ _)} (gate₂ h) = gate₂ h
  _↓-gen {₁₊ n} (g ↥) = (g ↓-gen) ↥


  lemma-[⇑]=[⇑]' : ∀ {n} (w : Word (Gen n)) → [ w ⇑] ≡ [ w ⇑]'
  lemma-[⇑]=[⇑]' {n} [ x ]ʷ = Eq.refl
  lemma-[⇑]=[⇑]' {n} ε = Eq.refl
  lemma-[⇑]=[⇑]' {n} (w • w₁) = Eq.cong₂ _•_ (lemma-[⇑]=[⇑]' w) (lemma-[⇑]=[⇑]' w₁)

  S : ∀ {n} → Word (Gen (₁₊ n))
  S = [ gate₁ (S-gen ₁) ]ʷ

  S⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  S⁻¹ = S ^ p-1
  
  H : ∀ {n} → Word (Gen (₁₊ n))
  H = [ gate₁ (H-gen ₁) ]ʷ

  H⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  H⁻¹ = H ^ 3

  HH : ∀ {n} → Word (Gen (₁₊ n))
  HH = H ^ 2

  SH : ∀ {n} → Word (Gen (₁₊ n))
  SH = S • H

  CZ : ∀ {n} → Word (Gen (₂₊ n))
  CZ = [ gate₂ (CZ-gen ₁) ]ʷ

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

  ₕ|ₕ : ∀ {n} → Word (Gen (₂₊ n))
  ₕ|ₕ = H ↓ • CZ • H ↓

  ʰ|ʰ : ∀ {n} → Word (Gen (₂₊ n))
  ʰ|ʰ = H ↑ • CZ • H ↑

  ⊥⊤ : ∀ {n} → Word (Gen (₂₊ n))
  ⊥⊤ = ₕ|ₕ • ʰ|ʰ

  ⊤⊥ : ∀ {n} → Word (Gen (₂₊ n))
  ⊤⊥ = ʰ|ʰ • ₕ|ₕ

  H^ : ∀ {n} → ℤ ₄ → Word (Gen (₁₊ n))
  H^ k = [ gate₁ (H-gen k) ]ʷ

  S^ : ∀ {n} → ℤ ₚ → Word (Gen (₁₊ n))
  S^ k = [ gate₁ (S-gen k) ]ʷ

  CZ^ : ∀ {n} → ℤ ₚ → Word (Gen (₂₊ n))
  CZ^ k = [ gate₂ (CZ-gen k) ]ʷ

  M : ∀ {n} → ℤ* ₚ → Word (Gen (₁₊ n))
  M x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  M₁ : ∀ {n} → Word (Gen (₁₊ n))
  M₁ = M (₁ , λ ())

  infixr 9 _^2
  _^2 : ℤ* ₚ → ℤ ₚ
  _^2 x' = let x = x' .proj₁ in x * x 

  infixr 9 _^1
  _^1 : ℤ* ₚ → ℤ ₚ
  _^1 x' = let x = x' .proj₁ in x

  -- The qupit-specific relations.  The structural rules — congruence
  -- under wire-shifting (cong↑) and gates commuting past shifted-up
  -- generators (comm₁/comm₂) — are supplied by Circuit.Base.Lift-Relation
  -- below, and so are omitted here.  (The old comm-H/comm-S/comm-CZ are
  -- the comm₁/comm₂ instances at gate₁ (H-gen ₁)/gate₁ (S-gen ₁)/
  -- gate₂ (CZ-gen ₁).)
  infix 4 _Q,_===_
  data _Q,_===_ : (n : ℕ) → CRel n where

    order-S :      ∀ {n} → (₁₊ n) Q,  S ^ p === ε
    order-H :      ∀ {n} → (₁₊ n) Q,  H ^ 4 === ε
    order-SH :     ∀ {n} → (₁₊ n) Q,  (S • H) ^ 3 === ε
    comm-HHS :     ∀ {n} → (₁₊ n) Q,  H • H • S === S • H • H

    M-mul :    ∀ {n} x y → (₁₊ n) Q,  M x • M y === M (x *' y)
    semi-MS :    ∀ {n} x → (₁₊ n) Q,  M x • S === S^ (x ^2) • M x
    semi-M↑CZ :  ∀ {n} x → (₂₊ n) Q,  M x ↑ • CZ === CZ^ (x ^1) • M x ↑
    semi-M↓CZ :  ∀ {n} x → (₂₊ n) Q,  M x ↓ • CZ === CZ^ (x ^1) • M x ↓

    order-CZ :     ∀ {n} → (₂₊ n) Q,  CZ ^ p === ε

    comm-CZ-S↓ :   ∀ {n} → (₂₊ n) Q,  CZ • S ↓ === S ↓ • CZ
    comm-CZ-S↑ :   ∀ {n} → (₂₊ n) Q,  CZ • S ↑ === S ↑ • CZ

    selinger-c10 : ∀ {n} → (₂₊ n) Q,  CZ • H ↑ • CZ === S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
    selinger-c11 : ∀ {n} → (₂₊ n) Q,  CZ • H ↓ • CZ === S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    selinger-c12 : ∀ {n} → (₃₊ n) Q,  CZ ↑ • CZ === CZ • CZ ↑
    selinger-c13 : ∀ {n} → (₃₊ n) Q,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓

    selinger-c14 : ∀ {n} → (₃₊ n) Q,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
    selinger-c15 : ∀ {n} → (₃₊ n) Q,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

    derived-S :  ∀ {n} k → (₁₊ n) Q,  S^ k === S ^ toℕ k
    derived-H :  ∀ {n} k → (₁₊ n) Q,  H^ k === H ^ toℕ k
    derived-CZ : ∀ {n} k → (₂₊ n) Q,  CZ^ k === CZ ^ toℕ k

  -- The full relation: the qupit-specific rules together with the
  -- structural rules (srel / cong↑ / comm₁ / comm₂) from Lift-Relation.
  open Lift-Relation _Q,_===_ public

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → CRel n
  _QRel,_===_ = _VRel,_===_

  lemma-cong↓-S^ : ∀ {n} k → let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ≈↓ S ^ k
  lemma-cong↓-S^ {n} ₀ = PB.refl
  lemma-cong↓-S^ {n} ₁ = PB.refl
  lemma-cong↓-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^ {n} (₁₊ k))


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


  lemma-comm-S-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    S • w ↑ ≈ w ↑ • S
    
  lemma-comm-S-w↑ {n} [ x ]ʷ = sym (axiom (comm₁ (S-gen ₁) x))
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
    
  lemma-comm-H-w↑ {n} [ x ]ʷ = sym (axiom (comm₁ (H-gen ₁) x))
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

  lemma-comm-CZ-w↑ : ∀ {n} w → let open PB ((₃₊ n) QRel,_===_) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑ {n} [ x ]ʷ = sym (axiom (comm₂ (CZ-gen ₁) x))
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

  -- lemma-comm-H↑-M : ∀ {n} m → let open PB ((₂₊ n) QRel,_===_) in
    
  --   H ↑ • M m ≈ M m • H ↑

  -- lemma-comm-H↑-M {n} m = begin    
  --   H ↑ • M m ≈⟨ {!!} ⟩
  --   M m • H ↑ ∎
  --   where
  --   open PB ((₂₊ n) QRel,_===_)
  --   open PP ((₂₊ n) QRel,_===_)
  --   open SR word-setoid


module Symplectic-Derived-GroupLike where
  private
    variable
      n : ℕ

  open Symplectic-Derived-Gen
  
  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (gate₁ (H-gen k)) = (H ^ toℕ k) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (H ^ toℕ k) ^ 3 • H^ k ≈ ε
    claim = begin
      (H ^ toℕ k) ^ 3 • H^ k ≈⟨ (cright axiom (srel (derived-H k))) ⟩
      (H ^ toℕ k) ^ 3 • H ^ toℕ k ≈⟨ sym (^-+ (H ^ toℕ k) 3 1) ⟩
      (H ^ toℕ k) ^ 4 ≈⟨ ^^' H (toℕ k) 4 ⟩
      (H ^ 4) ^ toℕ k ≈⟨ ^-cong (H ^ 4) ε (toℕ k) (axiom (srel order-H)) ⟩
      (ε) ^ toℕ k ≈⟨ ε^k=ε (toℕ k) ⟩
      ε ∎

  grouplike {₁₊ n} (gate₁ (S-gen k)) = (S ^ toℕ k) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (S ^ toℕ k) ^ p-1 • S^ k ≈ ε
    claim = begin
      (S ^ toℕ k) ^ p-1 • S^ k ≈⟨ (cright axiom (srel (derived-S k))) ⟩
      (S ^ toℕ k) ^ p-1 • S ^ toℕ k ≈⟨ sym (^-+ (S ^ toℕ k) p-1 1) ⟩
      (S ^ toℕ k) ^ (p-1 Nat.+ 1) ≈⟨ ^^' S (toℕ k) (p-1 Nat.+ 1) ⟩
      (S ^ (p-1 Nat.+ 1)) ^ toℕ k ≈⟨ ^-cong (S ^ (p-1 Nat.+ 1)) (S ^ p) (toℕ k) (refl' (Eq.cong (S ^_) (NP.+-comm p-1 1))) ⟩
      (S ^ p) ^ toℕ k ≈⟨ ^-cong (S ^ p) ε (toℕ k) (axiom (srel order-S)) ⟩
      (ε) ^ toℕ k ≈⟨ ε^k=ε (toℕ k) ⟩
      ε ∎

  grouplike {₂₊ n} (gate₂ (CZ-gen k)) = (CZ ^ toℕ k) ^ p-1 ,  claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : (CZ ^ toℕ k) ^ p-1 • CZ^ k ≈ ε
    claim = begin
      (CZ ^ toℕ k) ^ p-1 • CZ^ k ≈⟨ (cright axiom (srel (derived-CZ k))) ⟩
      (CZ ^ toℕ k) ^ p-1 • CZ ^ toℕ k ≈⟨ sym (^-+ (CZ ^ toℕ k) p-1 1) ⟩
      (CZ ^ toℕ k) ^ (p-1 Nat.+ 1) ≈⟨ ^^' CZ (toℕ k) (p-1 Nat.+ 1) ⟩
      (CZ ^ (p-1 Nat.+ 1)) ^ toℕ k ≈⟨ ^-cong (CZ ^ (p-1 Nat.+ 1)) (CZ ^ p) (toℕ k) (refl' (Eq.cong (CZ ^_) (NP.+-comm p-1 1))) ⟩
      (CZ ^ p) ^ toℕ k ≈⟨ ^-cong (CZ ^ p) ε (toℕ k) (axiom (srel order-CZ)) ⟩
      (ε) ^ toℕ k ≈⟨ ε^k=ε (toℕ k) ⟩
      ε ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
  -- At width 1 the shifted generator would live in Gen 0, where the only
  -- constructor is gate₀ and this gate set has no 0-ary gate.
  grouplike ((gate₀ ()) ↥)


  import Data.Nat.Literals as NL
  open import Agda.Builtin.FromNat
  open import Data.Unit.Base using (⊤)
  open import Data.Fin.Literals
  import Data.Nat.Literals as NL


  instance
    Numℕ' : Number ℕ
    Numℕ' = NL.number 

  instance
    NumFin' : Number (Fin p)
    NumFin' = number p


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


module Lemmas00 where

  variable
    n : ℕ

  -- open Lemmas hiding (n)
  -- open Lemmas2 hiding (n)
  -- open Lemmas3 hiding (n)

  open import ForStdlib.Data.Fin.Mod
  open Rewriting

  -- lemma-semi-CZ-HH↓ : let open PB ((₂₊ n) QRel,_===_) in

  --   CZ • H ↓ ^ 2 ≈ H ↓ ^ 2 • CZ^ ₋₁
    
  -- lemma-semi-CZ-HH↓ = {!!}
    

module Symplectic-Powers0 where

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.
  variable
    n : ℕ

  open Symplectic-Derived-Gen
  open Rewriting


  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  -- step-order (((gate₁ (S-gen ₁))) ∷ ((gate₁ (S-gen ₁))) ∷ ((gate₁ (S-gen ₁))) ∷ xs) = just (xs , at-head (PB.axiom (srel order-S)))
  -- step-order (((gate₁ (S-gen ₁)) ↥) ∷ ((gate₁ (S-gen ₁)) ↥) ∷ ((gate₁ (S-gen ₁)) ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  -- step-order (((gate₁ (S-gen ₁)) ↥ ↥) ∷ ((gate₁ (S-gen ₁)) ↥ ↥) ∷ ((gate₁ (S-gen ₁)) ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-order (((gate₁ (H-gen ₁))) ∷ ((gate₁ (H-gen ₁))) ∷ ((gate₁ (H-gen ₁))) ∷ ((gate₁ (H-gen ₁))) ∷ xs) = just (xs , at-head (PB.axiom (srel order-H)))
  step-order (((gate₁ (H-gen ₁)) ↥) ∷ ((gate₁ (H-gen ₁)) ↥) ∷ ((gate₁ (H-gen ₁)) ↥) ∷ ((gate₁ (H-gen ₁)) ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (srel order-H))))
  step-order (((gate₁ (H-gen ₁)) ↥ ↥) ∷ ((gate₁ (H-gen ₁)) ↥ ↥) ∷ ((gate₁ (H-gen ₁)) ↥ ↥) ∷ ((gate₁ (H-gen ₁)) ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ (srel order-H)))))
  -- step-order ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom (srel order-CZ)))
  -- step-order ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-order (((gate₁ (S-gen ₁))) ∷ ((gate₁ (H-gen ₁))) ∷ ((gate₁ (S-gen ₁))) ∷ ((gate₁ (H-gen ₁))) ∷ ((gate₁ (S-gen ₁))) ∷ ((gate₁ (H-gen ₁))) ∷ xs) = just (xs , at-head (PB.axiom (srel order-SH)))
  step-order (((gate₁ (S-gen ₁)) ↥) ∷ ((gate₁ (H-gen ₁)) ↥) ∷ ((gate₁ (S-gen ₁)) ↥) ∷ ((gate₁ (H-gen ₁)) ↥) ∷ ((gate₁ (S-gen ₁)) ↥) ∷ ((gate₁ (H-gen ₁)) ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (srel order-SH))))
  step-order (((gate₁ (S-gen ₁)) ↥ ↥) ∷ ((gate₁ (H-gen ₁)) ↥ ↥) ∷ ((gate₁ (S-gen ₁)) ↥ ↥) ∷ ((gate₁ (H-gen ₁)) ↥ ↥) ∷ ((gate₁ (S-gen ₁)) ↥ ↥) ∷ ((gate₁ (H-gen ₁)) ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ (srel order-SH)))))

--  step-order (CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ xs) = just (xs , at-head (PB.axiom lemma-order-Ex))
--  step-order (CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-Ex)))
  

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
module Powers0-Symplectic (n : ℕ) where

  open Rewriting
  open Symplectic-Powers0 hiding (n)
  open Rewriting.Step (step-cong (step-order {n})) renaming (general-rewrite to general-powers0) public

module Lemmas0 (n : ℕ) where

  open Symplectic-Derived-Gen
  open Symplectic-Derived-GroupLike
  open import ForStdlib.Data.Fin.Mod

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-S^k+l : ∀ k l → S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ cong (axiom (srel (derived-S k))) (axiom (srel (derived-S l))) ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ ^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (axiom (srel (derived-S (k + l))))) (sym (^^ S p (k+l Nat./ p))) ⟩
    S^ (k + l) • (S ^ p) ^ (k+l Nat./ p) ≈⟨ cright (^-cong (S ^ p) ε (k+l Nat./ p) (axiom (srel order-S))) ⟩
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
    S^ ₀ ≈⟨ axiom (srel (derived-S ₀)) ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k → S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ cong (axiom (srel (derived-S (- k)))) (axiom (srel (derived-S k))) ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ comm⇒pow-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ cong (sym (axiom (srel (derived-S k)))) (sym (axiom (srel (derived-S (- k))))) ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  
  lemma-M1 : ε ≈ M (₁ , λ ())
  lemma-M1 = begin
    ε ≈⟨ _≈_.sym (axiom (srel order-SH)) ⟩
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≡⟨ auto ⟩
    S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx → S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
    S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
    M (₁ , λ ()) ∎
    where
    open SR word-setoid


  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ ⁻¹-cong (axiom (srel order-SH)) ⟩
    winv ε ≈⟨ refl ⟩
    ε ∎
    where
    open Group-Lemmas _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright inverseˡ) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ by-passoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ inverseˡ ⟩
    ε ∎
    where
    open Group-Lemmas _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ sym (axiom (srel (derived-S ₚ₋₁))) ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid

  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright ^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (by-passoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft comm⇒pow-comm 1 p-1 (trans assoc (axiom (srel comm-HHS))))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft comm⇒pow-comm p-1 1 (sym (trans assoc (axiom (srel comm-HHS))))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright general-powers0 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ by-passoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft general-powers0 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ by-passoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright (cleft lemma-S⁻¹))) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx → S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy → S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx → S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where
    open Powers0-Symplectic n

    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁
    open SR word-setoid


  derived-D : ∀ x → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (axiom (srel order-H)) refl) ⟩
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
    M (x , nz) • S ≈⟨ axiom (srel (semi-MS (x , nz))) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ cong (axiom (srel (derived-S (x * x)))) refl ⟩
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
    S ^ (k Nat.% p) • (S ^ p) ^ (k Nat./ p) ≈⟨ (cright ^-cong (S ^ p) ε (k Nat./ p) (axiom (srel order-S))) ⟩
    S ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright ε^k=ε (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    S ^ (k % p) ∎
    where
    open SR word-setoid

  lemma-MS^k : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ cong refl (axiom (srel (derived-S k))) ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ cong (sym (axiom (srel (derived-S (k * (x * x)))))) refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
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
    S ^ (ab Nat.% p) • (ε) ^ (ab Nat./ p) ≈⟨ (cright sym (^-cong (S ^ p) ε (ab Nat./ p) (axiom (srel order-S)))) ⟩
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
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft (cright axiom (srel (derived-S -x⁻¹)))) ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft axiom (srel (M-mul (y , nzy) ((x , nz) ⁻¹)))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright by-passoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft axiom (srel (M-mul ((y , nzy) *' ((x , nz) ⁻¹)) -'₁))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ cong (sym (axiom (srel (derived-S (-x⁻¹ * (y * y)))))) refl ⟩
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


  semi-HM : ∀ (x : ℤ* ₚ) → H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ by-assoc auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong lemma-M1 refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-passoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright by-assoc auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft axiom (srel (M-mul (-' (x' ⁻¹)) -'₁))) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨ by-assoc auto ⟩
    (S^ -x⁻¹ • S^ x⁻¹) • M (x' ⁻¹) • H ≈⟨ (cleft lemma-S^-k+k x⁻¹) ⟩
    ε • M (x' ⁻¹) • H ≈⟨ left-unit ⟩
    M (x' ⁻¹) • H ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

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


module Lemmas-1 (n : ℕ) where

  open Symplectic-Derived-Gen
  open Symplectic-Derived-GroupLike
  open import ForStdlib.Data.Fin.Mod

  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-CZ^k-% : ∀ k → CZ ^ k ≈ CZ ^ (k % p)
  lemma-CZ^k-% k = begin
    CZ ^ k ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k p) ⟩
    CZ ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ ^-+ CZ (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    CZ ^ (k Nat.% p) • CZ ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (CZ ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    CZ ^ (k Nat.% p) • CZ ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright ^^ CZ p (k Nat./ p)) ⟩
    CZ ^ (k Nat.% p) • (CZ ^ p) ^ (k Nat./ p) ≈⟨ (cright ^-cong (CZ ^ p) ε (k Nat./ p) (axiom (srel order-CZ))) ⟩
    CZ ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright ε^k=ε (k Nat./ p)) ⟩
    CZ ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    CZ ^ (k % p) ∎
    where
    open SR word-setoid
