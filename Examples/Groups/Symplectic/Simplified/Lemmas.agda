------------------------------------------------------------------------
-- Presentations of groups
--
-- Derived rules: powers of S and H, and the M family
--
-- The core consequences of the simplified axioms at one wire: M ₁ ≈ ε,
-- the order of S • H, M-multiplicativity, semi-MS, and the order of H.
-- Together with the grouplike structure (every generator has a left
-- inverse) and the lemmas that need it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
open import Agda.Builtin.Nat using ()
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])


open import Data.Maybe
open import Data.Sum using ([_,_])

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
import Circuit.Base
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.Tactic.Rewriting

open import Presentation.Construct.Base hiding (_*_)


open import Data.Fin.Properties as FP using (toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module Examples.Groups.Symplectic.Simplified.Lemmas
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime as NSym
open Symplectic hiding (_QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ; order-S ; order-H ; semi-MS ; semi-M↑CZ ; semi-M↓CZ ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13 ; selinger-c14 ; selinger-c15)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen

module Lemmas1 (n : ℕ) where


  open Simplified-Relations

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx -> S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
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
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎

  lemma-M1 : M₁ ≈ ε
  lemma-M1 = begin
    M₁ ≡⟨ aux-M≡M ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (srel (M-power ₀))) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-order-SH : (S • H) ^ 3 ≈ ε
  lemma-order-SH = begin
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≈⟨ (cright (cright cong aux-S refl)) ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ refl ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid
    x' : ℤ* ₚ
    x' = (₁ , λ ())
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    aux-S : S ≈ S^ x⁻¹
    aux-S = begin
      S ≈⟨ refl ⟩
      S^ ₁ ≡⟨ Eq.cong S^ (Eq.sym aux₁⁻¹') ⟩
      S^ x⁻¹ ∎


  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid




  lemma-MgS^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • S ^ k ≈ S ^ (k Nat.* toℕ (g * g)) • Mg
  lemma-MgS^k k@0 = trans right-unit (sym left-unit)
  lemma-MgS^k k@1 = begin  
    Mg • S ^ k ≈⟨ refl ⟩
    Mg • S ≈⟨ axiom (srel semi-MS) ⟩
    S^ (g * g) • Mg ≈⟨ refl ⟩
    S ^ toℕ (g * g) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (g * g)))))) ⟩
    S ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid
  lemma-MgS^k k@(₂₊ k') = begin  
    Mg • S ^ k ≈⟨ refl ⟩
    Mg • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • S) • S ^ ₁₊ k' ≈⟨ (cleft lemma-MgS^k 1 ) ⟩
    (S ^ (1 Nat.* toℕ (g * g)) • Mg) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (g * g)) • Mg • S ^ ₁₊ k' ≈⟨ (cright lemma-MgS^k (₁₊ k')) ⟩
    S ^ (1 Nat.* toℕ (g * g)) • S ^ (₁₊ k' Nat.* toℕ (g * g)) • Mg ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (g * g)) • S ^ (₁₊ k' Nat.* toℕ (g * g))) • Mg ≈⟨ (cleft sym (^-+ S ((1 Nat.* toℕ (g * g))) ((₁₊ k' Nat.* toℕ (g * g))))) ⟩
    (S ^ ((1 Nat.* toℕ (g * g)) Nat.+ (₁₊ k' Nat.* toℕ (g * g)))) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (g * g)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (g * g) ) • Mg ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid

  lemma-S^k-% : ∀ k -> S ^ k ≈ S ^ (k % p)
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


  lemma-MgS^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • S^ k ≈ S^ (k * (g * g)) • Mg
  lemma-MgS^k' k = begin 
    Mg • S^ k ≈⟨ refl ⟩
    Mg • S ^ toℕ k ≈⟨ lemma-MgS^k (toℕ k) ⟩
    S ^ (toℕ k Nat.* toℕ (g * g)) • Mg ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (g * g))) ⟩
    S ^ ((toℕ k Nat.* toℕ (g * g)) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (g * g)))) ⟩
    S ^ toℕ (k * (g * g)) • Mg ≈⟨ refl ⟩
    S^ (k * (g * g)) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^kS : ∀ k -> Mg ^ k • S ≈ S^ ((g * g) ^′ k) • Mg ^ k
  lemma-Mg^kS k@0 = trans left-unit (sym right-unit)
  lemma-Mg^kS k@1 = begin
    Mg ^ k • S ≈⟨ axiom (srel semi-MS) ⟩
    S^ ((g * g)) • Mg ^ k ≈⟨ (cleft refl' (Eq.cong S^ (Eq.sym (lemma-x^′1=x (fromℕ< _))))) ⟩
    S^ ((g * g) ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^kS k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • S ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • S ≈⟨ (cright lemma-Mg^kS (₁₊ n)) ⟩
    Mg • S^ ((g * g) ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • S^ ((g * g) ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-MgS^k' ((g * g) ^′ (₁₊ n))) ⟩
    (S^ (((g * g) ^′ (₁₊ n)) * (g * g)) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (S^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm ((g * g) ^′ (₁₊ n)) (g * g))) ⟩
    (S^ ((g * g) * ((g * g) ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    S^ ((g * g) ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid


  lemma-semi-MS : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • S ≈ S^ ((x' * x')) • M x
  lemma-semi-MS x = begin
    M x • S ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • S ≈⟨ cong (sym (axiom (srel (M-power (k))))) refl ⟩
    Mg^ k • S ≈⟨ lemma-Mg^kS (toℕ k) ⟩
    S^ ((g * g) ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (srel (M-power (k)))) ⟩
    S^ ((g * g) ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong S^ (*-^′-distribʳ g g (toℕ k)))) ⟩
    S^ ((g ^′ toℕ k) * (g ^′ toℕ k)) • M (g^ k) ≈⟨ sym (cleft refl' (Eq.cong₂ (\ xx yy -> S^ (xx * yy)) (eqk) (eqk))) ⟩
    S^ (x' * x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    S^ (x' * x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)



  open import Data.Fin.Properties
  
  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (srel (M-power (₁₊ (fromℕ< _)))) ⟩
    M (g^ p-1') ≡⟨ aux-M≡M (g^ p-1') ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    M (g ^′ p-1 , lemma-g^′k≠0 p-1) ≡⟨ aux-M≡M ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (1ₚ , λ ()) Fermat's-little-theorem' ⟩
    M (1ₚ , λ ()) ≈⟨ sym (axiom (srel (M-power ₀))) ⟩
    ε ∎
    where
    open SR word-setoid
    p-1' = fromℕ< (NP.n<1+n p-1)

  aux-Mg^[kp-1] : ∀ k -> Mg ^ (k Nat.* p-1) ≈ ε
  aux-Mg^[kp-1] k = begin
    Mg ^ (k Nat.* p-1) ≈⟨ refl' (Eq.cong (Mg ^_) (NP.*-comm k p-1)) ⟩
    Mg ^ (p-1 Nat.* k) ≈⟨ sym (^^ Mg p-1 k) ⟩
    (Mg ^ p-1) ^ k ≈⟨ ^-cong (Mg ^ p-1) ε k lemma-Mg^p-1=ε ⟩
    ε ^ k ≈⟨ ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
  lemma-M-mul x y = begin
    M x • M y ≈⟨ cong (refl' (aux-M≡M x (g^ k) eqk)) (refl' (aux-M≡M y (g^ l) eql)) ⟩
    M (g^ k) • M (g^ l) ≈⟨ cong (sym (axiom (srel (M-power k)))) (sym (axiom (srel (M-power l)))) ⟩
    Mg ^ toℕ k • Mg ^ toℕ l ≈⟨ sym (^-+ Mg (toℕ k) (toℕ l)) ⟩
    Mg ^ [k+l] ≡⟨ Eq.cong (Mg ^_) (m≡m%n+[m/n]*n [k+l] p-1) ⟩
    Mg ^ ([k+l]%p-1 Nat.+ [k+l]/p-1 Nat.* p-1) ≈⟨ ^-+ Mg [k+l]%p-1 (([k+l]/p-1 Nat.* p-1)) ⟩
    Mg ^ [k+l]%p-1 • Mg ^ ([k+l]/p-1 Nat.* p-1) ≈⟨ (cright trans refl (aux-Mg^[kp-1] [k+l]/p-1)) ⟩
    Mg ^ [k+l]%p-1 • ε ≈⟨ right-unit ⟩
    Mg ^ [k+l]%p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (m%n<n [k+l] p-1))) ⟩
    Mg ^ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1))))) ⟩
    Mg ^ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ refl ⟩
    Mg^ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ axiom (srel (M-power (inject₁ (fromℕ< (m%n<n [k+l] p-1))))) ⟩
    M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ≡⟨ aux-M≡M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) (g^′ [k+l]) aux-2 ⟩
    M (g^′ [k+l]) ≡⟨ aux-M≡M (g^′ [k+l]) (g^′ toℕ k *' g^′ toℕ l) aux-1 ⟩
    M (g^′ toℕ k *' g^′ toℕ l) ≡⟨ aux-M≡M (g^′ toℕ k *' g^′ toℕ l) (x *' y) aux-0 ⟩
    M (x *' y) ∎
    where
    k = inject₁ (g-gen x .proj₁)
    l = inject₁ (g-gen y .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)
    eql : y .proj₁ ≡ (g^ l) .proj₁
    eql = Eq.sym (lemma-log-inject y)

    [k+l] = toℕ k Nat.+ toℕ l
    [k+l]%p-1 = [k+l] Nat.% p-1
    [k+l]/p-1 = [k+l] Nat./ p-1

    aux-0 : ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡ (x *' y) .proj₁
    aux-0 = begin
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡⟨ auto ⟩
      (g^′ toℕ k) .proj₁ * (g^′ toℕ l) .proj₁ ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) ) (lemma-log-inject x) (lemma-log-inject y) ⟩
      x .proj₁ * y .proj₁ ≡⟨ auto ⟩
      (x *' y) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-1 : (g^′ [k+l]) .proj₁ ≡ ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁
    aux-1 = begin
      (g^′ [k+l]) .proj₁ ≡⟨ auto ⟩
      (g ^′ [k+l]) ≡⟨ Eq.sym (+-^′-distribʳ g (toℕ k) (toℕ l)) ⟩
      ((g ^′ toℕ k) * (g ^′ toℕ l)) ≡⟨ auto ⟩
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-2 : g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡ g ^′ (toℕ k Nat.+ toℕ l)
    aux-2 = begin
      g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1)))) ⟩
      g ^′ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-fromℕ< ((m%n<n [k+l] p-1))) ⟩
      g ^′ [k+l]%p-1 ≡⟨ Eq.sym (aux-g^′-% [k+l]) ⟩
      g ^′ (toℕ k Nat.+ toℕ l) ∎
      where
      open ≡-Reasoning

    open SR word-setoid


  lemma-M₋₁^2 : M₋₁ ^ 2 ≈ ε
  lemma-M₋₁^2 = begin
    M₋₁ ^ 2 ≈⟨ lemma-M-mul -'₁ -'₁ ⟩
    M (-'₁ *' -'₁) ≡⟨ aux-M≡M (-'₁ *' -'₁) (₁ , (λ ())) aux-0 ⟩
    M₁ ≈⟨ sym (sym lemma-M1) ⟩
    ε ∎
    where
    open import Algebra.Properties.Ring (+-*-ring p-2)
    
    aux-0 : (-'₁ *' -'₁) .proj₁ ≡ ₁
    aux-0 = begin
      (- ₁ * - ₁) ≡⟨ -1*x≈-x (- ₁) ⟩
      (- - ₁) ≡⟨ -‿involutive ₁ ⟩
      ₁ ∎
      where
      open ≡-Reasoning
    open SR word-setoid

  lemma-order-H : H ^ 4 ≈ ε
  lemma-order-H = begin
    H ^ 4 ≈⟨ sym assoc ⟩
    HH ^ 2 ≈⟨ cong (axiom (srel order-H)) (axiom (srel order-H)) ⟩
    M₋₁ ^ 2 ≈⟨ lemma-M₋₁^2 ⟩
    ε ∎
    where
    open SR word-setoid

module Symplectic-Sim-GroupLike where

  private
    variable
      n : ℕ
    
  open Simplified-Relations
  open Lemmas-Sim


  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Lemmas1 n
    claim : (H ) ^ 3 • H ≈ ε
    claim = begin
      (H) ^ 3 • H ≈⟨ by-assoc auto ⟩
      (H) ^ 4 ≈⟨ lemma-order-H ⟩
      ε ∎

  grouplike {₁₊ n} (S-gen) = (S) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (S) ^ p-1 • S ≈ ε
    claim = begin
      (S) ^ p-1 • S ≈⟨ sym (^-+ (S) p-1 1) ⟩
      (S) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) ( NP.+-comm p-1 1) ⟩
      (S ^ p) ≈⟨ (axiom (srel order-S)) ⟩
      (ε) ∎

  grouplike {₂₊ n} (CZ-gen) = (CZ) ^ p-1 ,  claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : (CZ) ^ p-1 • CZ ≈ ε
    claim = begin
      (CZ) ^ p-1 • CZ ≈⟨ sym (^-+ (CZ) p-1 1) ⟩
      (CZ) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (CZ ^_) ( NP.+-comm p-1 1) ⟩
      (CZ ^ p) ≈⟨ (axiom (srel order-CZ)) ⟩
      (ε) ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)

module Lemmas1b (n : ℕ) where


  open Simplified-Relations

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open Symplectic-Sim-GroupLike
  open import Data.Nat.DivMod
  open import Data.Fin.Properties

  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ ⁻¹-cong (lemma-order-SH) ⟩
    winv ε ≈⟨ refl ⟩
    ε ∎
    where
    open Lemmas1 n
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
    open Pattern-Assoc

  derived-5 : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in

    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ lemma-semi-MS (x , nz) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    open Lemmas1 n
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


  lemma-MS^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ refl ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open Lemmas1 n    
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-comm-HHS : H • H • S ≈ S • H • H
  lemma-comm-HHS = begin
    H • H • S ≈⟨ sym assoc ⟩
    HH • S ≈⟨ (cleft axiom (srel order-H)) ⟩
    M₋₁ • S ≈⟨ lemma-semi-MS -'₁ ⟩
    S^ (- ₁ * - ₁) • M₋₁ ≈⟨ (cleft refl' (Eq.cong S^ aux-0)) ⟩
    S^ ₁ • M₋₁ ≈⟨ refl ⟩
    S • M₋₁ ≈⟨ (cright sym (axiom (srel order-H))) ⟩
    S • H • H ∎
    where
    open Lemmas1 n    
    open import Algebra.Properties.Ring (+-*-ring p-2)

    aux-0 : (-'₁ *' -'₁) .proj₁ ≡ ₁
    aux-0 = begin
      (- ₁ * - ₁) ≡⟨ -1*x≈-x (- ₁) ⟩
      (- - ₁) ≡⟨ -‿involutive ₁ ⟩
      ₁ ∎
      where
      open ≡-Reasoning
    
    open SR word-setoid
