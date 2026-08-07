-- {-# OPTIONS --cubical-compatible --allow-unsolved-metas #-}
{-# OPTIONS --cubical-compatible --safe #-}
-- {-# OPTIONS --prop #-}
{-# OPTIONS --termination-depth=20 #-}


open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

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
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
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

module Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where




open Primitive-Root-Modp' g* g-gen

module Symplectic-Simplified where

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
-- Same hiding list as Part1: only Symplectic's generator layer is taken
-- (see Part1 for the full note).
open Symplectic hiding
  ( _QRel,_===_ ; M ; M₁ ; module Base
  ; order-S ; order-H ; order-SH
  ; semi-M↑CZ ; semi-M↓CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑
  ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15
  ; comm-H ; comm-S ; comm-CZ ; comm-HHS
  ; M-mul ; semi-MS
  ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ) public

1/2 = ((₂ , λ ()) ⁻¹) .proj₁

-1/2 = - ((₂ , λ ()) ⁻¹) .proj₁

open import Examples.Groups.Clifford.Qupit.Simplified-V1.Clifford-Mod-Scalar.Syntactics p-3 p-prime g* g-gen using (module Clifford-Relations ; module Lemmas-Clifford)

module Lemmas1 (n : ℕ) where


  open Clifford-Relations

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    ζ^ x • H • ζ^ x⁻¹ • H • ζ^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> ζ^ xx • H • ζ^ yy • H • ζ^ x • H) eq aux-eq ⟩
    ζ^ x' • H • ζ^ x'⁻¹ • H • ζ^ x • H ≡⟨ Eq.cong (\ xx -> ζ^ x' • H • ζ^ x'⁻¹ • H • ζ^ xx • H) eq ⟩
    ζ^ x' • H • ζ^ x'⁻¹ • H • ζ^ x' • H ≡⟨ auto ⟩
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


  lemma-M1 : M (₁ , λ ()) ≈ ε
  lemma-M1 = begin
    M (₁ , λ ()) ≡⟨ aux-M≡M ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (M-power ₀)) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid




  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid



  lemma-Mgζ^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • ζ ^ k ≈ ζ ^ (k Nat.* toℕ (g * g)) • Mg
  lemma-Mgζ^k k@0 = trans right-unit (sym left-unit)
  lemma-Mgζ^k k@1 = begin  
    Mg • ζ ^ k ≈⟨ refl ⟩
    Mg • ζ ≈⟨ axiom semi-Mζ ⟩
    ζ^ (g * g) • Mg ≈⟨ refl ⟩
    ζ ^ toℕ (g * g) • Mg ≈⟨ (cleft refl' (Eq.cong (ζ ^_) (Eq.sym ( NP.*-identityˡ (toℕ (g * g)))))) ⟩
    ζ ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid
  lemma-Mgζ^k k@(₂₊ k') = begin  
    Mg • ζ ^ k ≈⟨ refl ⟩
    Mg • ζ • ζ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • ζ) • ζ ^ ₁₊ k' ≈⟨ (cleft lemma-Mgζ^k 1 ) ⟩
    (ζ ^ (1 Nat.* toℕ (g * g)) • Mg) • ζ ^ ₁₊ k' ≈⟨ assoc ⟩
    ζ ^ (1 Nat.* toℕ (g * g)) • Mg • ζ ^ ₁₊ k' ≈⟨ (cright lemma-Mgζ^k (₁₊ k')) ⟩
    ζ ^ (1 Nat.* toℕ (g * g)) • ζ ^ (₁₊ k' Nat.* toℕ (g * g)) • Mg ≈⟨ sym assoc ⟩
    (ζ ^ (1 Nat.* toℕ (g * g)) • ζ ^ (₁₊ k' Nat.* toℕ (g * g))) • Mg ≈⟨ (cleft sym (^-+ ζ ((1 Nat.* toℕ (g * g))) ((₁₊ k' Nat.* toℕ (g * g))))) ⟩
    (ζ ^ ((1 Nat.* toℕ (g * g)) Nat.+ (₁₊ k' Nat.* toℕ (g * g)))) • Mg ≈⟨ (cleft refl' (Eq.cong (ζ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (g * g)) ₁ (₁₊ k'))))) ⟩
    ζ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (g * g) ) • Mg ≈⟨ refl ⟩
    ζ ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid


  open import Data.Fin.Properties
  
  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (M-power (₂₊ (fromℕ< _))) ⟩
    M (g^ p-1') ≡⟨ aux-M≡M (g^ p-1') ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    M (g ^′ p-1 , lemma-g^′k≠0 p-1) ≡⟨ aux-M≡M ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (1ₚ , λ ()) Fermat's-little-theorem' ⟩
    M (1ₚ , λ ()) ≈⟨ sym (axiom (M-power ₀)) ⟩
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
    M (g^ k) • M (g^ l) ≈⟨ cong (sym (axiom (M-power k))) (sym (axiom (M-power l))) ⟩
    Mg ^ toℕ k • Mg ^ toℕ l ≈⟨ sym (^-+ Mg (toℕ k) (toℕ l)) ⟩
    Mg ^ [k+l] ≡⟨ Eq.cong (Mg ^_) (m≡m%n+[m/n]*n [k+l] p-1) ⟩
    Mg ^ ([k+l]%p-1 Nat.+ [k+l]/p-1 Nat.* p-1) ≈⟨ ^-+ Mg [k+l]%p-1 (([k+l]/p-1 Nat.* p-1)) ⟩
    Mg ^ [k+l]%p-1 • Mg ^ ([k+l]/p-1 Nat.* p-1) ≈⟨ (cright trans refl (aux-Mg^[kp-1] [k+l]/p-1)) ⟩
    Mg ^ [k+l]%p-1 • ε ≈⟨ right-unit ⟩
    Mg ^ [k+l]%p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (m%n<n [k+l] p-1))) ⟩
    Mg ^ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1))))) ⟩
    Mg ^ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ refl ⟩
    Mg^ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ axiom (M-power (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ⟩
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
    HH ^ 2 ≈⟨ cong (axiom order-H) (axiom order-H) ⟩
    M₋₁ ^ 2 ≈⟨ lemma-M₋₁^2 ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-comm-SHHS^kHH : ∀ k  -> S • H • H • S ^ k • H • H ≈ (H • H • S ^ k • H • H) • S
  lemma-comm-SHHS^kHH k@0 = begin
    S • H • H • ε • H • H ≈⟨ by-assoc auto ⟩
    S • H • H • H • H ≈⟨ (cright lemma-order-H) ⟩
    S • ε ≈⟨ trans right-unit (sym left-unit) ⟩
    ε • S ≈⟨ (cleft sym lemma-order-H) ⟩
    (H • H • H • H) • S ≈⟨ by-assoc auto ⟩
    (H • H • ε • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  lemma-comm-SHHS^kHH k@1 = sym (by-assoc-and (axiom comm-HHSHHS) auto auto)
  lemma-comm-SHHS^kHH k@(₁₊ k'@(₁₊ k'')) = begin
    S • H • H • S ^ k • H • H ≈⟨ refl ⟩
    S • H • H • (S • S ^ k') • H • H ≈⟨ (cright cright cright cleft cright sym left-unit) ⟩
    S • H • H • (S • ε • S ^ k') • H • H ≈⟨ (cright cright cright cleft cright cleft sym lemma-order-H) ⟩
    S • H • H • (S • (H • H • H • H) • S ^ k') • H • H ≈⟨ by-passoc (□ • □ • □ • (□ • □ ^ 4 • □) • □ ^ 2 ) (□ ^ 6 • □ ^ 5 ) auto ⟩
    (S • H • H • S • H • H) • H • H • S ^ k' • H • H ≈⟨ (cleft sym (axiom comm-HHSHHS)) ⟩
    (H • H • S • H • H • S) • H • H • S ^ k' • H • H ≈⟨ by-passoc (□ ^ 6 • □ ^ 5) (□ ^ 5 • □ ^ 6) auto ⟩
    (H • H • S • H • H) • S • H • H • S ^ k' • H • H ≈⟨ (cright lemma-comm-SHHS^kHH k') ⟩
    (H • H • S • H • H) • (H • H • S ^ k' • H • H) • S ≈⟨ by-passoc (□ ^ 5 • □ ^ 5 • □) (□ ^ 7 • □ ^ 4) auto ⟩
    (H • H • S • H • H • H • H) • S ^ k' • H • H • S ≈⟨ (cleft (cright cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • H • S) • S ^ k' • H • H • S ≈⟨ by-passoc (□ ^ 3 • □ ^ 4) (□ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    H • H • (S • S ^ k') • H • H • S ≈⟨ by-passoc (□ ^ 6) (□ ^ 5 • □) auto ⟩
    (H • H • S ^ k • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-Z^k-ℕ : ∀ k -> Z ^ k ≈ H • H • S ^ k • H • H • S⁻¹ ^ k
  lemma-Z^k-ℕ k@0 = sym (by-assoc-and ((lemma-order-H)) auto auto)
  lemma-Z^k-ℕ k@1 = refl
  lemma-Z^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    Z • Z ^ k' ≈⟨ (cright lemma-Z^k-ℕ k') ⟩
    Z • H • H • S ^ k' • H • H • S⁻¹ ^ k' ≈⟨ refl ⟩
    (H • H • S • H • H • S⁻¹) • H • H • S ^ k' • H • H • S⁻¹ ^ k' ≈⟨ by-passoc (□ ^ 6 • □ ^ 6) (□ ^ 5 • □ ^ 6 • □) auto ⟩
    (H • H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' ≈⟨ (cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH k')) ⟩
    (H • H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' ≈⟨ by-passoc (□ ^ 5 • (□ ^ 5 • □) • □) (□ ^ 7 • □ ^ 3 • □ ^ 2) auto ⟩
    (H • H • S • H • H • H • H) • (S ^ k' • H • H) • S⁻¹ • S⁻¹ ^ k' ≈⟨ (cleft (cright cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • H • S) • (S ^ k' • H • H) • S⁻¹ ^ ₁₊ k' ≈⟨ by-passoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H) • (S • S ^ k') • H • H • S⁻¹ ^ ₁₊ k' ≈⟨ refl ⟩
    (H • H) • S ^ ₁₊ k' • H • H • S⁻¹ ^ ₁₊ k' ≈⟨ assoc ⟩
    H • H • S ^ k • H • H • S⁻¹ ^ k ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-X^k-ℕ : ∀ k -> X ^ k ≈ H • S ^ k • H • H • S⁻¹ ^ k • H
  lemma-X^k-ℕ k@0 = sym (by-assoc-and lemma-order-H auto auto)
  lemma-X^k-ℕ k@1 = refl
  lemma-X^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    X • X ^ k' ≈⟨ (cright lemma-X^k-ℕ k') ⟩
    X • H • S ^ k' • H • H • S⁻¹ ^ k' • H ≈⟨ refl ⟩
    (H • S • H • H • S⁻¹ • H) • H • S ^ k' • H • H • S⁻¹ ^ k' • H ≈⟨ by-passoc (□ ^ 6 • □ ^ 6) (□ ^ 4 • □ ^ 6 • □ ^ 2) auto ⟩
    (H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' • H ≈⟨ (cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH k')) ⟩
    (H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' • H ≈⟨ by-passoc (□ ^ 4 • (□ ^ 5 • □) • □ ^ 2) (□ ^ 6 • □ ^ 3 • □ ^ 2 • □) auto ⟩
    (H • S • H • H • H • H) • (S ^ k' • H • H) • (S⁻¹ • S⁻¹ ^ k') • H ≈⟨ (cleft (cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • S) • (S ^ k' • H • H) • S⁻¹ ^ k • H ≈⟨ by-passoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 4) auto ⟩
    H • (S • S ^ k') • H • H • S⁻¹ ^ k • H ≈⟨ refl ⟩
    H • S ^ k • H • H • S⁻¹ ^ k • H ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-w^k : ∀ (w : Word (Gen (₁₊ n))) o k -> w ^ o ≈ ε -> (w ^ k) ^ o ≈ ε
  lemma-order-w^k w o k eq = begin
    (w ^ k) ^ o ≈⟨ ^^' w k o ⟩
    (w ^ o) ^ k ≈⟨ ^-cong (w ^ o) ε k eq ⟩
    ε ^ k ≈⟨ ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-Z : Z ^ p ≈ ε
  lemma-order-Z = begin
    Z ^ p ≈⟨ lemma-Z^k-ℕ p ⟩
    H • H • S ^ p • H • H • S⁻¹ ^ p ≈⟨ (cright cright cong (axiom order-S) (cright cright lemma-order-w^k S p p-1 (axiom order-S))) ⟩
    H • H • ε • H • H • ε ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ lemma-order-H ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-X : X ^ p ≈ ε
  lemma-order-X = begin
    X ^ p ≈⟨ lemma-X^k-ℕ p ⟩
    H • S ^ p • H • H • S⁻¹ ^ p • H ≈⟨ (cright  cong (axiom order-S) (cright cright cleft lemma-order-w^k S p p-1 (axiom order-S))) ⟩
    H • ε • H • H • ε • H ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ lemma-order-H ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-Z-S : Z • S ≈ S • Z
  lemma-comm-Z-S = begin
    (H • H • S • H • H • S⁻¹) • S ≈⟨ by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2 ) auto ⟩
    (H • H • S • H • H) • S⁻¹ • S ≈⟨ (cright comm⇒pow-comm p-1 1 refl) ⟩
    (H • H • S • H • H) • S • S⁻¹ ≈⟨ sym (by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2 ) auto) ⟩
    (H • H • S • H • H • S) • S⁻¹ ≈⟨ (cleft axiom comm-HHSHHS) ⟩
    (S • H • H • S • H • H) • S⁻¹ ≈⟨ by-passoc (□ ^ 6 • □) (□ • □ ^ 6) auto ⟩
    S • (H • H • S • H • H • S⁻¹) ≈⟨ refl ⟩
    S • Z ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  
  lemma-order-ζ : ζ ^ p ≈ ε
  lemma-order-ζ = begin
    (S • Z^ 1/2) ^ p ≈⟨ ^-cong (S • Z^ 1/2) (Z^ 1/2 • S) p (comm⇒pow-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)) ⟩
    (Z^ 1/2 • S) ^ p ≈⟨ ^-• (Z^ 1/2) S p (comm⇒pow-comm (toℕ 1/2) 1 lemma-comm-Z-S) ⟩
    Z^ 1/2 ^ p • S ^ p ≈⟨ (cright axiom order-S) ⟩
    Z^ 1/2 ^ p • ε ≈⟨ right-unit ⟩
    Z^ 1/2 ^ p ≈⟨ lemma-order-w^k Z p (toℕ 1/2) lemma-order-Z ⟩
    ε ∎
    where
    open SR word-setoid
    
  lemma-ζ^k-% : ∀ k -> ζ ^ k ≈ ζ ^ (k % p)
  lemma-ζ^k-% k = begin
    ζ ^ k ≡⟨ Eq.cong (ζ ^_) (m≡m%n+[m/n]*n k p) ⟩
    ζ ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ ^-+ ζ (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    ζ ^ (k Nat.% p) • ζ ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (ζ ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    ζ ^ (k Nat.% p) • ζ ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright ^^ ζ p (k Nat./ p)) ⟩
    ζ ^ (k Nat.% p) • (ζ ^ p) ^ (k Nat./ p) ≈⟨ (cright ^-cong (ζ ^ p) ε (k Nat./ p) (lemma-order-ζ)) ⟩
    ζ ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright ε^k=ε (k Nat./ p)) ⟩
    ζ ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    ζ ^ (k % p) ∎
    where
    open SR word-setoid






  lemma-Mgζ^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • ζ^ k ≈ ζ^ (k * (g * g)) • Mg
  lemma-Mgζ^k' k = begin 
    Mg • ζ^ k ≈⟨ refl ⟩
    Mg • ζ ^ toℕ k ≈⟨ lemma-Mgζ^k (toℕ k) ⟩
    ζ ^ (toℕ k Nat.* toℕ (g * g)) • Mg ≈⟨ (cleft lemma-ζ^k-% (toℕ k Nat.* toℕ (g * g))) ⟩
    ζ ^ ((toℕ k Nat.* toℕ (g * g)) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (ζ ^_) (lemma-toℕ-% k (g * g)))) ⟩
    ζ ^ toℕ (k * (g * g)) • Mg ≈⟨ refl ⟩
    ζ^ (k * (g * g)) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^kζ : ∀ k -> Mg ^ k • ζ ≈ ζ^ ((g * g) ^′ k) • Mg ^ k
  lemma-Mg^kζ k@0 = trans left-unit (sym right-unit)
  lemma-Mg^kζ k@1 = begin
    Mg ^ k • ζ ≈⟨ axiom semi-Mζ ⟩
    ζ^ ((g * g)) • Mg ^ k ≈⟨ (cleft refl' ( Eq.cong ζ^ (Eq.sym (lemma-x^′1=x (fromℕ< _))))) ⟩ -- 
    ζ^ ((g * g) ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^kζ k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • ζ ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • ζ ≈⟨ (cright lemma-Mg^kζ (₁₊ n)) ⟩
    Mg • ζ^ ((g * g) ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • ζ^ ((g * g) ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-Mgζ^k' ((g * g) ^′ (₁₊ n))) ⟩
    (ζ^ (((g * g) ^′ (₁₊ n)) * (g * g)) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (ζ^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm ((g * g) ^′ (₁₊ n)) (g * g))) ⟩
    (ζ^ ((g * g) * ((g * g) ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    ζ^ ((g * g) ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid


  lemma-semi-Mζ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • ζ ≈ ζ^ ((x' * x')) • M x
  lemma-semi-Mζ x = begin
    M x • ζ ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • ζ ≈⟨ cong (sym (axiom (M-power (k)))) refl ⟩
    Mg^ k • ζ ≈⟨ lemma-Mg^kζ (toℕ k) ⟩
    ζ^ ((g * g) ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (M-power (k))) ⟩
    ζ^ ((g * g) ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong ζ^ (*-^′-distribʳ g g (toℕ k)))) ⟩
    ζ^ ((g ^′ toℕ k) * (g ^′ toℕ k)) • M (g^ k) ≈⟨ sym (cleft refl' (Eq.cong₂ (\ xx yy -> ζ^ (xx * yy)) (eqk) (eqk))) ⟩
    ζ^ (x' * x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    ζ^ (x' * x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)





module Clifford-GroupLike where

  private
    variable
      n : ℕ
    
  open Clifford-Relations
  open Lemmas-Clifford


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
      (S ^ p) ≈⟨ (axiom order-S) ⟩
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
      (CZ ^ p) ≈⟨ (axiom order-CZ) ⟩
      (ε) ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
