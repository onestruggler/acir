{-# OPTIONS --cubical-compatible --safe #-}


open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq


open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)


open import Word.Base hiding (wfoldl ; _^'_)

open import Data.Nat.Primality

module Examples.Groups.Symplectic.BR.Calculations (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)

open import Algebra.Properties.Ring (+-*-ring p-2)


--open Lemmas-2Q 2


open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime


open ≡-Reasoning
open Eq

fig-24-3-cal-1 : ∀ (a* b* : ℤ* ₚ) →
  let
  a = a* .proj₁
  b = b* .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 b (- a) ((-' a*) .proj₂)
  [ab]⁻¹* = ( a* *' b* ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  y = a⁻¹
  nzy = ((a*) ⁻¹) .proj₂
  x = -b/a
  nzx = (-' b* *' a* ⁻¹).proj₂
  
  x⁻¹ = ((x , nzx) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nzx) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  -y/x' = (((y , nzy) *' ((x , nzx) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁
  
  in
  
  -x⁻¹ * (y * y) ≡ [ab]⁻¹ × -y/x ≡ b⁻¹ × -x⁻¹ ≡ - - a * b⁻¹

fig-24-3-cal-1 a* b* = aux'-1 , claim2 , claim3
  where
  a = a* .proj₁
  b = b* .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 b (- a) ((-' a*) .proj₂)
  [ab]⁻¹* = ( a* *' b* ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  y = a⁻¹
  nzy = ((a*) ⁻¹) .proj₂
  x = -b/a
  nzx = (-' b* *' a* ⁻¹).proj₂
  
  x⁻¹ = ((x , nzx) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nzx) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  -y/x' = (((y , nzy) *' ((x , nzx) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁
  
  aux'-1 : -x⁻¹ * (y * y) ≡ [ab]⁻¹
  aux'-1 = begin
    -x⁻¹ * (y * y) ≡⟨ Eq.cong (\ xx → - xx * (y * y)) (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (((-' b*) ⁻¹) .proj₁ * (a* ⁻¹ ⁻¹) .proj₁) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong (_* (a⁻¹ * a⁻¹)) (-‿distribˡ-* (((-' b*) ⁻¹) .proj₁) ((a* ⁻¹ ⁻¹) .proj₁)) ⟩
    (- ((-' b*) ⁻¹) .proj₁ * (a* ⁻¹ ⁻¹) .proj₁) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong₂ (\ xx yy → (xx * yy) * (a⁻¹ * a⁻¹)) (Eq.cong -_ (inv-neg-comm b*)) (inv-involutive a*) ⟩
    (- - (b⁻¹) * a) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong (\ xx → (xx * a) * (a⁻¹ * a⁻¹)) (-‿involutive ((b⁻¹))) ⟩
    ((b⁻¹) * a) * (a⁻¹ * a⁻¹) ≡⟨ *-assoc b⁻¹ a (a⁻¹ * a⁻¹) ⟩
    (b⁻¹) * (a * (a⁻¹ * a⁻¹)) ≡⟨ Eq.cong ((b⁻¹) *_) (Eq.sym (*-assoc a a⁻¹ a⁻¹)) ⟩
    (b⁻¹) * ((a * a⁻¹) * a⁻¹) ≡⟨ Eq.cong (\ xx → (b⁻¹) * (xx * a⁻¹)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}} ) ⟩
    (b⁻¹) * (₁ * a⁻¹) ≡⟨ Eq.cong ((b⁻¹) *_) (*-identityˡ ((a⁻¹))) ⟩
    (b⁻¹) * a⁻¹ ≡⟨ *-comm ((b⁻¹)) a⁻¹ ⟩
    a⁻¹ * (b⁻¹) ≡⟨ Eq.sym (inv-distrib a* b*) ⟩
    [ab]⁻¹ ∎


  claim2 : -y/x ≡ b⁻¹
  claim2 = begin
    -y/x ≡⟨ auto ⟩
    a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁ * - ₁ ≡⟨ *-comm (a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁) (- ₁) ⟩
    - ₁ * (a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁) ≡⟨ -1*x≈-x ((a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁)) ⟩
    - (a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁) ≡⟨ Eq.cong (\ xx → - (a⁻¹ * xx)) (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (a⁻¹ * (((-' b*) ⁻¹).proj₁ * (a* ⁻¹ ⁻¹).proj₁)) ≡⟨ Eq.cong (\ xx → - (a⁻¹ * (((-' b*) ⁻¹).proj₁ * xx))) (inv-involutive a*) ⟩
    - (a⁻¹ * (((-' b*) ⁻¹).proj₁ * a)) ≡⟨ Eq.cong (\ xx → - (a⁻¹ * xx)) (*-comm (((-' b*) ⁻¹).proj₁) a) ⟩
    - (a⁻¹ * (a * ((-' b*) ⁻¹).proj₁)) ≡⟨ Eq.cong -_ (sym (*-assoc a⁻¹ a (((-' b*) ⁻¹).proj₁))) ⟩
    - (a⁻¹ * a * ((-' b*) ⁻¹).proj₁) ≡⟨ Eq.cong -_  (cong (_* ((-' b*) ⁻¹).proj₁) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}})) ⟩
    - (₁ * ((-' b*) ⁻¹).proj₁) ≡⟨ Eq.cong -_ (*-identityˡ (((-' b*) ⁻¹).proj₁)) ⟩
    - (((-' b*) ⁻¹).proj₁) ≡⟨ Eq.cong -_ (inv-neg-comm b*) ⟩
    - - ((( b*) ⁻¹).proj₁) ≡⟨ -‿involutive b⁻¹ ⟩
    b⁻¹ ∎

  claim3 : -x⁻¹ ≡ - - a * b⁻¹
  claim3 = begin
    - ((-' b* *' a* ⁻¹) ⁻¹).proj₁ ≡⟨ Eq.cong -_ (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (((-' b*) ⁻¹).proj₁ * (a* ⁻¹ ⁻¹).proj₁) ≡⟨ Eq.cong (\ xx → - ((((-' b*) ⁻¹).proj₁ * xx))) (inv-involutive a*)  ⟩
    - (((-' b*) ⁻¹).proj₁ * a) ≡⟨ -‿distribˡ-* (((-' b*) ⁻¹).proj₁) a ⟩
    - ((-' b*) ⁻¹).proj₁ * a ≡⟨ cong (_* a) (cong -_ (inv-neg-comm b*)) ⟩
    - - ((b*) ⁻¹).proj₁ * a ≡⟨ cong (_* a) ( -‿involutive b⁻¹) ⟩
    ((b*) ⁻¹).proj₁ * a ≡⟨ *-comm b⁻¹ a ⟩
    a * b⁻¹ ≡⟨ cong (_* b⁻¹) (sym (-‿involutive a)) ⟩
    - - a * b⁻¹ ∎


fig-25-2-cal : ∀ (a*@(a , nza) : ℤ* ₚ) (b : ℤ ₚ) →
  let
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  
  -b/a + ₁ ≡ - (b + - a) * a⁻¹

fig-25-2-cal a*@(a , nza) b = aux
  where
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  
  aux : -b/a + ₁ ≡ - (b + - a) * a⁻¹
  aux = Eq.sym ( begin
    - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
    (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx → (- b + xx) * a⁻¹) (-‿involutive a) ⟩
    (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
    - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}}) ⟩
    - b * a⁻¹ + ₁ ≡⟨ auto ⟩
    -b/a + ₁ ∎
    )


cal-b1-a2' : ∀ (a1 a2 b1 : ℤ ₚ) (nz1 : a1 ≢ ₀) (nz2 : a2 ≢ ₀) →
  let
  a1⁻¹ = ((a1 , nz1) ⁻¹) .proj₁
  -b1/a1 = - b1 * a1⁻¹
  [a2-b1]/a1 = - (b1 + - a2) * a1⁻¹
  in

  a2 * (a1⁻¹) + -b1/a1 ≡ [a2-b1]/a1

cal-b1-a2' a1 a2 b1 nz1 nz2 = begin
  a2 * (a1⁻¹) + -b1/a1 ≡⟨ sym (*-distribʳ-+ a1⁻¹ a2 (- b1)) ⟩
  (a2 + - b1) * (a1⁻¹) ≡⟨ cong (_* (a1⁻¹)) (+-comm a2 (- b1)) ⟩
  (- b1 + a2) * (a1⁻¹) ≡⟨ cong (_* a1⁻¹) (cong (- b1 +_) (sym (-‿involutive a2))) ⟩
  (- b1 + - - a2) * (a1⁻¹) ≡⟨ cong (_* a1⁻¹) ( (-‿+-comm b1 (- a2))) ⟩
  - (b1 + - a2) * (a1⁻¹) ≡⟨ auto ⟩
  [a2-b1]/a1 ∎
  where
  a1⁻¹ = ((a1 , nz1) ⁻¹) .proj₁
  -b1/a1 = - b1 * a1⁻¹
  [a2-b1]/a1 = - (b1 + - a2) * a1⁻¹


aux-M≡M' : ∀ {n} y y' → y .proj₁ ≡ y' .proj₁ → ZM {n = n} y ≡ ZM y'
aux-M≡M' {n} y y' eq = begin
  ZM y ≡⟨ auto ⟩
  S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy → S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
  S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx → S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
  S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
  ZM y' ∎
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


aux--k*-k⁻¹ : ∀ (k*@(k , nz) : ℤ* ₚ) →
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  in
  
  - k * - k⁻¹ ≡ ₁

aux--k*-k⁻¹ k*@(k , nz) = begin
  - k * - k⁻¹ ≡⟨ sym (-‿distribˡ-* k (- k⁻¹)) ⟩
  - (k * - k⁻¹) ≡⟨ cong -_ (sym (-‿distribʳ-* k k⁻¹)) ⟩
  - - (k * k⁻¹) ≡⟨ -‿involutive (k * k⁻¹) ⟩
  (k * k⁻¹) ≡⟨ lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}} ⟩
  ₁ ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  

aux--b/a+₁ : ∀ (a*@(a , nz) : ℤ* ₚ) b →
  let
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  -b/a + ₁ ≡ - (b + - a) * a⁻¹
  
aux--b/a+₁ a*@(a , nz) b = Eq.sym ( begin
  - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
  (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx → (- b + xx) * a⁻¹) (-‿involutive a) ⟩
  (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
  - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nz}}}) ⟩
  - b * a⁻¹ + ₁ ≡⟨ auto ⟩
  -b/a + ₁ ∎
  )
  where
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹


aux--k⁻¹ : ∀ (a*@(a , nza)  b*@(b , nzb) : ℤ* ₚ) →
  let
  a⁻¹ = (a* ⁻¹) .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = b * a⁻¹
  a/b = a* *' b* ⁻¹
  k = -b/a
  k* = -' b* *' a* ⁻¹
  -k⁻¹ = - ((k* ⁻¹) .proj₁)
  l = ((-' k* ⁻¹) ⁻¹) .proj₁
  in
  (-' k* ⁻¹) .proj₁ ≡ a/b .proj₁ ×
  - k ≡ b/a ×
  - a * l ≡ - b ×
  -k⁻¹ ≡ - - a * b⁻¹

aux--k⁻¹ a*@(a , nza) b*@(b , nzb) = claim1 , claim2 , claim3 , claim4
  where
  a⁻¹ = (a* ⁻¹) .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = b * a⁻¹
  a/b = a* *' b* ⁻¹
  k = -b/a
  k* = -' b* *' a* ⁻¹
  -k⁻¹ = - ((k* ⁻¹) .proj₁)
  l = ((-' k* ⁻¹) ⁻¹) .proj₁
  claim1 : (-' k* ⁻¹) .proj₁ ≡ a/b .proj₁
  claim1 = begin
    (-' (-' b* *' a* ⁻¹) ⁻¹) .proj₁ ≡⟨ auto ⟩
    - ((-' b* *' a* ⁻¹) ⁻¹) .proj₁ ≡⟨ cong -_ (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - ((-' b*) ⁻¹  *' a* ⁻¹ ⁻¹) .proj₁ ≡⟨ cong -_ (cong (((-' b*) ⁻¹) .proj₁ *_) (inv-involutive a*)) ⟩
    - ((-' b*) ⁻¹  *' a*) .proj₁ ≡⟨ cong -_ (cong (_* a* .proj₁) (inv-neg-comm b*)) ⟩
    - (-' (b*) ⁻¹  *' a*) .proj₁ ≡⟨ auto ⟩
    - (- b⁻¹  * a) ≡⟨ -‿distribˡ-* (- b⁻¹) a ⟩
    - - b⁻¹  * a ≡⟨ cong (_* a) (-‿involutive b⁻¹) ⟩
    b⁻¹  * a ≡⟨ *-comm b⁻¹ a ⟩
    a/b .proj₁ ∎


  claim2 : - k ≡ b/a
  claim2 = begin
    - (- b * a⁻¹) ≡⟨ -‿distribˡ-* (- b) a⁻¹ ⟩
    - - b * a⁻¹ ≡⟨ cong (_* a⁻¹) (-‿involutive b) ⟩
    b * a⁻¹ ≡⟨ auto ⟩
    b/a ∎

  claim3 : - a * l ≡ - b
  claim3 = begin
    - a * ((-' k* ⁻¹) ⁻¹) .proj₁ ≡⟨ (cong (- a *_) (inv-neg-comm (k* ⁻¹))) ⟩
    - a * (-' k* ⁻¹ ⁻¹) .proj₁ ≡⟨ auto ⟩
    - a * - (k* ⁻¹ ⁻¹) .proj₁ ≡⟨ cong (- a *_) (cong -_ (inv-involutive k*)) ⟩
    - a * - (-' b* *' a* ⁻¹) .proj₁ ≡⟨ auto ⟩
    - a * - (- b * a⁻¹) ≡⟨ cong (- a *_) (-‿distribˡ-* (- b) a⁻¹) ⟩
    - a * (- - b * a⁻¹) ≡⟨ cong (- a *_) (cong (_* a⁻¹) (-‿involutive b)) ⟩
    - a * (b * a⁻¹) ≡⟨  cong (- a *_) (*-comm b a⁻¹) ⟩
    - a * (a⁻¹ * b) ≡⟨ sym (*-assoc (- a) a⁻¹ b) ⟩
    - a * a⁻¹ * b ≡⟨ cong (_* b) (sym (-‿distribˡ-* a a⁻¹)) ⟩
    - (a * a⁻¹) * b ≡⟨ cong (_* b) (cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}})) ⟩
    - (₁) * b ≡⟨ -1*x≈-x b ⟩
    - b ∎

  claim4 : -k⁻¹ ≡ - - a * b⁻¹
  claim4 = begin
    -k⁻¹ ≡⟨ claim1 ⟩
    a * b⁻¹ ≡⟨ sym (cong (_* b⁻¹) (-‿involutive a)) ⟩ 
    - - a * b⁻¹ ∎

aux-lkkk : ∀ (k*@(k , nzk) l*@(l , nzl) : ℤ* ₚ) →
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  in
  l * k * (k⁻¹ * k⁻¹) ≡ l * k⁻¹
aux-lkkk k*@(k , nzk) l*@(l , nzl) = begin
  l * k * (k⁻¹ * k⁻¹) ≡⟨ *-assoc l k (k⁻¹ * k⁻¹) ⟩
  l * (k * (k⁻¹ * k⁻¹)) ≡⟨ Eq.cong (l *_) (Eq.sym (*-assoc k k⁻¹ k⁻¹)) ⟩
  l * (k * k⁻¹ * k⁻¹) ≡⟨  Eq.cong (l *_) ( Eq.cong (_* k⁻¹) (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nzk}}})) ⟩
  l * (₁ * k⁻¹) ≡⟨ Eq.cong (l *_) (*-identityˡ k⁻¹) ⟩
  l * k⁻¹ ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  open ≡-Reasoning


aux-lkkk' : ∀ (k*@(k , nzk) : ℤ* ₚ) l →
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  in
  l * k * (k⁻¹ * k⁻¹) ≡ l * k⁻¹
aux-lkkk' k*@(k , nzk) l = begin
  l * k * (k⁻¹ * k⁻¹) ≡⟨ *-assoc l k (k⁻¹ * k⁻¹) ⟩
  l * (k * (k⁻¹ * k⁻¹)) ≡⟨ Eq.cong (l *_) (Eq.sym (*-assoc k k⁻¹ k⁻¹)) ⟩
  l * (k * k⁻¹ * k⁻¹) ≡⟨  Eq.cong (l *_) ( Eq.cong (_* k⁻¹) (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nzk}}})) ⟩
  l * (₁ * k⁻¹) ≡⟨ Eq.cong (l *_) (*-identityˡ k⁻¹) ⟩
  l * k⁻¹ ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  open ≡-Reasoning

aux-lkkk'' : ∀ (k*@(k , nzk) : ℤ* ₚ) l →
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  in
  l * k⁻¹ * (k * k) ≡ l * k
aux-lkkk'' k*@(k , nzk) l = begin
  l * k⁻¹ * (k * k) ≡⟨ *-assoc l k⁻¹ (k * k) ⟩
  l * (k⁻¹ * (k * k)) ≡⟨ Eq.cong (l *_) (Eq.sym (*-assoc k⁻¹ k k)) ⟩
  l * (k⁻¹ * k * k) ≡⟨  Eq.cong (l *_) ( Eq.cong (_* k) (lemma-⁻¹ˡ k {{nztoℕ {y = k} {neq0 = nzk}}})) ⟩
  l * (₁ * k) ≡⟨ Eq.cong (l *_) (*-identityˡ k) ⟩
  l * k ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  open ≡-Reasoning

