------------------------------------------------------------------------
-- The Agda standard library
--
-- Fermat's little theorem for a prime modulus
--
-- For a prime p and a unit a of ℤ/pℤ, a ^ (p-1) = 1.  The proof is the
-- classical one: multiplication by a permutes the p-1 nonzero
-- residues, so it fixes their product, and comparing that product with
-- the one obtained by pulling the a's out gives a ^ (p-1) = 1.
--
-- PrimeModulus' extends PrimeModulus with this theorem and, on top of
-- it, discrete logarithms to a primitive root.
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.Prime.Fermat.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod.Prime.Fermat where

open import Agda.Builtin.FromNat using (fromNat)
open import Data.Fin.Base using (Fin ; toℕ ; suc ; inject₁)
open import Data.Fin.Base using (punchIn)
open import Data.Fin.Permutation as F
  using (Permutation ; Permutation′ ; _⟨$⟩ʳ_ ; _≈_ ; permutation
        ; lift₀ ; lift₀-remove ; punchIn-permute)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n)
open import Data.Nat.Primality using (Prime)
open import Data.Nat.Properties as NP using ()
open import Data.Product.Base using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Functional using (Vector ; foldr)
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
open import Function.Base using (_∘_ ; _$_)
open import Notations using (auto ; ₀ ; ₁ ; ₁₊ ; ₂₊)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; _≗_ ; refl ; sym ; trans ; cong ; cong₂
        ; module ≡-Reasoning)

import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as PW

open import ForStdlib.Data.Fin.Mod

private
  variable
    n : ℕ


module PrimeModulus' (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open PrimeModulus p-2 p-prime public

  *-perm : ∀ (a : ℤ* ₚ) → Permutation p p
  *-perm a*@(a , nz) =
    record { to = a *_ ; from = a⁻¹ *_ ; to-cong = cong (a *_) ; from-cong = cong (a⁻¹ *_) ; inverse = invl , invr }
    where
    a⁻¹ = (a* ⁻¹) .proj₁
    open import Function.Definitions
    invl : Inverseˡ (_≡_ {A = ℤ ₚ}) (_≡_ {A = ℤ ₚ}) (a *_) (a⁻¹ *_)
    invl {x} {y} eq = begin
      a * y ≡⟨ cong (a *_) eq ⟩
      a * (a⁻¹ * x) ≡⟨ sym (*-assoc a a⁻¹ x) ⟩
      a * a⁻¹ * x ≡⟨ cong (_* x) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nz}}}) ⟩
      ₁ * x ≡⟨ *-identityˡ x  ⟩
      x ∎
      where open ≡-Reasoning

    invr : Inverseʳ (_≡_ {A = ℤ ₚ}) (_≡_ {A = ℤ ₚ}) (a *_) (a⁻¹ *_)
    invr {x} {y} eq = begin
      a⁻¹ * y ≡⟨ cong (a⁻¹ *_) eq ⟩
      a⁻¹ * (a * x) ≡⟨ sym (*-assoc a⁻¹ a x) ⟩
      a⁻¹ * a * x ≡⟨ cong (_* x) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nz}}}) ⟩
      ₁ * x ≡⟨ *-identityˡ x  ⟩
      x ∎
      where open ≡-Reasoning


  *-perm* : ∀ (a : ℤ* ₚ) → Permutation p-1 p-1
  *-perm* a = F.remove ₀ $ *-perm a


  *-perm-n : ∀ (a : ℤ* ₚ) → Vector (ℤ ₚ) n → Vector (ℤ ₚ) n
  *-perm-n a*@(a , nz) v = (a *_) ∘ v


  product : ∀ {n} → Vector (ℤ ₚ) n → ℤ ₚ
  product = foldr _*_ ₁

  perm₀ : ∀ (perm : Permutation 1 1) → perm ⟨$⟩ʳ ₀ ≡ ₀
  perm₀ perm with perm ⟨$⟩ʳ ₀
  ... | ₀ = auto

  lemma-product : ∀ ((a , nz) : ℤ* ₚ) (v : Vector (ℤ ₚ) n) → product ((a *_) ∘ v) ≡ a ^′ n * product  v
  lemma-product {₀} a v = auto
  lemma-product {n@(₁₊ n')} a*@(a , nz) v = begin
    product ((a *_) ∘ v) ≡⟨ auto ⟩
    (a * v ₀) * product ((a *_) ∘ v ∘ suc) ≡⟨ cong ((a * v ₀) *_) (lemma-product a* (v ∘ suc)) ⟩
    a * v ₀ * (a ^′ n' * product (v ∘ suc)) ≡⟨  *-assoc a (v ₀) (a ^′ n' * product (v ∘ suc)) ⟩
    a * (v ₀ * (a ^′ n' * product (v ∘ suc))) ≡⟨ cong (a *_) (sym ( *-assoc  (v ₀) (a ^′ n') (product (v ∘ suc)))) ⟩
    a * (v ₀ * a ^′ n' * product (v ∘ suc)) ≡⟨ cong (\ xx →  a * (xx * product (v ∘ suc))) (*-comm (v ₀) (a ^′ n')) ⟩
    a * (a ^′ n' * v ₀ * product (v ∘ suc)) ≡⟨ cong (a *_) (*-assoc (a ^′ n') (v ₀) (product (v ∘ suc))) ⟩
    a * (a ^′ n' * (v ₀ * product (v ∘ suc))) ≡⟨ sym (*-assoc a (a ^′ n') (v ₀ * product (v ∘ suc))) ⟩
    a * a ^′ n' * (v ₀ * product (v ∘ suc)) ≡⟨ auto ⟩
    a ^′ n * product v ∎
    where open ≡-Reasoning



  lemma-π∘suc : ∀ {n-1} → let n = ₁₊ n-1 in

    ∀ (p : Permutation n n) → let π = p ⟨$⟩ʳ_ in
    π ₀ ≡ ₀ → π ∘ suc ≗ suc ∘ (F.remove ₀ p ⟨$⟩ʳ_)

  lemma-π∘suc {n-1} p eq0 i = begin
     (π ∘ suc) i ≡⟨ auto ⟩
     π (₁₊ i) ≡⟨ sym (lift₀-remove p eq0 (₁₊ i)) ⟩
     lift₀ (F.remove ₀ p) ⟨$⟩ʳ (₁₊ i) ≡⟨ auto ⟩
     suc (F.remove ₀ p ⟨$⟩ʳ i) ≡⟨ auto ⟩
     (suc ∘ (F.remove ₀ p ⟨$⟩ʳ_)) i ∎
    where
    open ≡-Reasoning
    π = p ⟨$⟩ʳ_

  product-cong : ∀ {n} {u v : Vector (ℤ ₚ) n} → Pointwise _≡_ u v → product u ≡ product v
  product-cong {n} {u} {v} eq = PW.foldr-cong {R = _≡_ {A = ℤ ₚ}} {S = _≡_ {A = ℤ ₚ}} {f = _*_}  {g = _*_} (cong₂ _*_) (refl {x = ₁}) eq

  product-perm-cong : ∀ {n} (p q : Permutation n n) (v : Vector (ℤ ₚ) n) → p ≈ q → product {n} (v ∘ (p ⟨$⟩ʳ_)) ≡ product {n} (v ∘ (q ⟨$⟩ʳ_))
  product-perm-cong {n} p q v eq = product-cong (λ i → cong v (eq i))


  ----------------------------------------------------------------------
  -- Products are invariant under permuting the index

  -- Pulling one factor out of a product: `punchIn i` enumerates every
  -- index other than i, in order, so `v i` times the product over those
  -- is the whole product.
  product-punchIn : ∀ {n} (v : Vector (ℤ ₚ) (₁₊ n)) (i : Fin (₁₊ n)) →
    product v ≡ v i * product (v ∘ punchIn i)
  product-punchIn {n} v ₀ = auto
  product-punchIn {₁₊ n} v i@(₁₊ i') = begin
    v ₀ * product (v ∘ suc) ≡⟨ cong (v ₀ *_) (product-punchIn (v ∘ suc) i') ⟩
    v ₀ * (v i * rest) ≡⟨ sym (*-assoc (v ₀) (v i) rest) ⟩
    v ₀ * v i * rest ≡⟨ cong (_* rest) (*-comm (v ₀) (v i)) ⟩
    v i * v ₀ * rest ≡⟨ *-assoc (v i) (v ₀) rest ⟩
    v i * product (v ∘ punchIn i) ∎
    where
    open ≡-Reasoning
    rest = product (v ∘ suc ∘ punchIn i')

  -- Induction on n.  A permutation π of ₁₊ n sends ₀ to i₀ and restricts
  -- (`F.remove ₀`) to a permutation of the remaining n indices; the
  -- stdlib lemma `punchIn-permute` is exactly the statement that the
  -- restriction commutes with the two enumerations of "all but one".
  product∘p=product : ∀ {n} (p : Permutation n n) v → product {n} (v ∘ (p ⟨$⟩ʳ_)) ≡ product {n} v
  product∘p=product {₀} p v = auto
  product∘p=product {₁₊ n} p v = begin
    v i₀ * product (v ∘ (p ⟨$⟩ʳ_) ∘ suc) ≡⟨ cong (v i₀ *_) (product-cong step) ⟩
    v i₀ * product ((v ∘ punchIn i₀) ∘ (F.remove ₀ p ⟨$⟩ʳ_)) ≡⟨ cong (v i₀ *_) (product∘p=product (F.remove ₀ p) (v ∘ punchIn i₀)) ⟩
    v i₀ * product (v ∘ punchIn i₀) ≡⟨ sym (product-punchIn v i₀) ⟩
    product v ∎
    where
    open ≡-Reasoning
    i₀ = p ⟨$⟩ʳ ₀
    step : Pointwise _≡_ (v ∘ (p ⟨$⟩ʳ_) ∘ suc) ((v ∘ punchIn i₀) ∘ (F.remove ₀ p ⟨$⟩ʳ_))
    step j = cong v (punchIn-permute p ₀ j)


  ----------------------------------------------------------------------
  -- Fermat's little theorem

  1--p-1 : Vector (ℤ ₚ) (p-1)
  1--p-1 = suc

  import Function as Fun
  0--p-1 : Vector (ℤ ₚ) p
  0--p-1 = Fun.id

  a*1--p-1 : ∀ (a : ℤ* ₚ) → Vector (ℤ ₚ) (p-1)
  a*1--p-1 a*@(a , nz) = (a *_) ∘ 1--p-1


  -- Multiplying by a unit a permutes ℤₚ and fixes ₀, so it restricts to a
  -- permutation of the p-1 nonzero residues — which is what `1--p-1`
  -- enumerates.  `lemma-π∘suc` transports that restriction along `suc`.
  lemma-*-perm' : ∀ (a* : ℤ* ₚ) → Pointwise _≡_ (a*1--p-1 a*) (1--p-1 ∘ (*-perm* a* ⟨$⟩ʳ_))
  lemma-*-perm' a*@(a , nz) = lemma-π∘suc (*-perm a*) (*-zeroʳ a)


  prod-a*1--p-1 : ∀ (a : ℤ* ₚ) → product (a*1--p-1 a) ≡ product 1--p-1
  prod-a*1--p-1 a*@(a , nz) = begin
    product (a*1--p-1 a*) ≡⟨ product-cong (lemma-*-perm' a*) ⟩
    product (1--p-1 ∘ (*-perm* a* ⟨$⟩ʳ_)) ≡⟨ product∘p=product (*-perm* a*) 1--p-1 ⟩
    product 1--p-1 ∎
    where
    open ≡-Reasoning


  prod-a*1--p-1' : ∀ (a*@(a , nz) : ℤ* ₚ) → product (a*1--p-1 a*) ≡ a ^′ p-1 * product 1--p-1
  prod-a*1--p-1' a = lemma-product a 1--p-1


  lemma-nz : ∀ (v : Vector (ℤ ₚ) n) → (∀ i → v i ≢ ₀) → product v ≢ ₀
  lemma-nz {₀} v nz = λ ()
  lemma-nz {₁₊ n} v nz nzp = lemma-nz (v ∘ suc) (nz ∘ suc) claim
    where
    open ≡-Reasoning
    claim : product (v ∘ suc) ≡ ₀
    claim = begin
      product (v ∘ suc) ≡⟨ sym (*-identityˡ (product (v ∘ suc))) ⟩
      ₁ * product (v ∘ suc) ≡⟨ cong (\ xx → xx * (product (v ∘ suc))) (sym (lemma-⁻¹ˡ (v ₀) {{nztoℕ {y = v ₀} {neq0 = nz ₀}}} )) ⟩
      v₀⁻¹ * v ₀ * product (v ∘ suc) ≡⟨ *-assoc v₀⁻¹ (v ₀) (product (v ∘ suc)) ⟩
      v₀⁻¹ * (v ₀ * product (v ∘ suc)) ≡⟨ cong (v₀⁻¹ *_) nzp ⟩
      v₀⁻¹ * ₀ ≡⟨ *-zeroʳ v₀⁻¹ ⟩
      ₀ ∎
      where
      v₀⁻¹ = ((v ₀ , nz ₀) ⁻¹) .proj₁

  Fermat's-little-theorem : ∀ (a*@(a , nz) : ℤ* ₚ) → a ^′ p-1 ≡ ₁
  Fermat's-little-theorem a*@(a , nz) = begin
    a ^′ p-1 ≡⟨ sym (*-identityʳ (a ^′ p-1 ))  ⟩
    a ^′ p-1 * ₁ ≡⟨ cong (\ xx → a ^′ p-1 * xx) (sym (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = lemma-nz 1--p-1 λ i ()}}})) ⟩
    a ^′ p-1 * (x * x⁻¹) ≡⟨ sym (*-assoc (a ^′ p-1) x x⁻¹) ⟩
    a ^′ p-1 * x * x⁻¹ ≡⟨ cong (\ xx →  xx * x⁻¹) (trans (sym ( prod-a*1--p-1' a*)) (prod-a*1--p-1 a*)) ⟩
    x * x⁻¹ ≡⟨ lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = lemma-nz 1--p-1 λ i ()}}} ⟩
    ₁ ∎
    where
    open ≡-Reasoning
    x = product 1--p-1
    x⁻¹ = ((x , lemma-nz 1--p-1 λ i () ) ⁻¹) .proj₁



  module Primitive-Root-Modp'
    (g*@(g , g≠0) : ℤ* ₚ)
    (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k )
    where

    g-gen1 = g-gen (₁ , λ ())

    lemma-g^′k≠0 : ∀ k → g ^′ k ≢ 0ₚ
    lemma-g^′k≠0 k = lemma-x^′k≠0 g k g≠0


    lemma-g^′1=g : g ^′ 1 ≡ g
    lemma-g^′1=g = lemma-x^′1=x g


    g′ : ℤ* ₚ
    g′ = (g , g≠0)

    g^_ : ∀ (k : ℤ ₚ) → ℤ* ₚ
    g^_ k = (g ^′ toℕ k , lemma-g^′k≠0 (toℕ k))

    g^′_ : ∀ k → ℤ* ₚ
    g^′_ k = (g ^′ k , lemma-g^′k≠0 k)


    open import Algebra.Properties.Ring (+-*-ring p-2)

    aux-g^′-% : ∀ k → g ^′ k ≡ g ^′ (k ℕ.% p-1)
    aux-g^′-% k = begin
      g ^′ k ≡⟨ Eq.cong (g ^′_) ( m≡m%n+[m/n]*n k p-1) ⟩
      g ^′ (k%p-1 ℕ.+ k/p-1 ℕ.* p-1) ≡⟨ Eq.sym (+-^′-distribʳ g k%p-1 ((k/p-1 ℕ.* p-1))) ⟩
      g ^′ k%p-1 * g ^′ (k/p-1 ℕ.* p-1) ≡⟨ Eq.cong (\ xx → g ^′ k%p-1 * g ^′ xx) (NP.*-comm k/p-1 p-1) ⟩
      g ^′ k%p-1 * g ^′ (p-1 ℕ.* k/p-1) ≡⟨ Eq.cong (g ^′ k%p-1 *_) ( (lemma-^^-* g p-1 k/p-1)) ⟩
      g ^′ k%p-1 * (g ^′ p-1) ^′ k/p-1 ≡⟨ Eq.cong (\ xx → g ^′ k%p-1 * xx ^′ k/p-1) (Fermat's-little-theorem (g , g≠0)) ⟩
      g ^′ k%p-1 * 1ₚ ^′ k/p-1 ≡⟨ Eq.cong (\ xx → g ^′ k%p-1 * xx) (1^k=1 k/p-1) ⟩
      g ^′ k%p-1 * 1ₚ ≡⟨ *-identityʳ (g ^′ k%p-1) ⟩
      g ^′ k%p-1 ≡⟨ auto ⟩
      g ^′ (k ℕ.% p-1) ∎
      where
      open ≡-Reasoning
      k%p-1 = k ℕ.% p-1
      k/p-1 = k ℕ./ p-1


    log : ℤ* ₚ → ℤ ₚ-₁
    log  x = g-gen x .proj₁


    lemma-inject : ∀ (x : ℤ ₚ-₁) → g ^′ toℕ x ≡ (g^ (inject₁ x)) .proj₁
    lemma-inject  x = begin
      g ^′ toℕ x ≡⟨ Eq.cong (g ^′_) (Eq.sym (toℕ-inject₁ x) ) ⟩
      g ^′ toℕ (inject₁ x) ≡⟨ auto ⟩
      (g^ inject₁ x) .proj₁ ∎
      where
      open ≡-Reasoning

    lemma-log-inject : ∀ (x : ℤ* ₚ) → (g^ (inject₁ (log x))) .proj₁ ≡ x .proj₁
    lemma-log-inject x = begin
      (g^ (inject₁ (log x))) .proj₁ ≡⟨ Eq.sym (lemma-inject (log x)) ⟩
      g ^′ toℕ (log x) ≡⟨ Eq.sym (g-gen x .proj₂) ⟩
      x .proj₁ ∎
      where
      open ≡-Reasoning

    choose : ∀ (n k : ℕ)→ ℕ
    choose n ₀ = ₁
    choose ₀ (₁₊ _) = ₀
    choose (₁₊ n) (₁₊ k) = choose n k ℕ.+ choose n (₁₊ k)


    Fermat's-little-theorem' : g ^′ p-1 ≡ ₁
    Fermat's-little-theorem' = Fermat's-little-theorem (g , g≠0)
