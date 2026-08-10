------------------------------------------------------------------------
-- The Agda standard library
--
-- Modular arithmetic with a prime modulus: ℤ/pℤ is a field
--
-- For a prime p every nonzero residue is invertible, the inverse being
-- read off Bézout's identity.  PrimeModulus fixes the modulus as
-- p = 2+ p-2 and develops the units ℤ* p: inverses (_⁻¹), the group
-- operations _*'_ and -'_ on them, and powers.
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.Prime.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod.Prime where

open import Agda.Builtin.FromNat using (fromNat)
open import Algebra.Bundles using (Ring)
open import Algebra.Properties.Group
open import Data.Fin.Base using (Fin ; toℕ ; fromℕ< ; inject₁)
open import Data.Fin.Properties using (toℕ-fromℕ< ; toℕ<n ; fromℕ<-cong)
open import Data.Nat.Base as ℕ using (ℕ ; NonZero ; s≤s)
open import Data.Nat.Coprimality using (coprime-Bézout ; prime⇒coprime)
open import Data.Nat.DivMod
  using (_%_ ; m%n<n ; n%n≡0 ; m<n⇒m%n≡m ; m%n%n≡m%n ; m*n%n≡0
        ; %-distribˡ-+ ; %-distribˡ-*)
open import Data.Nat.GCD using (module Bézout)
open import Data.Nat.Primality using (Prime)
open import Data.Nat.Properties as NP using ()
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤)
open import Notations using (auto ; ₀ ; ₁ ; ₂ ; ₁₊ ; ₂₊)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import ForStdlib.Data.Fin.Mod.Base
open import ForStdlib.Data.Fin.Mod.Properties

open Bézout using (+- ; -+)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Units of ℤ/pℤ

module PrimeModulus (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Algebra.Properties.Ring (+-*-ring p-2)

  p-1 : ℕ
  p-1 = ₁₊ p-2

  
  ₚ : ℕ
  ₚ = ₁₊ p-1
  p = ₚ

  ₚ₋₁ = fromℕ< (NP.≤-refl {p})
  -- not the same
  ₚ-₁ : ℕ
  ₚ-₁ = p-1

  ₀ₚ : ℤ ₚ
  ₀ₚ = ₀

  0ₚ : ℤ ₚ
  0ₚ = ₀

  1ₚ : ℤ ₚ
  1ₚ = ₁

  ₁ₚ : ℤ* ₚ
  ₁ₚ = ₁ , λ ()

  0ₚ≢1ₚ : 0ₚ ≢ 1ₚ
  0ₚ≢1ₚ ()

  p-1=-1ₚ : fromℕ< (NP.≤-refl {p}) ≡ - 1ₚ
  p-1=-1ₚ = +-cancelˡ 1ₚ (fromℕ< (NP.≤-refl {p})) (- 1ₚ) (trans claim1 (sym claim2))
    where
    open ≡-Reasoning
    claim1 : 1ₚ + fromℕ< (NP.≤-refl {p}) ≡ 0ₚ
    claim1 = begin
      1ₚ + fromℕ< (NP.≤-refl {p}) ≡⟨ refl ⟩
      fromℕ< (m%n<n (1 ℕ.+ toℕ (fromℕ< (NP.≤-refl {p}))) p) ≡⟨ cong (\ xx → fromℕ< (m%n<n (1 ℕ.+ xx) p)) (toℕ-fromℕ< (NP.≤-refl {p})) ⟩
      fromℕ< (m%n<n (1 ℕ.+ p-1) p) ≡⟨ refl ⟩
      fromℕ< (m%n<n p p) ≡⟨ fromℕ<-cong (p % p) 0 (n%n≡0 p) (m%n<n p p) (NP.0<1+n {p-1}) ⟩
      fromℕ< (NP.0<1+n {p-1}) ≡⟨ refl ⟩
      0ₚ ∎

    claim2 : 1ₚ + - 1ₚ ≡ 0ₚ
    claim2 = +-inverseʳ 1ₚ

  aux-₋₁=-1 : ₋₁ ≡ - 1ₚ
  aux-₋₁=-1 = p-1=-1ₚ

  aux-₋₁*₋₁=₁ : ₋₁ * ₋₁ ≡ 1ₚ
  aux-₋₁*₋₁=₁ = begin
    ₋₁ * ₋₁ ≡⟨ cong₂ _*_ p-1=-1ₚ p-1=-1ₚ ⟩
    - ₁ * - ₁ ≡⟨ sym (-‿distribˡ-* ₁ (- ₁)) ⟩
    - (₁ * - ₁) ≡⟨ sym (cong -_ (-‿distribʳ-* ₁ ₁)) ⟩
    - - (₁ * ₁) ≡⟨ -‿involutive 1ₚ ⟩
    ₁ ∎
    where
    open ≡-Reasoning
  
  0ₚ≢p-1 : 0ₚ ≢ fromℕ< (NP.≤-refl {p})
  0ₚ≢p-1 ()

  0ₚ≢-1ₚ : 0ₚ ≢ - 1ₚ
  0ₚ≢-1ₚ eq with 0ₚ≢p-1 (trans eq (sym p-1=-1ₚ))
  ... | ()

  lemma-toℕ-ₚ₋₁ : toℕ ₚ₋₁ ≡ p-1
  lemma-toℕ-ₚ₋₁ = toℕ-fromℕ< (NP.≤-refl {p})

  lemma-toℕ-1ₚ : toℕ (- 1ₚ) ≡ p-1
  lemma-toℕ-1ₚ = trans (cong toℕ (sym p-1=-1ₚ)) lemma-toℕ-ₚ₋₁





  nztoℕ : ∀ {y : ℤ (₁₊ n)} → {neq0 : y ≢ ₀} → NonZero (toℕ y)
  nztoℕ {n} {₀} {neq0} with neq0 refl
  ... | ()
  nztoℕ {n} {₁₊ y} {neq0} = record { nonZero = Data.Unit.Base.tt }




  infixl 9 _⁻¹ _⁻¹'

  -- The modular inverse of a nonzero residue, read off the Bézout
  -- coefficients of gcd (p , x) = 1.
  _⁻¹' : (x : ℤ ₚ) → {{NonZero (toℕ x)}} → ℤ ₚ
  _⁻¹' x {{nz}} with coprime-Bézout (prime⇒coprime p-prime {{nz}} (toℕ<n x) )
  ... | +- x₁ y eq = - fromℕ< (m%n<n y p)
  ... | -+ x₁ y eq = fromℕ< (m%n<n y p)
  
  lemma-⁻¹ˡ : ∀ (x : ℤ ₚ) → {{nz : NonZero (toℕ x)}} →
    let xinv = (_⁻¹' x {{nz}}) in
    
    xinv * x ≡ ₁
    
  lemma-⁻¹ˡ x {{nz}} with coprime-Bézout (prime⇒coprime p-prime {{nz}} (toℕ<n x) )
  ... | +- x₁ y eq = claim1
    where
    open ≡.≡-Reasoning
    -xinv = fromℕ< (m%n<n y p)
    xinv = - -xinv

    +-group = Ring.+-group (+-*-ring (p-2))
    
    eq' : ₁₊ (y ℕ.* toℕ x) % p ≡ ₀
    eq' = begin
      ₁₊ (y ℕ.* toℕ x) % p ≡⟨ cong (_% p) eq ⟩
      x₁ ℕ.* p % p ≡⟨ m*n%n≡0 x₁ p ⟩
      ₀ ∎


    aux1 : xinv * x + -xinv * x ≡ ₀
    aux1 = begin
      xinv * x + -xinv * x ≡⟨ sym (*-distribʳ-+ x xinv -xinv) ⟩
      (xinv + -xinv) * x ≡⟨ cong (_* x) (+-inverseˡ -xinv) ⟩
      ₀ * x ≡⟨ refl ⟩
      ₀ ∎

    aux2 : ₁ + -xinv * x ≡ ₀
    aux2 = begin
      ₁ + -xinv * x ≡⟨ refl ⟩
      ₁ + fromℕ< (m%n<n y p) * x ≡⟨ refl ⟩
      ₁ + fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p) ≡⟨ refl ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+ toℕ (fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p))) p) ≡⟨ cong (\ □ → fromℕ< (m%n<n (toℕ 1ₚ ℕ.+ □) p)) (toℕ-fromℕ< ((m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p))) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+  (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) % p) p) ≡⟨ cong (\ □ → fromℕ< (m%n<n (toℕ 1ₚ ℕ.+  ( □ ℕ.* toℕ x) % p) p)) (toℕ-fromℕ< (m%n<n y p)) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+  ( (y % p) ℕ.* toℕ x) % p) p) ≡⟨ cong₂ (\ □₁ □₂ → fromℕ< (m%n<n (□₁ ℕ.+  ( (y % p) ℕ.* □₂) % p) p)) (m<n⇒m%n≡m (s≤s (NP.0<1+n {p-1}))) (sym (m<n⇒m%n≡m (toℕ<n x))) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ % p ℕ.+  ( (y % p) ℕ.* (toℕ x % p)) % p) p) ≡⟨ cong (\ □ → fromℕ< (m%n<n (toℕ 1ₚ % p ℕ.+  □) p)) (sym (%-distribˡ-* y (toℕ x) p)) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ % p ℕ.+  (y ℕ.* toℕ x) % p) p) ≡⟨ fromℕ<-cong ((toℕ 1ₚ % p ℕ.+  (y ℕ.* toℕ x) % p) % p) ((toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) % p) (sym (%-distribˡ-+ (toℕ 1ₚ) ((y ℕ.* toℕ x)) p)) (m%n<n (toℕ 1ₚ % p ℕ.+  (y ℕ.* toℕ x) % p) p) (m%n<n (toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) p) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) p) ≡⟨ fromℕ<-cong ((toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) % p) 0 eq' (m%n<n (toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) p) (NP.0<1+n {p-1}) ⟩
      fromℕ< (NP.0<1+n {p-1}) ≡⟨ refl ⟩
      ₀ ∎

    claim1 : (xinv * x) ≡ ₁
    claim1 = begin
      (xinv * x) ≡⟨ ∙-cancelʳ +-group (-xinv * x) ((xinv * x)) ₁ (trans aux1 (sym aux2)) ⟩
      ₁ ∎


  ... | -+ x₁ y eq = claim1
    where
    open ≡.≡-Reasoning
    xinv = fromℕ< (m%n<n y p)
    
    claim : (y ℕ.* toℕ x) % p ≡ ₁ % p
    claim = begin
      (y ℕ.* toℕ x) % p ≡⟨ cong (_% p) (≡.sym eq) ⟩
      (₁ ℕ.+ (x₁ ℕ.* ₂₊ p-2)) % p ≡⟨ (%-distribˡ-+ ₁ (x₁ ℕ.* ₂₊ p-2) p) ⟩
      (₁ % p ℕ.+ (x₁ ℕ.* ₂₊ p-2) % p) % p ≡⟨ cong (\ □ → (₁ % p ℕ.+ □) % p) (%-distribˡ-* x₁ p p) ⟩
      (₁ % p ℕ.+ (x₁ % p ℕ.* (₂₊ p-2 % p)) % p) % p ≡⟨ cong (\ □ → (₁ % p ℕ.+ □) % p) (cong (\ □ → (x₁ % p ℕ.* □) % p) (n%n≡0 p)) ⟩
      (₁ % p ℕ.+ (x₁ % p ℕ.* 0) % p) % p ≡⟨ cong (\ □ → (₁ % p ℕ.+ □) % p) (cong (_% p) (NP.*-zeroʳ (x₁ % p))) ⟩
      ₁ % p ℕ.+ 0 % p ≡⟨ refl ⟩
      ₁ % p ∎

    claim0 : ((y % p) ℕ.* toℕ x) % p ≡ ₁ % p
    claim0 = begin
      ((y % p) ℕ.* toℕ x) % p ≡⟨ %-distribˡ-* (y % p) (toℕ x) p ⟩
      ((y % p % p) ℕ.* (toℕ x % p)) % p ≡⟨ cong (\ □ → (□ ℕ.* (toℕ x % p)) % p) (m%n%n≡m%n y p) ⟩
      ((y % p) ℕ.* (toℕ x % p)) % p ≡⟨ ≡.sym ( %-distribˡ-* y (toℕ x) p) ⟩
      ((y) ℕ.* (toℕ x)) % p ≡⟨ claim ⟩
      ₁ % p ∎

    claim1 : (xinv * x) ≡ ₁
    claim1 = begin
      (xinv * x) ≡⟨ refl ⟩
      fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p) ≡⟨ cong (\ □ → fromℕ< (m%n<n (□ ℕ.* toℕ x) p)) (toℕ-fromℕ< (m%n<n y p)) ⟩
      fromℕ< (m%n<n ((y % p) ℕ.* toℕ x) p) ≡⟨ fromℕ<-cong (((y % p) ℕ.* toℕ x) % p) 1 claim0 (m%n<n ((y % p) ℕ.* toℕ x) p) (s≤s (NP.0<1+n {p-2})) ⟩
      fromℕ< (s≤s (NP.0<1+n {p-2})) ≡⟨ refl ⟩
      ₁ ∎

  lemma-⁻¹ʳ : ∀ (x : ℤ ₚ) → {{nz : NonZero (toℕ x)}} →
    let xinv = (_⁻¹' x {{nz}}) in
    
    x * xinv ≡ ₁
    
  lemma-⁻¹ʳ x {{nz}} = begin
    x * xinv ≡⟨ *-comm x xinv ⟩
    xinv * x ≡⟨ lemma-⁻¹ˡ x ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning
    xinv = _⁻¹' x {{nz}}


  lemma-⁻¹-nz : ∀ (x : ℤ ₚ) → {{nz : NonZero (toℕ x)}} → 
    let xinv = (_⁻¹' x {{nz}}) in

    xinv ≢ 0    
    
  lemma-⁻¹-nz x {{nz}} eq0 = 0ₚ≢1ₚ (trans (sym (claim2 eq0)) claim1)
    where
    open ≡.≡-Reasoning
    xinv = _⁻¹' x {{nz}}
    
    claim1 : (xinv * x) ≡ ₁
    claim1 = lemma-⁻¹ˡ x {{nz}}

    claim2 : xinv ≡ 0 → (xinv * x) ≡ ₀
    claim2 eq0 = begin
      (xinv * x) ≡⟨ cong (_* x) eq0 ⟩
      (0 * x) ≡⟨ refl ⟩
      ₀ ∎



  -- The inverse of a unit, packaged with the proof that it is again a
  -- unit.  This is the form the rest of the library uses; _⁻¹' is the
  -- underlying operation on residues.
  _⁻¹ : ∀ (x : ℤ* ₚ) → ℤ* ₚ
  _⁻¹ (x , nz) = (_⁻¹' x {{nztoℕ {y = x} {neq0 = nz}}}) , lemma-⁻¹-nz x {{nztoℕ {y = x} {neq0 = nz}}}





  lemma-⁻¹ˡ' : ∀ (x : ℤ ₚ) → {{nz : NonZero (toℕ x)}} →
    let xinv = (_⁻¹' x {{nz}}) in
    
    toℕ xinv ℕ.* toℕ x % ₚ ≡ ₁
    
  lemma-⁻¹ˡ' x {{nz}} = begin
    toℕ xinv ℕ.* toℕ x % ₚ ≡⟨ ≡.sym (toℕ-fromℕ< (m%n<n (toℕ xinv ℕ.* toℕ x) ₚ)) ⟩
    toℕ (fromℕ< (m%n<n (toℕ xinv ℕ.* toℕ x) ₚ)) ≡⟨ refl ⟩
    toℕ (xinv * x) ≡⟨ cong toℕ (lemma-⁻¹ˡ x {{nz}}) ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning
    xinv = (_⁻¹' x {{nz}})
  lemma-⁻¹ʳ' : ∀ (x : ℤ ₚ) → {{nz : NonZero (toℕ x)}} →
    let xinv = (_⁻¹' x {{nz}}) in
    
    toℕ x ℕ.* toℕ xinv % ₚ ≡ ₁
    
  lemma-⁻¹ʳ' x {{nz}} = begin
    toℕ x ℕ.* toℕ xinv % ₚ ≡⟨ cong (_% ₚ) (NP.*-comm (toℕ x) (toℕ xinv)) ⟩
    toℕ xinv ℕ.* toℕ x % ₚ ≡⟨ lemma-⁻¹ˡ' x ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning
    xinv = _⁻¹' x {{nz}}


  infixl 7 _*'_
  infixr 8 -'_


  _*'_ : ℤ* p → ℤ* p → ℤ* p
  _*'_ (a , nza) (b , nzb) = (a * b) , claim
    where
    ainv = _⁻¹' a {{nztoℕ {y = a} {neq0 = nza}}}
    binv = _⁻¹' b {{nztoℕ {y = b} {neq0 = nzb}}}
    
    claim : a * b ≢ ₀
    claim eq0 = 0ₚ≢1ₚ 0=1
      where
      open ≡.≡-Reasoning
      0=1 : 0ₚ ≡ 1ₚ
      0=1 = begin
        0ₚ ≡⟨ refl ⟩
        0ₚ * (binv * ainv) ≡⟨ cong (_* (binv * ainv)) (sym eq0) ⟩
        a * b * (binv * ainv) ≡⟨ *-assoc a b (binv * ainv) ⟩
        a * (b * (binv * ainv)) ≡⟨ cong (a *_) (sym (*-assoc b binv ainv)) ⟩
        a * ((b * binv) * ainv) ≡⟨ cong (a *_) (cong (_* ainv) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = nzb}}} )) ⟩
        a * (₁ * ainv) ≡⟨ cong (a *_) (*-identityˡ ainv) ⟩
        a * ainv ≡⟨ lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}} ⟩
        1ₚ ∎


  -'_ : ℤ* p → ℤ* p
  -'_ (a , nza) = - a , claim
    where
    ainv = _⁻¹' a {{nztoℕ {y = a} {neq0 = nza}}}
    open ≡.≡-Reasoning

    claim : - a ≢ ₀
    claim eq0 = 0ₚ≢-1ₚ 0=-1
      where
      0=-1 : 0ₚ ≡ - 1ₚ
      0=-1 = begin
        0ₚ ≡⟨ refl ⟩
        0ₚ * ainv ≡⟨ cong (_* ainv) (sym eq0) ⟩
        - a * ainv ≡⟨ sym (-‿distribˡ-* a ainv) ⟩
        - (a * ainv) ≡⟨ cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}}) ⟩
        - ₁ ≡⟨ refl ⟩
        - 1ₚ ∎


  inv-involutive : ∀ x → (x ⁻¹ ⁻¹) .proj₁ ≡ x .proj₁
  inv-involutive x = begin
    (x ⁻¹ ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ ((x ⁻¹ ⁻¹) .proj₁)) ⟩
    1ₚ * (x ⁻¹ ⁻¹) .proj₁ ≡⟨ sym (cong (_* (x ⁻¹ ⁻¹) .proj₁) (lemma-⁻¹ʳ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂} }})) ⟩
    (x .proj₁ * (x ⁻¹) .proj₁) * (x ⁻¹ ⁻¹) .proj₁ ≡⟨ *-assoc ( (x) .proj₁) ((x ⁻¹) .proj₁) ((x ⁻¹ ⁻¹) .proj₁) ⟩
    x .proj₁ * ((x ⁻¹) .proj₁ * (x ⁻¹ ⁻¹) .proj₁) ≡⟨ cong (x .proj₁ *_) (trans c1 (sym c2)) ⟩
    x .proj₁ * ((x ⁻¹) .proj₁ * (x) .proj₁) ≡⟨ sym (*-assoc ( (x) .proj₁) ((x ⁻¹) .proj₁) ((x) .proj₁)) ⟩
    (x .proj₁ * (x ⁻¹) .proj₁) * (x) .proj₁ ≡⟨ cong (_* (x) .proj₁) (lemma-⁻¹ʳ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂} }}) ⟩
    1ₚ * x .proj₁ ≡⟨ *-identityˡ (x .proj₁) ⟩
    x .proj₁ ∎
    where
    open ≡.≡-Reasoning
    c1 : (x ⁻¹) .proj₁ * (x ⁻¹ ⁻¹) .proj₁ ≡ 1ₚ
    c1 = lemma-⁻¹ʳ ((x ⁻¹) .proj₁) {{nztoℕ {y = (x ⁻¹) .proj₁} {neq0 = lemma-⁻¹-nz (x .proj₁) {{nztoℕ {y = (x) .proj₁} {neq0 = x .proj₂}}}}}}
    c2 : (x ⁻¹) .proj₁ * x .proj₁ ≡ 1ₚ
    c2 = lemma-⁻¹ˡ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂} }}

  inv-₁ : ((₁ , λ ()) ⁻¹) .proj₁ ≡ ₁
  inv-₁ = begin
    ((₁ , λ ()) ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ (((₁ , λ ()) ⁻¹) .proj₁)) ⟩
    ₁ * ((₁ , λ ()) ⁻¹) .proj₁ ≡⟨ lemma-⁻¹ʳ ₁ {{nztoℕ {y = 1ₚ} {neq0 = λ ()}}} ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning

  -- The modular inverse depends on its argument only through the value,
  -- not the ≢₀ proof: once the value is a successor, nztoℕ discards the
  -- proof (returning record { nonZero = tt }).  Casing on the value thus
  -- avoids heterogeneous equality (and hence axiom K).
  inv-cong : ∀ k* l* → k* .proj₁ ≡ l* .proj₁ → (k* ⁻¹) .proj₁ ≡ (l* ⁻¹) .proj₁
  inv-cong (₀ , nzk)    _         _    with () ← nzk refl
  inv-cong (₁₊ k , nzk) (l , nzl) refl = refl


  aux-inv-xy : ∀ x y → (y ⁻¹ *' x ⁻¹) .proj₁ * (x *' y) .proj₁ ≡ ₁
  aux-inv-xy x y = begin
    (y ⁻¹ *' x ⁻¹) .proj₁ * (x *' y) .proj₁ ≡⟨ *-assoc ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) ((x *' y) .proj₁) ⟩
    (y ⁻¹) .proj₁ * ((x ⁻¹) .proj₁ * (x .proj₁ * y .proj₁)) ≡⟨ cong ((y ⁻¹) .proj₁ *_) (sym (*-assoc ((x ⁻¹) .proj₁) (x .proj₁) (y .proj₁))) ⟩
    (y ⁻¹) .proj₁ * ((x ⁻¹) .proj₁ * x .proj₁ * y .proj₁) ≡⟨ cong ((y ⁻¹) .proj₁ *_) (cong (_* y .proj₁) (lemma-⁻¹ˡ ( x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂}}})) ⟩
    (y ⁻¹) .proj₁ * (₁ * y .proj₁) ≡⟨ cong ((y ⁻¹) .proj₁ *_) (*-identityˡ (y .proj₁)) ⟩
    (y ⁻¹) .proj₁ * y .proj₁ ≡⟨ lemma-⁻¹ˡ (y .proj₁) {{nztoℕ {y = y .proj₁} {neq0 = y .proj₂}}} ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning

  inv-distrib : ∀ x y → ((x *' y) ⁻¹) .proj₁ ≡ (x ⁻¹ *' y ⁻¹) .proj₁
  inv-distrib x y = begin
    ((x *' y) ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ (((x *' y) ⁻¹) .proj₁)) ⟩
    1ₚ * ((x *' y) ⁻¹) .proj₁ ≡⟨ sym (cong (_* ((x *' y) ⁻¹) .proj₁) (aux-inv-xy x y)) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ * (x *' y) .proj₁ * ((x *' y) ⁻¹) .proj₁ ≡⟨ *-assoc ((y ⁻¹ *' x ⁻¹) .proj₁) ((x *' y) .proj₁) (((x *' y) ⁻¹) .proj₁) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ * ((x *' y) .proj₁ * ((x *' y) ⁻¹) .proj₁) ≡⟨ cong ((y ⁻¹ *' x ⁻¹) .proj₁ *_) ((lemma-⁻¹ʳ ((x *' y) .proj₁)) {{nztoℕ {y = (x *' y) .proj₁} {neq0 = (x *' y) .proj₂}}}) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ * 1ₚ ≡⟨ *-identityʳ ((y ⁻¹ *' x ⁻¹) .proj₁) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ ≡⟨ *-comm ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) ⟩
    (x ⁻¹ *' y ⁻¹) .proj₁ ∎
    where
    open ≡.≡-Reasoning



  -1⁻¹ = - (((₁ , λ ())) ⁻¹) .proj₁
  -'₁ = -' (₁ , λ ())
  
  inv-neg₁ : -1⁻¹ ≡ - ₁
  inv-neg₁ = begin
    -1⁻¹ ≡⟨ cong -_ inv-₁ ⟩
    - ₁ ∎
    where
    open ≡.≡-Reasoning

  aux-₁² : - ₁ * - ₁ ≡ ₁
  aux-₁² = begin
    - ₁ * - ₁ ≡⟨ sym (-‿distribˡ-* ₁ (- ₁)) ⟩
    - (₁ * - ₁) ≡⟨ cong -_ (sym (-‿distribʳ-* ₁ ₁)) ⟩
    - - (₁ * ₁) ≡⟨ -‿involutive ₁ ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning

  aux-₁⁻¹ : let -'₁ = -' ((₁ , λ ())) in let -₁ = -'₁ .proj₁ in let -₁⁻¹ = (-'₁ ⁻¹) .proj₁ in
    -₁⁻¹ ≡ -₁
  aux-₁⁻¹ = begin
    -₁⁻¹ ≡⟨ sym (*-identityˡ -₁⁻¹) ⟩
    ₁ * -₁⁻¹ ≡⟨ cong (_* -₁⁻¹) (sym aux-₁²) ⟩
    (- ₁ * - ₁) * -₁⁻¹ ≡⟨ refl ⟩
    (-₁ * -₁) * -₁⁻¹ ≡⟨ *-assoc -₁ -₁ -₁⁻¹ ⟩
    -₁ * (-₁ * -₁⁻¹) ≡⟨ cong (-₁ *_) (lemma-⁻¹ʳ -₁ {{nztoℕ {y = -₁} {neq0 = -'₁ .proj₂}}}) ⟩
    -₁ * ₁ ≡⟨ *-identityʳ -₁ ⟩
    -₁ ∎
    where
    open ≡.≡-Reasoning

    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁


  aux₁⁻¹' : let ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁ in
    ₁⁻¹ ≡ ₁
  aux₁⁻¹' = begin
    ₁⁻¹ ≡⟨ sym (*-identityˡ ₁⁻¹) ⟩
    ₁ * ₁⁻¹ ≡⟨ lemma-⁻¹ʳ ₁ {{nztoℕ {y = 1ₚ} {neq0 = λ ()}}} ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning

    ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  aux-1=-1 : (-'₁ .proj₁) ≡ ₋₁
  aux-1=-1 = ≡.sym p-1=-1ₚ

  aux-'x=-x : ∀ (x : ℤ* ₚ) → ((-' x) .proj₁) ≡ - (x .proj₁)
  aux-'x=-x x = begin
    ((-' x) .proj₁) ≡⟨ refl ⟩
    - (x .proj₁) ∎
    where
    open ≡.≡-Reasoning


  inv-neg-comm : ∀ x → ((-' x) ⁻¹) .proj₁ ≡ - (x ⁻¹) .proj₁
  inv-neg-comm x@(x' , nz) = begin
    ((-' x) ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ (((-' x) ⁻¹) .proj₁)) ⟩
    ₁ * ((-' x) ⁻¹) .proj₁ ≡⟨ cong (_* ((-' x) ⁻¹) .proj₁) (sym aux) ⟩
    (- (x ⁻¹) .proj₁ * - x .proj₁) * ((-' x) ⁻¹) .proj₁  ≡⟨ *-assoc (- (x ⁻¹) .proj₁) (- x .proj₁) (((-' x) ⁻¹) .proj₁) ⟩
    - (x ⁻¹) .proj₁ * (- x .proj₁ * ((-' x) ⁻¹) .proj₁)  ≡⟨ cong (\ xx → - (x ⁻¹) .proj₁ * (xx * ((-' x) ⁻¹) .proj₁)) (sym (aux-'x=-x x)) ⟩
    - (x ⁻¹) .proj₁ * ((-' x) .proj₁ * ((-' x) ⁻¹) .proj₁)  ≡⟨ cong (- (x ⁻¹) .proj₁ *_) (lemma-⁻¹ʳ ((-' x) .proj₁) {{nztoℕ {y = (-' x) .proj₁} {neq0 = (-' x) .proj₂}}}) ⟩
    - (x ⁻¹) .proj₁ * ₁  ≡⟨ *-identityʳ (- (x ⁻¹) .proj₁) ⟩
    - (x ⁻¹) .proj₁ ∎
    where
    open ≡.≡-Reasoning
    aux : (- (x ⁻¹) .proj₁ * - x .proj₁) ≡ ₁
    aux = begin
      (- (x ⁻¹) .proj₁ * - x .proj₁) ≡⟨ sym (-‿distribˡ-* ((x ⁻¹) .proj₁) (- x .proj₁)) ⟩
      - ((x ⁻¹) .proj₁ * - x .proj₁) ≡⟨ sym (cong -_ (-‿distribʳ-* ((x ⁻¹) .proj₁) (x .proj₁))) ⟩
      - - ((x ⁻¹) .proj₁ * x .proj₁) ≡⟨ -‿involutive (((x ⁻¹) .proj₁ * x .proj₁)) ⟩
      ((x ⁻¹) .proj₁ * x .proj₁) ≡⟨ lemma-⁻¹ˡ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = nz}}} ⟩
      ₁ ∎

  inv-inv-neg : ∀ x → ((-' x ⁻¹) ⁻¹) .proj₁ ≡ - x .proj₁
  inv-inv-neg x = begin
    ((-' x ⁻¹) ⁻¹) .proj₁ ≡⟨ inv-neg-comm (x ⁻¹) ⟩
    - (x ⁻¹ ⁻¹) .proj₁ ≡⟨ cong -_ (inv-involutive x) ⟩
    - x .proj₁ ∎
    where
    open ≡.≡-Reasoning


  aux--b*-b⁻¹ : ∀ b' →
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in -b * -b⁻¹ ≡ ₁
  aux--b*-b⁻¹ b' =
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in begin
      -b * -b⁻¹ ≡⟨ sym (-‿distribˡ-* b -b⁻¹) ⟩
      -(b * -b⁻¹) ≡⟨ cong -_ (sym (-‿distribʳ-* b b⁻¹)) ⟩
      - -(b * b⁻¹) ≡⟨ -‿involutive ((b * b⁻¹)) ⟩
      (b * b⁻¹) ≡⟨ lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = b' .proj₂} }} ⟩
      ₁ ∎
    where
    open ≡.≡-Reasoning


  aux-xxxx : ∀ x → ((x ⁻¹ *' x ⁻¹) *' (x *' x)) .proj₁ ≡ ₁
  aux-xxxx x@(x0 , nz) = begin
    ((x ⁻¹ *' x ⁻¹) *' (x *' x)) .proj₁ ≡⟨ *-assoc x⁻¹ x⁻¹ (x0 * x0) ⟩
    (x ⁻¹ *' (x ⁻¹ *' (x *' x))) .proj₁ ≡⟨ cong ((x⁻¹ *_)) (sym (*-assoc x⁻¹ x0 x0)) ⟩
    (x ⁻¹ *' ((x ⁻¹ *' x) *' x)) .proj₁ ≡⟨ cong (\ xx → x⁻¹ * (xx * x0)) (lemma-⁻¹ˡ x0 {{nztoℕ {y = x0} {neq0 = x .proj₂} }}) ⟩
    (x ⁻¹) .proj₁ * (₁ * x .proj₁) ≡⟨ cong ((x⁻¹ *_)) (*-identityˡ x0) ⟩
    (x ⁻¹) .proj₁ * x .proj₁ ≡⟨ lemma-⁻¹ˡ x0 {{nztoℕ {y = x0} {neq0 = x .proj₂} }} ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning
    x⁻¹ = (x ⁻¹) .proj₁

  aux--b⁻¹*-b : ∀ b' →
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in -b⁻¹ * -b ≡ ₁

  aux--b⁻¹*-b b' = 
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in begin
      -b⁻¹ * -b ≡⟨ *-comm -b⁻¹ -b ⟩
      -b * -b⁻¹ ≡⟨ aux--b*-b⁻¹ b' ⟩
      ₁ ∎
    where
    open ≡.≡-Reasoning

  aux-k*-[-k]⁻¹ : ∀ k → (k *' -' (-' k) ⁻¹) .proj₁ ≡ ₁
  aux-k*-[-k]⁻¹ k = begin
    (k *' -' (-' k) ⁻¹) .proj₁ ≡⟨ auto ⟩
    k .proj₁ * (-' (-' k) ⁻¹) .proj₁ ≡⟨ auto ⟩
    k .proj₁ * - (((-' k) ⁻¹) .proj₁) ≡⟨ cong (\ xx → k .proj₁ * - xx) (inv-neg-comm k) ⟩
    k .proj₁ * - - ((k ⁻¹) .proj₁) ≡⟨ cong (k .proj₁ *_) (-‿involutive ((k ⁻¹) .proj₁)) ⟩
    k .proj₁ * ((k ⁻¹) .proj₁) ≡⟨ lemma-⁻¹ʳ (k .proj₁) {{nztoℕ {y = k .proj₁} {neq0 = k .proj₂}}} ⟩
    ₁ ∎
    where
    open ≡.≡-Reasoning

  aux-k⁻¹=-[-k⁻¹] : ∀ k → (k ⁻¹) .proj₁ ≡ - (((-' k) ⁻¹) .proj₁)
  aux-k⁻¹=-[-k⁻¹] k = begin
    (k ⁻¹) .proj₁ ≡⟨ auto ⟩
    ( k ⁻¹) .proj₁ ≡⟨ sym (-‿involutive ( (k ⁻¹) .proj₁)) ⟩
    - - ( k ⁻¹) .proj₁ ≡⟨ ≡.cong -_ (sym (inv-neg-comm k)) ⟩
    - (((-' k) ⁻¹) .proj₁) ∎
    where
    open ≡.≡-Reasoning


  aux-₁-b : ∀ k* a* →
    let
      a⁻¹ = (a* ⁻¹) .proj₁
      k = k* .proj₁
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
      b' = -' (k* ⁻¹) *' a*
      b = b' .proj₁
      -b = - b
      -b⁻¹* =  -' b' ⁻¹
      -b⁻¹ =  -b⁻¹* .proj₁
    in - ₁ * -b⁻¹ ≡ -k * a⁻¹
  aux-₁-b k* a* = begin
    - ₁ * -b⁻¹ ≡⟨ auto ⟩
    - ₁ * (-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ -1*x≈-x ((-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁) ⟩
    - (-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ auto ⟩
    - - ((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ -‿involutive (((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ) ⟩
    ((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ inv-distrib (-' (k* ⁻¹)) a* ⟩
    ((-' (k* ⁻¹)) ⁻¹ *' a* ⁻¹) .proj₁ ≡⟨ auto ⟩
    ((-' (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁ ≡⟨ cong (_* (a* ⁻¹) .proj₁) (inv-neg-comm (k* ⁻¹)) ⟩
    - (( (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁ ≡⟨ cong (_* (a* ⁻¹) .proj₁) (cong -_ (inv-involutive k*)) ⟩
    - k * (a* ⁻¹) .proj₁ ≡⟨ auto ⟩
    - k * a⁻¹ ∎
    where
    open ≡.≡-Reasoning
    a⁻¹ = (a* ⁻¹) .proj₁
    k = k* .proj₁
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = -' (k* ⁻¹) *' a*
    b = b' .proj₁
    -b = - b
    -b⁻¹* =  -' b' ⁻¹
    -b⁻¹ =  -b⁻¹* .proj₁


  aux--b⁻¹ : ∀ k* a* →
    let
      a⁻¹ = (a* ⁻¹) .proj₁
      k = k* .proj₁
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
      b' = -' (k* ⁻¹) *' a*
      b = b' .proj₁
      -b = - b
      -b⁻¹* =  -' b' ⁻¹
      -b⁻¹ =  -b⁻¹* .proj₁
    in -b⁻¹ ≡ a⁻¹ * k
  aux--b⁻¹ k* a* = begin
    -b⁻¹ ≡⟨ auto ⟩
    (-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ auto ⟩
    - (((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁) ≡⟨ cong -_ (inv-distrib (-' (k* ⁻¹)) a*) ⟩
    - (((-' (k* ⁻¹)) ⁻¹ *' a* ⁻¹) .proj₁) ≡⟨ auto ⟩
    - (((-' (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁) ≡⟨ cong -_ (cong (_* (a* ⁻¹) .proj₁) (inv-neg-comm (k* ⁻¹))) ⟩
    - (- (( (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁) ≡⟨ cong -_ (cong (_* (a* ⁻¹) .proj₁) (cong -_ (inv-involutive k*))) ⟩
    - (- k * (a* ⁻¹) .proj₁) ≡⟨ -‿distribˡ-* (- k) ((a* ⁻¹) .proj₁) ⟩
    - - k * (a* ⁻¹) .proj₁ ≡⟨ cong (_* (a* ⁻¹) .proj₁) (-‿involutive k) ⟩
    k * (a* ⁻¹) .proj₁ ≡⟨ *-comm k a⁻¹ ⟩
    a⁻¹ * k ∎
    where
    open ≡.≡-Reasoning
    a⁻¹ = (a* ⁻¹) .proj₁
    k = k* .proj₁
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = -' (k* ⁻¹) *' a*
    b = b' .proj₁
    -b = - b
    -b⁻¹* =  -' b' ⁻¹
    -b⁻¹ =  -b⁻¹* .proj₁



  aux-a*-b⁻¹ : ∀ k* a* →
    let
      a⁻¹ = (a* ⁻¹) .proj₁
      a = a* .proj₁
      -a = - a
      k = k* .proj₁
      k² = k * k
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
      b' = -' (k* ⁻¹) *' a*
      b = b' .proj₁
      -b = - b
      -b⁻¹* =  -' b' ⁻¹
      -b⁻¹ =  -b⁻¹* .proj₁
    in -a * -b⁻¹ ≡ -k
  aux-a*-b⁻¹ k* a* = begin
    -a * -b⁻¹ ≡⟨ cong (-a *_) (aux--b⁻¹ k* a*) ⟩
    -a * (a⁻¹ * k) ≡⟨ sym (*-assoc -a a⁻¹ k) ⟩
    -a * a⁻¹ * k ≡⟨ cong (_* k) (sym (-‿distribˡ-* a a⁻¹)) ⟩
    -(a * a⁻¹) * k ≡⟨ cong (_* k) (cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}})) ⟩
    - ₁ * k ≡⟨ -1*x≈-x k ⟩
    - k ∎
    where
    open ≡.≡-Reasoning
    a⁻¹ = (a* ⁻¹) .proj₁
    a = a* .proj₁
    -a = - a
    k = k* .proj₁
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = -' (k* ⁻¹) *' a*
    b = b' .proj₁
    -b = - b
    -b⁻¹* =  -' b' ⁻¹
    -b⁻¹ =  -b⁻¹* .proj₁



  lemma-toℕ-% : ∀ (a b : ℤ ₚ) → (toℕ a ℕ.* toℕ b) % p ≡ toℕ (a * b)
  lemma-toℕ-% a b = begin
    (toℕ a ℕ.* toℕ b) % p ≡⟨ sym (toℕ-fromℕ< (m%n<n (toℕ a ℕ.* toℕ b) p)) ⟩
    toℕ (a * b) ∎
    where
    open ≡.≡-Reasoning


  lemma-x^′1=x : ∀ (x : ℤ ₚ) → x ^′ 1 ≡ x
  lemma-x^′1=x x@₀ = auto
  lemma-x^′1=x x@(₁₊ _) = begin
    x ^′ 1 ≡⟨ auto ⟩
    x * (x ^′ 0) ≡⟨ auto ⟩
    x * ₁ ≡⟨ *-identityʳ x ⟩
    x ∎
    where
    open ≡-Reasoning

  lemma-x^′k≠0 : ∀ x k → x ≢ ₀ → x ^′ k ≢ 0ₚ
  lemma-x^′k≠0 x ₀ nz = λ ()
  lemma-x^′k≠0 x (₁₊ k) nz = xx .proj₂
    where
    xx = (x , nz) *' (x ^′ k , lemma-x^′k≠0 x k nz)

  infixr 8 _^'_
  _^'_ : ℤ* ₚ → ℕ → ℤ* ₚ 
  _^'_ (x , nz) k = (x ^′ k) , (lemma-x^′k≠0 x k nz)


  *-^′-distribʳ : ∀ (x y : ℤ ₚ) k → (x * y) ^′ k ≡ x ^′ k * y ^′ k
  *-^′-distribʳ x y 0 = auto
  *-^′-distribʳ x y k@(₁₊ k') = begin
    (x * y) ^′ k ≡⟨ auto ⟩
    (x * y) * (x * y) ^′ k' ≡⟨ ≡.cong ((x * y) *_) ( *-^′-distribʳ x y k') ⟩
    (x * y) * (x ^′ k' * y ^′ k') ≡⟨ *-assoc x y (x ^′ k' * y ^′ k') ⟩
    x * (y * (x ^′ k' * y ^′ k')) ≡⟨ ≡.sym (≡.cong (x *_) (*-assoc y (x ^′ k') (y ^′ k'))) ⟩
    x * ((y * x ^′ k') * y ^′ k') ≡⟨ ≡.cong (\ xx → x * ((xx) * y ^′ k')) (*-comm y (x ^′ k')) ⟩
    x * ((x ^′ k' * y) * y ^′ k') ≡⟨ ≡.cong (x *_) (*-assoc (x ^′ k') y (y ^′ k')) ⟩
    x * (x ^′ k' * (y * y ^′ k')) ≡⟨ ≡.sym (*-assoc x (x ^′ k') (y * y ^′ k')) ⟩
    (x * x ^′ k') * (y * y ^′ k') ≡⟨ auto ⟩
    x ^′ k * y ^′ k ∎
    where
    open ≡-Reasoning

  +-^′-distribʳ : ∀ (x : ℤ ₚ) k l → x ^′ k * x ^′ l ≡ x ^′ (k ℕ.+ l)
  +-^′-distribʳ x k@0 l = begin
    x ^′ k * x ^′ l ≡⟨ auto ⟩
    ₁ * x ^′ l ≡⟨ *-identityˡ (x ^′ l) ⟩
    x ^′ (k ℕ.+ l) ∎
    where
    open ≡-Reasoning
  +-^′-distribʳ x k@(₁₊ k') l = begin
    x ^′ k * x ^′ l ≡⟨ *-assoc x (x ^′ k') (x ^′ l) ⟩
    x * (x ^′ k' * x ^′ l) ≡⟨ ≡.cong (x *_) (+-^′-distribʳ x k' l) ⟩
    x * (x ^′ (k' ℕ.+ l)) ≡⟨ auto ⟩
    (x ^′ ₁₊ (k' ℕ.+ l)) ≡⟨ auto ⟩
    x ^′ (k ℕ.+ l) ∎
    where
    open ≡-Reasoning

  1^k=1 : ∀ k → ₁ ^′ k ≡ 1ₚ
  1^k=1 k@0 = auto
  1^k=1 k@(₁₊ k') = begin
    ₁ ^′ k ≡⟨ auto ⟩
    ₁ * ₁ ^′ k' ≡⟨ *-identityˡ (₁ ^′ k') ⟩
    ₁ ^′ k' ≡⟨ 1^k=1 k' ⟩
    ₁ ∎
    where
    open ≡-Reasoning


  x^1=x : ∀ (x : ℤ ₚ) → x ^′ 1 ≡ x
  x^1=x x = begin
    x * x ^′ 0 ≡⟨ ≡.cong (x *_) auto ⟩
    x * ₁ ≡⟨ *-identityʳ x ⟩
    x ∎
    where
    open ≡-Reasoning

  lemma-^^-comm : ∀ (x : ℤ ₚ) k l → x ^′ l ^′ k ≡ x ^′ k ^′ l
  lemma-^^-* : ∀ (x : ℤ ₚ) k l → x ^′ (k ℕ.* l) ≡ x ^′ k ^′ l

  lemma-^^-comm x k@0 l = begin
    x ^′ l ^′ k ≡⟨ auto ⟩
    ₁ ≡⟨ ≡.sym (1^k=1 l) ⟩
    ₁ ^′ l ≡⟨ auto ⟩
    x ^′ k ^′ l ∎
    where
    open ≡-Reasoning
  lemma-^^-comm x k@(₁₊ k') l = begin
    x ^′ l ^′ k ≡⟨ auto ⟩
    x ^′ l * x ^′ l ^′ k' ≡⟨ ≡.cong (x ^′ l *_) (lemma-^^-comm x k' l) ⟩
    (x ^′ l) * (x ^′ k') ^′ l  ≡⟨ ≡.sym (*-^′-distribʳ x (x ^′ k') l) ⟩
    (x * x ^′ k') ^′ l  ≡⟨ auto ⟩
    x ^′ k ^′ l ∎
    where
    open ≡-Reasoning

  lemma-^^-* x ₀ l = ≡.sym (1^k=1 l)
  lemma-^^-* x k@(₁₊ k') l = begin
    x ^′ (k ℕ.* l) ≡⟨ auto ⟩
    x ^′ (l ℕ.+ k' ℕ.* l) ≡⟨ ≡.sym (+-^′-distribʳ x l (k' ℕ.* l)) ⟩
    x ^′ l * x ^′ (k' ℕ.* l) ≡⟨ ≡.cong (x ^′ l *_) (lemma-^^-* x k' l) ⟩
    x ^′ l * x ^′ k' ^′ l ≡⟨ ≡.cong (x ^′ l *_) (lemma-^^-comm x l k') ⟩
    x ^′ l * x ^′ l ^′ k' ≡⟨ ≡.cong (_* x ^′ l ^′ k') (≡.sym (x^1=x (x ^′ l))) ⟩
    x ^′ l ^′ 1 * x ^′ l ^′ k' ≡⟨ +-^′-distribʳ (x ^′ l) 1 k' ⟩
    x ^′ l ^′ ₁₊ k' ≡⟨ lemma-^^-comm x k l ⟩
    x ^′ k ^′ l ∎
    where
    open ≡-Reasoning
