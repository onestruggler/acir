------------------------------------------------------------------------
-- Presentations of groups
--
-- Width-1 head-injectivity for the plain gate set: ML 1 coset
-- representatives are distinguished by the head of their Pauli action.
--
-- Transplanted from ExtendedGate.NF-Inj-Base.lemma-nf1-head-inj, with
-- the act-chains re-derived from BoxAction's act-S^ / act-HS^ / act-M
-- closed forms (the live section words S^ (- e) / M inv / H • S^ -b/a
-- unfold definitionally under act).  This is the width-1 base of the
-- lemma-lm-head-inj width induction — the sole postulate of
-- Normalization.NF-Inj, i.e. the completeness crux.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.NF1HeadInj
  (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Vec using (_∷_ ; [] ; head)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open ≡-Reasoning

open import Data.Fin using (Fin)
open import Notations

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; pZ ; pX)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (S^)
open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; act-S^ ; act-HS^ ; act-M)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (ML ; A ; [_]ᵐˡ)

------------------------------------------------------------------------
-- Small helpers

-- A-boxes are compared on their value component.
A-≡ : ∀ (a₁ a₂ : A) → a₁ .proj₁ ≡ a₂ .proj₁ → a₁ ≡ a₂
A-≡ (_ , _) (_ , _) refl = refl

neg-inj : ∀ (a b : ℤ ₚ) → - a ≡ - b → a ≡ b
neg-inj a b h = begin
  a     ≡⟨ sym (-‿involutive a) ⟩
  - - a ≡⟨ cong -_ h ⟩
  - - b ≡⟨ -‿involutive b ⟩
  b     ∎

-- Left multiplicative cancellation by a nonzero scalar.
*-cancelˡ-nz : ∀ (a x y : ℤ ₚ) (nz : a ≢ ₀) → a * x ≡ a * y → x ≡ y
*-cancelˡ-nz a x y nz eq = begin
  x               ≡⟨ sym (*-identityˡ x) ⟩
  ₁ * x           ≡⟨ cong (_* x) (sym (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nz}}})) ⟩
  ainv * a * x    ≡⟨ *-assoc ainv a x ⟩
  ainv * (a * x)  ≡⟨ cong (ainv *_) eq ⟩
  ainv * (a * y)  ≡⟨ sym (*-assoc ainv a y) ⟩
  ainv * a * y    ≡⟨ cong (_* y) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nz}}}) ⟩
  ₁ * y           ≡⟨ *-identityˡ y ⟩
  y               ∎
  where ainv = ((a , nz) ⁻¹) .proj₁

-- A nonzero scalar's negation is nonzero (via - ₀ ≡ ₀).
-₀≡₀ : _≡_ {A = ℤ ₚ} (- ₀) ₀
-₀≡₀ = trans (sym (+-identityʳ (- z))) (+-inverseˡ z)
  where
  z : ℤ ₚ
  z = ₀

suc≢₀ : ∀ {x : Fin (₁₊ p-2)} → _≡_ {A = ℤ ₚ} (₁₊ x) ₀ → ⊥
suc≢₀ ()

neg-suc-nz : ∀ (x : Fin (₁₊ p-2)) → - (₁₊ x) ≡ ₀ → ⊥
neg-suc-nz x h = suc≢₀
  (trans (sym (-‿involutive (₁₊ x))) (trans (cong -_ h) -₀≡₀))

------------------------------------------------------------------------
-- The four head evaluations
--
-- act [ lm ]ᵐˡ for lm : ML 1 is a single-qudit map; its head is the
-- whole entry.  Four evaluations pin the map down at pZ and pX for the
-- two A-shapes.  In each, the section word unfolds definitionally to
-- S^ (- e) ∘ M inv (x = ₀ shape) or S^ (- e) ∘ M inv ∘ (H • S^ k)
-- (x ≠ ₀ shape, k = - y * x⁻¹).

-- x = ₀ branch (a = (₀ , ₁₊ y')).
hdZ0 : ∀ e y' (pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₀ , ₁₊ y') (₀ , ₀) → ⊥) →
  head (act [ (([] , e) , ([] , ((₀ , ₁₊ y') , pr))) ]ᵐˡ (pZ ∷ []))
    ≡ (₀ , ((₁₊ y' , λ ()) ⁻¹) .proj₁)
hdZ0 e y' pr = cong head
  (trans (cong (act (S^ (- e))) (act-M inv ₀ ₁ []))
  (trans (act-S^ (- e) (₀ * invI) (₁ * xI) [])
         (cong (_∷ []) (≡×≡⇒≡ (z1 , z2)))))
  where
  inv  = (₁₊ y' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  z1 : ₀ * invI ≡ ₀
  z1 = *-zeroˡ invI
  z2 : ₁ * xI + (₀ * invI) * (- e) ≡ xI
  z2 = trans (cong₂ _+_ (*-identityˡ xI)
               (trans (cong (_* (- e)) (*-zeroˡ invI)) (*-zeroˡ (- e))))
             (+-identityʳ xI)

hdX0 : ∀ e y' (pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₀ , ₁₊ y') (₀ , ₀) → ⊥) →
  head (act [ (([] , e) , ([] , ((₀ , ₁₊ y') , pr))) ]ᵐˡ (pX ∷ []))
    ≡ (₁₊ y' , (₁₊ y') * (- e))
hdX0 e y' pr = cong head
  (trans (cong (act (S^ (- e))) (act-M inv ₁ ₀ []))
  (trans (act-S^ (- e) (₁ * invI) (₀ * xI) [])
         (cong (_∷ []) (≡×≡⇒≡ (p1 , p2)))))
  where
  inv  = (₁₊ y' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  p1 : ₁ * invI ≡ ₁₊ y'
  p1 = trans (*-identityˡ invI) (inv-involutive (₁₊ y' , λ ()))
  p2 : ₀ * xI + (₁ * invI) * (- e) ≡ (₁₊ y') * (- e)
  p2 = trans (cong₂ _+_ (*-zeroˡ xI) (cong (_* (- e)) p1))
             (+-identityˡ ((₁₊ y') * (- e)))

-- x ≠ ₀ branch (a = (₁₊ x' , y)); the section tail is H • S^ k with
-- k = - y * x⁻¹.
hdZ1 : ∀ e x' y (pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₁₊ x' , y) (₀ , ₀) → ⊥) →
  head (act [ (([] , e) , ([] , ((₁₊ x' , y) , pr))) ]ᵐˡ (pZ ∷ []))
    ≡ (- (₁₊ x') , (₁₊ x') * e)
hdZ1 e x' y pr = cong head
  (trans (cong (λ v → act (S^ (- e)) (act-M-chain v)) (act-HS^ k ₀ ₁ []))
  (trans (cong (act (S^ (- e))) (act-M inv (- (₁ + ₀ * k)) ₀ []))
  (trans (act-S^ (- e) ((- (₁ + ₀ * k)) * invI) (₀ * xI) [])
         (cong (_∷ []) (≡×≡⇒≡ (q1 , q2))))))
  where
  inv  = (₁₊ x' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  k    = - y * xI
  act-M-chain = act (Symplectic.M inv)
  s1 : ₁ + ₀ * k ≡ ₁
  s1 = trans (cong (₁ +_) (*-zeroˡ k)) (+-identityʳ ₁)
  q1 : (- (₁ + ₀ * k)) * invI ≡ - (₁₊ x')
  q1 = begin
    (- (₁ + ₀ * k)) * invI ≡⟨ cong (λ z → (- z) * invI) s1 ⟩
    (- ₁) * invI           ≡⟨ sym (-‿distribˡ-* ₁ invI) ⟩
    - (₁ * invI)           ≡⟨ cong -_ (*-identityˡ invI) ⟩
    - invI                 ≡⟨ cong -_ (inv-involutive (₁₊ x' , λ ())) ⟩
    - (₁₊ x')              ∎
  negneg : (- (₁₊ x')) * (- e) ≡ (₁₊ x') * e
  negneg = trans (sym (-‿distribˡ-* (₁₊ x') (- e)))
           (trans (cong -_ (sym (-‿distribʳ-* (₁₊ x') e)))
                  (-‿involutive ((₁₊ x') * e)))
  q2 : ₀ * xI + ((- (₁ + ₀ * k)) * invI) * (- e) ≡ (₁₊ x') * e
  q2 = trans (cong₂ _+_ (*-zeroˡ xI)
               (trans (cong (_* (- e)) q1) negneg))
             (+-identityˡ ((₁₊ x') * e))

hdX1 : ∀ e x' y (pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₁₊ x' , y) (₀ , ₀) → ⊥) →
  head (act [ (([] , e) , ([] , ((₁₊ x' , y) , pr))) ]ᵐˡ (pX ∷ [])) .proj₁ ≡ y
hdX1 e x' y pr = trans
  (cong proj₁ (cong head
    (trans (cong (λ v → act (S^ (- e)) (act-M-chain v)) (act-HS^ k ₁ ₀ []))
    (trans (cong (act (S^ (- e))) (act-M inv (- (₀ + ₁ * k)) ₁ []))
           (act-S^ (- e) ((- (₀ + ₁ * k)) * invI) (₁ * xI) [])))))
  r1
  where
  inv  = (₁₊ x' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  k    = - y * xI
  act-M-chain = act (Symplectic.M inv)
  ii : invI ≡ ₁₊ x'
  ii = inv-involutive (₁₊ x' , λ ())
  r1 : (- (₀ + ₁ * k)) * invI ≡ y
  r1 = begin
    (- (₀ + ₁ * k)) * invI  ≡⟨ cong (λ z → (- z) * invI)
                                 (trans (+-identityˡ (₁ * k)) (*-identityˡ k)) ⟩
    (- k) * invI            ≡⟨ cong (_* invI)
                                 (trans (-‿distribˡ-* (- y) xI)
                                        (cong (_* xI) (-‿involutive y))) ⟩
    y * xI * invI           ≡⟨ *-assoc y xI invI ⟩
    y * (xI * invI)         ≡⟨ cong (λ z → y * (xI * z)) ii ⟩
    y * (xI * (₁₊ x'))      ≡⟨ cong (y *_)
                                 (lemma-⁻¹ˡ (₁₊ x')
                                   {{nztoℕ {y = ₁₊ x'} {neq0 = λ ()}}}) ⟩
    y * ₁                   ≡⟨ *-identityʳ y ⟩
    y                       ∎

------------------------------------------------------------------------
-- n=1 head-injectivity: ML 1 elements are distinguished by the head of
-- their Pauli action.  Recover the A-shape (x = ₀ vs x ≠ ₀) from the
-- pZ head, then the remaining data from the pZ/pX heads.

lemma-nf1-head-inj : ∀ (lm₁ lm₂ : ML 1) →
  (∀ (ps : Pauli 1) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) →
  lm₁ ≡ lm₂
-- Absurd A = (₀ , ₀) cases.
lemma-nf1-head-inj (([] , _) , ([] , ((₀ , ₀) , pr₁))) _ _ = ⊥-elim (pr₁ refl)
lemma-nf1-head-inj (([] , _) , ([] , ((₁₊ _ , _) , _))) (([] , _) , ([] , ((₀ , ₀) , pr₂))) _ = ⊥-elim (pr₂ refl)
lemma-nf1-head-inj (([] , _) , ([] , ((₀ , ₁₊ _) , _))) (([] , _) , ([] , ((₀ , ₀) , pr₂))) _ = ⊥-elim (pr₂ refl)
-- x₁ = ₀ , x₂ = ₀.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₀ , ₁₊ y₁') , pr₁))) (([] , e₂) , ([] , ((₀ , ₁₊ y₂') , pr₂))) h =
  ≡×≡⇒≡ (cong ([] ,_) e-eq , cong ([] ,_) a-eq)
  where
  X0eq : (₁₊ y₁' , (₁₊ y₁') * (- e₁)) ≡ (₁₊ y₂' , (₁₊ y₂') * (- e₂))
  X0eq = trans (sym (hdX0 e₁ y₁' pr₁)) (trans (h (pX ∷ [])) (hdX0 e₂ y₂' pr₂))
  y-eq : _≡_ {A = ℤ ₚ} (₁₊ y₁') (₁₊ y₂')
  y-eq = cong proj₁ X0eq
  a-eq : ((₀ , ₁₊ y₁') , pr₁) ≡ ((₀ , ₁₊ y₂') , pr₂)
  a-eq = A-≡ _ _ (cong (₀ ,_) y-eq)
  coeff-eq : (₁₊ y₁') * (- e₁) ≡ (₁₊ y₁') * (- e₂)
  coeff-eq = trans (cong proj₂ X0eq) (cong (_* (- e₂)) (sym y-eq))
  e-eq : e₁ ≡ e₂
  e-eq = neg-inj e₁ e₂ (*-cancelˡ-nz (₁₊ y₁') (- e₁) (- e₂) (λ ()) coeff-eq)
-- x₁ = ₀ , x₂ ≠ ₀ : contradictory pZ heads.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₀ , ₁₊ y₁') , pr₁))) (([] , e₂) , ([] , ((₁₊ x₂' , y₂) , pr₂))) h =
  ⊥-elim (neg-suc-nz x₂' (sym peq))
  where
  Zeq : (₀ , ((₁₊ y₁' , λ ()) ⁻¹) .proj₁) ≡ (- (₁₊ x₂') , (₁₊ x₂') * e₂)
  Zeq = trans (sym (hdZ0 e₁ y₁' pr₁)) (trans (h (pZ ∷ [])) (hdZ1 e₂ x₂' y₂ pr₂))
  peq : ₀ ≡ - (₁₊ x₂')
  peq = cong proj₁ Zeq
-- x₁ ≠ ₀ , x₂ = ₀ : contradictory pZ heads.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₁₊ x₁' , y₁) , pr₁))) (([] , e₂) , ([] , ((₀ , ₁₊ y₂') , pr₂))) h =
  ⊥-elim (neg-suc-nz x₁' peq)
  where
  Zeq : (- (₁₊ x₁') , (₁₊ x₁') * e₁) ≡ (₀ , ((₁₊ y₂' , λ ()) ⁻¹) .proj₁)
  Zeq = trans (sym (hdZ1 e₁ x₁' y₁ pr₁)) (trans (h (pZ ∷ [])) (hdZ0 e₂ y₂' pr₂))
  peq : - (₁₊ x₁') ≡ ₀
  peq = cong proj₁ Zeq
-- x₁ ≠ ₀ , x₂ ≠ ₀.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₁₊ x₁' , y₁) , pr₁))) (([] , e₂) , ([] , ((₁₊ x₂' , y₂) , pr₂))) h =
  ≡×≡⇒≡ (cong ([] ,_) e-eq , cong ([] ,_) a-eq)
  where
  Zeq : (- (₁₊ x₁') , (₁₊ x₁') * e₁) ≡ (- (₁₊ x₂') , (₁₊ x₂') * e₂)
  Zeq = trans (sym (hdZ1 e₁ x₁' y₁ pr₁)) (trans (h (pZ ∷ [])) (hdZ1 e₂ x₂' y₂ pr₂))
  x-eq : _≡_ {A = ℤ ₚ} (₁₊ x₁') (₁₊ x₂')
  x-eq = neg-inj (₁₊ x₁') (₁₊ x₂') (cong proj₁ Zeq)
  y-eq : y₁ ≡ y₂
  y-eq = trans (sym (hdX1 e₁ x₁' y₁ pr₁)) (trans (cong proj₁ (h (pX ∷ []))) (hdX1 e₂ x₂' y₂ pr₂))
  a-eq : ((₁₊ x₁' , y₁) , pr₁) ≡ ((₁₊ x₂' , y₂) , pr₂)
  a-eq = A-≡ _ _ (≡×≡⇒≡ (x-eq , y-eq))
  coeff-eq : (₁₊ x₁') * e₁ ≡ (₁₊ x₁') * e₂
  coeff-eq = trans (cong proj₂ Zeq) (cong (_* e₂) (sym x-eq))
  e-eq : e₁ ≡ e₂
  e-eq = *-cancelˡ-nz (₁₊ x₁') e₁ e₂ (λ ()) coeff-eq
