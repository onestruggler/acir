------------------------------------------------------------------------
-- Presentations of groups
--
-- b-vector and d-vector row-clearing for the inj₁ case of Theorem-LM.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.BBox (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Nat using (zero ; suc)
open import Data.Fin using (toℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_ ; head ; tail)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; module ≡-Reasoning)

open import Notations
open import Word.Base using (_•_ ; _^_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; sform1 ; sform ; pZ ; pX ; pI ; pIₙ ; pZ₀ ; pX₀)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (_↑ ; CX' ; CX'^ ; H ; CZ ; S^ ; Ex)

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (D ; B ; E ; M ; [_]ᵈ ; [_]ᵛᵈ ; [_]ᵇ ; [_]ᵛᵇ ; [_]ᵐ ; [_]ᵉ)

open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; lemma-act-↑ ; act-CZ^ ; act-S^ ; act-H ; act-Ex)
open import Examples.Groups.Symplectic.DBox p-2 p-prime using (lemma-dbox-IZ ; lemma-dbox)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The CX' action (verified).

act-CX' : ∀ (a b c d : ℤ ₚ) (t : Pauli n) →
  act CX' ((a , b) ∷ (c , d) ∷ t) ≡ (- (- a + c) , - (- b)) ∷ (c , d + - (- b)) ∷ t
act-CX' a b c d t = Eq.refl

------------------------------------------------------------------------
-- CX'^ κ = H³ • CZ^κ • H (Syntactics), so its action is direct.

act-CX'^ : ∀ (κ a b c d : ℤ ₚ) (t : Pauli n) →
  act (CX'^ κ) ((a , b) ∷ (c , d) ∷ t)
    ≡ (- (- (a + c * κ)) , - (- b)) ∷ (c , d + (- b) * κ) ∷ t
act-CX'^ κ a b c d t = Eq.cong (act (H ^ 3)) (act-CZ^ κ (- b) a c d t)

------------------------------------------------------------------------
-- A single b-box clears its own vector:  act [ v ]ᵇ (pZ ∷ v ∷ t) = pI ∷ pZ ∷ t.

lemma-bbox : ∀ (v : B) (t : Pauli n) → act [ v ]ᵇ (pZ ∷ v ∷ t) ≡ pI ∷ pZ ∷ t
lemma-bbox (₀ , vb) t = begin
  act (Ex • CX'^ vb) (pZ ∷ (₀ , vb) ∷ t)
    ≡⟨ Eq.cong (act Ex) (act-CX'^ vb ₀ ₁ ₀ vb t) ⟩
  act Ex ((- (- (₀ + ₀ * vb)) , - (- ₁)) ∷ (₀ , vb + (- ₁) * vb) ∷ t)
    ≡⟨ act-Ex (- (- (₀ + ₀ * vb))) (- (- ₁)) ₀ (vb + (- ₁) * vb) t ⟩
  (₀ , vb + (- ₁) * vb) ∷ (- (- (₀ + ₀ * vb)) , - (- ₁)) ∷ t
    ≡⟨ Eq.cong₂ (λ u w → (₀ , u) ∷ w ∷ t) clear-vb (≡×≡⇒≡ (clear-x0 , -‿involutive ₁)) ⟩
  pI ∷ pZ ∷ t ∎
  where
  open ≡-Reasoning
  clear-vb : vb + (- ₁) * vb ≡ ₀
  clear-vb = Eq.trans (Eq.cong (vb +_) (-1*x≈-x vb)) (+-inverseʳ vb)
  clear-x0 : - (- (₀ + ₀ * vb)) ≡ ₀
  clear-x0 = Eq.trans (Eq.cong (λ z → - (- z)) (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ vb)) (+-identityʳ ₀))) (-‿involutive ₀)
lemma-bbox (₁₊ va' , vb) t = begin
  act (Ex • CX'^ (₁₊ va') • H ↑ • S^ (- vb * a⁻¹) ↑) (pZ ∷ (₁₊ va' , vb) ∷ t)
    ≡⟨ Eq.cong (λ z → act (Ex • CX'^ (₁₊ va') • H ↑) z) (lemma-act-↑ (S^ (- vb * a⁻¹)) pZ ((₁₊ va' , vb) ∷ t)) ⟩
  act (Ex • CX'^ (₁₊ va') • H ↑) (pZ ∷ act (S^ (- vb * a⁻¹)) ((₁₊ va' , vb) ∷ t))
    ≡⟨ Eq.cong (λ z → act (Ex • CX'^ (₁₊ va') • H ↑) (pZ ∷ z)) (act-S^ (- vb * a⁻¹) (₁₊ va') vb t) ⟩
  act (Ex • CX'^ (₁₊ va') • H ↑) (pZ ∷ (₁₊ va' , vb + (₁₊ va') * (- vb * a⁻¹)) ∷ t)
    ≡⟨ Eq.cong (λ z → act (Ex • CX'^ (₁₊ va') • H ↑) (pZ ∷ (₁₊ va' , z) ∷ t)) clear-top ⟩
  act (Ex • CX'^ (₁₊ va') • H ↑) (pZ ∷ (₁₊ va' , ₀) ∷ t)
    ≡⟨ Eq.cong (act (Ex • CX'^ (₁₊ va'))) (lemma-act-↑ H pZ ((₁₊ va' , ₀) ∷ t)) ⟩
  act (Ex • CX'^ (₁₊ va')) (pZ ∷ (- ₀ , ₁₊ va') ∷ t)
    ≡⟨ Eq.cong (λ z → act (Ex • CX'^ (₁₊ va')) (pZ ∷ (z , ₁₊ va') ∷ t)) -0#≈0# ⟩
  act (Ex • CX'^ (₁₊ va')) (pZ ∷ (₀ , ₁₊ va') ∷ t)
    ≡⟨ Eq.cong (act Ex) (act-CX'^ (₁₊ va') ₀ ₁ ₀ (₁₊ va') t) ⟩
  act Ex ((- (- (₀ + ₀ * (₁₊ va'))) , - (- ₁)) ∷ (₀ , (₁₊ va') + (- ₁) * (₁₊ va')) ∷ t)
    ≡⟨ act-Ex (- (- (₀ + ₀ * (₁₊ va')))) (- (- ₁)) ₀ ((₁₊ va') + (- ₁) * (₁₊ va')) t ⟩
  (₀ , (₁₊ va') + (- ₁) * (₁₊ va')) ∷ (- (- (₀ + ₀ * (₁₊ va'))) , - (- ₁)) ∷ t
    ≡⟨ Eq.cong₂ (λ u w → (₀ , u) ∷ w ∷ t) clear-vb (≡×≡⇒≡ (clear-x0 , -‿involutive ₁)) ⟩
  pI ∷ pZ ∷ t ∎
  where
  open ≡-Reasoning
  a⁻¹ = ((₁₊ va' , λ ()) ⁻¹) .proj₁
  -- vb + (₁₊va')·(-vb·a⁻¹) = vb + (-vb)·((₁₊va')·a⁻¹) = vb + (-vb) = 0.
  clear-top : vb + (₁₊ va') * (- vb * a⁻¹) ≡ ₀
  clear-top = begin
    vb + (₁₊ va') * (- vb * a⁻¹)   ≡⟨ Eq.cong (vb +_) (Eq.sym (*-assoc (₁₊ va') (- vb) a⁻¹)) ⟩
    vb + (₁₊ va') * (- vb) * a⁻¹   ≡⟨ Eq.cong (λ z → vb + z * a⁻¹) (*-comm (₁₊ va') (- vb)) ⟩
    vb + (- vb) * (₁₊ va') * a⁻¹   ≡⟨ Eq.cong (vb +_) (*-assoc (- vb) (₁₊ va') a⁻¹) ⟩
    vb + (- vb) * ((₁₊ va') * a⁻¹) ≡⟨ Eq.cong (λ z → vb + (- vb) * z) (lemma-⁻¹ʳ (₁₊ va') {{nztoℕ {y = ₁₊ va'} {neq0 = λ ()}}}) ⟩
    vb + (- vb) * ₁               ≡⟨ Eq.cong (vb +_) (*-identityʳ (- vb)) ⟩
    vb + (- vb)                   ≡⟨ +-inverseʳ vb ⟩
    ₀ ∎
  clear-vb : (₁₊ va') + (- ₁) * (₁₊ va') ≡ ₀
  clear-vb = Eq.trans (Eq.cong ((₁₊ va') +_) (-1*x≈-x (₁₊ va'))) (+-inverseʳ (₁₊ va'))
  clear-x0 : - (- (₀ + ₀ * (₁₊ va'))) ≡ ₀
  clear-x0 = Eq.trans (Eq.cong (λ z → - (- z)) (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (₁₊ va'))) (+-identityʳ ₀))) (-‿involutive ₀)

------------------------------------------------------------------------
-- The b-vector clears the whole row:  act [ ps ]ᵛᵇ (pZ ∷ ps) = pZₙ.

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (pZₙ)

lemma-bboxes : ∀ (ps : Pauli n) → act [ ps ]ᵛᵇ (pZ ∷ ps) ≡ pZₙ
lemma-bboxes {0}    []       = Eq.refl
lemma-bboxes {₁₊ n} (b ∷ vb) = begin
  act ([ vb ]ᵛᵇ ↑ • [ b ]ᵇ) (pZ ∷ b ∷ vb)
    ≡⟨ Eq.cong (act ([ vb ]ᵛᵇ ↑)) (lemma-bbox b vb) ⟩
  act ([ vb ]ᵛᵇ ↑) (pI ∷ pZ ∷ vb)
    ≡⟨ lemma-act-↑ [ vb ]ᵛᵇ pI (pZ ∷ vb) ⟩
  pI ∷ act [ vb ]ᵛᵇ (pZ ∷ vb)
    ≡⟨ Eq.cong (pI ∷_) (lemma-bboxes vb) ⟩
  pZₙ ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- d-vector clears (pIₙ ∷ʳ pZ) to pZ₀  (uses only lemma-dbox-IZ, lemma-act-↑)

lemma-dboxes-Z : ∀ (ps : Pauli n) → act [ ps ]ᵛᵈ (pIₙ {n} ∷ʳ pZ) ≡ pZ₀
lemma-dboxes-Z {0}    []       = Eq.refl
lemma-dboxes-Z {₁₊ n} (d ∷ vd) = begin
  act ([ d ]ᵈ • [ vd ]ᵛᵈ ↑) (pI ∷ (pIₙ ∷ʳ pZ))
    ≡⟨ Eq.cong (act [ d ]ᵈ) (lemma-act-↑ [ vd ]ᵛᵈ pI (pIₙ ∷ʳ pZ)) ⟩
  act [ d ]ᵈ (pI ∷ act [ vd ]ᵛᵈ (pIₙ ∷ʳ pZ))
    ≡⟨ Eq.cong (λ z → act [ d ]ᵈ (pI ∷ z)) (lemma-dboxes-Z vd) ⟩
  act [ d ]ᵈ (pI ∷ pZ₀)
    ≡⟨ lemma-dbox-IZ d pIₙ ⟩
  pZ₀ ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- pZₙ = pIₙ ∷ʳ pZ (Z on the last wire), and the m-column moves it to pZ₀.

lemma-pZₙ : ∀ {n} → pZₙ {₁₊ n} ≡ pIₙ {n} ∷ʳ pZ
lemma-pZₙ {0}    = Eq.refl
lemma-pZₙ {₁₊ n} = Eq.cong (pI ∷_) (lemma-pZₙ {n})

lemma-mcol-Z : ∀ {n} (vd : Vec D n) (e : E) →
  act [ (vd , e) ]ᵐ (pIₙ {n} ∷ʳ pZ) ≡ pZ₀
lemma-mcol-Z {0} [] e = begin
  act [ ([] , e) ]ᵐ (pIₙ {0} ∷ʳ pZ)
    ≡⟨ act-S^ (- e) ₀ ₁ [] ⟩
  (₀ , ₁ + ₀ * (- e)) ∷ []
    ≡⟨ Eq.cong (λ z → (₀ , z) ∷ []) (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ (- e))) (+-identityʳ ₁)) ⟩
  pZ₀ ∎
  where open ≡-Reasoning
lemma-mcol-Z {₁₊ n} (d ∷ vd) e = begin
  act ([ d ]ᵈ • [ (vd , e) ]ᵐ ↑) (pI ∷ (pIₙ ∷ʳ pZ))
    ≡⟨ Eq.cong (act [ d ]ᵈ) (lemma-act-↑ [ (vd , e) ]ᵐ pI (pIₙ ∷ʳ pZ)) ⟩
  act [ d ]ᵈ (pI ∷ act [ (vd , e) ]ᵐ (pIₙ ∷ʳ pZ))
    ≡⟨ Eq.cong (λ z → act [ d ]ᵈ (pI ∷ z)) (lemma-mcol-Z vd e) ⟩
  act [ d ]ᵈ (pI ∷ pZ₀)
    ≡⟨ lemma-dbox-IZ d pIₙ ⟩
  pZ₀ ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- General single b-box action (arbitrary head p, wire1 q, param xy).

act-bbox : (xy p q : Pauli1) (ps : Pauli n) → Pauli (₂₊ n)
act-bbox (₀ , xyb) (pa , pb) (qa , qb) ps =
  (qa , qb + (- pb) * xyb) ∷ (- (- (pa + qa * xyb)) , - (- pb)) ∷ ps
act-bbox (₁₊ xa' , xyb) (pa , pb) (qa , qb) ps =
  let x = ((₁₊ xa' , λ ()) ⁻¹) .proj₁
      w = - (qb + qa * (- xyb * x))
  in (w , qa + (- pb) * (₁₊ xa')) ∷ (- (- (pa + w * (₁₊ xa'))) , - (- pb)) ∷ ps

lemma-bbox-X : ∀ (xy p q : Pauli1) (ps : Pauli n) →
  act [ xy ]ᵇ (p ∷ q ∷ ps) ≡ act-bbox xy p q ps
lemma-bbox-X (₀ , xyb) (pa , pb) (qa , qb) ps = begin
  act (Ex • CX'^ xyb) ((pa , pb) ∷ (qa , qb) ∷ ps)
    ≡⟨ Eq.cong (act Ex) (act-CX'^ xyb pa pb qa qb ps) ⟩
  act Ex ((- (- (pa + qa * xyb)) , - (- pb)) ∷ (qa , qb + (- pb) * xyb) ∷ ps)
    ≡⟨ act-Ex (- (- (pa + qa * xyb))) (- (- pb)) qa (qb + (- pb) * xyb) ps ⟩
  (qa , qb + (- pb) * xyb) ∷ (- (- (pa + qa * xyb)) , - (- pb)) ∷ ps ∎
  where open ≡-Reasoning
lemma-bbox-X (₁₊ xa' , xyb) (pa , pb) (qa , qb) ps = begin
  act (Ex • CX'^ (₁₊ xa') • H ↑ • S^ (- xyb * x) ↑) ((pa , pb) ∷ (qa , qb) ∷ ps)
    ≡⟨ Eq.cong (λ z → act (Ex • CX'^ (₁₊ xa') • H ↑) z) (lemma-act-↑ (S^ (- xyb * x)) (pa , pb) ((qa , qb) ∷ ps)) ⟩
  act (Ex • CX'^ (₁₊ xa') • H ↑) ((pa , pb) ∷ act (S^ (- xyb * x)) ((qa , qb) ∷ ps))
    ≡⟨ Eq.cong (λ z → act (Ex • CX'^ (₁₊ xa') • H ↑) ((pa , pb) ∷ z)) (act-S^ (- xyb * x) qa qb ps) ⟩
  act (Ex • CX'^ (₁₊ xa') • H ↑) ((pa , pb) ∷ (qa , qb + qa * (- xyb * x)) ∷ ps)
    ≡⟨ Eq.cong (act (Ex • CX'^ (₁₊ xa'))) (lemma-act-↑ H (pa , pb) ((qa , qb + qa * (- xyb * x)) ∷ ps)) ⟩
  act (Ex • CX'^ (₁₊ xa')) ((pa , pb) ∷ (- (qb + qa * (- xyb * x)) , qa) ∷ ps)
    ≡⟨ Eq.cong (act Ex) (act-CX'^ (₁₊ xa') pa pb (- (qb + qa * (- xyb * x))) qa ps) ⟩
  act Ex ((- (- (pa + (- (qb + qa * (- xyb * x))) * (₁₊ xa'))) , - (- pb)) ∷ (- (qb + qa * (- xyb * x)) , qa + (- pb) * (₁₊ xa')) ∷ ps)
    ≡⟨ act-Ex (- (- (pa + (- (qb + qa * (- xyb * x))) * (₁₊ xa')))) (- (- pb)) (- (qb + qa * (- xyb * x))) (qa + (- pb) * (₁₊ xa')) ps ⟩
  (- (qb + qa * (- xyb * x)) , qa + (- pb) * (₁₊ xa')) ∷ (- (- (pa + (- (qb + qa * (- xyb * x))) * (₁₊ xa'))) , - (- pb)) ∷ ps ∎
  where
  open ≡-Reasoning
  x = ((₁₊ xa' , λ ()) ⁻¹) .proj₁

------------------------------------------------------------------------
-- The general b-vector action (arbitrary head p0) via act-bboxes.

act-bbox-cons : ∀ (xy p q : Pauli1) (ps : Pauli n) →
  act-bbox xy p q ps ≡ head (act-bbox xy p q ps) ∷ head (tail (act-bbox xy p q ps)) ∷ ps
act-bbox-cons (₀ , _)     p q ps = Eq.refl
act-bbox-cons (₁₊ _ , _)  p q ps = Eq.refl

act-bboxes : (p0 : Pauli1) (ps qs : Pauli n) → Pauli (₁₊ n)
act-bboxes p0 []       []       = p0 ∷ []
act-bboxes p0 (p1 ∷ ps) (q1 ∷ qs) =
  head t ∷ act-bboxes (head (tail t)) ps qs
  where t = act-bbox p1 p0 q1 qs

lemma-bboxes-X' : ∀ (p0 : Pauli1) (ps qs : Pauli n) →
  act [ ps ]ᵛᵇ (p0 ∷ qs) ≡ act-bboxes p0 ps qs
lemma-bboxes-X' p0 []       []       = Eq.refl
lemma-bboxes-X' p0 (p1 ∷ ps) (q1 ∷ qs) = begin
  act ([ ps ]ᵛᵇ ↑ • [ p1 ]ᵇ) (p0 ∷ q1 ∷ qs)
    ≡⟨ Eq.cong (act ([ ps ]ᵛᵇ ↑)) (lemma-bbox-X p1 p0 q1 qs) ⟩
  act ([ ps ]ᵛᵇ ↑) (act-bbox p1 p0 q1 qs)
    ≡⟨ Eq.cong (act ([ ps ]ᵛᵇ ↑)) (act-bbox-cons p1 p0 q1 qs) ⟩
  act ([ ps ]ᵛᵇ ↑) (head t ∷ head (tail t) ∷ qs)
    ≡⟨ lemma-act-↑ [ ps ]ᵛᵇ (head t) (head (tail t) ∷ qs) ⟩
  head t ∷ act [ ps ]ᵛᵇ (head (tail t) ∷ qs)
    ≡⟨ Eq.cong (head t ∷_) (lemma-bboxes-X' (head (tail t)) ps qs) ⟩
  head t ∷ act-bboxes (head (tail t)) ps qs ∎
  where
  open ≡-Reasoning
  t = act-bbox p1 p0 q1 qs

------------------------------------------------------------------------
-- The m-column on the X-input:  act [ (vd , e) ]ᵐ (vd ∷ʳ (₁ , e)) ≡ pX₀
-- (moves the X on the last wire to the front; mirrors lemma-mcol-Z).

lemma-mcol-X : ∀ {n} (vd : Vec D n) (e : E) →
  act [ (vd , e) ]ᵐ (vd ∷ʳ (₁ , e)) ≡ pX₀
lemma-mcol-X {0} [] e = begin
  act [ ([] , e) ]ᵐ ([] ∷ʳ (₁ , e))
    ≡⟨ act-S^ (- e) ₁ e [] ⟩
  (₁ , e + ₁ * (- e)) ∷ []
    ≡⟨ Eq.cong (λ z → (₁ , z) ∷ []) (Eq.trans (Eq.cong (e +_) (*-identityˡ (- e))) (+-inverseʳ e)) ⟩
  pX₀ ∎
  where open ≡-Reasoning
lemma-mcol-X {₁₊ n} (d ∷ vd) e = begin
  act ([ d ]ᵈ • [ (vd , e) ]ᵐ ↑) (d ∷ (vd ∷ʳ (₁ , e)))
    ≡⟨ Eq.cong (act [ d ]ᵈ) (lemma-act-↑ [ (vd , e) ]ᵐ d (vd ∷ʳ (₁ , e))) ⟩
  act [ d ]ᵈ (d ∷ act [ (vd , e) ]ᵐ (vd ∷ʳ (₁ , e)))
    ≡⟨ Eq.cong (λ z → act [ d ]ᵈ (d ∷ z)) (lemma-mcol-X vd e) ⟩
  act [ d ]ᵈ (d ∷ pX₀)
    ≡⟨ lemma-dbox d pIₙ ⟩
  pX₀ ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Shape of the general b-vector output on an arbitrary head (a , e0):
-- its last wire keeps b-component e0 and accumulates a + sform ps qs.

thread-eq : ∀ (xy p q : Pauli1) (ps : Pauli n) →
  head (tail (act-bbox xy p q ps)) ≡ (proj₁ p + sform1 xy q , proj₂ p)
thread-eq (₀ , xyb) (pa , pb) (qa , qb) ps = ≡×≡⇒≡ (a-eq , -‿involutive pb)
  where
  open ≡-Reasoning
  sform-simp : sform1 (₀ , xyb) (qa , qb) ≡ qa * xyb
  sform-simp = Eq.trans (Eq.cong (_+ qa * xyb) (Eq.trans (Eq.cong (_* qb) -0#≈0#) (*-zeroˡ qb))) (+-identityˡ (qa * xyb))
  a-eq : - (- (pa + qa * xyb)) ≡ pa + sform1 (₀ , xyb) (qa , qb)
  a-eq = Eq.trans (-‿involutive (pa + qa * xyb)) (Eq.cong (pa +_) (Eq.sym sform-simp))
thread-eq (₁₊ xa' , xyb) (pa , pb) (qa , qb) ps = ≡×≡⇒≡ (a-eq , -‿involutive pb)
  where
  open ≡-Reasoning
  x = ((₁₊ xa' , λ ()) ⁻¹) .proj₁
  w = - (qb + qa * (- xyb * x))
  reduce-c : qa * (- xyb * x) * (₁₊ xa') ≡ - (qa * xyb)
  reduce-c = begin
    qa * (- xyb * x) * (₁₊ xa')       ≡⟨ *-assoc qa (- xyb * x) (₁₊ xa') ⟩
    qa * ((- xyb * x) * (₁₊ xa'))     ≡⟨ Eq.cong (qa *_) (*-assoc (- xyb) x (₁₊ xa')) ⟩
    qa * ((- xyb) * (x * (₁₊ xa')))   ≡⟨ Eq.cong (λ z → qa * ((- xyb) * z)) (Eq.trans (*-comm x (₁₊ xa')) (lemma-⁻¹ʳ (₁₊ xa') {{nztoℕ {y = ₁₊ xa'} {neq0 = λ ()}}})) ⟩
    qa * ((- xyb) * ₁)                ≡⟨ Eq.cong (qa *_) (*-identityʳ (- xyb)) ⟩
    qa * (- xyb)                      ≡⟨ Eq.trans (*-comm qa (- xyb)) (Eq.trans (Eq.sym (-‿distribˡ-* xyb qa)) (Eq.cong -_ (*-comm xyb qa))) ⟩
    - (qa * xyb) ∎
  first-eq : w * (₁₊ xa') ≡ sform1 (₁₊ xa' , xyb) (qa , qb)
  first-eq = begin
    w * (₁₊ xa')
      ≡⟨ Eq.sym (-‿distribˡ-* (qb + qa * (- xyb * x)) (₁₊ xa')) ⟩
    - ((qb + qa * (- xyb * x)) * (₁₊ xa'))
      ≡⟨ Eq.cong -_ (*-distribʳ-+ (₁₊ xa') qb (qa * (- xyb * x))) ⟩
    - (qb * (₁₊ xa') + qa * (- xyb * x) * (₁₊ xa'))
      ≡⟨ Eq.cong (λ z → - (qb * (₁₊ xa') + z)) reduce-c ⟩
    - (qb * (₁₊ xa') + (- (qa * xyb)))
      ≡⟨ Eq.trans (Eq.sym (-‿+-comm (qb * (₁₊ xa')) (- (qa * xyb)))) (Eq.cong (- (qb * (₁₊ xa')) +_) (-‿involutive (qa * xyb))) ⟩
    - (qb * (₁₊ xa')) + qa * xyb
      ≡⟨ Eq.cong (_+ qa * xyb) (Eq.trans (Eq.cong -_ (*-comm qb (₁₊ xa'))) (-‿distribˡ-* (₁₊ xa') qb)) ⟩
    (- (₁₊ xa')) * qb + qa * xyb ∎
  a-eq : - (- (pa + w * (₁₊ xa'))) ≡ pa + sform1 (₁₊ xa' , xyb) (qa , qb)
  a-eq = Eq.trans (-‿involutive (pa + w * (₁₊ xa'))) (Eq.cong (pa +_) first-eq)

lemma-act-bboxes-shape : ∀ (a e0 : ℤ ₚ) (ps qs : Pauli n) →
  ∃ λ (vd : Vec D n) → act-bboxes (a , e0) ps qs ≡ vd ∷ʳ (a + sform ps qs , e0)
lemma-act-bboxes-shape a e0 [] [] =
  [] , Eq.cong (λ z → (z , e0) ∷ []) (Eq.sym (+-identityʳ a))
lemma-act-bboxes-shape a e0 (p1 ∷ ps) (q1 ∷ qs) =
  (head t ∷ vd') , (begin
    head t ∷ act-bboxes (head (tail t)) ps qs
      ≡⟨ Eq.cong (λ h → head t ∷ act-bboxes h ps qs) (thread-eq p1 (a , e0) q1 qs) ⟩
    head t ∷ act-bboxes (a + sform1 p1 q1 , e0) ps qs
      ≡⟨ Eq.cong (head t ∷_) shape-rest ⟩
    head t ∷ (vd' ∷ʳ ((a + sform1 p1 q1) + sform ps qs , e0))
      ≡⟨ Eq.cong (λ z → head t ∷ (vd' ∷ʳ (z , e0))) (+-assoc a (sform1 p1 q1) (sform ps qs)) ⟩
    (head t ∷ vd') ∷ʳ (a + (sform1 p1 q1 + sform ps qs) , e0) ∎)
  where
  open ≡-Reasoning
  t = act-bbox p1 (a , e0) q1 qs
  rest = lemma-act-bboxes-shape (a + sform1 p1 q1) e0 ps qs
  vd' = proj₁ rest
  shape-rest = proj₂ rest
