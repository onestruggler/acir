------------------------------------------------------------------------
-- Presentations of groups
--
-- The lemma-lm-head-inj width induction for the plain gate set: the
-- inj₂ spine runs at ALL widths ≥ 2 (the ML 2 inj₂ side is covered by
-- the same argument, so no cosets2 base is needed).  Everything is
-- proved here
-- except the ML' branch facts, which are module parameters of
-- `Induction` (so this file stays --safe while they are ground
-- separately):
--   • inj₁-head-inj / inj₁≁inj₂ : the ML' branch at width ₂₊.
-- The width-1 base is lemma-nf1-head-inj (NF1HeadInj, proved).
--
-- Infrastructure proved here: the CZ-power action closed form
-- (act-CZ^), linear actions fix the identity Pauli (act-pIₙ), and the
-- D-box head laws (dbox-pZ-head / dbox-pX-head): prefixing pZ / pX
-- reads off the D box's components as head shifts.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+ ; zero ; suc)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.LMHeadInj
  (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using (Vec ; _∷_ ; [] ; head ; tail)
open import Function using (_∋_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ;
               module ≡-Reasoning)
open ≡-Reasoning

open import Notations
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pZ ; pX ; pIₙ ; _+₁_)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (S^ ; CZ^ ; S ; H ; CZ ; Ex ; Circuit ; Gen ;
  gate₁ ; gate₂ ; _↥ ; _↑ ; H-gate ; S-gate ; CZ-gate)
open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; sc ; sc-toℕ ; sc-suc ; act-S^ ; act-H ; act-HS^ ; act-M ; act-XM ;
         act-Ex)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (A ; B ; D ; E ; M ; L' ; ML ; ML' ;
         [_]ᵐˡ ; [_]ᵈ ; [_]ᵃ ; [_]ᵇ ; [_]ᵐ ; [_]ᵛᵇ)
open import Examples.Groups.Symplectic.Normalization.NF1HeadInj p-2 p-prime
  using (lemma-nf1-head-inj ; A-≡ ; *-cancelˡ-nz)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Ring helpers

neg-inj : ∀ (a b : ℤ ₚ) → - a ≡ - b → a ≡ b
neg-inj a b h = begin
  a     ≡⟨ sym (-‿involutive a) ⟩
  - - a ≡⟨ cong -_ h ⟩
  - - b ≡⟨ -‿involutive b ⟩
  b     ∎

-₀≡₀ : _≡_ {A = ℤ ₚ} (- ₀) ₀
-₀≡₀ = trans (sym (+-identityʳ (- z))) (+-inverseˡ z)
  where
  z : ℤ ₚ
  z = ₀

negneg : ∀ (x y : ℤ ₚ) → (- x) * (- y) ≡ x * y
negneg x y = begin
  (- x) * (- y) ≡⟨ sym (-‿distribˡ-* x (- y)) ⟩
  - (x * (- y)) ≡⟨ cong -_ (sym (-‿distribʳ-* x y)) ⟩
  - - (x * y)   ≡⟨ -‿involutive (x * y) ⟩
  x * y         ∎

+-cancelʳ' : ∀ (c a b : ℤ ₚ) → a + c ≡ b + c → a ≡ b
+-cancelʳ' c a b eq = begin
  a             ≡⟨ sym (+-identityʳ a) ⟩
  a + ₀         ≡⟨ cong (a +_) (sym (+-inverseʳ c)) ⟩
  a + (c + - c) ≡⟨ sym (+-assoc a c (- c)) ⟩
  (a + c) + - c ≡⟨ cong (_+ - c) eq ⟩
  (b + c) + - c ≡⟨ +-assoc b c (- c) ⟩
  b + (c + - c) ≡⟨ cong (b +_) (+-inverseʳ c) ⟩
  b + ₀         ≡⟨ +-identityʳ b ⟩
  b             ∎

+₁-cancelʳ : ∀ (x y z : Pauli1) → x +₁ z ≡ y +₁ z → x ≡ y
+₁-cancelʳ (x1 , x2) (y1 , y2) (z1 , z2) eq = ≡×≡⇒≡
  ( +-cancelʳ' z1 x1 y1 (cong proj₁ eq)
  , +-cancelʳ' z2 x2 y2 (cong proj₂ eq) )

------------------------------------------------------------------------
-- The CZ-power action closed form (mirror of BoxAction.act-S^ℕ)

act-CZ^ℕ : ∀ (m : ℕ) (a b c d : ℤ ₚ) (t : Pauli n) →
  act (CZ ^ m) ((a , b) ∷ (c , d) ∷ t) ≡
    (a , b + c * sc m) ∷ (c , d + a * sc m) ∷ t
act-CZ^ℕ zero a b c d t = cong₂ (λ y z → (a , y) ∷ (c , z) ∷ t)
  (trans (sym (+-identityʳ b)) (cong (b +_) (sym (*-zeroʳ c))))
  (trans (sym (+-identityʳ d)) (cong (d +_) (sym (*-zeroʳ a))))
act-CZ^ℕ 1 a b c d t = cong₂ (λ y z → (a , y) ∷ (c , z) ∷ t)
  (cong (b +_) (sym (*-identityʳ c)))
  (cong (d +_) (sym (*-identityʳ a)))
act-CZ^ℕ (2+ m) a b c d t = begin
  act (CZ • CZ ^ ₁₊ m) ((a , b) ∷ (c , d) ∷ t)
    ≡⟨ cong (act CZ) (act-CZ^ℕ (₁₊ m) a b c d t) ⟩
  act CZ ((a , b + c * sc (₁₊ m)) ∷ (c , d + a * sc (₁₊ m)) ∷ t)
    ≡⟨ cong₂ (λ y z → (a , y) ∷ (c , z) ∷ t) (step c b) (step a d) ⟩
  (a , b + c * sc (2+ m)) ∷ (c , d + a * sc (2+ m)) ∷ t ∎
  where
  step : ∀ (u v : ℤ ₚ) → (v + u * sc (₁₊ m)) + u ≡ v + u * sc (2+ m)
  step u v = begin
    (v + u * sc (₁₊ m)) + u          ≡⟨ +-assoc v (u * sc (₁₊ m)) u ⟩
    v + (u * sc (₁₊ m) + u)          ≡⟨ cong (v +_) (+-comm (u * sc (₁₊ m)) u) ⟩
    v + (u + u * sc (₁₊ m))          ≡⟨ cong (λ z → v + (z + u * sc (₁₊ m))) (sym (*-identityʳ u)) ⟩
    v + (u * ₁ + u * sc (₁₊ m))      ≡⟨ cong (v +_) (sym (*-distribˡ-+ u ₁ (sc (₁₊ m)))) ⟩
    v + u * (₁ + sc (₁₊ m))          ≡⟨ cong (λ z → v + u * z) (sym (sc-suc (₁₊ m))) ⟩
    v + u * sc (2+ m) ∎

act-CZ^ : ∀ (κ : ℤ ₚ) (a b c d : ℤ ₚ) (t : Pauli n) →
  act (CZ^ κ) ((a , b) ∷ (c , d) ∷ t) ≡
    (a , b + c * κ) ∷ (c , d + a * κ) ∷ t
act-CZ^ κ a b c d t = trans (act-CZ^ℕ (toℕ κ) a b c d t)
  (cong (λ z → (a , b + c * z) ∷ (c , d + a * z) ∷ t) (sc-toℕ κ))

------------------------------------------------------------------------
-- Linear actions fix the identity Pauli

act-pIₙ : ∀ (w : Circuit n) → act w (pIₙ {n}) ≡ pIₙ
act-pIₙ [ gate₁ H-gate ]ʷ =
  cong (λ z → (z , ₀) ∷ pIₙ) -₀≡₀
act-pIₙ [ gate₁ S-gate ]ʷ =
  cong (λ z → (₀ , z) ∷ pIₙ) (+-identityʳ ₀)
act-pIₙ [ gate₂ CZ-gate ]ʷ =
  cong₂ (λ y z → (₀ , y) ∷ (₀ , z) ∷ pIₙ) (+-identityʳ ₀) (+-identityʳ ₀)
act-pIₙ [ g ↥ ]ʷ = cong ((₀ , ₀) ∷_) (act-pIₙ [ g ]ʷ)
act-pIₙ ε = refl
act-pIₙ (w • v) = trans (cong (act w) (act-pIₙ v)) (act-pIₙ w)

------------------------------------------------------------------------
-- Lifting acts on the tail only (same proof as NF-Inj.lemma-act-↑)

lemma-act-↑ : ∀ (w : Circuit n) p ps → act (w ↑) (p ∷ ps) ≡ p ∷ act w ps
lemma-act-↑ [ g ]ʷ  p ps = refl
lemma-act-↑ ε       p ps = refl
lemma-act-↑ (w • v) p ps =
  trans (cong (act (w ↑)) (lemma-act-↑ v p ps))
        (lemma-act-↑ w p (act v ps))

lemma-aux-vec : ∀ {A : Set} n (v : Vec A (₁₊ n)) → head v ∷ tail v ≡ v
lemma-aux-vec ₀      (x ∷ v) = refl
lemma-aux-vec (₁₊ n) (x ∷ v) = refl

------------------------------------------------------------------------
-- The D-box head laws
--
-- [ d ]ᵈ = Ex • CZ^ (- b)                        (d = (₀ , b))
--        = Ex • CZ^ (- a) • H • S^ (- b * a⁻¹)   (d = (a , b), a ≠ ₀)
--
-- Prefixing pZ (resp. pX) shifts the head by (₀ , d .proj₁)
-- (resp. (₀ , - d .proj₂)).

dbox-pZ-head : ∀ (d : D) (q : Pauli1) (t : Pauli n) →
  head (act ([_]ᵈ {n} d) (pZ ∷ q ∷ t)) ≡ q +₁ (₀ , d .proj₁)
dbox-pZ-head (₀ , b) (c , e) t = trans
  (cong head
    (trans (cong (act Ex) (act-CZ^ (- b) ₀ ₁ c e t))
           (act-Ex ₀ (₁ + c * (- b)) c (e + ₀ * (- b)) t)))
  (≡×≡⇒≡ ( sym (+-identityʳ c)
         , cong (e +_) (*-zeroˡ (- b)) ))
dbox-pZ-head (₁₊ a' , b) (c , e) t = trans
  (cong head
    (trans (cong (λ v → act Ex (act (CZ^ (- ₁₊ a')) (act H v)))
             (act-S^ k' ₀ ₁ ((c , e) ∷ t)))
    (trans (cong (act Ex)
             (act-CZ^ (- ₁₊ a') (- (₁ + ₀ * k')) ₀ c e t))
           (act-Ex (- (₁ + ₀ * k')) (₀ + c * (- ₁₊ a'))
                   c (e + (- (₁ + ₀ * k')) * (- ₁₊ a')) t))))
  (≡×≡⇒≡ ( sym (+-identityʳ c)
         , cong (e +_) snd-eq ))
  where
  k' = - b * (((₁₊ a' , λ ()) ⁻¹) .proj₁)
  s1 : ₁ + ₀ * k' ≡ ₁
  s1 = trans (cong (₁ +_) (*-zeroˡ k')) (+-identityʳ ₁)
  snd-eq : (- (₁ + ₀ * k')) * (- ₁₊ a') ≡ ₁₊ a'
  snd-eq = trans (cong (λ z → (- z) * (- ₁₊ a')) s1)
    (trans (negneg ₁ (₁₊ a')) (*-identityˡ (₁₊ a')))

dbox-pX-head : ∀ (d : D) (q : Pauli1) (t : Pauli n) →
  head (act ([_]ᵈ {n} d) (pX ∷ q ∷ t)) ≡ q +₁ (₀ , - (d .proj₂))
dbox-pX-head (₀ , b) (c , e) t = trans
  (cong head
    (trans (cong (act Ex) (act-CZ^ (- b) ₁ ₀ c e t))
           (act-Ex ₁ (₀ + c * (- b)) c (e + ₁ * (- b)) t)))
  (≡×≡⇒≡ ( sym (+-identityʳ c)
         , cong (e +_) (*-identityˡ (- b)) ))
dbox-pX-head (₁₊ a' , b) (c , e) t = trans
  (cong head
    (trans (cong (λ v → act Ex (act (CZ^ (- ₁₊ a')) (act H v)))
             (act-S^ k' ₁ ₀ ((c , e) ∷ t)))
    (trans (cong (act Ex)
             (act-CZ^ (- ₁₊ a') (- (₀ + ₁ * k')) ₁ c e t))
           (act-Ex (- (₀ + ₁ * k')) (₁ + c * (- ₁₊ a'))
                   c (e + (- (₀ + ₁ * k')) * (- ₁₊ a')) t))))
  (≡×≡⇒≡ ( sym (+-identityʳ c)
         , cong (e +_) snd-eq ))
  where
  a⁻¹ = ((₁₊ a' , λ ()) ⁻¹) .proj₁
  k' = - b * a⁻¹
  s1 : ₀ + ₁ * k' ≡ k'
  s1 = trans (+-identityˡ (₁ * k')) (*-identityˡ k')
  snd-eq : (- (₀ + ₁ * k')) * (- ₁₊ a') ≡ - b
  snd-eq = begin
    (- (₀ + ₁ * k')) * (- ₁₊ a')  ≡⟨ cong (λ z → (- z) * (- ₁₊ a')) s1 ⟩
    (- k') * (- ₁₊ a')            ≡⟨ negneg k' (₁₊ a') ⟩
    k' * (₁₊ a')                  ≡⟨ *-assoc (- b) a⁻¹ (₁₊ a') ⟩
    - b * (a⁻¹ * ₁₊ a')           ≡⟨ cong ((- b) *_)
                                       (lemma-⁻¹ˡ (₁₊ a')
                                         {{nztoℕ {y = ₁₊ a'} {neq0 = λ ()}}}) ⟩
    - b * ₁                       ≡⟨ *-identityʳ (- b) ⟩
    - b ∎

------------------------------------------------------------------------
-- The head's a-component under a D box is the incoming wire-1
-- a-component: the H / S^ letters act on wire 0, CZ powers preserve
-- a-components, and the final Ex swaps wire 1 down.  This is the
-- inj₂-branch invariant behind the inj₁ ≁ inj₂ separation.

dbox-head-fst : ∀ (d : D) (x z c e : ℤ ₚ) (t : Pauli n) →
  head (act ([_]ᵈ {n} d) ((x , z) ∷ (c , e) ∷ t)) .proj₁ ≡ c
dbox-head-fst (₀ , b) x z c e t = cong (λ v → head v .proj₁)
  (trans (cong (act Ex) (act-CZ^ (- b) x z c e t))
         (act-Ex x (z + c * (- b)) c (e + x * (- b)) t))
dbox-head-fst (₁₊ a' , b) x z c e t = cong (λ v → head v .proj₁)
  (trans (cong (λ v → act Ex (act (CZ^ (- ₁₊ a')) (act H v)))
           (act-S^ k' x z ((c , e) ∷ t)))
  (trans (cong (act Ex)
           (act-CZ^ (- ₁₊ a') (- (z + x * k')) x c e t))
         (act-Ex (- (z + x * k')) (x + c * (- ₁₊ a'))
                 c (e + (- (z + x * k')) * (- ₁₊ a')) t)))
  where
  k' = - b * (((₁₊ a' , λ ()) ⁻¹) .proj₁)

-- The inj₂ unfolding, and the resulting zero invariant: an inj₂ coset
-- word, applied to any input whose tail is the identity Pauli, returns
-- a head with zero a-component (the tail is fixed by the inner action,
-- so wire 1 feeds ₀ into dbox-head-fst).

inj₂-unfold : ∀ {n} (d : D) (lm' : ML (₁₊ n)) (p₀ : Pauli1)
  (ps' : Pauli (₁₊ n)) →
  act [ ML (₂₊ n) ∋ inj₂ (d , lm') ]ᵐˡ (p₀ ∷ ps') ≡
    act ([_]ᵈ {n} d) (p₀ ∷ act [ lm' ]ᵐˡ ps')
inj₂-unfold {n} d lm' p₀ ps' =
  cong (act ([_]ᵈ {n} d)) (lemma-act-↑ [ lm' ]ᵐˡ p₀ ps')

inj₂-head-fst-0 : ∀ {n} (d : D) (lm' : ML (₁₊ n)) (p₀ : Pauli1) →
  head (act [ ML (₂₊ n) ∋ inj₂ (d , lm') ]ᵐˡ (p₀ ∷ pIₙ {₁₊ n})) .proj₁ ≡ ₀
inj₂-head-fst-0 {n} d lm' p₀ =
  trans (cong (λ v → head v .proj₁)
          (inj₂-unfold d lm' p₀ (pIₙ {₁₊ n})))
  (trans (cong (λ v → head (act ([_]ᵈ {n} d) (p₀ ∷ v)) .proj₁)
          (act-pIₙ [ lm' ]ᵐˡ))
         (dbox-head-fst d (p₀ .proj₁) (p₀ .proj₂) ₀ ₀ (pIₙ {n})))

------------------------------------------------------------------------
-- The A-box head transform: [ a ]ᵃ is a word of wire-0 gates, so it
-- acts on the head alone, by the closed form aHd.  At a shape-chosen
-- input (pX for the (₀,·) shape, pZ otherwise) the transformed head
-- has NONZERO a-component — the inj₁ side of the separation.

aHd : A → Pauli1 → Pauli1
aHd ((₀ , ₀) , pr) q = ⊥-elim (pr refl)
aHd ((₀ , ₁₊ b') , pr) (q₁ , q₂) =
  (q₁ * (((₁₊ b' , λ ()) ⁻¹ ⁻¹) .proj₁) , q₂ * (((₁₊ b' , λ ()) ⁻¹) .proj₁))
aHd ((₁₊ a' , b) , pr) (q₁ , q₂) =
  ( (- (q₂ + q₁ * (- b * xI))) * (((₁₊ a' , λ ()) ⁻¹ ⁻¹) .proj₁)
  , q₁ * xI )
  where xI = ((₁₊ a' , λ ()) ⁻¹) .proj₁

abox-hd : ∀ (a : A) (q : Pauli1) (t : Pauli n) →
  act ([_]ᵃ {n} a) (q ∷ t) ≡ aHd a q ∷ t
abox-hd ((₀ , ₀) , pr) q t = ⊥-elim (pr refl)
abox-hd ((₀ , ₁₊ b') , pr) (q₁ , q₂) t =
  trans (act-XM (₁₊ b' , λ ()) ((q₁ , q₂) ∷ t))
        (act-M ((₁₊ b' , λ ()) ⁻¹) q₁ q₂ t)
abox-hd ((₁₊ a' , b) , pr) (q₁ , q₂) t =
  trans (cong (act (Symplectic.XM (₁₊ a' , λ ()))) (act-HS^ k q₁ q₂ t))
        (trans (act-XM (₁₊ a' , λ ()) ((- (q₂ + q₁ * k) , q₁) ∷ t))
               (act-M inv (- (q₂ + q₁ * k)) q₁ t))
  where
  inv = (₁₊ a' , λ ()) ⁻¹
  k   = - b * (inv .proj₁)

-- The shape-chosen probe input, and nonzeroness of the transformed
-- a-component there.
aProbe : A → Pauli1
aProbe ((₀ , _) , _)  = pX
aProbe ((₁₊ _ , _) , _) = pZ

suc≢₀' : ∀ {x : Fin (₁₊ p-2)} → _≡_ {A = ℤ ₚ} (₁₊ x) ₀ → ⊥
suc≢₀' ()

neg-suc-nz' : ∀ (x : Fin (₁₊ p-2)) → - (₁₊ x) ≡ ₀ → ⊥
neg-suc-nz' x h = suc≢₀'
  (trans (sym (-‿involutive (₁₊ x))) (trans (cong -_ h) -₀≡₀))

aProbe-fst-nz : ∀ (a : A) → aHd a (aProbe a) .proj₁ ≡ ₀ → ⊥
aProbe-fst-nz ((₀ , ₀) , pr) _ = pr refl
aProbe-fst-nz ((₀ , ₁₊ b') , pr) eq = suc≢₀' (trans (sym p1) eq)
  where
  invI = (((₁₊ b' , λ ()) ⁻¹ ⁻¹) .proj₁)
  p1 : ₁ * invI ≡ ₁₊ b'
  p1 = trans (*-identityˡ invI) (inv-involutive (₁₊ b' , λ ()))
aProbe-fst-nz ((₁₊ a' , b) , pr) eq = neg-suc-nz' a' (trans (sym q1) eq)
  where
  inv  = (₁₊ a' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  k    = - b * xI
  s1 : ₁ + ₀ * k ≡ ₁
  s1 = trans (cong (₁ +_) (*-zeroˡ k)) (+-identityʳ ₁)
  q1 : (- (₁ + ₀ * k)) * invI ≡ - (₁₊ a')
  q1 = begin
    (- (₁ + ₀ * k)) * invI ≡⟨ cong (λ z → (- z) * invI) s1 ⟩
    (- ₁) * invI           ≡⟨ sym (-‿distribˡ-* ₁ invI) ⟩
    - (₁ * invI)           ≡⟨ cong -_ (*-identityˡ invI) ⟩
    - invI                 ≡⟨ cong -_ (inv-involutive (₁₊ a' , λ ())) ⟩
    - (₁₊ a')              ∎

------------------------------------------------------------------------
-- The B-box carrier law: on an input whose wire 1 is the identity, a
-- B-box word deposits junk on wire 0 and passes the old head to wire 1
-- UNCHANGED.  (CX'^ κ = H³ • CZ^ κ • H, so first the closed form.)

act-CX'^ : ∀ (κ : ℤ ₚ) (x z c e : ℤ ₚ) (t : Pauli n) →
  act (Symplectic.CX'^ κ) ((x , z) ∷ (c , e) ∷ t) ≡
    (x + c * κ , z) ∷ (c , e + - (z * κ)) ∷ t
act-CX'^ κ x z c e t =
  trans (cong (act (H ^ 3)) (act-CZ^ κ (- z) x c e t))
        (cong₂ (λ P Q → P ∷ Q ∷ t)
          (≡×≡⇒≡ (-‿involutive (x + c * κ) , -‿involutive z))
          (cong (λ w → (c , e + w)) (sym (-‿distribˡ-* z κ))))

bJunk : B → ℤ ₚ → Pauli1
bJunk (₀ , b₂) z = (₀ , - (z * b₂))
bJunk (₁₊ c₁' , _) z = (₀ , - (z * ₁₊ c₁'))

bbox-carrier : ∀ (b : B) (x z : ℤ ₚ) (t : Pauli n) →
  act ([_]ᵇ {n} b) ((x , z) ∷ (₀ , ₀) ∷ t) ≡ bJunk b z ∷ (x , z) ∷ t
bbox-carrier (₀ , b₂) x z t =
  trans (cong (act Ex) (act-CX'^ b₂ x z ₀ ₀ t))
  (trans (act-Ex (x + ₀ * b₂) z ₀ (₀ + - (z * b₂)) t)
         (cong₂ (λ P Q → P ∷ Q ∷ t)
           (cong (₀ ,_) (+-identityˡ (- (z * b₂))))
           (cong (_, z) (trans (cong (x +_) (*-zeroˡ b₂)) (+-identityʳ x)))))
bbox-carrier (₁₊ c₁' , b₂) x z t =
  trans (cong (λ v → act Ex (act (Symplectic.CX'^ (₁₊ c₁')) (act (H ↑) v)))
          (trans (lemma-act-↑ (S^ k) (x , z) ((₀ , ₀) ∷ t))
                 (cong ((x , z) ∷_) (act-S^ k ₀ ₀ t))))
  (trans (cong (λ v → act Ex (act (Symplectic.CX'^ (₁₊ c₁')) v))
          (trans (lemma-act-↑ H (x , z) ((₀ , ₀ + ₀ * k) ∷ t))
                 (cong ((x , z) ∷_) (act-H ₀ (₀ + ₀ * k) t))))
  (trans (cong (act Ex)
          (act-CX'^ (₁₊ c₁') x z (- (₀ + ₀ * k)) ₀ t))
  (trans (act-Ex (x + (- (₀ + ₀ * k)) * ₁₊ c₁') z
                 (- (₀ + ₀ * k)) (₀ + - (z * ₁₊ c₁')) t)
         (cong₂ (λ P Q → P ∷ Q ∷ t)
           (≡×≡⇒≡ (c̃0 , +-identityˡ (- (z * ₁₊ c₁'))))
           (cong (_, z) carrier-eq)))))
  where
  k = - b₂ * (((₁₊ c₁' , λ ()) ⁻¹) .proj₁)
  z00 : ₀ + ₀ * k ≡ ₀
  z00 = trans (cong (₀ +_) (*-zeroˡ k)) (+-identityʳ ₀)
  c̃0 : - (₀ + ₀ * k) ≡ ₀
  c̃0 = trans (cong -_ z00) -₀≡₀
  carrier-eq : x + (- (₀ + ₀ * k)) * ₁₊ c₁' ≡ x
  carrier-eq = trans (cong (λ w → x + w * ₁₊ c₁') c̃0)
    (trans (cong (x +_) (*-zeroˡ (₁₊ c₁'))) (+-identityʳ x))

------------------------------------------------------------------------
-- The M-column/B-column composite fixes the head's a-component: the
-- carrier climbs the B staircase unchanged, and the D staircase hands
-- a-components straight down (dbox-head-fst), meeting in the middle.

mb-fst : ∀ {k} (dv : Vec D k) (e : E) (bv : Vec B k) (q : Pauli1) →
  head (act ([ (dv , e) ]ᵐ • [ bv ]ᵛᵇ) (q ∷ pIₙ {k})) .proj₁ ≡ q .proj₁
mb-fst [] e [] (q₁ , q₂) =
  cong (λ v → head v .proj₁) (act-S^ (- e) q₁ q₂ [])
mb-fst {₁₊ k'} (d₁ ∷ dv') e (b₁ ∷ bv') q@(q₁ , q₂) =
  trans (cong (λ v → head v .proj₁) V)
  (trans (cong (λ v → head (act ([_]ᵈ {k'} d₁) (bJunk b₁ q₂ ∷ v)) .proj₁)
           (sym (lemma-aux-vec k' inner)))
  (trans (dbox-head-fst d₁ (bJunk b₁ q₂ .proj₁) (bJunk b₁ q₂ .proj₂)
           (head inner .proj₁) (head inner .proj₂) (tail inner))
         (mb-fst dv' e bv' q)))
  where
  inner = act ([ (dv' , e) ]ᵐ • [ bv' ]ᵛᵇ) (q ∷ pIₙ {k'})
  V : act ([ (d₁ ∷ dv' , e) ]ᵐ • [ b₁ ∷ bv' ]ᵛᵇ) (q ∷ pIₙ {₁₊ k'}) ≡
      act ([_]ᵈ {k'} d₁) (bJunk b₁ q₂ ∷ inner)
  V = trans (cong (λ v → act ([_]ᵈ {k'} d₁)
               (act ([ (dv' , e) ]ᵐ ↑) (act ([ bv' ]ᵛᵇ ↑) v)))
          (bbox-carrier b₁ q₁ q₂ (pIₙ {k'})))
      (trans (cong (λ v → act ([_]ᵈ {k'} d₁) (act ([ (dv' , e) ]ᵐ ↑) v))
          (lemma-act-↑ [ bv' ]ᵛᵇ (bJunk b₁ q₂) ((q₁ , q₂) ∷ pIₙ {k'})))
        (cong (act ([_]ᵈ {k'} d₁))
          (lemma-act-↑ [ (dv' , e) ]ᵐ (bJunk b₁ q₂)
            (act [ bv' ]ᵛᵇ ((q₁ , q₂) ∷ pIₙ {k'})))))

------------------------------------------------------------------------
-- The assembled separation: at the probe input, an inj₁ word's head
-- a-component is the A-box transform's (nonzero), an inj₂ word's is ₀.

inj₁-fst : ∀ {n} (dv : Vec D (₁₊ n)) (e : E) (bv : Vec B (₁₊ n)) (a : A)
  (p₀ : Pauli1) →
  head (act [ ML (₂₊ n) ∋ inj₁ ((dv , e) , (bv , a)) ]ᵐˡ
    (p₀ ∷ pIₙ {₁₊ n})) .proj₁ ≡ aHd a p₀ .proj₁
inj₁-fst {n} dv e bv a p₀ =
  trans (cong (λ v → head v .proj₁)
          (cong (λ v → act [ (dv , e) ]ᵐ (act [ bv ]ᵛᵇ v))
            (abox-hd a p₀ (pIₙ {₁₊ n}))))
        (mb-fst dv e bv (aHd a p₀))

inj₁≁inj₂-proved : ∀ {n} (ml : ML' (₂₊ n)) (d : D) (lm' : ML (₁₊ n)) →
  (∀ (ps : Pauli (₂₊ n)) →
    head (act [ ML (₂₊ n) ∋ inj₁ ml ]ᵐˡ ps) ≡
    head (act [ ML (₂₊ n) ∋ inj₂ (d , lm') ]ᵐˡ ps)) →
  ⊥
inj₁≁inj₂-proved {n} ((dv , e) , (bv , a)) d lm' h = aProbe-fst-nz a
  (trans (sym (inj₁-fst dv e bv a (aProbe a)))
  (trans (cong proj₁ (h (aProbe a ∷ pIₙ {₁₊ n})))
         (inj₂-head-fst-0 d lm' (aProbe a))))

------------------------------------------------------------------------
-- The width induction
--
-- The two remaining base facts are module parameters; instantiating
-- them (ML 2 head-injectivity, and the ML' branch at ₃₊) yields the
-- full lemma-lm-head-inj — the sole postulate of Normalization.NF-Inj.

module Induction
  (inj₁-head-inj : ∀ {n} (ml₁ ml₂ : ML' (₂₊ n)) →
    (∀ (ps : Pauli (₂₊ n)) →
      head (act [ ML (₂₊ n) ∋ inj₁ ml₁ ]ᵐˡ ps) ≡
      head (act [ ML (₂₊ n) ∋ inj₁ ml₂ ]ᵐˡ ps)) →
    ml₁ ≡ ml₂)
  (inj₁≁inj₂ : ∀ {n} (ml : ML' (₂₊ n)) (d : D) (lm' : ML (₁₊ n)) →
    (∀ (ps : Pauli (₂₊ n)) →
      head (act [ ML (₂₊ n) ∋ inj₁ ml ]ᵐˡ ps) ≡
      head (act [ ML (₂₊ n) ∋ inj₂ (d , lm') ]ᵐˡ ps)) →
    ⊥)
  where

  lemma-lm-head-inj : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
    (∀ (ps : Pauli (₁₊ n)) →
      head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) →
    lm₁ ≡ lm₂
  lemma-lm-head-inj {₀} lm₁ lm₂ h = lemma-nf1-head-inj lm₁ lm₂ h
  lemma-lm-head-inj {₁₊ n} (inj₁ ml₁) (inj₁ ml₂) h =
    cong inj₁ (inj₁-head-inj ml₁ ml₂ h)
  lemma-lm-head-inj {₁₊ n} (inj₁ ml) (inj₂ (d , lm')) h =
    ⊥-elim (inj₁≁inj₂ ml d lm' h)
  lemma-lm-head-inj {₁₊ n} (inj₂ (d , lm')) (inj₁ ml) h =
    ⊥-elim (inj₁≁inj₂ ml d lm' (λ ps → sym (h ps)))
  lemma-lm-head-inj {₁₊ n} (inj₂ (d₁ , lm₁')) (inj₂ (d₂ , lm₂')) h =
    cong inj₂ (≡×≡⇒≡ (d-eq , lm'-eq))
    where
    -- act [inj₂(d,lm')]ᵐˡ (p ∷ ps') = act [d]ᵈ (p ∷ act [lm']ᵐˡ ps').
    unfold-act : ∀ (d : D) (lm' : ML (₁₊ n)) (p₀ : Pauli1)
      (ps' : Pauli (₁₊ n)) →
      act [ ML (₂₊ n) ∋ inj₂ (d , lm') ]ᵐˡ (p₀ ∷ ps') ≡
        act ([_]ᵈ {n} d) (p₀ ∷ act [ lm' ]ᵐˡ ps')
    unfold-act d lm' p₀ ps' =
      cong (act ([_]ᵈ {n} d)) (lemma-act-↑ [ lm' ]ᵐˡ p₀ ps')

    -- Head agreement with the tails cancelled at the identity Pauli.
    head-at-pI : ∀ (p₀ : Pauli1) →
      head (act ([_]ᵈ {n} d₁) (p₀ ∷ pIₙ {₁₊ n})) ≡
      head (act ([_]ᵈ {n} d₂) (p₀ ∷ pIₙ {₁₊ n}))
    head-at-pI p₀ = begin
      head (act ([_]ᵈ {n} d₁) (p₀ ∷ pIₙ {₁₊ n}))
        ≡⟨ cong (λ v → head (act ([_]ᵈ {n} d₁) (p₀ ∷ v)))
             (sym (act-pIₙ [ lm₁' ]ᵐˡ)) ⟩
      head (act ([_]ᵈ {n} d₁) (p₀ ∷ act [ lm₁' ]ᵐˡ (pIₙ {₁₊ n})))
        ≡⟨ cong head (sym (unfold-act d₁ lm₁' p₀ (pIₙ {₁₊ n}))) ⟩
      head (act [ ML (₂₊ n) ∋ inj₂ (d₁ , lm₁') ]ᵐˡ (p₀ ∷ pIₙ {₁₊ n}))
        ≡⟨ h (p₀ ∷ pIₙ {₁₊ n}) ⟩
      head (act [ ML (₂₊ n) ∋ inj₂ (d₂ , lm₂') ]ᵐˡ (p₀ ∷ pIₙ {₁₊ n}))
        ≡⟨ cong head (unfold-act d₂ lm₂' p₀ (pIₙ {₁₊ n})) ⟩
      head (act ([_]ᵈ {n} d₂) (p₀ ∷ act [ lm₂' ]ᵐˡ (pIₙ {₁₊ n})))
        ≡⟨ cong (λ v → head (act ([_]ᵈ {n} d₂) (p₀ ∷ v)))
             (act-pIₙ [ lm₂' ]ᵐˡ) ⟩
      head (act ([_]ᵈ {n} d₂) (p₀ ∷ pIₙ {₁₊ n})) ∎

    -- d .proj₁ via the pZ prefix at the identity.
    d-eq-fst : d₁ .proj₁ ≡ d₂ .proj₁
    d-eq-fst = +-cancelˡ-strip
      (cong proj₂
        (trans (sym (dbox-pZ-head d₁ (₀ , ₀) (pIₙ {n})))
        (trans (head-at-pI pZ)
               (dbox-pZ-head d₂ (₀ , ₀) (pIₙ {n})))))
      where
      +-cancelˡ-strip : ₀ + d₁ .proj₁ ≡ ₀ + d₂ .proj₁ →
        d₁ .proj₁ ≡ d₂ .proj₁
      +-cancelˡ-strip eq = trans (sym (+-identityˡ (d₁ .proj₁)))
        (trans eq (+-identityˡ (d₂ .proj₁)))

    -- d .proj₂ via the pX prefix at the identity.
    d-eq-snd : d₁ .proj₂ ≡ d₂ .proj₂
    d-eq-snd = neg-inj _ _ (+-cancelˡ-strip
      (cong proj₂
        (trans (sym (dbox-pX-head d₁ (₀ , ₀) (pIₙ {n})))
        (trans (head-at-pI pX)
               (dbox-pX-head d₂ (₀ , ₀) (pIₙ {n}))))))
      where
      +-cancelˡ-strip : ₀ + - (d₁ .proj₂) ≡ ₀ + - (d₂ .proj₂) →
        - (d₁ .proj₂) ≡ - (d₂ .proj₂)
      +-cancelˡ-strip eq = trans (sym (+-identityˡ (- (d₁ .proj₂))))
        (trans eq (+-identityˡ (- (d₂ .proj₂))))

    d-eq : d₁ ≡ d₂
    d-eq = ≡×≡⇒≡ (d-eq-fst , d-eq-snd)

    -- Head equality one width down, from the pZ prefix at arbitrary
    -- inputs, cancelling the d shift.
    lm'-head-eq : ∀ (ps' : Pauli (₁₊ n)) →
      head (act [ lm₁' ]ᵐˡ ps') ≡ head (act [ lm₂' ]ᵐˡ ps')
    lm'-head-eq ps' =
      let
        v₁ = act [ lm₁' ]ᵐˡ ps'
        v₂ = act [ lm₂' ]ᵐˡ ps'
        raw : head (act ([_]ᵈ {n} d₁) (pZ ∷ v₁))
            ≡ head (act ([_]ᵈ {n} d₂) (pZ ∷ v₂))
        raw = trans (cong head (sym (unfold-act d₁ lm₁' pZ ps')))
              (trans (h (pZ ∷ ps'))
                     (cong head (unfold-act d₂ lm₂' pZ ps')))
        lhs : head (act ([_]ᵈ {n} d₁) (pZ ∷ v₁))
            ≡ head v₁ +₁ (₀ , d₁ .proj₁)
        lhs = trans
          (cong (λ v → head (act ([_]ᵈ {n} d₁) (pZ ∷ v)))
            (sym (lemma-aux-vec n v₁)))
          (dbox-pZ-head d₁ (head v₁) (tail v₁))
        rhs : head (act ([_]ᵈ {n} d₂) (pZ ∷ v₂))
            ≡ head v₂ +₁ (₀ , d₂ .proj₁)
        rhs = trans
          (cong (λ v → head (act ([_]ᵈ {n} d₂) (pZ ∷ v)))
            (sym (lemma-aux-vec n v₂)))
          (dbox-pZ-head d₂ (head v₂) (tail v₂))
        combined : head v₁ +₁ (₀ , d₁ .proj₁) ≡ head v₂ +₁ (₀ , d₂ .proj₁)
        combined = trans (sym lhs) (trans raw rhs)
        combined' : head v₁ +₁ (₀ , d₁ .proj₁) ≡ head v₂ +₁ (₀ , d₁ .proj₁)
        combined' = subst
          (λ z → head v₁ +₁ (₀ , d₁ .proj₁) ≡ head v₂ +₁ (₀ , z))
          (sym d-eq-fst) combined
      in +₁-cancelʳ (head v₁) (head v₂) (₀ , d₁ .proj₁) combined'

    lm'-eq : lm₁' ≡ lm₂'
    lm'-eq = lemma-lm-head-inj lm₁' lm₂' lm'-head-eq

  -- Full-action injectivity follows from head-injectivity.
  lemma-lm-inj : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
    (∀ (ps : Pauli (₁₊ n)) → act [ lm₁ ]ᵐˡ ps ≡ act [ lm₂ ]ᵐˡ ps) →
    lm₁ ≡ lm₂
  lemma-lm-inj lm₁ lm₂ h =
    lemma-lm-head-inj lm₁ lm₂ (λ ps → cong head (h ps))

------------------------------------------------------------------------
-- Toward inj₁-head-inj: the A-box transform's a-component is the
-- uniform linear functional q ↦ q₁·y − x·q₂ (both shapes), so the two
-- probes pX / pZ read off y and −x, and the A box of an inj₁ coset is
-- determined by its head behaviour.

aHd-fst-lin : ∀ (x y : ℤ ₚ) (pr : (x , y) ≢ (₀ , ₀)) (q₁ q₂ : ℤ ₚ) →
  aHd ((x , y) , pr) (q₁ , q₂) .proj₁ ≡ q₁ * y + - (x * q₂)
aHd-fst-lin ₀ ₀ pr q₁ q₂ = ⊥-elim (pr refl)
aHd-fst-lin ₀ (₁₊ y') pr q₁ q₂ = begin
  q₁ * invI              ≡⟨ cong (q₁ *_) (inv-involutive (₁₊ y' , λ ())) ⟩
  q₁ * ₁₊ y'             ≡⟨ sym (+-identityʳ (q₁ * ₁₊ y')) ⟩
  q₁ * ₁₊ y' + ₀         ≡⟨ cong (q₁ * ₁₊ y' +_)
                              (sym (trans (cong -_ (*-zeroˡ q₂)) -₀≡₀)) ⟩
  q₁ * ₁₊ y' + - (₀ * q₂) ∎
  where
  invI = (((₁₊ y' , λ ()) ⁻¹ ⁻¹) .proj₁)
aHd-fst-lin (₁₊ x') y pr q₁ q₂ = begin
  (- (q₂ + q₁ * k)) * invI
    ≡⟨ cong ((- (q₂ + q₁ * k)) *_) ii ⟩
  (- (q₂ + q₁ * k)) * ₁₊ x'
    ≡⟨ sym (-‿distribˡ-* (q₂ + q₁ * k) (₁₊ x')) ⟩
  - ((q₂ + q₁ * k) * ₁₊ x')
    ≡⟨ cong -_ (*-distribʳ-+ (₁₊ x') q₂ (q₁ * k)) ⟩
  - (q₂ * ₁₊ x' + q₁ * k * ₁₊ x')
    ≡⟨ sym (-‿+-comm (q₂ * ₁₊ x') (q₁ * k * ₁₊ x')) ⟩
  - (q₂ * ₁₊ x') + - (q₁ * k * ₁₊ x')
    ≡⟨ cong₂ _+_ (cong -_ (*-comm q₂ (₁₊ x'))) (cong -_ kx-eq) ⟩
  - (₁₊ x' * q₂) + - (- (q₁ * y))
    ≡⟨ cong (- (₁₊ x' * q₂) +_) (-‿involutive (q₁ * y)) ⟩
  - (₁₊ x' * q₂) + q₁ * y
    ≡⟨ +-comm (- (₁₊ x' * q₂)) (q₁ * y) ⟩
  q₁ * y + - (₁₊ x' * q₂) ∎
  where
  inv  = (₁₊ x' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  k    = - y * xI
  ii : invI ≡ ₁₊ x'
  ii = inv-involutive (₁₊ x' , λ ())
  kx-eq : q₁ * k * ₁₊ x' ≡ - (q₁ * y)
  kx-eq = begin
    q₁ * (- y * xI) * ₁₊ x'   ≡⟨ cong (_* ₁₊ x') (sym (*-assoc q₁ (- y) xI)) ⟩
    q₁ * - y * xI * ₁₊ x'     ≡⟨ *-assoc (q₁ * - y) xI (₁₊ x') ⟩
    q₁ * - y * (xI * ₁₊ x')   ≡⟨ cong (q₁ * - y *_)
                                   (lemma-⁻¹ˡ (₁₊ x')
                                     {{nztoℕ {y = ₁₊ x'} {neq0 = λ ()}}}) ⟩
    q₁ * - y * ₁              ≡⟨ *-identityʳ (q₁ * - y) ⟩
    q₁ * - y                  ≡⟨ sym (-‿distribʳ-* q₁ y) ⟩
    - (q₁ * y)                ∎

aHd-pX : ∀ (x y : ℤ ₚ) (pr : (x , y) ≢ (₀ , ₀)) →
  aHd ((x , y) , pr) pX .proj₁ ≡ y
aHd-pX x y pr = trans (aHd-fst-lin x y pr ₁ ₀)
  (trans (cong₂ _+_ (*-identityˡ y)
           (trans (cong -_ (*-zeroʳ x)) -₀≡₀))
         (+-identityʳ y))

aHd-pZ : ∀ (x y : ℤ ₚ) (pr : (x , y) ≢ (₀ , ₀)) →
  aHd ((x , y) , pr) pZ .proj₁ ≡ - x
aHd-pZ x y pr = trans (aHd-fst-lin x y pr ₀ ₁)
  (trans (cong₂ _+_ (*-zeroˡ y) (cong -_ (*-identityʳ x)))
         (+-identityˡ (- x)))

-- The A box of an inj₁ coset is determined by its head behaviour.
inj₁-recover-a : ∀ {n} (dv₁ dv₂ : Vec D (₁₊ n)) (e₁ e₂ : E)
  (bv₁ bv₂ : Vec B (₁₊ n)) (a₁ a₂ : A) →
  (∀ (ps : Pauli (₂₊ n)) →
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv₁ , e₁) , (bv₁ , a₁)) ]ᵐˡ ps) ≡
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv₂ , e₂) , (bv₂ , a₂)) ]ᵐˡ ps)) →
  a₁ ≡ a₂
inj₁-recover-a {n} dv₁ dv₂ e₁ e₂ bv₁ bv₂
  ((x₁ , y₁) , pr₁) ((x₂ , y₂) , pr₂) h =
  A-≡ _ _ (≡×≡⇒≡ (x-eq , y-eq))
  where
  probe-eq : ∀ (p₀ : Pauli1) →
    aHd ((x₁ , y₁) , pr₁) p₀ .proj₁ ≡ aHd ((x₂ , y₂) , pr₂) p₀ .proj₁
  probe-eq p₀ =
    trans (sym (inj₁-fst dv₁ e₁ bv₁ ((x₁ , y₁) , pr₁) p₀))
    (trans (cong proj₁ (h (p₀ ∷ pIₙ {₁₊ n})))
           (inj₁-fst dv₂ e₂ bv₂ ((x₂ , y₂) , pr₂) p₀))
  y-eq : y₁ ≡ y₂
  y-eq = trans (sym (aHd-pX x₁ y₁ pr₁))
         (trans (probe-eq pX) (aHd-pX x₂ y₂ pr₂))
  x-eq : x₁ ≡ x₂
  x-eq = neg-inj x₁ x₂
    (trans (sym (aHd-pZ x₁ y₁ pr₁))
    (trans (probe-eq pZ) (aHd-pZ x₂ y₂ pr₂)))

------------------------------------------------------------------------
-- Toward E-recovery: the FULL head value of the M/B composite.  The
-- D-box head law with both components (dShift is the exact raw shift),
-- and the closed form mbSnd accumulating the staircase contributions.

dShift : D → ℤ ₚ → ℤ ₚ → ℤ ₚ
dShift (₀ , b) x z = x * (- b)
dShift (₁₊ a' , b) x z =
  (- (z + x * (- b * (((₁₊ a' , λ ()) ⁻¹) .proj₁)))) * (- ₁₊ a')

dbox-head-full : ∀ (d : D) (x z c e : ℤ ₚ) (t : Pauli n) →
  head (act ([_]ᵈ {n} d) ((x , z) ∷ (c , e) ∷ t)) ≡ (c , e + dShift d x z)
dbox-head-full (₀ , b) x z c e t = cong head
  (trans (cong (act Ex) (act-CZ^ (- b) x z c e t))
         (act-Ex x (z + c * (- b)) c (e + x * (- b)) t))
dbox-head-full (₁₊ a' , b) x z c e t = cong head
  (trans (cong (λ v → act Ex (act (CZ^ (- ₁₊ a')) (act H v)))
           (act-S^ k' x z ((c , e) ∷ t)))
  (trans (cong (act Ex)
           (act-CZ^ (- ₁₊ a') (- (z + x * k')) x c e t))
         (act-Ex (- (z + x * k')) (x + c * (- ₁₊ a'))
                 c (e + (- (z + x * k')) * (- ₁₊ a')) t)))
  where
  k' = - b * (((₁₊ a' , λ ()) ⁻¹) .proj₁)

mbSnd : ∀ {k} → Vec D k → E → Vec B k → Pauli1 → ℤ ₚ
mbSnd [] e [] (q₁ , q₂) = q₂ + q₁ * (- e)
mbSnd (d₁ ∷ dv') e (b₁ ∷ bv') q@(q₁ , q₂) =
  mbSnd dv' e bv' q +
    dShift d₁ (bJunk b₁ q₂ .proj₁) (bJunk b₁ q₂ .proj₂)

mb-full : ∀ {k} (dv : Vec D k) (e : E) (bv : Vec B k) (q : Pauli1) →
  head (act ([ (dv , e) ]ᵐ • [ bv ]ᵛᵇ) (q ∷ pIₙ {k})) ≡
    (q .proj₁ , mbSnd dv e bv q)
mb-full [] e [] (q₁ , q₂) = cong head (act-S^ (- e) q₁ q₂ [])
mb-full {₁₊ k'} (d₁ ∷ dv') e (b₁ ∷ bv') q@(q₁ , q₂) =
  trans (cong head V)
  (trans (cong (λ v → head (act ([_]ᵈ {k'} d₁) (bJunk b₁ q₂ ∷ v)))
           (sym (lemma-aux-vec k' inner)))
  (trans (dbox-head-full d₁ (bJunk b₁ q₂ .proj₁) (bJunk b₁ q₂ .proj₂)
           (head inner .proj₁) (head inner .proj₂) (tail inner))
         (cong (λ w → (w .proj₁ , w .proj₂ +
             dShift d₁ (bJunk b₁ q₂ .proj₁) (bJunk b₁ q₂ .proj₂)))
           (mb-full dv' e bv' q))))
  where
  inner = act ([ (dv' , e) ]ᵐ • [ bv' ]ᵛᵇ) (q ∷ pIₙ {k'})
  V : act ([ (d₁ ∷ dv' , e) ]ᵐ • [ b₁ ∷ bv' ]ᵛᵇ) (q ∷ pIₙ {₁₊ k'}) ≡
      act ([_]ᵈ {k'} d₁) (bJunk b₁ q₂ ∷ inner)
  V = trans (cong (λ v → act ([_]ᵈ {k'} d₁)
               (act ([ (dv' , e) ]ᵐ ↑) (act ([ bv' ]ᵛᵇ ↑) v)))
          (bbox-carrier b₁ q₁ q₂ (pIₙ {k'})))
      (trans (cong (λ v → act ([_]ᵈ {k'} d₁) (act ([ (dv' , e) ]ᵐ ↑) v))
          (lemma-act-↑ [ bv' ]ᵛᵇ (bJunk b₁ q₂) ((q₁ , q₂) ∷ pIₙ {k'})))
        (cong (act ([_]ᵈ {k'} d₁))
          (lemma-act-↑ [ (dv' , e) ]ᵐ (bJunk b₁ q₂)
            (act [ bv' ]ᵛᵇ ((q₁ , q₂) ∷ pIₙ {k'})))))

-- At a probe whose transformed second component is ₀ the staircase
-- contributions all vanish, leaving q₁ · (− e).

bJunk-snd-0 : ∀ (b : B) (σ : ℤ ₚ) → σ ≡ ₀ → bJunk b σ .proj₂ ≡ ₀
bJunk-snd-0 (₀ , b₂) σ σ0 =
  trans (cong (λ w → - (w * b₂)) σ0)
    (trans (cong -_ (*-zeroˡ b₂)) -₀≡₀)
bJunk-snd-0 (₁₊ c₁' , _) σ σ0 =
  trans (cong (λ w → - (w * ₁₊ c₁')) σ0)
    (trans (cong -_ (*-zeroˡ (₁₊ c₁'))) -₀≡₀)

dShift-00 : ∀ (d : D) (z : ℤ ₚ) → z ≡ ₀ → dShift d ₀ z ≡ ₀
dShift-00 (₀ , b) z z0 = *-zeroˡ (- b)
dShift-00 (₁₊ a' , b) z z0 =
  trans (cong (λ w → (- (w + ₀ * k')) * (- ₁₊ a')) z0)
    (trans (cong (λ w → (- (₀ + w)) * (- ₁₊ a')) (*-zeroˡ k'))
      (trans (cong (λ w → (- w) * (- ₁₊ a')) (+-identityʳ ₀))
        (trans (cong (_* (- ₁₊ a')) -₀≡₀) (*-zeroˡ (- ₁₊ a')))))
  where
  k' = - b * (((₁₊ a' , λ ()) ⁻¹) .proj₁)

mbSnd-σ0 : ∀ {k} (dv : Vec D k) (e : E) (bv : Vec B k) (α σ : ℤ ₚ) →
  σ ≡ ₀ → mbSnd dv e bv (α , σ) ≡ α * (- e)
mbSnd-σ0 [] e [] α σ σ0 =
  trans (cong (_+ α * (- e)) σ0) (+-identityˡ (α * (- e)))
mbSnd-σ0 (d₁ ∷ dv') e (b₁ ∷ bv') α σ σ0 =
  trans (cong₂ _+_ (mbSnd-σ0 dv' e bv' α σ σ0)
                   (dShift-0-arg))
        (+-identityʳ (α * (- e)))
  where
  bJunk-fst : ∀ (b : B) → bJunk b σ .proj₁ ≡ ₀
  bJunk-fst (₀ , _) = refl
  bJunk-fst (₁₊ _ , _) = refl
  dShift-0-arg : dShift d₁ (bJunk b₁ σ .proj₁) (bJunk b₁ σ .proj₂) ≡ ₀
  dShift-0-arg = trans
    (cong₂ (dShift d₁) (bJunk-fst b₁) (bJunk-snd-0 b₁ σ σ0))
    (dShift-00 d₁ ₀ refl)

aProbe-snd-0 : ∀ (a : A) → aHd a (aProbe a) .proj₂ ≡ ₀
aProbe-snd-0 ((₀ , ₀) , pr) = ⊥-elim (pr refl)
aProbe-snd-0 ((₀ , ₁₊ y') , pr) = *-zeroˡ (((₁₊ y' , λ ()) ⁻¹) .proj₁)
aProbe-snd-0 ((₁₊ x' , y) , pr) = *-zeroˡ (((₁₊ x' , λ ()) ⁻¹) .proj₁)

-- The full head value of an inj₁ coset word at a probed input.
inj₁-full : ∀ {n} (dv : Vec D (₁₊ n)) (e : E) (bv : Vec B (₁₊ n))
  (a : A) (p₀ : Pauli1) →
  head (act [ ML (₂₊ n) ∋ inj₁ ((dv , e) , (bv , a)) ]ᵐˡ
    (p₀ ∷ pIₙ {₁₊ n})) ≡ (aHd a p₀ .proj₁ , mbSnd dv e bv (aHd a p₀))
inj₁-full {n} dv e bv a p₀ =
  trans (cong head
          (cong (λ v → act [ (dv , e) ]ᵐ (act [ bv ]ᵛᵇ v))
            (abox-hd a p₀ (pIₙ {₁₊ n}))))
        (mb-full dv e bv (aHd a p₀))

-- E is recovered: with the A boxes already equal, compare the second
-- head components at the probe.
inj₁-recover-e : ∀ {n} (dv₁ dv₂ : Vec D (₁₊ n)) (e₁ e₂ : E)
  (bv₁ bv₂ : Vec B (₁₊ n)) (a : A) →
  (∀ (ps : Pauli (₂₊ n)) →
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv₁ , e₁) , (bv₁ , a)) ]ᵐˡ ps) ≡
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv₂ , e₂) , (bv₂ , a)) ]ᵐˡ ps)) →
  e₁ ≡ e₂
inj₁-recover-e {n} dv₁ dv₂ e₁ e₂ bv₁ bv₂ a h =
  neg-inj e₁ e₂
    (*-cancelˡ-nz α (- e₁) (- e₂) (aProbe-fst-nz a)
      (trans (sym (mbSnd-σ0 dv₁ e₁ bv₁ α σ σ0))
      (trans snd-eq (mbSnd-σ0 dv₂ e₂ bv₂ α σ σ0))))
  where
  α = aHd a (aProbe a) .proj₁
  σ = aHd a (aProbe a) .proj₂
  σ0 = aProbe-snd-0 a
  snd-eq : mbSnd dv₁ e₁ bv₁ (α , σ) ≡ mbSnd dv₂ e₂ bv₂ (α , σ)
  snd-eq =
    trans (sym (cong proj₂ (inj₁-full dv₁ e₁ bv₁ a (aProbe a))))
    (trans (cong proj₂ (h (aProbe a ∷ pIₙ {₁₊ n})))
           (cong proj₂ (inj₁-full dv₂ e₂ bv₂ a (aProbe a))))

------------------------------------------------------------------------
-- The full B-box law with BOTH wires general: the box deposits
-- bTop b z c f on wire 0 and sends the head up as (x + bMix b c f , z).
-- Both closed forms are the exact raw outputs — no rewriting needed.

bTop : B → ℤ ₚ → ℤ ₚ → ℤ ₚ → Pauli1
bTop (₀ , b₂) z c f = (c , f + - (z * b₂))
bTop (₁₊ c₁' , b₂) z c f =
  (- (f + c * (- b₂ * (((₁₊ c₁' , λ ()) ⁻¹) .proj₁))) , c + - (z * ₁₊ c₁'))

bMix : B → ℤ ₚ → ℤ ₚ → ℤ ₚ
bMix (₀ , b₂) c f = c * b₂
bMix (₁₊ c₁' , b₂) c f =
  (- (f + c * (- b₂ * (((₁₊ c₁' , λ ()) ⁻¹) .proj₁)))) * ₁₊ c₁'

bbox-full : ∀ (b : B) (x z c f : ℤ ₚ) (t : Pauli n) →
  act ([_]ᵇ {n} b) ((x , z) ∷ (c , f) ∷ t) ≡
    bTop b z c f ∷ (x + bMix b c f , z) ∷ t
bbox-full (₀ , b₂) x z c f t =
  trans (cong (act Ex) (act-CX'^ b₂ x z c f t))
        (act-Ex (x + c * b₂) z c (f + - (z * b₂)) t)
bbox-full (₁₊ c₁' , b₂) x z c f t =
  trans (cong (λ v → act Ex (act (Symplectic.CX'^ (₁₊ c₁')) (act (H ↑) v)))
          (trans (lemma-act-↑ (S^ k) (x , z) ((c , f) ∷ t))
                 (cong ((x , z) ∷_) (act-S^ k c f t))))
  (trans (cong (λ v → act Ex (act (Symplectic.CX'^ (₁₊ c₁')) v))
          (trans (lemma-act-↑ H (x , z) ((c , f + c * k) ∷ t))
                 (cong ((x , z) ∷_) (act-H c (f + c * k) t))))
  (trans (cong (act Ex)
          (act-CX'^ (₁₊ c₁') x z (- (f + c * k)) c t))
         (act-Ex (x + (- (f + c * k)) * ₁₊ c₁') z
                 (- (f + c * k)) (c + - (z * ₁₊ c₁')) t)))
  where
  k = - b₂ * (((₁₊ c₁' , λ ()) ⁻¹) .proj₁)

-- One-step unfolding of the M/B staircase at a fully general input:
-- the head one level down enters shifted by bMix, and the D box adds
-- the dShift of the deposited bTop junk.

mb-step : ∀ {k} (d₁ : D) (dv' : Vec D k) (e : E) (b₁ : B)
  (bv' : Vec B k) (q₁ q₂ c f : ℤ ₚ) (t : Pauli k) →
  head (act ([ (d₁ ∷ dv' , e) ]ᵐ • [ b₁ ∷ bv' ]ᵛᵇ)
    ((q₁ , q₂) ∷ (c , f) ∷ t)) ≡
  ( head (act ([ (dv' , e) ]ᵐ • [ bv' ]ᵛᵇ)
      ((q₁ + bMix b₁ c f , q₂) ∷ t)) .proj₁
  , head (act ([ (dv' , e) ]ᵐ • [ bv' ]ᵛᵇ)
      ((q₁ + bMix b₁ c f , q₂) ∷ t)) .proj₂ +
    dShift d₁ (bTop b₁ q₂ c f .proj₁) (bTop b₁ q₂ c f .proj₂) )
mb-step {k} d₁ dv' e b₁ bv' q₁ q₂ c f t =
  trans (cong head V)
  (trans (cong (λ v → head (act ([_]ᵈ {k} d₁) (bTop b₁ q₂ c f ∷ v)))
           (sym (lemma-aux-vec k inner)))
         (dbox-head-full d₁ (bTop b₁ q₂ c f .proj₁)
           (bTop b₁ q₂ c f .proj₂)
           (head inner .proj₁) (head inner .proj₂) (tail inner)))
  where
  inner = act ([ (dv' , e) ]ᵐ • [ bv' ]ᵛᵇ) ((q₁ + bMix b₁ c f , q₂) ∷ t)
  V : act ([ (d₁ ∷ dv' , e) ]ᵐ • [ b₁ ∷ bv' ]ᵛᵇ)
        ((q₁ , q₂) ∷ (c , f) ∷ t) ≡
      act ([_]ᵈ {k} d₁) (bTop b₁ q₂ c f ∷ inner)
  V = trans (cong (λ v → act ([_]ᵈ {k} d₁)
               (act ([ (dv' , e) ]ᵐ ↑) (act ([ bv' ]ᵛᵇ ↑) v)))
          (bbox-full b₁ q₁ q₂ c f t))
      (trans (cong (λ v → act ([_]ᵈ {k} d₁) (act ([ (dv' , e) ]ᵐ ↑) v))
          (lemma-act-↑ [ bv' ]ᵛᵇ (bTop b₁ q₂ c f)
            ((q₁ + bMix b₁ c f , q₂) ∷ t)))
        (cong (act ([_]ᵈ {k} d₁))
          (lemma-act-↑ [ (dv' , e) ]ᵐ (bTop b₁ q₂ c f)
            (act [ bv' ]ᵛᵇ ((q₁ + bMix b₁ c f , q₂) ∷ t)))))

-- bMix is the uniform linear functional (c , f) ↦ c·b₂ − f·c₁, so two
-- probes read the B box off; and it vanishes at (₀ , ₀), which is what
-- lets the recursion pass full input generality down a level.

bMix-lin : ∀ (c₁ b₂ : ℤ ₚ) (c f : ℤ ₚ) →
  bMix (c₁ , b₂) c f ≡ c * b₂ + - (f * c₁)
bMix-lin ₀ b₂ c f = sym
  (trans (cong (c * b₂ +_) (trans (cong -_ (*-zeroʳ f)) -₀≡₀))
         (+-identityʳ (c * b₂)))
bMix-lin (₁₊ c₁') b₂ c f = begin
  (- (f + c * k)) * ₁₊ c₁'
    ≡⟨ sym (-‿distribˡ-* (f + c * k) (₁₊ c₁')) ⟩
  - ((f + c * k) * ₁₊ c₁')
    ≡⟨ cong -_ (*-distribʳ-+ (₁₊ c₁') f (c * k)) ⟩
  - (f * ₁₊ c₁' + c * k * ₁₊ c₁')
    ≡⟨ sym (-‿+-comm (f * ₁₊ c₁') (c * k * ₁₊ c₁')) ⟩
  - (f * ₁₊ c₁') + - (c * k * ₁₊ c₁')
    ≡⟨ cong (- (f * ₁₊ c₁') +_) (cong -_ kc-eq) ⟩
  - (f * ₁₊ c₁') + - (- (c * b₂))
    ≡⟨ cong (- (f * ₁₊ c₁') +_) (-‿involutive (c * b₂)) ⟩
  - (f * ₁₊ c₁') + c * b₂
    ≡⟨ +-comm (- (f * ₁₊ c₁')) (c * b₂) ⟩
  c * b₂ + - (f * ₁₊ c₁') ∎
  where
  xI = (((₁₊ c₁' , λ ()) ⁻¹) .proj₁)
  k  = - b₂ * xI
  kc-eq : c * k * ₁₊ c₁' ≡ - (c * b₂)
  kc-eq = begin
    c * (- b₂ * xI) * ₁₊ c₁'  ≡⟨ cong (_* ₁₊ c₁') (sym (*-assoc c (- b₂) xI)) ⟩
    c * - b₂ * xI * ₁₊ c₁'    ≡⟨ *-assoc (c * - b₂) xI (₁₊ c₁') ⟩
    c * - b₂ * (xI * ₁₊ c₁')  ≡⟨ cong (c * - b₂ *_)
                                   (lemma-⁻¹ˡ (₁₊ c₁')
                                     {{nztoℕ {y = ₁₊ c₁'} {neq0 = λ ()}}}) ⟩
    c * - b₂ * ₁              ≡⟨ *-identityʳ (c * - b₂) ⟩
    c * - b₂                  ≡⟨ sym (-‿distribʳ-* c b₂) ⟩
    - (c * b₂)                ∎

-- dShift is likewise the uniform linear functional
-- (x , z) ↦ δ₁·z − δ₂·x.
dShift-lin : ∀ (δ₁ δ₂ : ℤ ₚ) (x z : ℤ ₚ) →
  dShift (δ₁ , δ₂) x z ≡ δ₁ * z + - (δ₂ * x)
dShift-lin ₀ δ₂ x z = begin
  x * - δ₂          ≡⟨ sym (-‿distribʳ-* x δ₂) ⟩
  - (x * δ₂)        ≡⟨ cong -_ (*-comm x δ₂) ⟩
  - (δ₂ * x)        ≡⟨ sym (+-identityˡ (- (δ₂ * x))) ⟩
  ₀ + - (δ₂ * x)    ≡⟨ cong (_+ - (δ₂ * x)) (sym (*-zeroˡ z)) ⟩
  ₀ * z + - (δ₂ * x) ∎
dShift-lin (₁₊ d') δ₂ x z = begin
  (- (z + x * k')) * (- ₁₊ d')
    ≡⟨ negneg (z + x * k') (₁₊ d') ⟩
  (z + x * k') * ₁₊ d'
    ≡⟨ *-distribʳ-+ (₁₊ d') z (x * k') ⟩
  z * ₁₊ d' + x * k' * ₁₊ d'
    ≡⟨ cong₂ _+_ (*-comm z (₁₊ d')) kx-eq ⟩
  ₁₊ d' * z + - (δ₂ * x) ∎
  where
  dI = (((₁₊ d' , λ ()) ⁻¹) .proj₁)
  k' = - δ₂ * dI
  kx-eq : x * k' * ₁₊ d' ≡ - (δ₂ * x)
  kx-eq = begin
    x * (- δ₂ * dI) * ₁₊ d'  ≡⟨ cong (_* ₁₊ d') (sym (*-assoc x (- δ₂) dI)) ⟩
    x * - δ₂ * dI * ₁₊ d'    ≡⟨ *-assoc (x * - δ₂) dI (₁₊ d') ⟩
    x * - δ₂ * (dI * ₁₊ d')  ≡⟨ cong (x * - δ₂ *_)
                                  (lemma-⁻¹ˡ (₁₊ d')
                                    {{nztoℕ {y = ₁₊ d'} {neq0 = λ ()}}}) ⟩
    x * - δ₂ * ₁             ≡⟨ *-identityʳ (x * - δ₂) ⟩
    x * - δ₂                 ≡⟨ sym (-‿distribʳ-* x δ₂) ⟩
    - (x * δ₂)               ≡⟨ cong -_ (*-comm x δ₂) ⟩
    - (δ₂ * x)               ∎

+-cancelˡ'' : ∀ (x y₁ y₂ : ℤ ₚ) → x + y₁ ≡ x + y₂ → y₁ ≡ y₂
+-cancelˡ'' x y₁ y₂ eq = begin
  y₁              ≡⟨ sym (+-identityˡ y₁) ⟩
  ₀ + y₁          ≡⟨ cong (_+ y₁) (sym (+-inverseˡ x)) ⟩
  (- x + x) + y₁  ≡⟨ +-assoc (- x) x y₁ ⟩
  - x + (x + y₁)  ≡⟨ cong (- x +_) eq ⟩
  - x + (x + y₂)  ≡⟨ sym (+-assoc (- x) x y₂) ⟩
  (- x + x) + y₂  ≡⟨ cong (_+ y₂) (+-inverseˡ x) ⟩
  ₀ + y₂          ≡⟨ +-identityˡ y₂ ⟩
  y₂              ∎

bMix-00 : ∀ (b : B) → bMix b ₀ ₀ ≡ ₀
bMix-00 (₀ , b₂) = *-zeroˡ b₂
bMix-00 (₁₊ c₁' , b₂) =
  trans (cong (λ w → (- (₀ + w)) * ₁₊ c₁') (*-zeroˡ k))
    (trans (cong (λ w → (- w) * ₁₊ c₁') (+-identityʳ ₀))
      (trans (cong (_* ₁₊ c₁') -₀≡₀) (*-zeroˡ (₁₊ c₁'))))
  where
  k = - b₂ * (((₁₊ c₁' , λ ()) ⁻¹) .proj₁)

------------------------------------------------------------------------
-- Recovery of a B box from its bMix functional (two probes).

bM10 : ∀ (c₁ β₂ : ℤ ₚ) → bMix (c₁ , β₂) ₁ ₀ ≡ β₂
bM10 c₁ β₂ = trans (bMix-lin c₁ β₂ ₁ ₀)
  (trans (cong₂ _+_ (*-identityˡ β₂)
           (trans (cong -_ (*-zeroˡ c₁)) -₀≡₀))
         (+-identityʳ β₂))

bM01 : ∀ (c₁ β₂ : ℤ ₚ) → bMix (c₁ , β₂) ₀ ₁ ≡ - c₁
bM01 c₁ β₂ = trans (bMix-lin c₁ β₂ ₀ ₁)
  (trans (cong₂ _+_ (*-zeroˡ β₂) (cong -_ (*-identityˡ c₁)))
         (+-identityˡ (- c₁)))

b-recover : ∀ (b₁ b₂ : B) → (∀ c f → bMix b₁ c f ≡ bMix b₂ c f) →
  b₁ ≡ b₂
b-recover (c₁ , β₂) (c₁' , β₂') hyp = ≡×≡⇒≡
  ( neg-inj c₁ c₁'
      (trans (sym (bM01 c₁ β₂)) (trans (hyp ₀ ₁) (bM01 c₁' β₂')))
  , trans (sym (bM10 c₁ β₂)) (trans (hyp ₁ ₀) (bM10 c₁' β₂')) )

------------------------------------------------------------------------
-- Recovery of a D box from its shift-through-the-B-junk functional.

T : B → D → ℤ ₚ → ℤ ₚ → ℤ ₚ
T b d c f = dShift d (bTop b ₀ c f .proj₁) (bTop b ₀ c f .proj₂)

T-lin1 : ∀ (β₂ δ₁ δ₂ c f : ℤ ₚ) →
  T (₀ , β₂) (δ₁ , δ₂) c f ≡ δ₁ * f + - (δ₂ * c)
T-lin1 β₂ δ₁ δ₂ c f =
  trans (cong (dShift (δ₁ , δ₂) c) sndfix) (dShift-lin δ₁ δ₂ c f)
  where
  sndfix : f + - (₀ * β₂) ≡ f
  sndfix = trans (cong (f +_) (trans (cong -_ (*-zeroˡ β₂)) -₀≡₀))
                 (+-identityʳ f)

T-lin2 : ∀ (γ₁' : Fin (₁₊ p-2)) (β₂ δ₁ δ₂ c f : ℤ ₚ) →
  let k = - β₂ * (((₁₊ γ₁' , λ ()) ⁻¹) .proj₁) in
  T (₁₊ γ₁' , β₂) (δ₁ , δ₂) c f ≡ δ₁ * c + - (δ₂ * (- (f + c * k)))
T-lin2 γ₁' β₂ δ₁ δ₂ c f =
  trans (cong (dShift (δ₁ , δ₂) (- (f + c * k))) sndfix)
        (dShift-lin δ₁ δ₂ (- (f + c * k)) c)
  where
  k = - β₂ * (((₁₊ γ₁' , λ ()) ⁻¹) .proj₁)
  sndfix : c + - (₀ * ₁₊ γ₁') ≡ c
  sndfix = trans (cong (c +_) (trans (cong -_ (*-zeroˡ (₁₊ γ₁'))) -₀≡₀))
                 (+-identityʳ c)

T-00 : ∀ (b : B) (d : D) → T b d ₀ ₀ ≡ ₀
T-00 (₀ , β₂) (δ₁ , δ₂) = trans (T-lin1 β₂ δ₁ δ₂ ₀ ₀)
  (trans (cong₂ _+_ (*-zeroʳ δ₁) (trans (cong -_ (*-zeroʳ δ₂)) -₀≡₀))
         (+-identityʳ ₀))
T-00 (₁₊ γ₁' , β₂) (δ₁ , δ₂) = trans (T-lin2 γ₁' β₂ δ₁ δ₂ ₀ ₀)
  (trans (cong₂ _+_ (*-zeroʳ δ₁)
           (trans (cong (λ w → - (δ₂ * - w))
                    (trans (cong (₀ +_) (*-zeroˡ k)) (+-identityʳ ₀)))
             (trans (cong (λ w → - (δ₂ * w)) -₀≡₀)
               (trans (cong -_ (*-zeroʳ δ₂)) -₀≡₀))))
         (+-identityʳ ₀))
  where
  k = - β₂ * (((₁₊ γ₁' , λ ()) ⁻¹) .proj₁)

d-recover : ∀ (b : B) (d₁ d₂ : D) →
  (∀ c f → T b d₁ c f ≡ T b d₂ c f) → d₁ ≡ d₂
d-recover (₀ , β₂) (δ₁ , δ₂) (δ₁' , δ₂') hyp = ≡×≡⇒≡ (δ₁-eq , δ₂-eq)
  where
  ev10 : ∀ (u₁ u₂ : ℤ ₚ) → T (₀ , β₂) (u₁ , u₂) ₁ ₀ ≡ - u₂
  ev10 u₁ u₂ = trans (T-lin1 β₂ u₁ u₂ ₁ ₀)
    (trans (cong₂ _+_ (*-zeroʳ u₁) (cong -_ (*-identityʳ u₂)))
           (+-identityˡ (- u₂)))
  ev01 : ∀ (u₁ u₂ : ℤ ₚ) → T (₀ , β₂) (u₁ , u₂) ₀ ₁ ≡ u₁
  ev01 u₁ u₂ = trans (T-lin1 β₂ u₁ u₂ ₀ ₁)
    (trans (cong₂ _+_ (*-identityʳ u₁)
             (trans (cong -_ (*-zeroʳ u₂)) -₀≡₀))
           (+-identityʳ u₁))
  δ₂-eq : δ₂ ≡ δ₂'
  δ₂-eq = neg-inj δ₂ δ₂'
    (trans (sym (ev10 δ₁ δ₂)) (trans (hyp ₁ ₀) (ev10 δ₁' δ₂')))
  δ₁-eq : δ₁ ≡ δ₁'
  δ₁-eq = trans (sym (ev01 δ₁ δ₂)) (trans (hyp ₀ ₁) (ev01 δ₁' δ₂'))
d-recover (₁₊ γ₁' , β₂) (δ₁ , δ₂) (δ₁' , δ₂') hyp = ≡×≡⇒≡ (δ₁-eq , δ₂-eq)
  where
  k = - β₂ * (((₁₊ γ₁' , λ ()) ⁻¹) .proj₁)
  ev01 : ∀ (u₁ u₂ : ℤ ₚ) → T (₁₊ γ₁' , β₂) (u₁ , u₂) ₀ ₁ ≡ u₂
  ev01 u₁ u₂ = trans (T-lin2 γ₁' β₂ u₁ u₂ ₀ ₁)
    (trans (cong₂ _+_ (*-zeroʳ u₁)
             (trans (cong (λ w → - (u₂ * - w))
                      (trans (cong (₁ +_) (*-zeroˡ k)) (+-identityʳ ₁)))
               (trans (cong -_ (sym (-‿distribʳ-* u₂ ₁)))
                 (trans (cong -_ (cong -_ (*-identityʳ u₂)))
                        (-‿involutive u₂)))))
           (+-identityˡ u₂))
  ev10 : ∀ (u₁ u₂ : ℤ ₚ) →
    T (₁₊ γ₁' , β₂) (u₁ , u₂) ₁ ₀ ≡ u₁ + - (u₂ * - (₀ + ₁ * k))
  ev10 u₁ u₂ = trans (T-lin2 γ₁' β₂ u₁ u₂ ₁ ₀)
    (cong (_+ - (u₂ * - (₀ + ₁ * k))) (*-identityʳ u₁))
  δ₂-eq : δ₂ ≡ δ₂'
  δ₂-eq = trans (sym (ev01 δ₁ δ₂)) (trans (hyp ₀ ₁) (ev01 δ₁' δ₂'))
  eq10 : δ₁ + - (δ₂ * - (₀ + ₁ * k)) ≡ δ₁' + - (δ₂ * - (₀ + ₁ * k))
  eq10 = trans (sym (ev10 δ₁ δ₂))
         (trans (hyp ₁ ₀)
         (trans (ev10 δ₁' δ₂')
           (cong (λ w → δ₁' + - (w * - (₀ + ₁ * k))) (sym δ₂-eq))))
  δ₁-eq : δ₁ ≡ δ₁'
  δ₁-eq = +-cancelʳ' (- (δ₂ * - (₀ + ₁ * k))) δ₁ δ₁' eq10

------------------------------------------------------------------------
-- The probe formulas at a pIₙ tail.

F-probe : ∀ {k} (d : D) (dv : Vec D k) (e : E) (b : B) (bv : Vec B k)
  (q₁ q₂ c f : ℤ ₚ) →
  head (act ([ (d ∷ dv , e) ]ᵐ • [ b ∷ bv ]ᵛᵇ)
    ((q₁ , q₂) ∷ (c , f) ∷ pIₙ {k})) .proj₁ ≡ q₁ + bMix b c f
F-probe {k} d dv e b bv q₁ q₂ c f =
  trans (cong proj₁ (mb-step d dv e b bv q₁ q₂ c f (pIₙ {k})))
        (mb-fst dv e bv (q₁ + bMix b c f , q₂))

G-probe : ∀ {k} (d : D) (dv : Vec D k) (e : E) (b : B) (bv : Vec B k)
  (q₁ c f : ℤ ₚ) →
  head (act ([ (d ∷ dv , e) ]ᵐ • [ b ∷ bv ]ᵛᵇ)
    ((q₁ , ₀) ∷ (c , f) ∷ pIₙ {k})) .proj₂ ≡
  (q₁ + bMix b c f) * (- e) + T b d c f
G-probe {k} d dv e b bv q₁ c f =
  trans (cong proj₂ (mb-step d dv e b bv q₁ ₀ c f (pIₙ {k})))
        (cong (_+ T b d c f)
          (trans (cong proj₂ (mb-full dv e bv (q₁ + bMix b c f , ₀)))
                 (mbSnd-σ0 dv e bv (q₁ + bMix b c f) ₀ refl)))

------------------------------------------------------------------------
-- The column-recovery induction: two M/B staircase composites with the
-- same head behaviour have equal D columns, E, and B columns.

mb-inj : ∀ {k} (dv₁ dv₂ : Vec D k) (e₁ e₂ : E) (bv₁ bv₂ : Vec B k) →
  (∀ (v : Pauli (₁₊ k)) →
    head (act ([ (dv₁ , e₁) ]ᵐ • [ bv₁ ]ᵛᵇ) v) ≡
    head (act ([ (dv₂ , e₂) ]ᵐ • [ bv₂ ]ᵛᵇ) v)) →
  _≡_ {A = M (₁₊ k) × Vec B k} ((dv₁ , e₁) , bv₁) ((dv₂ , e₂) , bv₂)
mb-inj {₀} [] [] e₁ e₂ [] [] hyp =
  cong (λ w → (([] , w) , [])) (neg-inj e₁ e₂ neg-e-eq)
  where
  strip : ∀ e → ₀ + ₁ * (- e) ≡ - e
  strip e = trans (+-identityˡ (₁ * (- e))) (*-identityˡ (- e))
  neg-e-eq : - e₁ ≡ - e₂
  neg-e-eq =
    trans (sym (strip e₁))
    (trans (sym (cong proj₂ (cong head (act-S^ (- e₁) ₁ ₀ []))))
    (trans (cong proj₂ (hyp ((₁ , ₀) ∷ [])))
    (trans (cong proj₂ (cong head (act-S^ (- e₂) ₁ ₀ [])))
           (strip e₂))))
mb-inj {₁₊ k'} (d₁ ∷ dv₁') (d₂ ∷ dv₂') e₁ e₂ (b₁ ∷ bv₁') (b₂ ∷ bv₂') hyp =
  ≡×≡⇒≡ ( ≡×≡⇒≡ (cong₂ _∷_ d-eq dv'-eq , e-eq)
        , cong₂ _∷_ b-eq bv'-eq )
  where
  b-eq : b₁ ≡ b₂
  b-eq = b-recover b₁ b₂ λ c f → +-cancelˡ'' ₀ _ _
    (trans (sym (F-probe d₁ dv₁' e₁ b₁ bv₁' ₀ ₀ c f))
    (trans (cong proj₁ (hyp ((₀ , ₀) ∷ (c , f) ∷ pIₙ {k'})))
           (F-probe d₂ dv₂' e₂ b₂ bv₂' ₀ ₀ c f)))

  Gsimp : ∀ (d : D) (dv : Vec D k') (e : E) (b : B) (bv : Vec B k') →
    head (act ([ (d ∷ dv , e) ]ᵐ • [ b ∷ bv ]ᵛᵇ)
      ((₁ , ₀) ∷ (₀ , ₀) ∷ pIₙ {k'})) .proj₂ ≡ - e
  Gsimp d dv e b bv = trans (G-probe d dv e b bv ₁ ₀ ₀)
    (trans (cong₂ _+_
             (trans (cong (_* (- e))
                      (trans (cong (₁ +_) (bMix-00 b)) (+-identityʳ ₁)))
                    (*-identityˡ (- e)))
             (T-00 b d))
           (+-identityʳ (- e)))

  e-eq : e₁ ≡ e₂
  e-eq = neg-inj e₁ e₂
    (trans (sym (Gsimp d₁ dv₁' e₁ b₁ bv₁'))
    (trans (cong proj₂ (hyp ((₁ , ₀) ∷ (₀ , ₀) ∷ pIₙ {k'})))
           (Gsimp d₂ dv₂' e₂ b₂ bv₂')))

  d-eq : d₁ ≡ d₂
  d-eq = d-recover b₁ d₁ d₂ λ c f →
    +-cancelˡ'' ((₀ + bMix b₁ c f) * (- e₁)) _ _
      (trans (sym (G-probe d₁ dv₁' e₁ b₁ bv₁' ₀ c f))
      (trans (cong proj₂ (hyp ((₀ , ₀) ∷ (c , f) ∷ pIₙ {k'})))
      (trans (G-probe d₂ dv₂' e₂ b₂ bv₂' ₀ c f)
        (cong₂ _+_
          (cong₂ (λ u w → (₀ + bMix u c f) * (- w)) (sym b-eq) (sym e-eq))
          (cong (λ u → T u d₂ c f) (sym b-eq))))))

  sub-hyp : ∀ (w : Pauli (₁₊ k')) →
    head (act ([ (dv₁' , e₁) ]ᵐ • [ bv₁' ]ᵛᵇ) w) ≡
    head (act ([ (dv₂' , e₂) ]ᵐ • [ bv₂' ]ᵛᵇ) w)
  sub-hyp ((wh₁ , wh₂) ∷ wt) = ≡×≡⇒≡ (fst-eq , snd-eq)
    where
    S₁ = head (act ([ (dv₁' , e₁) ]ᵐ • [ bv₁' ]ᵛᵇ) ((wh₁ , wh₂) ∷ wt))
    S₂ = head (act ([ (dv₂' , e₂) ]ᵐ • [ bv₂' ]ᵛᵇ) ((wh₁ , wh₂) ∷ wt))
    T₁' = dShift d₁ (bTop b₁ wh₂ ₀ ₀ .proj₁) (bTop b₁ wh₂ ₀ ₀ .proj₂)
    T₂' = dShift d₂ (bTop b₂ wh₂ ₀ ₀ .proj₁) (bTop b₂ wh₂ ₀ ₀ .proj₂)
    inFix : ∀ (b : B) → (wh₁ + bMix b ₀ ₀ , wh₂) ≡ (wh₁ , wh₂)
    inFix b = ≡×≡⇒≡
      (trans (cong (wh₁ +_) (bMix-00 b)) (+-identityʳ wh₁) , refl)
    step₁ : head (act ([ (d₁ ∷ dv₁' , e₁) ]ᵐ • [ b₁ ∷ bv₁' ]ᵛᵇ)
              ((wh₁ , wh₂) ∷ (₀ , ₀) ∷ wt)) ≡ (S₁ .proj₁ , S₁ .proj₂ + T₁')
    step₁ = trans (mb-step d₁ dv₁' e₁ b₁ bv₁' wh₁ wh₂ ₀ ₀ wt)
      (cong (λ s → (s .proj₁ , s .proj₂ + T₁'))
        (cong (λ p → head (act ([ (dv₁' , e₁) ]ᵐ • [ bv₁' ]ᵛᵇ) (p ∷ wt)))
          (inFix b₁)))
    step₂ : head (act ([ (d₂ ∷ dv₂' , e₂) ]ᵐ • [ b₂ ∷ bv₂' ]ᵛᵇ)
              ((wh₁ , wh₂) ∷ (₀ , ₀) ∷ wt)) ≡ (S₂ .proj₁ , S₂ .proj₂ + T₂')
    step₂ = trans (mb-step d₂ dv₂' e₂ b₂ bv₂' wh₁ wh₂ ₀ ₀ wt)
      (cong (λ s → (s .proj₁ , s .proj₂ + T₂'))
        (cong (λ p → head (act ([ (dv₂' , e₂) ]ᵐ • [ bv₂' ]ᵛᵇ) (p ∷ wt)))
          (inFix b₂)))
    combined : (S₁ .proj₁ , S₁ .proj₂ + T₁') ≡ (S₂ .proj₁ , S₂ .proj₂ + T₂')
    combined = trans (sym step₁)
      (trans (hyp ((wh₁ , wh₂) ∷ (₀ , ₀) ∷ wt)) step₂)
    T-eq : T₂' ≡ T₁'
    T-eq = cong₂ (λ u v →
        dShift v (bTop u wh₂ ₀ ₀ .proj₁) (bTop u wh₂ ₀ ₀ .proj₂))
      (sym b-eq) (sym d-eq)
    fst-eq : S₁ .proj₁ ≡ S₂ .proj₁
    fst-eq = cong proj₁ combined
    snd-eq : S₁ .proj₂ ≡ S₂ .proj₂
    snd-eq = +-cancelʳ' T₁' (S₁ .proj₂) (S₂ .proj₂)
      (trans (cong proj₂ combined) (cong (S₂ .proj₂ +_) T-eq))

  IH : _≡_ {A = M (₁₊ k') × Vec B k'}
    ((dv₁' , e₁) , bv₁') ((dv₂' , e₂) , bv₂')
  IH = mb-inj dv₁' dv₂' e₁ e₂ bv₁' bv₂' sub-hyp
  dv'-eq : dv₁' ≡ dv₂'
  dv'-eq = cong (λ w → w .proj₁ .proj₁) IH
  bv'-eq : bv₁' ≡ bv₂'
  bv'-eq = cong proj₂ IH

------------------------------------------------------------------------
-- The A transform is surjective: aInv is a right inverse of aHd, so
-- full input generality passes through the A box to the staircase.

aInv : A → Pauli1 → Pauli1
aInv ((₀ , ₀) , pr) r = ⊥-elim (pr refl)
aInv ((₀ , ₁₊ y') , pr) (r₁ , r₂) =
  (r₁ * (((₁₊ y' , λ ()) ⁻¹) .proj₁) , r₂ * (((₁₊ y' , λ ()) ⁻¹ ⁻¹) .proj₁))
aInv ((₁₊ x' , y) , pr) (r₁ , r₂) =
  ( r₂ * ₁₊ x'
  , - (r₁ * xI) + - (r₂ * ₁₊ x' * (- y * xI)) )
  where xI = ((₁₊ x' , λ ()) ⁻¹) .proj₁

aHd-aInv : ∀ (a : A) (r : Pauli1) → aHd a (aInv a r) ≡ r
aHd-aInv ((₀ , ₀) , pr) r = ⊥-elim (pr refl)
aHd-aInv ((₀ , ₁₊ y') , pr) (r₁ , r₂) = ≡×≡⇒≡ (fst-eq , snd-eq)
  where
  inv  = (₁₊ y' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  fst-eq : r₁ * xI * invI ≡ r₁
  fst-eq = trans (*-assoc r₁ xI invI)
    (trans (cong (r₁ *_)
             (lemma-⁻¹ʳ xI {{nztoℕ {y = xI} {neq0 = inv .proj₂}}}))
           (*-identityʳ r₁))
  snd-eq : r₂ * invI * xI ≡ r₂
  snd-eq = trans (*-assoc r₂ invI xI)
    (trans (cong (r₂ *_)
             (lemma-⁻¹ˡ xI {{nztoℕ {y = xI} {neq0 = inv .proj₂}}}))
           (*-identityʳ r₂))
aHd-aInv ((₁₊ x' , y) , pr) (r₁ , r₂) = ≡×≡⇒≡ (fst-eq , snd-eq)
  where
  inv  = (₁₊ x' , λ ()) ⁻¹
  xI   = inv .proj₁
  invI = ((inv ⁻¹) .proj₁)
  k    = - y * xI
  q₁ = r₂ * ₁₊ x'
  q₂ = - (r₁ * xI) + - (q₁ * k)
  inner : q₂ + q₁ * k ≡ - (r₁ * xI)
  inner = trans (+-assoc (- (r₁ * xI)) (- (q₁ * k)) (q₁ * k))
    (trans (cong (- (r₁ * xI) +_) (+-inverseˡ (q₁ * k)))
           (+-identityʳ (- (r₁ * xI))))
  fst-eq : (- (q₂ + q₁ * k)) * invI ≡ r₁
  fst-eq = trans (cong (λ w → (- w) * invI) inner)
    (trans (cong (_* invI) (-‿involutive (r₁ * xI)))
    (trans (*-assoc r₁ xI invI)
    (trans (cong (r₁ *_)
             (lemma-⁻¹ʳ xI {{nztoℕ {y = xI} {neq0 = inv .proj₂}}}))
           (*-identityʳ r₁))))
  snd-eq : q₁ * xI ≡ r₂
  snd-eq = trans (*-assoc r₂ (₁₊ x') xI)
    (trans (cong (r₂ *_)
             (lemma-⁻¹ʳ (₁₊ x') {{nztoℕ {y = ₁₊ x'} {neq0 = λ ()}}}))
           (*-identityʳ r₂))

------------------------------------------------------------------------
-- THE LAST BASE: ML' (₂₊) head-injectivity, assembled.

inj₁-head-inj-proved : ∀ {n} (ml₁ ml₂ : ML' (₂₊ n)) →
  (∀ (ps : Pauli (₂₊ n)) →
    head (act [ ML (₂₊ n) ∋ inj₁ ml₁ ]ᵐˡ ps) ≡
    head (act [ ML (₂₊ n) ∋ inj₁ ml₂ ]ᵐˡ ps)) →
  ml₁ ≡ ml₂
inj₁-head-inj-proved {n} ((dv₁ , e₁) , (bv₁ , a₁))
                         ((dv₂ , e₂) , (bv₂ , a₂)) h =
  ≡×≡⇒≡ (cong proj₁ mb-eq , ≡×≡⇒≡ (cong proj₂ mb-eq , a-eq))
  where
  a-eq : a₁ ≡ a₂
  a-eq = inj₁-recover-a dv₁ dv₂ e₁ e₂ bv₁ bv₂ a₁ a₂ h

  h' : ∀ (ps : Pauli (₂₊ n)) →
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv₁ , e₁) , (bv₁ , a₁)) ]ᵐˡ ps) ≡
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv₂ , e₂) , (bv₂ , a₁)) ]ᵐˡ ps)
  h' ps = trans (h ps)
    (cong (λ u →
        head (act [ ML (₂₊ n) ∋ inj₁ ((dv₂ , e₂) , (bv₂ , u)) ]ᵐˡ ps))
      (sym a-eq))

  fix : ∀ (dv : Vec D (₁₊ n)) (e : E) (bv : Vec B (₁₊ n))
    (q : Pauli1) (ps' : Pauli (₁₊ n)) →
    head (act [ ML (₂₊ n) ∋ inj₁ ((dv , e) , (bv , a₁)) ]ᵐˡ
      (aInv a₁ q ∷ ps')) ≡
    head (act ([ (dv , e) ]ᵐ • [ bv ]ᵛᵇ) (q ∷ ps'))
  fix dv e bv q ps' = cong head
    (trans (cong (λ v' → act [ (dv , e) ]ᵐ (act [ bv ]ᵛᵇ v'))
             (abox-hd a₁ (aInv a₁ q) ps'))
           (cong (λ p → act ([ (dv , e) ]ᵐ • [ bv ]ᵛᵇ) (p ∷ ps'))
             (aHd-aInv a₁ q)))

  mb-hyp : ∀ (v : Pauli (₂₊ n)) →
    head (act ([ (dv₁ , e₁) ]ᵐ • [ bv₁ ]ᵛᵇ) v) ≡
    head (act ([ (dv₂ , e₂) ]ᵐ • [ bv₂ ]ᵛᵇ) v)
  mb-hyp (q ∷ ps') =
    trans (sym (fix dv₁ e₁ bv₁ q ps'))
    (trans (h' (aInv a₁ q ∷ ps'))
           (fix dv₂ e₂ bv₂ q ps'))

  mb-eq : _≡_ {A = M (₂₊ n) × Vec B (₁₊ n)}
    ((dv₁ , e₁) , bv₁) ((dv₂ , e₂) , bv₂)
  mb-eq = mb-inj dv₁ dv₂ e₁ e₂ bv₁ bv₂ mb-hyp

------------------------------------------------------------------------
-- With the separation proved, ONE parameter remains: ML' (₂₊)
-- head-injectivity.

module Induction!
  (inj₁-head-inj : ∀ {n} (ml₁ ml₂ : ML' (₂₊ n)) →
    (∀ (ps : Pauli (₂₊ n)) →
      head (act [ ML (₂₊ n) ∋ inj₁ ml₁ ]ᵐˡ ps) ≡
      head (act [ ML (₂₊ n) ∋ inj₁ ml₂ ]ᵐˡ ps)) →
    ml₁ ≡ ml₂)
  = Induction inj₁-head-inj inj₁≁inj₂-proved

------------------------------------------------------------------------
-- THE THEOREM, closed: every parameter is discharged.  This is the
-- statement postulated as lemma-lm-head-inj in Normalization.NF-Inj —
-- the completeness crux — now proved outright, --safe.

module Complete = Induction! inj₁-head-inj-proved

lemma-lm-head-inj-proved : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
  (∀ (ps : Pauli (₁₊ n)) →
    head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) →
  lm₁ ≡ lm₂
lemma-lm-head-inj-proved = Complete.lemma-lm-head-inj

lemma-lm-inj-proved : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
  (∀ (ps : Pauli (₁₊ n)) → act [ lm₁ ]ᵐˡ ps ≡ act [ lm₂ ]ᵐˡ ps) →
  lm₁ ≡ lm₂
lemma-lm-inj-proved = Complete.lemma-lm-inj
