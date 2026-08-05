------------------------------------------------------------------------
-- Presentations of groups
--
-- The lemma-lm-head-inj width induction for the plain gate set,
-- transplanted from ExtendedGate.NF-Inj-LM.  Everything is proved here
-- except the two remaining base facts, which are module parameters of
-- `Induction` (so this file stays --safe while they are ground
-- separately):
--   • cosets2-head-inj : ML 2 head-injectivity;
--   • inj₁-head-inj / inj₁≁inj₂ : the ML' branch at width ₃₊.
-- The width-1 base is lemma-nf1-head-inj (NF1HeadInj, proved).
--
-- Infrastructure proved here: the CZ-power action closed form
-- (act-CZ^), linear actions fix the identity Pauli (act-pIₙ), and the
-- D-box head laws (dbox-pZ-head / dbox-pX-head): prefixing pZ / pX
-- reads off the D box's components as head shifts.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --termination-depth=4 #-}

open import Data.Nat using (ℕ ; 2+ ; zero ; suc)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.LMHeadInj
  (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Fin using (toℕ)
open import Data.Vec using (Vec ; _∷_ ; [] ; head ; tail)
open import Function using (_∋_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ;
               module ≡-Reasoning)
open ≡-Reasoning

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pZ ; pX ; pIₙ ; _+₁_)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (S^ ; CZ^ ; S ; H ; CZ ; Ex ; Circuit ; Gen ;
  gate₁ ; gate₂ ; _↥ ; _↑ ; H-gate ; S-gate ; CZ-gate)
open import Examples.Groups.Symplectic.BoxAction p-2 p-prime
  using (act ; sc ; sc-toℕ ; sc-suc ; act-S^ ; act-H ; act-Ex)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (D ; M ; L' ; ML ; ML' ; [_]ᵐˡ ; [_]ᵈ)
open import Examples.Groups.Symplectic.Normalization.NF1HeadInj p-2 p-prime
  using (lemma-nf1-head-inj)

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
-- The width induction
--
-- The two remaining base facts are module parameters; instantiating
-- them (ML 2 head-injectivity, and the ML' branch at ₃₊) yields the
-- full lemma-lm-head-inj — the sole postulate of Normalization.NF-Inj.

module Induction
  (cosets2-head-inj : ∀ (lm₁ lm₂ : ML 2) →
    (∀ (ps : Pauli 2) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) →
    lm₁ ≡ lm₂)
  (inj₁-head-inj : ∀ {n} (ml₁ ml₂ : ML' (₃₊ n)) →
    (∀ (ps : Pauli (₃₊ n)) →
      head (act [ ML (₃₊ n) ∋ inj₁ ml₁ ]ᵐˡ ps) ≡
      head (act [ ML (₃₊ n) ∋ inj₁ ml₂ ]ᵐˡ ps)) →
    ml₁ ≡ ml₂)
  (inj₁≁inj₂ : ∀ {n} (ml : ML' (₃₊ n)) (d : D) (lm' : ML (₂₊ n)) →
    (∀ (ps : Pauli (₃₊ n)) →
      head (act [ ML (₃₊ n) ∋ inj₁ ml ]ᵐˡ ps) ≡
      head (act [ ML (₃₊ n) ∋ inj₂ (d , lm') ]ᵐˡ ps)) →
    ⊥)
  where

  lemma-lm-head-inj : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
    (∀ (ps : Pauli (₁₊ n)) →
      head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) →
    lm₁ ≡ lm₂
  lemma-lm-head-inj {₀} lm₁ lm₂ h = lemma-nf1-head-inj lm₁ lm₂ h
  lemma-lm-head-inj {₁} lm₁ lm₂ h = cosets2-head-inj lm₁ lm₂ h
  lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₁ ml₁) (inj₁ ml₂) h =
    cong inj₁ (inj₁-head-inj ml₁ ml₂ h)
  lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₁ ml) (inj₂ (d , lm')) h =
    ⊥-elim (inj₁≁inj₂ ml d lm' h)
  lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₂ (d , lm')) (inj₁ ml) h =
    ⊥-elim (inj₁≁inj₂ ml d lm' (λ ps → sym (h ps)))
  lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₂ (d₁ , lm₁')) (inj₂ (d₂ , lm₂')) h =
    cong inj₂ (≡×≡⇒≡ (d-eq , lm'-eq))
    where
    -- act [inj₂(d,lm')]ᵐˡ (p ∷ ps') = act [d]ᵈ (p ∷ act [lm']ᵐˡ ps').
    unfold-act : ∀ (d : D) (lm' : ML (₂₊ n)) (p₀ : Pauli1)
      (ps' : Pauli (₂₊ n)) →
      act [ ML (₃₊ n) ∋ inj₂ (d , lm') ]ᵐˡ (p₀ ∷ ps') ≡
        act ([_]ᵈ {₁₊ n} d) (p₀ ∷ act [ lm' ]ᵐˡ ps')
    unfold-act d lm' p₀ ps' =
      cong (act ([_]ᵈ {₁₊ n} d)) (lemma-act-↑ [ lm' ]ᵐˡ p₀ ps')

    -- Head agreement with the tails cancelled at the identity Pauli.
    head-at-pI : ∀ (p₀ : Pauli1) →
      head (act ([_]ᵈ {₁₊ n} d₁) (p₀ ∷ pIₙ {₂₊ n})) ≡
      head (act ([_]ᵈ {₁₊ n} d₂) (p₀ ∷ pIₙ {₂₊ n}))
    head-at-pI p₀ = begin
      head (act ([_]ᵈ {₁₊ n} d₁) (p₀ ∷ pIₙ {₂₊ n}))
        ≡⟨ cong (λ v → head (act ([_]ᵈ {₁₊ n} d₁) (p₀ ∷ v)))
             (sym (act-pIₙ [ lm₁' ]ᵐˡ)) ⟩
      head (act ([_]ᵈ {₁₊ n} d₁) (p₀ ∷ act [ lm₁' ]ᵐˡ (pIₙ {₂₊ n})))
        ≡⟨ cong head (sym (unfold-act d₁ lm₁' p₀ (pIₙ {₂₊ n}))) ⟩
      head (act [ ML (₃₊ n) ∋ inj₂ (d₁ , lm₁') ]ᵐˡ (p₀ ∷ pIₙ {₂₊ n}))
        ≡⟨ h (p₀ ∷ pIₙ {₂₊ n}) ⟩
      head (act [ ML (₃₊ n) ∋ inj₂ (d₂ , lm₂') ]ᵐˡ (p₀ ∷ pIₙ {₂₊ n}))
        ≡⟨ cong head (unfold-act d₂ lm₂' p₀ (pIₙ {₂₊ n})) ⟩
      head (act ([_]ᵈ {₁₊ n} d₂) (p₀ ∷ act [ lm₂' ]ᵐˡ (pIₙ {₂₊ n})))
        ≡⟨ cong (λ v → head (act ([_]ᵈ {₁₊ n} d₂) (p₀ ∷ v)))
             (act-pIₙ [ lm₂' ]ᵐˡ) ⟩
      head (act ([_]ᵈ {₁₊ n} d₂) (p₀ ∷ pIₙ {₂₊ n})) ∎

    -- d .proj₁ via the pZ prefix at the identity.
    d-eq-fst : d₁ .proj₁ ≡ d₂ .proj₁
    d-eq-fst = +-cancelˡ-strip
      (cong proj₂
        (trans (sym (dbox-pZ-head d₁ (₀ , ₀) (pIₙ {₁₊ n})))
        (trans (head-at-pI pZ)
               (dbox-pZ-head d₂ (₀ , ₀) (pIₙ {₁₊ n})))))
      where
      +-cancelˡ-strip : ₀ + d₁ .proj₁ ≡ ₀ + d₂ .proj₁ →
        d₁ .proj₁ ≡ d₂ .proj₁
      +-cancelˡ-strip eq = trans (sym (+-identityˡ (d₁ .proj₁)))
        (trans eq (+-identityˡ (d₂ .proj₁)))

    -- d .proj₂ via the pX prefix at the identity.
    d-eq-snd : d₁ .proj₂ ≡ d₂ .proj₂
    d-eq-snd = neg-inj _ _ (+-cancelˡ-strip
      (cong proj₂
        (trans (sym (dbox-pX-head d₁ (₀ , ₀) (pIₙ {₁₊ n})))
        (trans (head-at-pI pX)
               (dbox-pX-head d₂ (₀ , ₀) (pIₙ {₁₊ n}))))))
      where
      +-cancelˡ-strip : ₀ + - (d₁ .proj₂) ≡ ₀ + - (d₂ .proj₂) →
        - (d₁ .proj₂) ≡ - (d₂ .proj₂)
      +-cancelˡ-strip eq = trans (sym (+-identityˡ (- (d₁ .proj₂))))
        (trans eq (+-identityˡ (- (d₂ .proj₂))))

    d-eq : d₁ ≡ d₂
    d-eq = ≡×≡⇒≡ (d-eq-fst , d-eq-snd)

    -- Head equality one width down, from the pZ prefix at arbitrary
    -- inputs, cancelling the d shift.
    lm'-head-eq : ∀ (ps' : Pauli (₂₊ n)) →
      head (act [ lm₁' ]ᵐˡ ps') ≡ head (act [ lm₂' ]ᵐˡ ps')
    lm'-head-eq ps' =
      let
        v₁ = act [ lm₁' ]ᵐˡ ps'
        v₂ = act [ lm₂' ]ᵐˡ ps'
        raw : head (act ([_]ᵈ {₁₊ n} d₁) (pZ ∷ v₁))
            ≡ head (act ([_]ᵈ {₁₊ n} d₂) (pZ ∷ v₂))
        raw = trans (cong head (sym (unfold-act d₁ lm₁' pZ ps')))
              (trans (h (pZ ∷ ps'))
                     (cong head (unfold-act d₂ lm₂' pZ ps')))
        lhs : head (act ([_]ᵈ {₁₊ n} d₁) (pZ ∷ v₁))
            ≡ head v₁ +₁ (₀ , d₁ .proj₁)
        lhs = trans
          (cong (λ v → head (act ([_]ᵈ {₁₊ n} d₁) (pZ ∷ v)))
            (sym (lemma-aux-vec (₁₊ n) v₁)))
          (dbox-pZ-head d₁ (head v₁) (tail v₁))
        rhs : head (act ([_]ᵈ {₁₊ n} d₂) (pZ ∷ v₂))
            ≡ head v₂ +₁ (₀ , d₂ .proj₁)
        rhs = trans
          (cong (λ v → head (act ([_]ᵈ {₁₊ n} d₂) (pZ ∷ v)))
            (sym (lemma-aux-vec (₁₊ n) v₂)))
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
