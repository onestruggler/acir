------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the plain qupit-Clifford presentation in the symplectic
-- semantics, proved directly.
--
-- This replaces Examples.Groups.Symplectic.Transport, which proved the
-- same statement by carrying it across the isomorphism with the
-- extended gate set, where the work happened (ExtendedGate.Soundness).
-- That module is in the history if the comparison is ever wanted.
--
-- What the extended gate set bought is that S^k, CZ^k and M are single
-- generators there, carrying their scalar in the action.  Here they are
-- words, so the direct proof needs power lemmas first — lemma-S^ and
-- lemma-CZ^ below — after which each rule is the same computation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; suc ; 2+)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.SoundnessDirect
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Fin using (toℕ)
open import Data.Product using (_,_ ; proj₁)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli)
open import Examples.Groups.Pauli.Presentation-Alt p-2 p-prime
  using (mult ; mult-toℕ ; mult-p)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using ( Circuit ; Gen ; SympGate ; gate₁ ; gate₂ ; _↥
                      ; H-gate ; S-gate ; CZ-gate ; S ; H ; CZ ; _↑ ; _↓
                      ; S^ ; CZ^ ; M ; _^1 ; _^2 ; S⁻¹ ; ₕ|ₕ ; ʰ|ʰ ; ⊥⊤ ; ⊤⊥
                      ; _QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂
                      ; module Base )

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧ ; actg)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The action of a circuit
--
-- ⟦_⟧ is a monoid map into Symplectic and ap is the action, so this
-- computes: act [ g ]ʷ = actg g, act ε q = q and act (w • v) q =
-- act w (act v q), all definitionally.

act : Circuit n → Pauli n → Pauli n
act w q = ap ⟦ w ⟧ q

-- A shifted circuit acts on the tail.
act-↑ : ∀ (w : Circuit n) q qs → act (w ↑) (q ∷ qs) ≡ q ∷ act w qs
act-↑ [ x ]ʷ  q qs = Eq.refl
act-↑ ε       q qs = Eq.refl
act-↑ (w • v) q qs =
  Eq.trans (Eq.cong (act (w ↑)) (act-↑ v q qs)) (act-↑ w q (act v qs))

------------------------------------------------------------------------
-- ℤ/pℤ lemmas used by the power lemmas

private
  -- One more application of S, absorbed into the coefficient.
  step : ∀ (b m a : ℤ ₚ) → (b + m * a) + a ≡ b + (₁ + m) * a
  step b m a = begin
    (b + m * a) + a     ≡⟨ +-assoc b (m * a) a ⟩
    b + (m * a + a)     ≡⟨ Eq.cong (b +_) (+-comm (m * a) a) ⟩
    b + (a + m * a)     ≡⟨ Eq.cong (λ z → b + (z + m * a)) (Eq.sym (*-identityˡ a)) ⟩
    b + (₁ * a + m * a) ≡⟨ Eq.cong (b +_) (Eq.sym (*-distribʳ-+ a ₁ m)) ⟩
    b + (₁ + m) * a     ∎
    where open ≡-Reasoning

  zero-step : ∀ (b a : ℤ ₚ) → b ≡ b + ₀ * a
  zero-step b a =
    Eq.sym (Eq.trans (Eq.cong (b +_) (*-zeroˡ a)) (+-identityʳ b))

  one-step : ∀ (b a : ℤ ₚ) → b + a ≡ b + (₁ + ₀) * a
  one-step b a = Eq.cong (b +_) (begin
    a           ≡⟨ Eq.sym (*-identityˡ a) ⟩
    ₁ * a       ≡⟨ Eq.cong (_* a) (Eq.sym (+-identityʳ ₁)) ⟩
    (₁ + ₀) * a ∎)
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Powers of S and of CZ
--
-- S adds the X-exponent to the Z-exponent, so S^k adds it k times, and
-- mult k — the image of k in ℤ/pℤ — turns those k additions into one
-- multiplication.  CZ does the same across two wires.

lemma-S^ : ∀ k a b (t : Pauli n) →
           act (S ^ k) ((a , b) ∷ t) ≡ (a , b + mult k * a) ∷ t
lemma-S^ ₀      a b t = Eq.cong (λ z → (a , z) ∷ t) (zero-step b a)
lemma-S^ ₁      a b t = Eq.cong (λ z → (a , z) ∷ t) (one-step b a)
lemma-S^ (₂₊ k) a b t = begin
  act (S • S ^ ₁₊ k) ((a , b) ∷ t)
    ≡⟨ Eq.cong (act S) (lemma-S^ (₁₊ k) a b t) ⟩
  ((a , (b + mult (₁₊ k) * a) + a) ∷ t)
    ≡⟨ Eq.cong (λ z → (a , z) ∷ t) (step b (mult (₁₊ k)) a) ⟩
  ((a , b + mult (₂₊ k) * a) ∷ t) ∎
  where open ≡-Reasoning

lemma-CZ^ : ∀ k a b a' b' (t : Pauli n) →
            act (CZ ^ k) ((a , b) ∷ (a' , b') ∷ t)
              ≡ (a , b + mult k * a') ∷ (a' , b' + mult k * a) ∷ t
lemma-CZ^ ₀ a b a' b' t =
  Eq.cong₂ (λ z z' → (a , z) ∷ (a' , z') ∷ t)
    (zero-step b a') (zero-step b' a)
lemma-CZ^ ₁ a b a' b' t =
  Eq.cong₂ (λ z z' → (a , z) ∷ (a' , z') ∷ t)
    (one-step b a') (one-step b' a)
lemma-CZ^ (₂₊ k) a b a' b' t = begin
  act (CZ • CZ ^ ₁₊ k) ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.cong (act CZ) (lemma-CZ^ (₁₊ k) a b a' b' t) ⟩
  ((a , (b + mult (₁₊ k) * a') + a') ∷ (a' , (b' + mult (₁₊ k) * a) + a) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (a , z) ∷ (a' , z') ∷ t)
         (step b (mult (₁₊ k)) a') (step b' (mult (₁₊ k)) a) ⟩
  ((a , b + mult (₂₊ k) * a') ∷ (a' , b' + mult (₂₊ k) * a) ∷ t) ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- ℤ/pℤ lemmas used by the rules

private
  neg-sub : ∀ (a b : ℤ ₚ) → - (a + - b) ≡ - a + b
  neg-sub a b =
    Eq.trans (Eq.sym (-‿+-comm a (- b))) (Eq.cong (- a +_) (-‿involutive b))

  -- The middle step of (SH)³.
  sh₂ : ∀ (a b : ℤ ₚ) → - b + - (a + - b) ≡ - a
  sh₂ a b = begin
    - b + - (a + - b) ≡⟨ Eq.cong (- b +_) (neg-sub a b) ⟩
    - b + (- a + b)   ≡⟨ Eq.cong (- b +_) (+-comm (- a) b) ⟩
    - b + (b + - a)   ≡⟨ Eq.sym (+-assoc (- b) b (- a)) ⟩
    (- b + b) + - a   ≡⟨ Eq.cong (_+ - a) (+-inverseˡ b) ⟩
    ₀ + - a           ≡⟨ +-identityˡ (- a) ⟩
    - a               ∎
    where open ≡-Reasoning

  sh₃ : ∀ (a b : ℤ ₚ) → (- a + b) + - - a ≡ b
  sh₃ a b = begin
    (- a + b) + - - a ≡⟨ Eq.cong ((- a + b) +_) (-‿involutive a) ⟩
    (- a + b) + a     ≡⟨ Eq.cong (_+ a) (+-comm (- a) b) ⟩
    (b + - a) + a     ≡⟨ +-assoc b (- a) a ⟩
    b + (- a + a)     ≡⟨ Eq.cong (b +_) (+-inverseˡ a) ⟩
    b + ₀             ≡⟨ +-identityʳ b ⟩
    b                 ∎
    where open ≡-Reasoning

  -- Swapping the two summands added to b.
  swap-add : ∀ (b x y : ℤ ₚ) → (b + x) + y ≡ (b + y) + x
  swap-add b x y = begin
    (b + x) + y ≡⟨ +-assoc b x y ⟩
    b + (x + y) ≡⟨ Eq.cong (b +_) (+-comm x y) ⟩
    b + (y + x) ≡⟨ Eq.sym (+-assoc b y x) ⟩
    (b + y) + x ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- The rules that need no scalar gate

-- S has order p: p additions of a amount to ₀ * a.
sound-order-S : ∀ (q : Pauli (₁₊ n)) → act (S ^ p) q ≡ q
sound-order-S ((a , b) ∷ t) = begin
  act (S ^ p) ((a , b) ∷ t)  ≡⟨ lemma-S^ p a b t ⟩
  ((a , b + mult p * a) ∷ t) ≡⟨ Eq.cong (λ z → (a , b + z * a) ∷ t) mult-p ⟩
  ((a , b + ₀ * a) ∷ t)      ≡⟨ Eq.cong (λ z → (a , z) ∷ t) (Eq.sym (zero-step b a)) ⟩
  ((a , b) ∷ t)              ∎
  where open ≡-Reasoning

-- H is (a , b) ↦ (- b , a), so H² negates both and H⁴ is the identity.
sound-order-H : ∀ (q : Pauli (₁₊ n)) → act (H ^ 4) q ≡ q
sound-order-H ((a , b) ∷ t) =
  Eq.cong₂ (λ z z' → (z , z') ∷ t) (-‿involutive a) (-‿involutive b)

-- SH is (a , b) ↦ (- b , a + - b); iterating it three times is the
-- identity.
sound-order-SH : ∀ (q : Pauli (₁₊ n)) → act ((S • H) ^ 3) q ≡ q
sound-order-SH ((a , b) ∷ t) =
  Eq.cong₂ (λ z z' → (z , z') ∷ t) fst snd
  where
  open ≡-Reasoning
  fst : - (- b + - (a + - b)) ≡ a
  fst = Eq.trans (Eq.cong -_ (sh₂ a b)) (-‿involutive a)
  snd : - (a + - b) + - (- b + - (a + - b)) ≡ b
  snd = begin
    - (a + - b) + - (- b + - (a + - b))
      ≡⟨ Eq.cong₂ _+_ (neg-sub a b) (Eq.cong -_ (sh₂ a b)) ⟩
    (- a + b) + - - a ≡⟨ sh₃ a b ⟩
    b ∎

-- H² is negation, which commutes with S.
sound-comm-HHS : ∀ (q : Pauli (₁₊ n)) → act (H • H • S) q ≡ act (S • H • H) q
sound-comm-HHS ((a , b) ∷ t) =
  Eq.cong (λ z → (- a , z) ∷ t) (Eq.sym (-‿+-comm b a))

-- CZ has order p, by the same count as S.
sound-order-CZ : ∀ (q : Pauli (₂₊ n)) → act (CZ ^ p) q ≡ q
sound-order-CZ ((a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ ^ p) ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ lemma-CZ^ p a b a' b' t ⟩
  ((a , b + mult p * a') ∷ (a' , b' + mult p * a) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (a , b + z * a') ∷ (a' , b' + z' * a) ∷ t) mult-p mult-p ⟩
  ((a , b + ₀ * a') ∷ (a' , b' + ₀ * a) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (a , z) ∷ (a' , z') ∷ t)
         (Eq.sym (zero-step b a')) (Eq.sym (zero-step b' a)) ⟩
  ((a , b) ∷ (a' , b') ∷ t) ∎
  where open ≡-Reasoning

-- CZ and S on the bottom wire both only add to that wire's Z-exponent.
sound-comm-CZ-S↓ : ∀ (q : Pauli (₂₊ n)) →
                   act (CZ • S ↓) q ≡ act (S ↓ • CZ) q
sound-comm-CZ-S↓ ((a , b) ∷ (a' , b') ∷ t) =
  Eq.cong (λ z → (a , z) ∷ (a' , b' + a) ∷ t) (swap-add b a a')

sound-comm-CZ-S↑ : ∀ (q : Pauli (₂₊ n)) →
                   act (CZ • S ↑) q ≡ act (S ↑ • CZ) q
sound-comm-CZ-S↑ ((a , b) ∷ (a' , b') ∷ t) =
  Eq.cong (λ z → (a , b + a') ∷ (a' , z) ∷ t) (swap-add b' a' a)

------------------------------------------------------------------------
-- The structural rules
--
-- A gate at the bottom and a generator shifted past it touch disjoint
-- wires, so the two actions commute definitionally.

sound-comm₁ : ∀ (h : SympGate 1) (g : Gen n) (q : Pauli (₁₊ n)) →
              act ([ g ↥ ]ʷ • [ gate₁ h ]ʷ) q ≡ act ([ gate₁ h ]ʷ • [ g ↥ ]ʷ) q
sound-comm₁ H-gate g ((a , b) ∷ qs) = Eq.refl
sound-comm₁ S-gate g ((a , b) ∷ qs) = Eq.refl

sound-comm₂ : ∀ (h : SympGate 2) (g : Gen n) (q : Pauli (₂₊ n)) →
              act ([ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ) q
                ≡ act ([ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ) q
sound-comm₂ CZ-gate g ((a , b) ∷ (a' , b') ∷ qs) = Eq.refl

------------------------------------------------------------------------
-- The M gate
--
-- M x = S^x H S^x⁻¹ H S^x H is the scaling map, and the point of the
-- whole rule set: it is what makes the multiplicative group of ℤ/pℤ
-- available inside the presentation.  Semantically it multiplies the
-- X-exponent by x⁻¹ and the Z-exponent by x.

-- S to a ℤ/pℤ exponent: mult (toℕ k) is k.
lemma-S^' : ∀ (k : ℤ ₚ) a b (t : Pauli n) →
            act (S^ k) ((a , b) ∷ t) ≡ (a , b + k * a) ∷ t
lemma-S^' k a b t =
  Eq.trans (lemma-S^ (toℕ k) a b t)
           (Eq.cong (λ z → (a , b + z * a) ∷ t) (mult-toℕ k))

private
  -- x⁻¹ x ≡ ₁ and x x⁻¹ ≡ ₁, with the instance argument discharged.
  inv-left : ∀ (x : ℤ* ₚ) → (x ⁻¹) .proj₁ * x .proj₁ ≡ ₁
  inv-left (x , nz) = lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = nz}}}

  inv-right : ∀ (x : ℤ* ₚ) → x .proj₁ * (x ⁻¹) .proj₁ ≡ ₁
  inv-right x = Eq.trans (*-comm (x .proj₁) ((x ⁻¹) .proj₁)) (inv-left x)

  -- (- a + c) + a ≡ c
  cancel-l : ∀ (a c : ℤ ₚ) → (- a + c) + a ≡ c
  cancel-l a c = begin
    (- a + c) + a ≡⟨ Eq.cong (_+ a) (+-comm (- a) c) ⟩
    (c + - a) + a ≡⟨ +-assoc c (- a) a ⟩
    c + (- a + a) ≡⟨ Eq.cong (c +_) (+-inverseˡ a) ⟩
    c + ₀         ≡⟨ +-identityʳ c ⟩
    c             ∎
    where open ≡-Reasoning

  -- - (a + u * - b) ≡ - a + u * b
  neg-mix : ∀ (u a b : ℤ ₚ) → - (a + u * - b) ≡ - a + u * b
  neg-mix u a b = begin
    - (a + u * - b)   ≡⟨ Eq.sym (-‿+-comm a (u * - b)) ⟩
    - a + - (u * - b) ≡⟨ Eq.cong (λ z → - a + - z) (Eq.sym (-‿distribʳ-* u b)) ⟩
    - a + - - (u * b) ≡⟨ Eq.cong (- a +_) (-‿involutive (u * b)) ⟩
    - a + u * b       ∎
    where open ≡-Reasoning

  -- The middle of M collapses: with v = u⁻¹ the Z-slot becomes - (v a).
  mid : ∀ (x : ℤ* ₚ) a b →
        let u = x .proj₁ ; v = (x ⁻¹) .proj₁ in
        - b + v * - (a + u * - b) ≡ - (v * a)
  mid x a b = begin
    - b + v * - (a + u * - b) ≡⟨ Eq.cong (- b +_) (Eq.sym (-‿distribʳ-* v (a + u * - b))) ⟩
    - b + - (v * (a + u * - b))
      ≡⟨ Eq.cong (λ z → - b + - z) (*-distribˡ-+ v a (u * - b)) ⟩
    - b + - (v * a + v * (u * - b))
      ≡⟨ Eq.cong (λ z → - b + - (v * a + z)) (Eq.sym (*-assoc v u (- b))) ⟩
    - b + - (v * a + (v * u) * - b)
      ≡⟨ Eq.cong (λ z → - b + - (v * a + z * - b)) (inv-left x) ⟩
    - b + - (v * a + ₁ * - b)
      ≡⟨ Eq.cong (λ z → - b + - (v * a + z)) (*-identityˡ (- b)) ⟩
    - b + - (v * a + - b) ≡⟨ sh₂ (v * a) b ⟩
    - (v * a)             ∎
    where
    open ≡-Reasoning
    u = x .proj₁
    v = (x ⁻¹) .proj₁

lemma-M : ∀ (x : ℤ* ₚ) a b (t : Pauli n) →
          act (M x) ((a , b) ∷ t)
            ≡ (a * (x ⁻¹) .proj₁ , b * x .proj₁) ∷ t
lemma-M x a b t = begin
  act (M x) ((a , b) ∷ t)
    ≡⟨ Eq.cong (λ z → act (S^ u • H • S^ v • H) z) (lemma-S^' u (- b) a t) ⟩
  act (S^ u • H • S^ v • H) ((- b , a + u * - b) ∷ t)
    ≡⟨ Eq.cong (λ z → act (S^ u • H) z) (lemma-S^' v (- (a + u * - b)) (- b) t) ⟩
  act (S^ u • H) ((- (a + u * - b) , - b + v * - (a + u * - b)) ∷ t)
    ≡⟨ Eq.cong (λ z → act (S^ u • H) ((- (a + u * - b) , z) ∷ t)) (mid x a b) ⟩
  act (S^ u • H) ((- (a + u * - b) , - (v * a)) ∷ t)
    ≡⟨ lemma-S^' u (- - (v * a)) (- (a + u * - b)) t ⟩
  ((- - (v * a) , - (a + u * - b) + u * - - (v * a)) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (z , z') ∷ t) (-‿involutive (v * a))
         (Eq.cong₂ _+_ (neg-mix u a b)
                       (Eq.cong (u *_) (-‿involutive (v * a)))) ⟩
  ((v * a , (- a + u * b) + u * (v * a)) ∷ t)
    ≡⟨ Eq.cong (λ z → (v * a , (- a + u * b) + z) ∷ t) collapse ⟩
  ((v * a , (- a + u * b) + a) ∷ t)
    ≡⟨ Eq.cong (λ z → (v * a , z) ∷ t) (cancel-l a (u * b)) ⟩
  ((v * a , u * b) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (z , z') ∷ t) (*-comm v a) (*-comm u b) ⟩
  ((a * v , b * u) ∷ t) ∎
  where
  open ≡-Reasoning
  u = x .proj₁
  v = (x ⁻¹) .proj₁
  collapse : u * (v * a) ≡ a
  collapse = begin
    u * (v * a) ≡⟨ Eq.sym (*-assoc u v a) ⟩
    (u * v) * a ≡⟨ Eq.cong (_* a) (inv-right x) ⟩
    ₁ * a       ≡⟨ *-identityˡ a ⟩
    a           ∎

-- CZ to a ℤ/pℤ exponent.
lemma-CZ^' : ∀ (k : ℤ ₚ) a b a' b' (t : Pauli n) →
             act (CZ^ k) ((a , b) ∷ (a' , b') ∷ t)
               ≡ (a , b + k * a') ∷ (a' , b' + k * a) ∷ t
lemma-CZ^' k a b a' b' t =
  Eq.trans (lemma-CZ^ (toℕ k) a b a' b' t)
           (Eq.cong₂ (λ z z' → (a , b + z * a') ∷ (a' , b' + z' * a) ∷ t)
                     (mult-toℕ k) (mult-toℕ k))

private
  -- x (c x⁻¹) ≡ c: scaling a coordinate and unscaling it.
  scale-cancel : ∀ (x : ℤ* ₚ) (c : ℤ ₚ) →
                 x .proj₁ * (c * (x ⁻¹) .proj₁) ≡ c
  scale-cancel x c = begin
    x' * (c * v) ≡⟨ Eq.cong (x' *_) (*-comm c v) ⟩
    x' * (v * c) ≡⟨ Eq.sym (*-assoc x' v c) ⟩
    (x' * v) * c ≡⟨ Eq.cong (_* c) (inv-right x) ⟩
    ₁ * c        ≡⟨ *-identityˡ c ⟩
    c            ∎
    where
    open ≡-Reasoning
    x' = x .proj₁
    v  = (x ⁻¹) .proj₁

------------------------------------------------------------------------
-- The rules governing M

-- Scaling by y and then by x is scaling by xy; the inverses multiply
-- the other way round, which is what inv-distrib says.
sound-M-mul : ∀ (x y : ℤ* ₚ) (q : Pauli (₁₊ n)) →
              act (M x • M y) q ≡ act (M (x *' y)) q
sound-M-mul x y ((a , b) ∷ t) = begin
  act (M x • M y) ((a , b) ∷ t)
    ≡⟨ Eq.cong (act (M x)) (lemma-M y a b t) ⟩
  act (M x) ((a * y⁻¹ , b * y') ∷ t)
    ≡⟨ lemma-M x (a * y⁻¹) (b * y') t ⟩
  (((a * y⁻¹) * x⁻¹ , (b * y') * x') ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (z , z') ∷ t) (*-assoc a y⁻¹ x⁻¹) (*-assoc b y' x') ⟩
  ((a * (y⁻¹ * x⁻¹) , b * (y' * x')) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (a * z , b * z') ∷ t)
         (Eq.sym (Eq.trans (inv-distrib x y) (*-comm x⁻¹ y⁻¹)))
         (*-comm y' x') ⟩
  ((a * ((x *' y) ⁻¹) .proj₁ , b * (x' * y')) ∷ t)
    ≡⟨ Eq.sym (lemma-M (x *' y) a b t) ⟩
  act (M (x *' y)) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  x'  = x .proj₁
  x⁻¹ = (x ⁻¹) .proj₁
  y'  = y .proj₁
  y⁻¹ = (y ⁻¹) .proj₁

-- Conjugating S by M scales the shear by x².
sound-semi-MS : ∀ (x : ℤ* ₚ) (q : Pauli (₁₊ n)) →
                act (M x • S) q ≡ act (S^ (x ^2) • M x) q
sound-semi-MS x ((a , b) ∷ t) = begin
  act (M x • S) ((a , b) ∷ t)
    ≡⟨ lemma-M x a (b + a) t ⟩
  ((a * x⁻¹ , (b + a) * x') ∷ t)
    ≡⟨ Eq.cong (λ z → (a * x⁻¹ , z) ∷ t) aux ⟩
  ((a * x⁻¹ , b * x' + (x ^2) * (a * x⁻¹)) ∷ t)
    ≡⟨ Eq.sym (lemma-S^' (x ^2) (a * x⁻¹) (b * x') t) ⟩
  act (S^ (x ^2)) ((a * x⁻¹ , b * x') ∷ t)
    ≡⟨ Eq.sym (Eq.cong (act (S^ (x ^2))) (lemma-M x a b t)) ⟩
  act (S^ (x ^2) • M x) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  x'  = x .proj₁
  x⁻¹ = (x ⁻¹) .proj₁
  aux : (b + a) * x' ≡ b * x' + (x ^2) * (a * x⁻¹)
  aux = begin
    (b + a) * x'                 ≡⟨ *-distribʳ-+ x' b a ⟩
    b * x' + a * x'              ≡⟨ Eq.cong (λ z → b * x' + z) (*-comm a x') ⟩
    b * x' + x' * a              ≡⟨ Eq.cong (λ z → b * x' + x' * z)
                                      (Eq.sym (scale-cancel x a)) ⟩
    b * x' + x' * (x' * (a * x⁻¹))
                                 ≡⟨ Eq.cong (b * x' +_)
                                      (Eq.sym (*-assoc x' x' (a * x⁻¹))) ⟩
    b * x' + (x ^2) * (a * x⁻¹)  ∎

-- Conjugating CZ by M on either wire scales the coupling by x.
sound-semi-M↑CZ : ∀ (x : ℤ* ₚ) (q : Pauli (₂₊ n)) →
                  act (M x ↑ • CZ) q ≡ act (CZ^ (x ^1) • M x ↑) q
sound-semi-M↑CZ x ((a , b) ∷ (a' , b') ∷ t) = begin
  act (M x ↑ • CZ) ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ act-↑ (M x) (a , b + a') ((a' , b' + a) ∷ t) ⟩
  ((a , b + a') ∷ act (M x) ((a' , b' + a) ∷ t))
    ≡⟨ Eq.cong (λ z → (a , b + a') ∷ z) (lemma-M x a' (b' + a) t) ⟩
  ((a , b + a') ∷ (a' * x⁻¹ , (b' + a) * x') ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (a , b + z) ∷ (a' * x⁻¹ , z') ∷ t)
         (Eq.sym (scale-cancel x a')) aux ⟩
  ((a , b + x' * (a' * x⁻¹)) ∷ (a' * x⁻¹ , b' * x' + x' * a) ∷ t)
    ≡⟨ Eq.sym (lemma-CZ^' x' a b (a' * x⁻¹) (b' * x') t) ⟩
  act (CZ^ (x ^1)) ((a , b) ∷ (a' * x⁻¹ , b' * x') ∷ t)
    ≡⟨ Eq.sym (Eq.cong (λ z → act (CZ^ (x ^1)) ((a , b) ∷ z))
                       (lemma-M x a' b' t)) ⟩
  act (CZ^ (x ^1)) ((a , b) ∷ act (M x) ((a' , b') ∷ t))
    ≡⟨ Eq.cong (act (CZ^ (x ^1)))
               (Eq.sym (act-↑ (M x) (a , b) ((a' , b') ∷ t))) ⟩
  act (CZ^ (x ^1) • M x ↑) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  x'  = x .proj₁
  x⁻¹ = (x ⁻¹) .proj₁
  aux : (b' + a) * x' ≡ b' * x' + x' * a
  aux = Eq.trans (*-distribʳ-+ x' b' a)
                 (Eq.cong (b' * x' +_) (*-comm a x'))

sound-semi-M↓CZ : ∀ (x : ℤ* ₚ) (q : Pauli (₂₊ n)) →
                  act (M x ↓ • CZ) q ≡ act (CZ^ (x ^1) • M x ↓) q
sound-semi-M↓CZ x ((a , b) ∷ (a' , b') ∷ t) = begin
  act (M x ↓ • CZ) ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ lemma-M x a (b + a') ((a' , b' + a) ∷ t) ⟩
  ((a * x⁻¹ , (b + a') * x') ∷ (a' , b' + a) ∷ t)
    ≡⟨ Eq.cong₂ (λ z z' → (a * x⁻¹ , z) ∷ (a' , b' + z') ∷ t)
         aux (Eq.sym (scale-cancel x a)) ⟩
  ((a * x⁻¹ , b * x' + x' * a') ∷ (a' , b' + x' * (a * x⁻¹)) ∷ t)
    ≡⟨ Eq.sym (lemma-CZ^' x' (a * x⁻¹) (b * x') a' b' t) ⟩
  act (CZ^ (x ^1)) ((a * x⁻¹ , b * x') ∷ (a' , b') ∷ t)
    ≡⟨ Eq.sym (Eq.cong (act (CZ^ (x ^1)))
                       (lemma-M x a b ((a' , b') ∷ t))) ⟩
  act (CZ^ (x ^1) • M x ↓) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  x'  = x .proj₁
  x⁻¹ = (x ⁻¹) .proj₁
  aux : (b + a') * x' ≡ b * x' + x' * a'
  aux = Eq.trans (*-distribʳ-+ x' b a')
                 (Eq.cong (b * x' +_) (*-comm a' x'))

------------------------------------------------------------------------
-- The inverse shear
--
-- S⁻¹ is S ^ p-1, and p is ₁₊ p-1 definitionally, so mult p-1 is - ₁:
-- one step short of the full cycle.

private
  mult-p-1 : mult p-1 ≡ - ₁
  mult-p-1 = begin
    mult p-1              ≡⟨ Eq.sym (+-identityˡ (mult p-1)) ⟩
    ₀ + mult p-1          ≡⟨ Eq.cong (_+ mult p-1) (Eq.sym (+-inverseˡ ₁)) ⟩
    (- ₁ + ₁) + mult p-1  ≡⟨ +-assoc (- ₁) ₁ (mult p-1) ⟩
    - ₁ + (₁ + mult p-1)  ≡⟨ Eq.cong (- ₁ +_) mult-p ⟩
    - ₁ + ₀               ≡⟨ +-identityʳ (- ₁) ⟩
    - ₁                   ∎
    where open ≡-Reasoning

act-S⁻¹ : ∀ a b (t : Pauli n) → act S⁻¹ ((a , b) ∷ t) ≡ (a , b + - a) ∷ t
act-S⁻¹ a b t = begin
  act (S ^ p-1) ((a , b) ∷ t)  ≡⟨ lemma-S^ p-1 a b t ⟩
  ((a , b + mult p-1 * a) ∷ t) ≡⟨ Eq.cong (λ z → (a , b + z * a) ∷ t) mult-p-1 ⟩
  ((a , b + - ₁ * a) ∷ t)      ≡⟨ Eq.cong (λ z → (a , b + z) ∷ t) neg-one ⟩
  ((a , b + - a) ∷ t)          ∎
  where
  open ≡-Reasoning
  neg-one : - ₁ * a ≡ - a
  neg-one = Eq.trans (Eq.sym (-‿distribˡ-* ₁ a)) (Eq.cong -_ (*-identityˡ a))

------------------------------------------------------------------------
-- The Selinger rules

-- Two CZs on overlapping pairs commute: each adds to a different
-- wire's Z-exponent, and the middle wire receives both.
sound-c12 : ∀ (q : Pauli (₃₊ n)) → act (CZ ↑ • CZ) q ≡ act (CZ • CZ ↑) q
sound-c12 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) =
  Eq.cong (λ z → (a , b + a') ∷ (a' , z) ∷ (a'' , b'' + a') ∷ t)
          (swap-add b' a a'')

private
  -- Rearranging four summands in the commutative group.
  rearr4 : ∀ (w x y z : ℤ ₚ) → (w + x) + (y + z) ≡ (w + z) + (y + x)
  rearr4 w x y z = begin
    (w + x) + (y + z) ≡⟨ +-assoc w x (y + z) ⟩
    w + (x + (y + z)) ≡⟨ Eq.cong (w +_) (Eq.sym (+-assoc x y z)) ⟩
    w + ((x + y) + z) ≡⟨ Eq.cong (λ u → w + (u + z)) (+-comm x y) ⟩
    w + ((y + x) + z) ≡⟨ Eq.cong (w +_) (+-comm (y + x) z) ⟩
    w + (z + (y + x)) ≡⟨ Eq.sym (+-assoc w z (y + x)) ⟩
    (w + z) + (y + x) ∎
    where open ≡-Reasoning

  -- (a' + a) + (b' + - a') ≡ a + b'
  mid-X : ∀ (a a' b' : ℤ ₚ) → (a' + a) + (b' + - a') ≡ a + b'
  mid-X a a' b' = begin
    (a' + a) + (b' + - a') ≡⟨ +-assoc a' a (b' + - a') ⟩
    a' + (a + (b' + - a')) ≡⟨ Eq.cong (a' +_) (Eq.sym (+-assoc a b' (- a'))) ⟩
    a' + ((a + b') + - a') ≡⟨ Eq.cong (a' +_) (+-comm (a + b') (- a')) ⟩
    a' + (- a' + (a + b')) ≡⟨ Eq.sym (+-assoc a' (- a') (a + b')) ⟩
    (a' + - a') + (a + b') ≡⟨ Eq.cong (_+ (a + b')) (+-inverseʳ a') ⟩
    ₀ + (a + b')           ≡⟨ +-identityˡ (a + b') ⟩
    a + b'                 ∎
    where open ≡-Reasoning

  -- (- b' + a') + (b' + a) ≡ a' + a
  mid-Z : ∀ (a a' b' : ℤ ₚ) → (- b' + a') + (b' + a) ≡ a' + a
  mid-Z a a' b' = begin
    (- b' + a') + (b' + a) ≡⟨ +-assoc (- b') a' (b' + a) ⟩
    - b' + (a' + (b' + a)) ≡⟨ Eq.cong (- b' +_) (Eq.sym (+-assoc a' b' a)) ⟩
    - b' + ((a' + b') + a) ≡⟨ Eq.cong (λ u → - b' + (u + a)) (+-comm a' b') ⟩
    - b' + ((b' + a') + a) ≡⟨ Eq.cong (- b' +_) (+-assoc b' a' a) ⟩
    - b' + (b' + (a' + a)) ≡⟨ Eq.sym (+-assoc (- b') b' (a' + a)) ⟩
    (- b' + b') + (a' + a) ≡⟨ Eq.cong (_+ (a' + a)) (+-inverseˡ b') ⟩
    ₀ + (a' + a)           ≡⟨ +-identityˡ (a' + a) ⟩
    a' + a                 ∎
    where open ≡-Reasoning

-- Conjugating CZ by H on the upper wire.  Both sides send
-- (a , b) (a' , b') to (a , b + a' - b' - a) (- b' - a , a' + a); the
-- right-hand side gets there through four shears.
sound-c10 : ∀ (q : Pauli (₂₊ n)) →
            act (CZ • H ↑ • CZ) q
              ≡ act (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) q
sound-c10 ((a , b) ∷ (a' , b') ∷ t) = Eq.sym (begin
  act (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)
      ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.cong (act (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑))
               (act-S⁻¹ a b ((a' , b') ∷ t)) ⟩
  act (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑)
      ((a , b + - a) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.cong (act (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑))
               (Eq.trans (act-↑ S⁻¹ (a , b + - a) ((a' , b') ∷ t))
                         (Eq.cong (λ z → (a , b + - a) ∷ z)
                                  (act-S⁻¹ a' b' t))) ⟩
  act (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑)
      ((a , b + - a) ∷ (a' , b' + - a') ∷ t)
    ≡⟨ Eq.cong (act (S⁻¹ ↑ • H ↑))
               (Eq.trans (act-↑ S⁻¹ (a , (b + - a) + - (b' + - a'))
                                    ((- (b' + - a') , a' + a) ∷ t))
                         (Eq.cong (λ z → (a , (b + - a) + - (b' + - a')) ∷ z)
                                  (act-S⁻¹ (- (b' + - a')) (a' + a) t))) ⟩
  act (S⁻¹ ↑ • H ↑)
      ((a , (b + - a) + - (b' + - a'))
        ∷ (- (b' + - a') , (a' + a) + - - (b' + - a')) ∷ t)
    ≡⟨ Eq.trans (act-↑ S⁻¹ (a , (b + - a) + - (b' + - a'))
                           (act H ((- (b' + - a') , (a' + a) + - - (b' + - a')) ∷ t)))
                (Eq.cong (λ z → (a , (b + - a) + - (b' + - a')) ∷ z)
                         (act-S⁻¹ (- ((a' + a) + - - (b' + - a')))
                                  (- (b' + - a')) t)) ⟩
  ((a , (b + - a) + - (b' + - a'))
    ∷ ( - ((a' + a) + - - (b' + - a'))
      , - (b' + - a') + - - ((a' + a) + - - (b' + - a'))) ∷ t)
    ≡⟨ Eq.cong₂ (λ u v → (a , u) ∷ v ∷ t) fstZ sndPair ⟩
  ((a , (b + a') + - (b' + a)) ∷ (- (b' + a) , a' + a) ∷ t) ∎)
  where
  open ≡-Reasoning

  -- The upper wire's X-slot, - ((a' + a) + - - (b' + - a')), is - (b' + a).
  X≡ : - ((a' + a) + - - (b' + - a')) ≡ - (b' + a)
  X≡ = begin
    - ((a' + a) + - - (b' + - a'))
      ≡⟨ Eq.cong (λ z → - ((a' + a) + z)) (-‿involutive (b' + - a')) ⟩
    - ((a' + a) + (b' + - a')) ≡⟨ Eq.cong -_ (mid-X a a' b') ⟩
    - (a + b')                 ≡⟨ Eq.cong -_ (+-comm a b') ⟩
    - (b' + a)                 ∎

  fstZ : (b + - a) + - (b' + - a') ≡ (b + a') + - (b' + a)
  fstZ = begin
    (b + - a) + - (b' + - a') ≡⟨ Eq.cong ((b + - a) +_) (neg-sub b' a') ⟩
    (b + - a) + (- b' + a')   ≡⟨ rearr4 b (- a) (- b') a' ⟩
    (b + a') + (- b' + - a)   ≡⟨ Eq.cong ((b + a') +_) (-‿+-comm b' a) ⟩
    (b + a') + - (b' + a)     ∎

  sndZ : - (b' + - a') + - - ((a' + a) + - - (b' + - a')) ≡ a' + a
  sndZ = begin
    - (b' + - a') + - - ((a' + a) + - - (b' + - a'))
      ≡⟨ Eq.cong (- (b' + - a') +_) (-‿involutive ((a' + a) + - - (b' + - a'))) ⟩
    - (b' + - a') + ((a' + a) + - - (b' + - a'))
      ≡⟨ Eq.cong₂ _+_ (neg-sub b' a')
           (Eq.trans (Eq.cong (λ z → (a' + a) + z) (-‿involutive (b' + - a')))
                     (Eq.trans (mid-X a a' b') (+-comm a b'))) ⟩
    (- b' + a') + (b' + a) ≡⟨ mid-Z a a' b' ⟩
    a' + a                 ∎

  sndPair : ( - ((a' + a) + - - (b' + - a'))
            , - (b' + - a') + - - ((a' + a) + - - (b' + - a')))
            ≡ (- (b' + a) , a' + a)
  sndPair = Eq.cong₂ _,_ X≡ sndZ

-- The mirror image of c10, conjugating CZ by H on the lower wire.  The
-- helpers are the same ones with the two wires exchanged.
sound-c11 : ∀ (q : Pauli (₂₊ n)) →
            act (CZ • H ↓ • CZ) q
              ≡ act (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) q
sound-c11 ((a , b) ∷ (a' , b') ∷ t) = Eq.sym (begin
  act (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)
      ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.cong (act (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓))
               (Eq.trans (act-↑ S⁻¹ (a , b) ((a' , b') ∷ t))
                         (Eq.cong (λ z → (a , b) ∷ z) (act-S⁻¹ a' b' t))) ⟩
  act (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓)
      ((a , b) ∷ (a' , b' + - a') ∷ t)
    ≡⟨ Eq.cong (act (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓))
               (act-S⁻¹ a b ((a' , b' + - a') ∷ t)) ⟩
  act (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓)
      ((a , b + - a) ∷ (a' , b' + - a') ∷ t)
    ≡⟨ Eq.cong (act (S⁻¹ ↓ • H ↓))
               (act-S⁻¹ (- (b + - a)) (a + a')
                        ((a' , (b' + - a') + - (b + - a)) ∷ t)) ⟩
  act (S⁻¹ ↓ • H ↓)
      ((- (b + - a) , (a + a') + - - (b + - a))
        ∷ (a' , (b' + - a') + - (b + - a)) ∷ t)
    ≡⟨ act-S⁻¹ (- ((a + a') + - - (b + - a))) (- (b + - a))
               ((a' , (b' + - a') + - (b + - a)) ∷ t) ⟩
  (( - ((a + a') + - - (b + - a))
   , - (b + - a) + - - ((a + a') + - - (b + - a)))
     ∷ (a' , (b' + - a') + - (b + - a)) ∷ t)
    ≡⟨ Eq.cong₂ (λ u v → u ∷ (a' , v) ∷ t) fstPair sndZ ⟩
  ((- (b + a') , a + a') ∷ (a' , (b' + a) + - (b + a')) ∷ t) ∎)
  where
  open ≡-Reasoning

  X≡ : - ((a + a') + - - (b + - a)) ≡ - (b + a')
  X≡ = begin
    - ((a + a') + - - (b + - a))
      ≡⟨ Eq.cong (λ z → - ((a + a') + z)) (-‿involutive (b + - a)) ⟩
    - ((a + a') + (b + - a)) ≡⟨ Eq.cong -_ (mid-X a' a b) ⟩
    - (a' + b)               ≡⟨ Eq.cong -_ (+-comm a' b) ⟩
    - (b + a')               ∎

  fstZ : - (b + - a) + - - ((a + a') + - - (b + - a)) ≡ a + a'
  fstZ = begin
    - (b + - a) + - - ((a + a') + - - (b + - a))
      ≡⟨ Eq.cong (- (b + - a) +_) (-‿involutive ((a + a') + - - (b + - a))) ⟩
    - (b + - a) + ((a + a') + - - (b + - a))
      ≡⟨ Eq.cong₂ _+_ (neg-sub b a)
           (Eq.trans (Eq.cong (λ z → (a + a') + z) (-‿involutive (b + - a)))
                     (Eq.trans (mid-X a' a b) (+-comm a' b))) ⟩
    (- b + a) + (b + a') ≡⟨ mid-Z a' a b ⟩
    a + a'               ∎

  fstPair : ( - ((a + a') + - - (b + - a))
            , - (b + - a) + - - ((a + a') + - - (b + - a)))
            ≡ (- (b + a') , a + a')
  fstPair = Eq.cong₂ _,_ X≡ fstZ

  sndZ : (b' + - a') + - (b + - a) ≡ (b' + a) + - (b + a')
  sndZ = begin
    (b' + - a') + - (b + - a) ≡⟨ Eq.cong ((b' + - a') +_) (neg-sub b a) ⟩
    (b' + - a') + (- b + a)   ≡⟨ rearr4 b' (- a') (- b) a ⟩
    (b' + a) + (- b + - a')   ≡⟨ Eq.cong ((b' + a) +_) (-‿+-comm b a') ⟩
    (b' + a) + - (b + a')     ∎

------------------------------------------------------------------------
-- The compound two-wire words
--
-- ₕ|ₕ = H CZ H on the lower wire and ʰ|ʰ = H CZ H on the upper one are
-- the CX-like gates; ⊥⊤ and ⊤⊥ are their two products.  Closed forms
-- for all four, so that c13 to c15 — which are built entirely from them
-- — can be computed without unfolding to twenty-odd letters.

-- Both single ones are already in normal form.
act-ₕ|ₕ : ∀ a b a' b' (t : Pauli n) →
          act ₕ|ₕ ((a , b) ∷ (a' , b') ∷ t)
            ≡ (- (a + a') , - b) ∷ (a' , b' + - b) ∷ t
act-ₕ|ₕ a b a' b' t = Eq.refl

act-ʰ|ʰ : ∀ a b a' b' (t : Pauli n) →
          act ʰ|ʰ ((a , b) ∷ (a' , b') ∷ t)
            ≡ (a , b + - b') ∷ (- (a' + a) , - b') ∷ t
act-ʰ|ʰ a b a' b' t = Eq.refl

private
  -- a + - (a' + a) ≡ - a'
  cancel-mid : ∀ (a a' : ℤ ₚ) → a + - (a' + a) ≡ - a'
  cancel-mid a a' = begin
    a + - (a' + a)  ≡⟨ Eq.cong (a +_) (Eq.sym (-‿+-comm a' a)) ⟩
    a + (- a' + - a) ≡⟨ Eq.sym (+-assoc a (- a') (- a)) ⟩
    (a + - a') + - a ≡⟨ Eq.cong (_+ - a) (+-comm a (- a')) ⟩
    (- a' + a) + - a ≡⟨ +-assoc (- a') a (- a) ⟩
    - a' + (a + - a) ≡⟨ Eq.cong (- a' +_) (+-inverseʳ a) ⟩
    - a' + ₀         ≡⟨ +-identityʳ (- a') ⟩
    - a'             ∎
    where open ≡-Reasoning

  -- - y + (- x + y) ≡ - x
  cancel-out : ∀ (x y : ℤ ₚ) → - y + (- x + y) ≡ - x
  cancel-out x y = begin
    - y + (- x + y) ≡⟨ Eq.cong (- y +_) (+-comm (- x) y) ⟩
    - y + (y + - x) ≡⟨ Eq.sym (+-assoc (- y) y (- x)) ⟩
    (- y + y) + - x ≡⟨ Eq.cong (_+ - x) (+-inverseˡ y) ⟩
    ₀ + - x         ≡⟨ +-identityˡ (- x) ⟩
    - x             ∎
    where open ≡-Reasoning

act-⊥⊤ : ∀ a b a' b' (t : Pauli n) →
         act ⊥⊤ ((a , b) ∷ (a' , b') ∷ t)
           ≡ (a' , - b + b') ∷ (- (a' + a) , - b) ∷ t
act-⊥⊤ a b a' b' t = begin
  act ⊥⊤ ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.cong (act ₕ|ₕ) (act-ʰ|ʰ a b a' b' t) ⟩
  act ₕ|ₕ ((a , b + - b') ∷ (- (a' + a) , - b') ∷ t)
    ≡⟨ act-ₕ|ₕ a (b + - b') (- (a' + a)) (- b') t ⟩
  (( - (a + - (a' + a)) , - (b + - b'))
    ∷ (- (a' + a) , - b' + - (b + - b')) ∷ t)
    ≡⟨ Eq.cong₂ (λ u v → u ∷ (- (a' + a) , v) ∷ t)
         (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (cancel-mid a a'))
                                 (-‿involutive a'))
                       (neg-sub b b'))
         (Eq.trans (Eq.cong (- b' +_) (neg-sub b b')) (cancel-out b b')) ⟩
  ((a' , - b + b') ∷ (- (a' + a) , - b) ∷ t) ∎
  where open ≡-Reasoning

act-⊤⊥ : ∀ a b a' b' (t : Pauli n) →
         act ⊤⊥ ((a , b) ∷ (a' , b') ∷ t)
           ≡ (- (a + a') , - b') ∷ (a , - b' + b) ∷ t
act-⊤⊥ a b a' b' t = begin
  act ⊤⊥ ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.cong (act ʰ|ʰ) (act-ₕ|ₕ a b a' b' t) ⟩
  act ʰ|ʰ ((- (a + a') , - b) ∷ (a' , b' + - b) ∷ t)
    ≡⟨ act-ʰ|ʰ (- (a + a')) (- b) a' (b' + - b) t ⟩
  (( - (a + a') , - b + - (b' + - b))
    ∷ (- (a' + - (a + a')) , - (b' + - b)) ∷ t)
    ≡⟨ Eq.cong₂ (λ u v → (- (a + a') , u) ∷ v ∷ t)
         (Eq.trans (Eq.cong (- b +_) (neg-sub b' b)) (cancel-out b' b))
         (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (cancel-mid a' a))
                                 (-‿involutive a))
                       (neg-sub b' b)) ⟩
  ((- (a + a') , - b') ∷ (a , - b' + b) ∷ t) ∎
  where open ≡-Reasoning

private
  -- x + - (x + y) ≡ - y, the other association of cancel-mid.
  cancel-mid₂ : ∀ (x y : ℤ ₚ) → x + - (x + y) ≡ - y
  cancel-mid₂ x y =
    Eq.trans (Eq.cong (λ z → x + - z) (+-comm x y)) (cancel-mid x y)

  -- x + ((- x + y) + z) ≡ y + z
  absorb : ∀ (x y z : ℤ ₚ) → x + ((- x + y) + z) ≡ y + z
  absorb x y z = begin
    x + ((- x + y) + z) ≡⟨ Eq.sym (+-assoc x (- x + y) z) ⟩
    (x + (- x + y)) + z ≡⟨ Eq.cong (_+ z) (Eq.sym (+-assoc x (- x) y)) ⟩
    ((x + - x) + y) + z ≡⟨ Eq.cong (λ u → (u + y) + z) (+-inverseʳ x) ⟩
    (₀ + y) + z         ≡⟨ Eq.cong (_+ z) (+-identityˡ y) ⟩
    y + z               ∎
    where open ≡-Reasoning

-- Both sides are CZ between wires 0 and 2, built two different ways.
sound-c13 : ∀ (q : Pauli (₃₊ n)) →
            act (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) q ≡ act (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) q
sound-c13 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = Eq.trans lhs (Eq.sym rhs)
  where
  open ≡-Reasoning

  C : Pauli (₃₊ _)
  C = (a , b + a'') ∷ (a' , b') ∷ (a'' , b'' + a) ∷ t

  lhs : act (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡ C
  lhs = begin
    act (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
      ≡⟨ Eq.cong (act (⊤⊥ ↑ • CZ ↓))
           (Eq.trans (act-↑ ⊥⊤ (a , b) ((a' , b') ∷ (a'' , b'') ∷ t))
                     (Eq.cong (λ z → (a , b) ∷ z)
                              (act-⊥⊤ a' b' a'' b'' t))) ⟩
    act (⊤⊥ ↑ • CZ ↓)
        ((a , b) ∷ (a'' , - b' + b'') ∷ (- (a'' + a') , - b') ∷ t)
      ≡⟨ act-↑ ⊤⊥ (a , b + a'')
               ((a'' , (- b' + b'') + a) ∷ (- (a'' + a') , - b') ∷ t) ⟩
    ((a , b + a'')
      ∷ act ⊤⊥ ((a'' , (- b' + b'') + a) ∷ (- (a'' + a') , - b') ∷ t))
      ≡⟨ Eq.cong (λ z → (a , b + a'') ∷ z)
           (act-⊤⊥ a'' ((- b' + b'') + a) (- (a'' + a')) (- b') t) ⟩
    ((a , b + a'')
      ∷ (- (a'' + - (a'' + a')) , - - b')
      ∷ (a'' , - - b' + ((- b' + b'') + a)) ∷ t)
      ≡⟨ Eq.cong₂ (λ u v → (a , b + a'') ∷ u ∷ (a'' , v) ∷ t)
           (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (cancel-mid₂ a'' a'))
                                   (-‿involutive a'))
                         (-‿involutive b'))
           (Eq.trans (Eq.cong (λ z → z + ((- b' + b'') + a))
                              (-‿involutive b'))
                     (absorb b' b'' a)) ⟩
    C ∎

  rhs : act (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡ C
  rhs = begin
    act (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
      ≡⟨ Eq.cong (act (⊥⊤ ↓ • CZ ↑)) (act-⊤⊥ a b a' b' ((a'' , b'') ∷ t)) ⟩
    act (⊥⊤ ↓ • CZ ↑)
        ((- (a + a') , - b') ∷ (a , - b' + b) ∷ (a'' , b'') ∷ t)
      ≡⟨ Eq.cong (act ⊥⊤)
           (act-↑ CZ (- (a + a') , - b') ((a , - b' + b) ∷ (a'' , b'') ∷ t)) ⟩
    act ⊥⊤ ((- (a + a') , - b')
             ∷ (a , (- b' + b) + a'') ∷ (a'' , b'' + a) ∷ t)
      ≡⟨ act-⊥⊤ (- (a + a')) (- b') a ((- b' + b) + a'') ((a'' , b'' + a) ∷ t) ⟩
    ((a , - - b' + ((- b' + b) + a''))
      ∷ (- (a + - (a + a')) , - - b') ∷ (a'' , b'' + a) ∷ t)
      ≡⟨ Eq.cong₂ (λ u v → (a , u) ∷ v ∷ (a'' , b'' + a) ∷ t)
           (Eq.trans (Eq.cong (λ z → z + ((- b' + b) + a''))
                              (-‿involutive b'))
                     (absorb b' b a''))
           (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (cancel-mid₂ a a'))
                                   (-‿involutive a'))
                         (-‿involutive b')) ⟩
    C ∎

------------------------------------------------------------------------
-- The factors that c14 and c15 cube
--
-- Closed forms for one application, so that the cube can be taken three
-- of these at a time rather than by unfolding twenty-one letters.

act-⊤⊥↑CZ : ∀ a b a' b' a'' b'' (t : Pauli n) →
            act (⊤⊥ ↑ • CZ ↓) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
              ≡ (a , b + a')
                ∷ (- (a' + a'') , - b'')
                ∷ (a' , - b'' + (b' + a)) ∷ t
act-⊤⊥↑CZ a b a' b' a'' b'' t =
  Eq.trans (act-↑ ⊤⊥ (a , b + a') ((a' , b' + a) ∷ (a'' , b'') ∷ t))
           (Eq.cong (λ z → (a , b + a') ∷ z)
                    (act-⊤⊥ a' (b' + a) a'' b'' t))

act-⊥⊤↓CZ↑ : ∀ a b a' b' a'' b'' (t : Pauli n) →
             act (⊥⊤ ↓ • CZ ↑) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
               ≡ (a' , - b + (b' + a''))
                 ∷ (- (a' + a) , - b)
                 ∷ (a'' , b'' + a') ∷ t
act-⊥⊤↓CZ↑ a b a' b' a'' b'' t =
  Eq.trans (Eq.cong (act ⊥⊤)
                    (act-↑ CZ (a , b) ((a' , b') ∷ (a'' , b'') ∷ t)))
           (act-⊥⊤ a b a' (b' + a'') ((a'' , b'' + a') ∷ t))

private
  -- (b + x) + - (x + y) ≡ b + - y
  shift-cancel : ∀ (b x y : ℤ ₚ) → (b + x) + - (x + y) ≡ b + - y
  shift-cancel b x y = begin
    (b + x) + - (x + y)   ≡⟨ Eq.cong ((b + x) +_) (Eq.sym (-‿+-comm x y)) ⟩
    (b + x) + (- x + - y) ≡⟨ rearr4 b x (- x) (- y) ⟩
    (b + - y) + (- x + x) ≡⟨ Eq.cong ((b + - y) +_) (+-inverseˡ x) ⟩
    (b + - y) + ₀         ≡⟨ +-identityʳ (b + - y) ⟩
    b + - y               ∎
    where open ≡-Reasoning

  -- - (x + y) + x ≡ - y
  neg-sum-cancel : ∀ (x y : ℤ ₚ) → - (x + y) + x ≡ - y
  neg-sum-cancel x y = begin
    - (x + y) + x   ≡⟨ Eq.cong (_+ x) (Eq.sym (-‿+-comm x y)) ⟩
    (- x + - y) + x ≡⟨ +-assoc (- x) (- y) x ⟩
    - x + (- y + x) ≡⟨ Eq.cong (- x +_) (+-comm (- y) x) ⟩
    - x + (x + - y) ≡⟨ Eq.sym (+-assoc (- x) x (- y)) ⟩
    (- x + x) + - y ≡⟨ Eq.cong (_+ - y) (+-inverseˡ x) ⟩
    ₀ + - y         ≡⟨ +-identityˡ (- y) ⟩
    - y             ∎
    where open ≡-Reasoning

  -- - (- x + (y + z)) ≡ (x + - y) + - z
  neg-mix2 : ∀ (x y z : ℤ ₚ) → - (- x + (y + z)) ≡ (x + - y) + - z
  neg-mix2 x y z = begin
    - (- x + (y + z))   ≡⟨ Eq.sym (-‿+-comm (- x) (y + z)) ⟩
    - - x + - (y + z)   ≡⟨ Eq.cong (_+ - (y + z)) (-‿involutive x) ⟩
    x + - (y + z)       ≡⟨ Eq.cong (x +_) (Eq.sym (-‿+-comm y z)) ⟩
    x + (- y + - z)     ≡⟨ Eq.sym (+-assoc x (- y) (- z)) ⟩
    (x + - y) + - z     ∎
    where open ≡-Reasoning

  -- (b + - x) + x ≡ b
  add-cancel : ∀ (b x : ℤ ₚ) → (b + - x) + x ≡ b
  add-cancel b x = begin
    (b + - x) + x ≡⟨ +-assoc b (- x) x ⟩
    b + (- x + x) ≡⟨ Eq.cong (b +_) (+-inverseˡ x) ⟩
    b + ₀         ≡⟨ +-identityʳ b ⟩
    b             ∎
    where open ≡-Reasoning

  -- (x + - y) + - x ≡ - y
  drop-x : ∀ (x y : ℤ ₚ) → (x + - y) + - x ≡ - y
  drop-x x y = begin
    (x + - y) + - x ≡⟨ +-assoc x (- y) (- x) ⟩
    x + (- y + - x) ≡⟨ Eq.cong (x +_) (+-comm (- y) (- x)) ⟩
    x + (- x + - y) ≡⟨ Eq.sym (+-assoc x (- x) (- y)) ⟩
    (x + - x) + - y ≡⟨ Eq.cong (_+ - y) (+-inverseʳ x) ⟩
    ₀ + - y         ≡⟨ +-identityˡ (- y) ⟩
    - y             ∎
    where open ≡-Reasoning

  -- ((x + - y) + - z) + (- x + z) ≡ - y
  cross-cancel : ∀ (x y z : ℤ ₚ) → ((x + - y) + - z) + (- x + z) ≡ - y
  cross-cancel x y z = begin
    ((x + - y) + - z) + (- x + z) ≡⟨ +-assoc (x + - y) (- z) (- x + z) ⟩
    (x + - y) + (- z + (- x + z)) ≡⟨ Eq.cong ((x + - y) +_) (cancel-out x z) ⟩
    (x + - y) + - x               ≡⟨ drop-x x y ⟩
    - y                           ∎
    where open ≡-Reasoning

  -- x + (y + - x) ≡ y
  absorb' : ∀ (x y : ℤ ₚ) → x + (y + - x) ≡ y
  absorb' x y = begin
    x + (y + - x) ≡⟨ Eq.cong (x +_) (+-comm y (- x)) ⟩
    x + (- x + y) ≡⟨ Eq.sym (+-assoc x (- x) y) ⟩
    (x + - x) + y ≡⟨ Eq.cong (_+ y) (+-inverseʳ x) ⟩
    ₀ + y         ≡⟨ +-identityˡ y ⟩
    y             ∎
    where open ≡-Reasoning

-- Cubing ⊤⊥↑ CZ is the identity.  The X-slots permute as
-- a , a' + a'' , a' and the Z-slots pick up shears; three rounds bring
-- every wire back.
sound-c14 : ∀ (q : Pauli (₃₊ n)) → act ((⊤⊥ ↑ • CZ ↓) ^ 3) q ≡ q
sound-c14 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = begin
  act ((⊤⊥ ↑ • CZ ↓) ^ 3) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
    ≡⟨ Eq.cong (λ z → act (⊤⊥ ↑ • CZ ↓) (act (⊤⊥ ↑ • CZ ↓) z))
               (act-⊤⊥↑CZ a b a' b' a'' b'' t) ⟩
  act (⊤⊥ ↑ • CZ ↓) (act (⊤⊥ ↑ • CZ ↓) S1)
    ≡⟨ Eq.cong (act (⊤⊥ ↑ • CZ ↓)) round2 ⟩
  act (⊤⊥ ↑ • CZ ↓) S2
    ≡⟨ round3 ⟩
  ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎
  where
  open ≡-Reasoning

  S1 : Pauli (₃₊ _)
  S1 = (a , b + a') ∷ (- (a' + a'') , - b'') ∷ (a' , - b'' + (b' + a)) ∷ t

  S2 : Pauli (₃₊ _)
  S2 = (a , b + - a'')
        ∷ (a'' , (b'' + - b') + - a)
        ∷ (- (a' + a'') , - b') ∷ t

  round2 : act (⊤⊥ ↑ • CZ ↓) S1 ≡ S2
  round2 = begin
    act (⊤⊥ ↑ • CZ ↓) S1
      ≡⟨ act-⊤⊥↑CZ a (b + a') (- (a' + a'')) (- b'') a'
                   (- b'' + (b' + a)) t ⟩
    ((a , (b + a') + - (a' + a''))
      ∷ (- (- (a' + a'') + a') , - (- b'' + (b' + a)))
      ∷ (- (a' + a'') , - (- b'' + (b' + a)) + (- b'' + a)) ∷ t)
      ≡⟨ Eq.cong₂ (λ u v → (a , u) ∷ v
                             ∷ (- (a' + a'')
                               , - (- b'' + (b' + a)) + (- b'' + a)) ∷ t)
           (shift-cancel b a' a'')
           (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (neg-sum-cancel a' a''))
                                   (-‿involutive a''))
                         (neg-mix2 b'' b' a)) ⟩
    ((a , b + - a'') ∷ (a'' , (b'' + - b') + - a)
      ∷ (- (a' + a'') , - (- b'' + (b' + a)) + (- b'' + a)) ∷ t)
      ≡⟨ Eq.cong (λ z → (a , b + - a'') ∷ (a'' , (b'' + - b') + - a)
                          ∷ (- (a' + a'') , z) ∷ t)
           (Eq.trans (Eq.cong (_+ (- b'' + a)) (neg-mix2 b'' b' a))
                     (cross-cancel b'' b' a)) ⟩
    S2 ∎

  round3 : act (⊤⊥ ↑ • CZ ↓) S2
             ≡ ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
  round3 = begin
    act (⊤⊥ ↑ • CZ ↓) S2
      ≡⟨ act-⊤⊥↑CZ a (b + - a'') a'' ((b'' + - b') + - a)
                   (- (a' + a'')) (- b') t ⟩
    ((a , (b + - a'') + a'')
      ∷ (- (a'' + - (a' + a'')) , - - b')
      ∷ (a'' , - - b' + (((b'' + - b') + - a) + a)) ∷ t)
      ≡⟨ Eq.cong₂ (λ u v → (a , u) ∷ v
                             ∷ (a'' , - - b' + (((b'' + - b') + - a) + a)) ∷ t)
           (add-cancel b a'')
           (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (cancel-mid a'' a'))
                                   (-‿involutive a'))
                         (-‿involutive b')) ⟩
    ((a , b) ∷ (a' , b')
      ∷ (a'' , - - b' + (((b'' + - b') + - a) + a)) ∷ t)
      ≡⟨ Eq.cong (λ z → (a , b) ∷ (a' , b') ∷ (a'' , z) ∷ t)
           (Eq.trans (Eq.cong₂ _+_ (-‿involutive b')
                                   (add-cancel (b'' + - b') a))
                     (absorb' b' b'')) ⟩
    ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎

-- The mirror of c14, on the other pair of wires.
sound-c15 : ∀ (q : Pauli (₃₊ n)) → act ((⊥⊤ ↓ • CZ ↑) ^ 3) q ≡ q
sound-c15 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = begin
  act ((⊥⊤ ↓ • CZ ↑) ^ 3) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
    ≡⟨ Eq.cong (λ z → act (⊥⊤ ↓ • CZ ↑) (act (⊥⊤ ↓ • CZ ↑) z))
               (act-⊥⊤↓CZ↑ a b a' b' a'' b'' t) ⟩
  act (⊥⊤ ↓ • CZ ↑) (act (⊥⊤ ↓ • CZ ↑) S1)
    ≡⟨ Eq.cong (act (⊥⊤ ↓ • CZ ↑)) round2 ⟩
  act (⊥⊤ ↓ • CZ ↑) S2
    ≡⟨ round3 ⟩
  ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎
  where
  open ≡-Reasoning

  S1 : Pauli (₃₊ _)
  S1 = (a' , - b + (b' + a''))
        ∷ (- (a' + a) , - b) ∷ (a'' , b'' + a') ∷ t

  S2 : Pauli (₃₊ _)
  S2 = (- (a' + a) , - b')
        ∷ (a , (b + - b') + - a'') ∷ (a'' , b'' + - a) ∷ t

  round2 : act (⊥⊤ ↓ • CZ ↑) S1 ≡ S2
  round2 = begin
    act (⊥⊤ ↓ • CZ ↑) S1
      ≡⟨ act-⊥⊤↓CZ↑ a' (- b + (b' + a'')) (- (a' + a)) (- b)
                    a'' (b'' + a') t ⟩
    (( - (a' + a) , - (- b + (b' + a'')) + (- b + a''))
      ∷ (- (- (a' + a) + a') , - (- b + (b' + a'')))
      ∷ (a'' , (b'' + a') + - (a' + a)) ∷ t)
      ≡⟨ Eq.cong₂ (λ u v → u ∷ v ∷ (a'' , (b'' + a') + - (a' + a)) ∷ t)
           (Eq.cong₂ _,_ Eq.refl
              (Eq.trans (Eq.cong (_+ (- b + a'')) (neg-mix2 b b' a''))
                        (cross-cancel b b' a'')))
           (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (neg-sum-cancel a' a))
                                   (-‿involutive a))
                         (neg-mix2 b b' a'')) ⟩
    ((- (a' + a) , - b') ∷ (a , (b + - b') + - a'')
      ∷ (a'' , (b'' + a') + - (a' + a)) ∷ t)
      ≡⟨ Eq.cong (λ z → (- (a' + a) , - b') ∷ (a , (b + - b') + - a'')
                          ∷ (a'' , z) ∷ t)
           (shift-cancel b'' a' a) ⟩
    S2 ∎

  round3 : act (⊥⊤ ↓ • CZ ↑) S2
             ≡ ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t)
  round3 = begin
    act (⊥⊤ ↓ • CZ ↑) S2
      ≡⟨ act-⊥⊤↓CZ↑ (- (a' + a)) (- b') a ((b + - b') + - a'')
                    a'' (b'' + - a) t ⟩
    (( a , - - b' + (((b + - b') + - a'') + a''))
      ∷ (- (a + - (a' + a)) , - - b')
      ∷ (a'' , (b'' + - a) + a) ∷ t)
      ≡⟨ Eq.cong₂ (λ u v → u ∷ v ∷ (a'' , (b'' + - a) + a) ∷ t)
           (Eq.cong₂ _,_ Eq.refl
              (Eq.trans (Eq.cong₂ _+_ (-‿involutive b')
                                      (add-cancel (b + - b') a''))
                        (absorb' b' b)))
           (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ (cancel-mid a a'))
                                   (-‿involutive a'))
                         (-‿involutive b')) ⟩
    ((a , b) ∷ (a' , b') ∷ (a'' , (b'' + - a) + a) ∷ t)
      ≡⟨ Eq.cong (λ z → (a , b) ∷ (a' , b') ∷ (a'' , z) ∷ t)
           (add-cancel b'' a) ⟩
    ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎

------------------------------------------------------------------------
-- Soundness
--
-- Every raw relation of the plain presentation preserves the symplectic
-- action.  This is Transport.sound-ax, proved without leaving the plain
-- gate set: seventeen group-specific rules, two structural ones, and
-- the shift case, which is act-↑ either side of the induction
-- hypothesis.

sound-ax : ∀ {n} {w v : Circuit n} → n QRel, w === v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
sound-ax (srel Base.order-S)       = sound-order-S
sound-ax (srel Base.order-H)       = sound-order-H
sound-ax (srel Base.order-SH)      = sound-order-SH
sound-ax (srel Base.comm-HHS)      = sound-comm-HHS
sound-ax (srel (Base.M-mul x y))   = sound-M-mul x y
sound-ax (srel (Base.semi-MS x))   = sound-semi-MS x
sound-ax (srel (Base.semi-M↑CZ x)) = sound-semi-M↑CZ x
sound-ax (srel (Base.semi-M↓CZ x)) = sound-semi-M↓CZ x
sound-ax (srel Base.order-CZ)      = sound-order-CZ
sound-ax (srel Base.comm-CZ-S↓)    = sound-comm-CZ-S↓
sound-ax (srel Base.comm-CZ-S↑)    = sound-comm-CZ-S↑
sound-ax (srel Base.selinger-c10)  = sound-c10
sound-ax (srel Base.selinger-c11)  = sound-c11
sound-ax (srel Base.selinger-c12)  = sound-c12
sound-ax (srel Base.selinger-c13)  = sound-c13
sound-ax (srel Base.selinger-c14)  = sound-c14
sound-ax (srel Base.selinger-c15)  = sound-c15
sound-ax (comm₁ h g)               = sound-comm₁ h g
sound-ax (comm₂ h g)               = sound-comm₂ h g
sound-ax (cong↑ {w = w} {v = v} r) (q ∷ qs) =
  Eq.trans (act-↑ w q qs)
    (Eq.trans (Eq.cong (q ∷_) (sound-ax r qs))
              (Eq.sym (act-↑ v q qs)))
