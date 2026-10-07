------------------------------------------------------------------------
-- Presentations of groups
--
-- Evaluating circuits on symbolic labels
--
-- With p symbolic, the rules cannot be checked by computing tables;
-- they are checked by evaluating both sides on labels a ∷ b ∷ … ∷ x.
-- A word is evaluated letter by letter (•-at, ↑-at), each generator by
-- its operator, and an iterate w ^ᶠ k through two shapes:
--
--   a shear  (a ∷ y) ↦ (a + f y ∷ y)   — X, CX, and CX on wires 2, 0 —
--            iterates to (a + k f y ∷ y);
--   a diagonal circuit with phase φ iterates to the phase k φ.
--
-- Diagonal circuits (DiagC) compose by adding phases and shift by
-- reading the upper wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Soundness.Eval
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc ; _≤_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letter by letter

-- u after v.
•-at : {u v : Circuit n} {x y z : Labels n} {φ ψ : F} →
       ⟦ v ⟧ x ≡ (y , φ) → ⟦ u ⟧ y ≡ (z , ψ) → ⟦ u • v ⟧ x ≡ (z , φ + ψ)
•-at {u = u} {v} {x} {φ = φ} ev eu =
  trans (⟦⟧-• u v x)
    (trans (cong (λ q → proj₁ (⟦ u ⟧ (proj₁ q)) , proj₂ q + proj₂ (⟦ u ⟧ (proj₁ q))) ev)
           (cong (λ q → proj₁ q , φ + proj₂ q) eu))

-- A circuit shifted up a wire leaves wire 0.
↑-at : {w : Circuit n} {a : F} {x y : Labels n} {φ : F} →
       ⟦ w ⟧ x ≡ (y , φ) → ⟦ w ↑ ⟧ (a ∷ x) ≡ (a ∷ y , φ)
↑-at {w = w} {a} {x} e = trans (up-word w (a ∷ x)) (cong (λ q → a ∷ proj₁ q , proj₂ q) e)

-- Rewriting the result.
at-≡ : {w : Circuit n} {x y y′ : Labels n} {φ φ′ : F} →
       ⟦ w ⟧ x ≡ (y , φ) → y ≡ y′ → φ ≡ φ′ → ⟦ w ⟧ x ≡ (y′ , φ′)
at-≡ e refl refl = e

------------------------------------------------------------------------
-- The generators

X-at : (a : F) (x : Labels n) → ⟦ X ⟧ (a ∷ x) ≡ (a + 1F ∷ x , 0F)
X-at a x = ⟦⟧-gen (gate₁ X-gate) (a ∷ x)

M-at : (c : F) .(nz : c ≢ 0F) (a : F) (x : Labels n) → ⟦ M c nz ⟧ (a ∷ x) ≡ (c * a ∷ x , 0F)
M-at c nz a x = ⟦⟧-gen (gate₁ (M-gate c nz)) (a ∷ x)

CX-at : (a b : F) (x : Labels n) → ⟦ CX ⟧ (a ∷ b ∷ x) ≡ (a + b ∷ b ∷ x , 0F)
CX-at a b x = ⟦⟧-gen (gate₂ CX-gate) (a ∷ b ∷ x)

SWAP-at : (a b : F) (x : Labels n) → ⟦ SWAP ⟧ (a ∷ b ∷ x) ≡ (b ∷ a ∷ x , 0F)
SWAP-at a b x = ⟦⟧-gen (gate₂ SWAP-gate) (a ∷ b ∷ x)

ω-at : .(h : 1 ≤ lv) (x : Labels n) → ⟦ ω h ⟧ x ≡ (x , 1F)
ω-at h x = ⟦⟧-gen (gate₀ (ω-gate h)) x

Z-at : .(h : 1 ≤ lv) (a : F) (x : Labels n) → ⟦ Z h ⟧ (a ∷ x) ≡ (a ∷ x , a)
Z-at h a x = ⟦⟧-gen (gate₁ (Z-gate h)) (a ∷ x)

S-at : .(h : 2 ≤ lv) (a : F) (x : Labels n) → ⟦ S h ⟧ (a ∷ x) ≡ (a ∷ x , binom2 a)
S-at h a x = ⟦⟧-gen (gate₁ (S-gate h)) (a ∷ x)

T-at : .(h : 3 ≤ lv) (a : F) (x : Labels n) → ⟦ T h ⟧ (a ∷ x) ≡ (a ∷ x , binom3 a)
T-at h a x = ⟦⟧-gen (gate₁ (T-gate h)) (a ∷ x)

------------------------------------------------------------------------
-- Iterates

private
  ^ₒ-cong : {M N : Op n} → M ≐ N → (m : ℕ) → M ^ₒ m ≐ N ^ₒ m
  ^ₒ-cong e zero    = ≐-refl Idₒ
  ^ₒ-cong e (suc m) = ⊙-cong e (^ₒ-cong e m)

  -- k copies of 0 make 0, k copies of 1 make k.
  ×ᶠ-0 : (k : F) → toℕ k ×ᶠ 0F ≡ 0F
  ×ᶠ-0 k = trans (×ᶠ-toℕ k 0F) (FR.zeroʳ k)

  ×ᶠ-1 : (k : F) → toℕ k ×ᶠ 1F ≡ k
  ×ᶠ-1 k = trans (×ᶠ-toℕ k 1F) (FR.*-identityʳ k)

-- Shears: adding a function of the other wires to wire 0.
Shear : Op (₁₊ n) → (Labels n → F) → Set
Shear L f = ∀ a y → L (a ∷ y) ≡ (a + f y ∷ y , 0F)

^ₒ-shear : {L : Op (₁₊ n)} {f : Labels n → F} → Shear L f → (m : ℕ) →
           ∀ a y → (L ^ₒ m) (a ∷ y) ≡ (a + (m ×ᶠ f y) ∷ y , m ×ᶠ 0F)
^ₒ-shear s zero    a y = cong (λ b → b ∷ y , 0F) (sym (FR.+-identityʳ a))
^ₒ-shear {L = L} {f} s (suc m) a y = begin
  (L ⊙ L ^ₒ m) (a ∷ y)
    ≡⟨ cong (λ q → proj₁ (L (proj₁ q)) , proj₂ q + proj₂ (L (proj₁ q))) (^ₒ-shear s m a y) ⟩
  proj₁ (L (a + (m ×ᶠ f y) ∷ y)) , m ×ᶠ 0F + proj₂ (L (a + (m ×ᶠ f y) ∷ y))
    ≡⟨ cong (λ q → proj₁ q , m ×ᶠ 0F + proj₂ q) (s (a + (m ×ᶠ f y)) y) ⟩
  (a + (m ×ᶠ f y)) + f y ∷ y , m ×ᶠ 0F + 0F
    ≡⟨ cong₂ (λ b c → b ∷ y , c)
         (trans (FR.+-assoc a (m ×ᶠ f y) (f y)) (cong (a +_) (FR.+-comm (m ×ᶠ f y) (f y))))
         (trans (FR.+-identityʳ (m ×ᶠ 0F)) (sym (FR.+-identityˡ (m ×ᶠ 0F)))) ⟩
  a + (f y + (m ×ᶠ f y)) ∷ y , 0F + (m ×ᶠ 0F)
    ∎
  where open ≡-Reasoning

-- The iterate of a shear circuit, at a label k.
shear-^ᶠ : {w : Circuit (₁₊ n)} {f : Labels n → F} → Shear ⟦ w ⟧ f →
           (k a : F) (y : Labels n) → ⟦ w ^ᶠ k ⟧ (a ∷ y) ≡ (a + k * f y ∷ y , 0F)
shear-^ᶠ {w = w} {f} s k a y =
  trans (⟦⟧-^ w (toℕ k) (a ∷ y))
    (trans (^ₒ-shear s (toℕ k) a y)
      (cong₂ (λ b c → a + b ∷ y , c) (×ᶠ-toℕ k (f y)) (×ᶠ-0 k)))

X-shear : Shear (⟦ X {n} ⟧) (λ _ → 1F)
X-shear = X-at

CX-shear : Shear (⟦ CX {n} ⟧) head
CX-shear a (b ∷ x) = CX-at a b x

-- CX from wire 2 to wire 0.
CX₂₀-at : (a b c : F) (x : Labels n) → ⟦ CX₂₀ ⟧ (a ∷ b ∷ c ∷ x) ≡ (a + c ∷ b ∷ c ∷ x , 0F)
CX₂₀-at a b c x =
  at-≡ (•-at (•-at (↑-at (SWAP-at b c x)) (CX-at a c (b ∷ x))) (↑-at (SWAP-at c b x)))
       refl (trans (FR.+-identityʳ _) (FR.+-identityʳ _))

CX₂₀-shear : Shear (⟦ CX₂₀ {n} ⟧) (λ y → head (tail y))
CX₂₀-shear a (b ∷ c ∷ x) = CX₂₀-at a b c x

Xᶠ-at : (k a : F) (x : Labels n) → ⟦ X ^ᶠ k ⟧ (a ∷ x) ≡ (a + k ∷ x , 0F)
Xᶠ-at k a x = at-≡ (shear-^ᶠ X-shear k a x) (cong (_∷ x) (cong (a +_) (FR.*-identityʳ k))) refl

CXᶠ-at : (k a b : F) (x : Labels n) → ⟦ CX ^ᶠ k ⟧ (a ∷ b ∷ x) ≡ (a + k * b ∷ b ∷ x , 0F)
CXᶠ-at k a b x = shear-^ᶠ CX-shear k a (b ∷ x)

CX₂₀ᶠ-at : (k a b c : F) (x : Labels n) → ⟦ CX₂₀ ^ᶠ k ⟧ (a ∷ b ∷ c ∷ x) ≡ (a + k * c ∷ b ∷ c ∷ x , 0F)
CX₂₀ᶠ-at k a b c x = shear-^ᶠ CX₂₀-shear k a (b ∷ c ∷ x)

------------------------------------------------------------------------
-- Diagonal circuits

DiagC : Circuit n → (Labels n → F) → Set
DiagC w φ = ∀ x → ⟦ w ⟧ x ≡ (x , φ x)

DiagC-• : {u v : Circuit n} {φ ψ : Labels n → F} → DiagC u φ → DiagC v ψ →
          DiagC (u • v) (λ x → ψ x + φ x)
DiagC-• du dv x = •-at (dv x) (du x)

DiagC-↑ : {w : Circuit n} {φ : Labels n → F} → DiagC w φ → DiagC (w ↑) (λ x → φ (tail x))
DiagC-↑ d (a ∷ x) = ↑-at (d x)

DiagC-ε : DiagC {n} ε (λ _ → 0F)
DiagC-ε x = ⟦⟧-ε x

DiagC-≡ : {w : Circuit n} {φ ψ : Labels n → F} → DiagC w φ → (∀ x → φ x ≡ ψ x) → DiagC w ψ
DiagC-≡ d e x = trans (d x) (cong (x ,_) (e x))

-- The iterate at a label k multiplies the phase by k.
DiagC-^ᶠ : {w : Circuit n} {φ : Labels n → F} → DiagC w φ → (k : F) → DiagC (w ^ᶠ k) (λ x → k * φ x)
DiagC-^ᶠ {w = w} {φ} d k x =
  trans (⟦⟧-^ w (toℕ k) x)
    (trans (^ₒ-diagonal {M = ⟦ w ⟧} {φ} d (toℕ k) x) (cong (x ,_) (×ᶠ-toℕ k (φ x))))

-- The iterate by a natural number m multiplies the phase by m.
DiagC-^ : {w : Circuit n} {φ : Labels n → F} → DiagC w φ → (m : ℕ) → DiagC (w ^ m) (λ x → m ×ᶠ φ x)
DiagC-^ {w = w} {φ} d m x = trans (⟦⟧-^ w m x) (^ₒ-diagonal {M = ⟦ w ⟧} {φ} d m x)

-- Two evaluations of the same labels meet.
meet : {w v : Circuit n} {x y y′ : Labels n} {φ φ′ : F} →
       ⟦ w ⟧ x ≡ (y , φ) → ⟦ v ⟧ x ≡ (y′ , φ′) → y ≡ y′ → φ ≡ φ′ → ⟦ w ⟧ x ≡ ⟦ v ⟧ x
meet ew ev refl refl = trans ew (sym ev)

ω-diag : .(h : 1 ≤ lv) → DiagC {n} (ω h) (λ _ → 1F)
ω-diag h x = ω-at h x

Z-diag : .(h : 1 ≤ lv) → DiagC {₁₊ n} (Z h) head
Z-diag h (a ∷ x) = Z-at h a x

S-diag : .(h : 2 ≤ lv) → DiagC {₁₊ n} (S h) (λ x → binom2 (head x))
S-diag h (a ∷ x) = S-at h a x

T-diag : .(h : 3 ≤ lv) → DiagC {₁₊ n} (T h) (λ x → binom3 (head x))
T-diag h (a ∷ x) = T-at h a x

-- Conjugation by an involutive relabelling with no phase.
DiagC-conj : {σ w : Circuit n} {π : Labels n → Labels n} {φ : Labels n → F} →
             (∀ x → ⟦ σ ⟧ x ≡ (π x , 0F)) → (∀ x → π (π x) ≡ x) →
             DiagC w φ → DiagC (σ • w • σ) (λ x → φ (π x))
DiagC-conj {π = π} {φ} eσ inv d x =
  at-≡ (•-at (•-at (eσ x) (d (π x))) (eσ (π x))) (inv x)
       (trans (FR.+-identityʳ _) (FR.+-identityˡ (φ (π x))))

-- The relabellings of SWAP ↑ and SWAP ↑ ↑.
sw₁₂ : Labels (₃₊ n) → Labels (₃₊ n)
sw₁₂ (a ∷ b ∷ c ∷ x) = a ∷ c ∷ b ∷ x

sw₂₃ : Labels (₁₊ (₃₊ n)) → Labels (₁₊ (₃₊ n))
sw₂₃ (a ∷ b ∷ c ∷ d ∷ x) = a ∷ b ∷ d ∷ c ∷ x

SWAP↑-at : (x : Labels (₃₊ n)) → ⟦ SWAP ↑ ⟧ x ≡ (sw₁₂ x , 0F)
SWAP↑-at (a ∷ b ∷ c ∷ x) = ↑-at (SWAP-at b c x)

SWAP↑↑-at : (x : Labels (₁₊ (₃₊ n))) → ⟦ SWAP ↑ ↑ ⟧ x ≡ (sw₂₃ x , 0F)
SWAP↑↑-at (a ∷ b ∷ c ∷ d ∷ x) = ↑-at (↑-at (SWAP-at c d x))

sw₁₂-inv : (x : Labels (₃₊ n)) → sw₁₂ (sw₁₂ x) ≡ x
sw₁₂-inv (a ∷ b ∷ c ∷ x) = refl

sw₂₃-inv : (x : Labels (₁₊ (₃₊ n))) → sw₂₃ (sw₂₃ x) ≡ x
sw₂₃-inv (a ∷ b ∷ c ∷ d ∷ x) = refl
