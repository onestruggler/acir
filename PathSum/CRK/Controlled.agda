------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled rotations over {H, CNOT, R_k, R_k†}, and their path-sums
--
-- Section 5.2 of Amy's QPL 2018 paper verifies the quantum Fourier
-- transform, whose circuit (Nielsen and Chuang, figure 5.1) is built
-- from Hadamards and controlled rotations CR_k, the diagonal gate
--
--    CR_k : |x⟩ ↦ e^(2πi x_c x_t / 2^k) |x⟩        (c ≠ t).
--
-- The gate set of PathSum.CRK.Circuit has no controlled rotation, so
-- CR k c t is the usual subcircuit
--
--    R_(k+1) c ; R_(k+1) t ; CNOT c t ; R_(k+1)† t ; CNOT c t,
--
-- whose phase is x_c/2^(k+1) + x_t/2^(k+1) - (x_t ⊕ x_c)/2^(k+1).  Once
-- ⊕ is read as an integer, x_t ⊕ x_c = x_c + x_t - 2 x_c x_t, that is
-- exactly x_c x_t / 2^k, and the second CNOT restores the target.
-- CR-≋ proves that the path-sum of the subcircuit is the diagonal
-- path-sum CRᴾ k c t, for every number of wires, every pair of
-- distinct wires and every k with k + 1 ≤ M; amp-CRᴾ shows CRᴾ is the
-- diagonal matrix above.  The proof reads ⟦ CR k c t ⟧ path by path
-- through PathSum.CRK.Trace (there is only one path: no Hadamard), so
-- no polynomial is ever compared coefficient by coefficient.
--
-- The hypothesis k + 1 ≤ M is the precision the subcircuit needs: its
-- gates are R_(k+1), and PathSum.CRK.Circuit interprets R_j by the
-- exponent 2^(M ∸ j), which is R_j only when j ≤ M.  (For k + 1 > M
-- the subcircuit computes the phase 2 x_c x_t / 2^M, which is not
-- CR_k.)  The phase polynomial of CRᴾ is written as the paper builds
-- its polynomials, as a product: 2^(M-k) · (x_c · x_t).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.CRK.Controlled (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-assoc; xor-same; xor-identityʳ)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (zero; suc; _∸_; _≤_; s≤s)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-self; ≔-≔; same; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.Compose.Gates M₀ using (≋-amp; amp-ext)
open import PathSum.Compose.Properties M₀ using (hits-same)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.CRK.Circuit M using (Circuit; CNOT; R; R†; ⟦_⟧)
open import PathSum.CRK.Trace M₀ using
  (Stream; _≈ᶜ_; conf≈; ≈φ; ≈v; ≔-cong₂; trace; str; eval-⟦⟧; outBit-⟦⟧)
open import PathSum.Cyclotomic M₀ using (0ᴬ; _≐_; zpow)
open import PathSum.Denotation M₀ using
  (Assign; amp; outBit; _≋_; outBit-μ)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using (x[_]; μ; _·ᴾ_; eval)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ)
open import PathSum.Polynomial.Properties using (eval-·ᴾ)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The subcircuit

CR : ℕ → (c t : Fin n) → c ≢ t → Circuit n
CR k c t c≢t =
  R (suc k) c ∷ R (suc k) t ∷ CNOT c t c≢t ∷ R† (suc k) t ∷ CNOT c t c≢t ∷ []


------------------------------------------------------------------------
-- Its trace

-- Half of 2^(M-k) is 2^(M-(k+1)) when k + 1 ≤ M.

private
  ∸-suc : ∀ a k → suc k ≤ a → a ∸ k ≡ suc (a ∸ suc k)
  ∸-suc (suc a) zero      _         = refl
  ∸-suc (suc a) (suc k)   (s≤s le)  = ∸-suc a k le

pow-half : ∀ k → suc k ≤ M → pow (M ∸ k) ≡ pow (M ∸ suc k) * (+ 2)
pow-half k le = trans (cong pow (∸-suc M k le)) (pow-suc (M ∸ suc k))

-- A product of bits is their conjunction.

bit-* : ∀ a b → [ a ]ᶻ * [ b ]ᶻ ≡ [ a ∧ b ]ᶻ
bit-* true  true  = refl
bit-* true  false = refl
bit-* false true  = refl
bit-* false false = refl

private
  -- The phase of the subcircuit, bit by bit: a + b - (b ⊕ a) = 2ab.

  bits : ∀ φ p a b →
         ((φ + p * [ a ]ᶻ) + p * [ b ]ᶻ) - p * [ b xor a ]ᶻ ≡
         φ + (p * (+ 2)) * [ a ∧ b ]ᶻ
  bits φ p false false = solve 2 (λ φ p →
    ((φ :+ p :* con 0ℤ) :+ p :* con 0ℤ) :- p :* con 0ℤ :=
    φ :+ (p :* con (+ 2)) :* con 0ℤ) refl φ p
  bits φ p false true  = solve 2 (λ φ p →
    ((φ :+ p :* con 0ℤ) :+ p :* con 1ℤ) :- p :* con 1ℤ :=
    φ :+ (p :* con (+ 2)) :* con 0ℤ) refl φ p
  bits φ p true  false = solve 2 (λ φ p →
    ((φ :+ p :* con 1ℤ) :+ p :* con 0ℤ) :- p :* con 1ℤ :=
    φ :+ (p :* con (+ 2)) :* con 0ℤ) refl φ p
  bits φ p true  true  = solve 2 (λ φ p →
    ((φ :+ p :* con 1ℤ) :+ p :* con 1ℤ) :- p :* con 0ℤ :=
    φ :+ (p :* con (+ 2)) :* con 1ℤ) refl φ p

  xor-cancel : ∀ a b → (a xor b) xor b ≡ a
  xor-cancel a b = trans (xor-assoc a b b)
    (trans (cong (a xor_) (xor-same b)) (xor-identityʳ a))

-- Along any path, CR k c t adds 2^(M-k) x_c x_t to the phase and
-- leaves every wire as it was.

trace-CR : ∀ k → suc k ≤ M → (c t : Fin n) (c≢t : c ≢ t) (s : Stream)
           (φ : ℤ) (v : Assign n) →
           trace (CR k c t c≢t) s (φ , v) ≈ᶜ
           (φ + pow (M ∸ k) * [ v c ∧ v t ]ᶻ , v)
trace-CR k le c t c≢t s φ v = conf≈
  (trans (cong (λ e → ((φ + p * [ v c ]ᶻ) + p * [ v t ]ᶻ) - p * [ e ]ᶻ)
               (≔-here v t (v t xor v c)))
    (trans (bits φ p (v c) (v t))
           (cong (λ q → φ + q * [ v c ∧ v t ]ᶻ) (sym (pow-half k le)))))
  (λ u → trans
    (≔-cong₂ {z = v₁} {z′ = v₁} t restore (λ _ → refl) u)
    (trans (≔-≔ v t (v t xor v c) (v t) u) (≔-self v t u)))
  where
  p  = pow (M ∸ suc k)
  v₁ = v [ t ≔ v t xor v c ]

  restore : v₁ t xor v₁ c ≡ v t
  restore = trans (cong₂ _xor_ (≔-here v t (v t xor v c))
                               (≔-there v (v t xor v c) c≢t))
                  (xor-cancel (v t) (v c))


------------------------------------------------------------------------
-- The diagonal path-sum

-- |x⟩ ↦ e^(2πi x_c x_t / 2^k) |x⟩: no path variables, the outputs the
-- inputs, the phase 2^(M-k) · (x_c · x_t) over 2^M.

CRᴾ : ℕ → Fin n → Fin n → PathSum n 0 0
CRᴾ k c t = ⟨ pow (M ∸ k) ·ᴾ (μ x[ c ] *ᴾ μ x[ t ]) , (λ w → μ x[ w ]) ⟩

eval-CRᴾ : (k : ℕ) (c t : Fin n) (x : Assign n) (y : Assign 0) →
           eval (phase (CRᴾ k c t)) x y ≡ pow (M ∸ k) * [ x c ∧ x t ]ᶻ
eval-CRᴾ k c t x y = trans
  (eval-·ᴾ (pow (M ∸ k)) (μ x[ c ] *ᴾ μ x[ t ]) x y)
  (cong (pow (M ∸ k) *_) (trans (eval-*ᴾ (μ x[ c ]) (μ x[ t ]) x y)
    (trans (cong₂ _*_ (eval-μᴾ x[ c ] x y) (eval-μᴾ x[ t ] x y))
           (bit-* (x c) (x t)))))

-- It is the diagonal matrix: the entry from x to z is
-- ζ^(2^(M-k) x_c x_t) when z = x, and 0 otherwise.

amp-CRᴾ : (k : ℕ) (c t : Fin n) (x z : Assign n) →
          amp (CRᴾ k c t) x z ≐
          (if same x z then zpow (pow (M ∸ k) * [ x c ∧ x t ]ᶻ) else 0ᴬ)
amp-CRᴾ {n} k c t x z = if-cong
  (trans (hits-same (CRᴾ k c t) x y z)
         (same-≗ {x = outBit (CRᴾ k c t) x y} {x′ = x} {z = z} {z′ = z}
                 (λ w → outBit-μ (CRᴾ k c t) x y w x[ w ] refl)
                 (λ _ → refl)))
  (zpow-≡ (eval-CRᴾ k c t x y))
  where
  y : Assign 0
  y = λ ()


------------------------------------------------------------------------
-- The subcircuit computes the diagonal

CR-≋ : ∀ k → suc k ≤ M → (c t : Fin n) (c≢t : c ≢ t) →
       ⟦ CR k c t c≢t ⟧ ≋ CRᴾ k c t
CR-≋ k le c t c≢t = ≋-amp ⟦ CR k c t c≢t ⟧ (CRᴾ k c t) refl
  (amp-ext ⟦ CR k c t c≢t ⟧ (CRᴾ k c t) ph ob)
  where
  ph : ∀ x y → eval (phase ⟦ CR k c t c≢t ⟧) x y ≡
               eval (phase (CRᴾ k c t)) x y
  ph x y = trans (eval-⟦⟧ (CR k c t c≢t) x y)
    (trans (≈φ (trace-CR k le c t c≢t (str y) 0ℤ x))
      (trans (+-identityˡ (pow (M ∸ k) * [ x c ∧ x t ]ᶻ))
             (sym (eval-CRᴾ k c t x y))))

  ob : ∀ x y w → outBit ⟦ CR k c t c≢t ⟧ x y w ≡ outBit (CRᴾ k c t) x y w
  ob x y w = trans (outBit-⟦⟧ (CR k c t c≢t) x y w)
    (trans (≈v (trace-CR k le c t c≢t (str y) 0ℤ x) w)
           (sym (outBit-μ (CRᴾ k c t) x y w x[ w ] refl)))
