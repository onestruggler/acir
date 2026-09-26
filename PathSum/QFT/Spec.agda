------------------------------------------------------------------------
-- Presentations of groups
--
-- The specification of the quantum Fourier transform (Amy, QPL 2018,
-- section 5.2)
--
-- Section 5.2 verifies a circuit for the quantum Fourier transform
-- against the path-sum
--
--    QFT_n : |x⟩ ↦ 1/√2^n Σ_{y ∈ Z₂^n} e^{2πi [x·y]/2^n} |y⟩,
--
-- "the phase polynomial [x·y] ... generated in the obvious way -- by
-- computing [x] = x₁ + 2x₂ + ... + 2^(n-1) x_n and multiplying the
-- polynomials".  QFTˢ n is that path-sum, built the same way: numᴾ
-- is the polynomial [u] = Σ_i 2^i u_i in a list of variables, the
-- phase is [x] · [y] (the product of multilinear polynomials,
-- PathSum.Polynomial.Product) scaled by 2^(M-n) -- phases are
-- numerators over 2^M -- and the outputs are the path variables
-- themselves.  Normalisation n and n path variables, as definition
-- 2.1 asks.  Wire i carries the bit of weight 2^i, the paper's
-- x_(i+1).
--
-- The phase is exactly 2^(M-n) · [x] · [y], as an integer, at every
-- point (eval-QFTˢ); bin is [x] as an integer.  So QFTˢ n is the
-- Fourier matrix: its unnormalised entry from x to z is the single
-- power ζ^(2^(M-n) [x][z]) = e^{2πi [x][z]/2^n} (QFTˢ-matrix), the
-- path y = z being the only one ending at z.  This reading needs
-- n ≤ M: 2^(M ∸ n) is 2^(M-n) only then, and for n > M the phase
-- is [x][y]/2^M, which is not the Fourier transform.  The theorems
-- about QFTˢ n carry that hypothesis.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.QFT.Spec (M₀ : ℕ) where

open import Data.Bool.Base using (not; _∧_; if_then_else_)
open import Data.Bool.Properties using (xor-comm)
open import Data.Fin.Base using (Fin; zero; suc; fromℕ; inject₁)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; _=ᵇ_; same; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.Compose.Properties M₀ using (hits-same)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡; Σᴮ-δ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; Respects; zpow)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; outBit-μ)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using
  (Poly; Var; x[_]; y[_]; 0ᴾ; μ; _+ᴾ_; _·ᴾ_; eval)
open import PathSum.Polynomial.Product using
  (_*ᴾ_; eval-*ᴾ; eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-·ᴾ; valᵛ)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n m k : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)


------------------------------------------------------------------------
-- The integer a register holds

-- [v] = v₀ + 2 v₁ + ... + 2^(n-1) v_(n-1).

bin : Assign n → ℤ
bin {zero}  v = 0ℤ
bin {suc n} v = [ v zero ]ᶻ + (+ 2) * bin (λ i → v (suc i))

bin-≗ : {v v′ : Assign n} → (∀ i → v i ≡ v′ i) → bin v ≡ bin v′
bin-≗ {zero}  v≗ = refl
bin-≗ {suc n} v≗ = cong₂ (λ a b → [ a ]ᶻ + (+ 2) * b)
  (v≗ zero) (bin-≗ (λ i → v≗ (suc i)))

-- Peeling off the most significant bit instead of the least.

bin-top : (v : Assign (suc n)) →
          bin v ≡ bin (λ i → v (inject₁ i)) + pow n * [ v (fromℕ n) ]ᶻ
bin-top {zero}  v = solve 1 (λ a →
  a :+ con (+ 2) :* con 0ℤ := con 0ℤ :+ con 1ℤ :* a) refl [ v zero ]ᶻ
bin-top {suc n} v = trans
  (cong (λ b → [ v zero ]ᶻ + (+ 2) * b) (bin-top (λ i → v (suc i))))
  (trans (solve 4 (λ a b q c →
            a :+ con (+ 2) :* (b :+ q :* c) :=
            (a :+ con (+ 2) :* b) :+ (q :* con (+ 2)) :* c)
          refl [ v zero ]ᶻ (bin (λ i → v (suc (inject₁ i))))
               (pow n) [ v (fromℕ (suc n)) ]ᶻ)
         (cong (λ q → bin (λ i → v (inject₁ i)) + q * [ v (fromℕ (suc n)) ]ᶻ)
               (sym (pow-suc n))))


------------------------------------------------------------------------
-- The polynomial [u]

-- Σ_i 2^i u_i, for variables u_0, u_1, ... of a path-sum.

numᴾ : (Fin k → Var n m) → Poly n m
numᴾ {k = zero}  u = 0ᴾ
numᴾ {k = suc k} u = μ (u zero) +ᴾ ((+ 2) ·ᴾ numᴾ (λ i → u (suc i)))

eval-numᴾ : (u : Fin k → Var n m) (x : Assign n) (y : Assign m) →
            eval (numᴾ u) x y ≡ bin (λ i → valᵛ (u i) x y)
eval-numᴾ {k = zero}  u x y = eval-0ᴾ x y
eval-numᴾ {k = suc k} u x y = trans
  (eval-+ᴾ (μ (u zero)) ((+ 2) ·ᴾ numᴾ (λ i → u (suc i))) x y)
  (cong₂ _+_ (eval-μᴾ (u zero) x y)
    (trans (eval-·ᴾ (+ 2) (numᴾ (λ i → u (suc i))) x y)
           (cong ((+ 2) *_) (eval-numᴾ (λ i → u (suc i)) x y))))


------------------------------------------------------------------------
-- The specification

-- |x⟩ ↦ 1/√2^n Σ_y e^{2πi [x][y]/2^n} |y⟩.

QFTˢ : (n : ℕ) → PathSum n n n
QFTˢ n = ⟨ pow (M ∸ n) ·ᴾ (numᴾ (λ i → x[ i ]) *ᴾ numᴾ (λ j → y[ j ]))
         , (λ w → μ y[ w ]) ⟩

-- Its phase along a path, and its outputs.

eval-QFTˢ : (x y : Assign n) →
            eval (phase (QFTˢ n)) x y ≡ pow (M ∸ n) * (bin x * bin y)
eval-QFTˢ {n} x y = trans
  (eval-·ᴾ (pow (M ∸ n)) (numᴾ (λ i → x[ i ]) *ᴾ numᴾ (λ j → y[ j ])) x y)
  (cong (pow (M ∸ n) *_)
    (trans (eval-*ᴾ (numᴾ (λ i → x[ i ])) (numᴾ (λ j → y[ j ])) x y)
           (cong₂ _*_ (eval-numᴾ (λ i → x[ i ]) x y)
                      (eval-numᴾ (λ j → y[ j ]) x y))))

outBit-QFTˢ : (x y : Assign n) (w : Fin n) → outBit (QFTˢ n) x y w ≡ y w
outBit-QFTˢ {n} x y w = outBit-μ (QFTˢ n) x y w y[ w ] refl

-- The amplitude as a sum over the paths: the path y ends at y.

amp-QFTˢ : (x z : Assign n) →
           amp (QFTˢ n) x z ≐
           Σᴮ (λ y → if same y z then zpow (pow (M ∸ n) * (bin x * bin y))
                     else 0ᴬ)
amp-QFTˢ {n} x z = Σᴮ-cong (λ y → if-cong
  (trans (hits-same (QFTˢ n) x y z)
         (same-≗ {x = outBit (QFTˢ n) x y} {x′ = y} {z = z} {z′ = z}
                 (outBit-QFTˢ x y) (λ _ → refl)))
  (zpow-≡ (eval-QFTˢ x y)))

-- The Fourier matrix: from x to z the single power
-- ζ^(2^(M-n) [x][z]).

private
  =ᵇ-comm : ∀ a b → (a =ᵇ b) ≡ (b =ᵇ a)
  =ᵇ-comm a b = cong not (xor-comm a b)

  same-comm : (u v : Assign k) → same u v ≡ same v u
  same-comm {zero}  u v = refl
  same-comm {suc k} u v = cong₂ _∧_ (=ᵇ-comm (u zero) (v zero))
    (same-comm (λ j → u (suc j)) (λ j → v (suc j)))

QFTˢ-matrix : (x z : Assign n) →
              amp (QFTˢ n) x z ≐ zpow (pow (M ∸ n) * (bin x * bin z))
QFTˢ-matrix {n} x z =
  amp-QFTˢ x z
  ∙ Σᴮ-cong (λ y → if-cong (same-comm y z) (λ _ → refl))
  ∙ Σᴮ-δ z F resp
  where
  F : Assign n → Amp
  F y = zpow (pow (M ∸ n) * (bin x * bin y))

  resp : Respects F
  resp g h g≗h = zpow-≡ (cong (λ b → pow (M ∸ n) * (bin x * b)) (bin-≗ g≗h))
