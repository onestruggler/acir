------------------------------------------------------------------------
-- Presentations of groups
--
-- The arithmetic of the Toffoli gate's paths
--
-- The integer, Boolean and amplitude identities that PathSum.Toffoli
-- needs, apart from any circuit.  Along one path of the seven-T
-- Toffoli circuit the seven T and T† contribute 2^(M-3) times a signed
-- sum of bits that is 4 x₁ x₂ y₁ (T-bracket), and 4 · 2^(M-3) is ½
-- (four-T); the phase is gathered into the Hadamards' terms plus that
-- multiple (tidy).  Three halves ½a + ½b + ½c differ from ½(a ⊕ b ⊕ c)
-- by a multiple of 1, so ζ takes the same value at both (zpow-½³).
-- Summing ζ^(½·y₁q) over y₁ gives 2 when q = 0 and 0 when q = 1
-- (pair), and of the two values of y₂ only one survives (outer); the
-- 2 is √2², the circuit's normalisation (scale-two).
--
-- Every Boolean identity is proved by cases (at most sixteen), the
-- integer ones by the laws of ℤ, with 2^(M-3) and ½ kept symbolic; none
-- mentions a polynomial.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Toffoli.Arith (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _∨_; _xor_)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (divides)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-assoc; +-comm; *-identityʳ;
   *-zeroʳ; *-assoc; *-comm; *-distribˡ-+; neg-distribʳ-*; pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (_∸_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-+; scale-twice)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Compose.Sum M₀ using (zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; -ᴬ_; _·ᴬ_; _≐_; zpow; zpow-anti; zpow-cong; scale; N)
  renaming (H to rank)
open import PathSum.Order M using (pow; pow-+)
open import PathSum.Reduction M using (½)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)


------------------------------------------------------------------------
-- The phase of a path

-- The seven T and T† add 2^(M-3) times this signed sum of bits (the
-- target's four values between the Hadamards, c₂'s value, and c₂'s and
-- c₁'s values after the second Hadamard), which is 4 x₁ x₂ b.

T-bracket : ∀ b x₁ x₂ →
  0ℤ - [ b xor x₂ ]ᶻ + [ (b xor x₂) xor x₁ ]ᶻ
  - [ ((b xor x₂) xor x₁) xor x₂ ]ᶻ
  + [ (((b xor x₂) xor x₁) xor x₂) xor x₁ ]ᶻ
  + [ x₂ ]ᶻ - [ x₂ xor x₁ ]ᶻ + [ x₁ ]ᶻ
  ≡ (+ 4) * [ (x₁ ∧ x₂) ∧ b ]ᶻ
T-bracket false false false = refl
T-bracket false false true  = refl
T-bracket false true  false = refl
T-bracket false true  true  = refl
T-bracket true  false false = refl
T-bracket true  false true  = refl
T-bracket true  true  false = refl
T-bracket true  true  true  = refl

-- Collecting the multiples of T in a running sum B, one term at a time.

private
  acc0 : ∀ a T → 0ℤ + a ≡ a + T * 0ℤ
  acc0 a T = trans (+-identityˡ a)
    (sym (trans (cong (λ w → a + w) (*-zeroʳ T)) (+-identityʳ a)))

  acc+ : ∀ a T B v {u} → u ≡ a + T * B → u + T * v ≡ a + T * (B + v)
  acc+ a T B v eq = trans (cong (_+ T * v) eq)
    (trans (+-assoc a (T * B) (T * v))
           (cong (λ w → a + w) (sym (*-distribˡ-+ T B v))))

  acc- : ∀ a T B v {u} → u ≡ a + T * B → u - T * v ≡ a + T * (B - v)
  acc- a T B v eq = trans (cong (_- T * v) eq)
    (trans (+-assoc a (T * B) (- (T * v)))
      (cong (λ w → a + w)
            (trans (cong (λ w → T * B + w) (neg-distribʳ-* T v))
                   (sym (*-distribˡ-+ T B (- v))))))

  accH : ∀ a T B q {u} → u ≡ a + T * B → u + q ≡ a + q + T * B
  accH a T B q eq = trans (cong (_+ q) eq)
    (trans (+-assoc a (T * B) q)
      (trans (cong (λ w → a + w) (+-comm (T * B) q))
             (sym (+-assoc a q (T * B)))))

-- The phase along a path, tidied: the two Hadamards' terms, and T
-- times the signed sum above.

tidy : ∀ h T p q e₂ e₄ e₆ e₈ f₂ f₂₁ f₁ →
  0ℤ + h * p - T * e₂ + T * e₄ - T * e₆ + T * e₈ + T * f₂ + h * q
  - T * f₂₁ + T * f₁
  ≡ h * p + h * q + T * (0ℤ - e₂ + e₄ - e₆ + e₈ + f₂ - f₂₁ + f₁)
tidy h T p q e₂ e₄ e₆ e₈ f₂ f₂₁ f₁ =
  acc+ (a + b) T (B₆ - f₂₁) f₁ (acc- (a + b) T B₆ f₂₁ (accH a T B₆ b
    (acc+ a T B₅ f₂ (acc+ a T B₄ e₈ (acc- a T B₃ e₆
      (acc+ a T B₂ e₄ (acc- a T 0ℤ e₂ (acc0 a T))))))))
  where
  a b B₂ B₃ B₄ B₅ B₆ : ℤ
  a  = h * p
  b  = h * q
  B₂ = 0ℤ - e₂
  B₃ = B₂ + e₄
  B₄ = B₃ - e₆
  B₅ = B₄ + e₈
  B₆ = B₅ + f₂

-- ½ = 4 · 2^(M-3).

four-T : ∀ s → pow (M ∸ 3) * ((+ 4) * s) ≡ ½ * s
four-T s = trans (sym (*-assoc (pow (M ∸ 3)) (+ 4) s))
  (cong (_* s) (trans (*-comm (pow (M ∸ 3)) (+ 4)) (pow-+ 2 M₀)))

-- The circuit produces the paper's three terms in the order x_t y₁,
-- y₁ y₂, x₁ x₂ y₁; example 3.3 prints the last two the other way round.

swap-last : ∀ a b c → a + b + c ≡ a + c + b
swap-last a b c = trans (+-assoc a b c)
  (trans (cong (λ w → a + w) (+-comm b c)) (sym (+-assoc a c b)))


------------------------------------------------------------------------
-- Halves modulo 1

-- ½a + ½b + ½c is ½(a ⊕ b ⊕ c) modulo 1: they differ by ½ · 2 = 1
-- times the majority of a, b and c.

private
  maj : Bool → Bool → Bool → Bool
  maj a b c = (a ∧ b) ∨ ((a ∨ b) ∧ c)

  bits3 : ∀ a b c → [ a ]ᶻ + [ b ]ᶻ + [ c ]ᶻ - [ (a xor b) xor c ]ᶻ ≡
                    (+ 2) * [ maj a b c ]ᶻ
  bits3 false false false = refl
  bits3 false false true  = refl
  bits3 false true  false = refl
  bits3 false true  true  = refl
  bits3 true  false false = refl
  bits3 true  false true  = refl
  bits3 true  true  false = refl
  bits3 true  true  true  = refl

  ½·2 : ½ * (+ 2) ≡ + N
  ½·2 = trans (sym (pos-* rank 2)) (cong +_ (ℕ.*-comm rank 2))

  factor : ∀ h p q r s → h * p + h * q + h * r - h * s ≡ h * (p + q + r - s)
  factor h p q r s = sym (trans (*-distribˡ-+ h (p + q + r) (- s))
    (cong₂ _+_ (trans (*-distribˡ-+ h (p + q) r)
                      (cong (_+ h * r) (*-distribˡ-+ h p q)))
               (sym (neg-distribʳ-* h s))))

  swap : ∀ h k → h * ((+ 2) * k) ≡ k * (h * (+ 2))
  swap = solve 2 (λ h k → h :* (con (+ 2) :* k) := k :* (h :* con (+ 2)))
                 refl

zpow-½³ : ∀ a b c → zpow (½ * [ a ]ᶻ + ½ * [ b ]ᶻ + ½ * [ c ]ᶻ) ≐
                    zpow (½ * [ (a xor b) xor c ]ᶻ)
zpow-½³ a b c =
  zpow-cong {½ * [ a ]ᶻ + ½ * [ b ]ᶻ + ½ * [ c ]ᶻ} {½ * [ (a xor b) xor c ]ᶻ}
    (divides [ maj a b c ]ᶻ
      (trans (factor ½ [ a ]ᶻ [ b ]ᶻ [ c ]ᶻ [ (a xor b) xor c ]ᶻ)
        (trans (cong (½ *_) (bits3 a b c))
          (trans (swap ½ [ maj a b c ]ᶻ) (cong ([ maj a b c ]ᶻ *_) ½·2)))))


------------------------------------------------------------------------
-- Boolean identities

-- After the four CNOTs onto t, t reads y₁ again; after the two onto
-- c₂, c₂ reads x₂ again.

back-t : ∀ b x₁ x₂ → (((b xor x₂) xor x₁) xor x₂) xor x₁ ≡ b
back-t false false false = refl
back-t false false true  = refl
back-t false true  false = refl
back-t false true  true  = refl
back-t true  false false = refl
back-t true  false true  = refl
back-t true  true  false = refl
back-t true  true  true  = refl

back-c₂ : ∀ x₂ x₁ → (x₂ xor x₁) xor x₁ ≡ x₂
back-c₂ false false = refl
back-c₂ false true  = refl
back-c₂ true  false = refl
back-c₂ true  true  = refl

-- The phase bit: x_t y₁ ⊕ a y₁ ⊕ y₁ y₂ = y₁ (y₂ ⊕ x_t ⊕ a), for y₂
-- (the head path variable) b₀ and y₁ b₁.

phase-bit : ∀ xt a b₀ b₁ → ((xt ∧ b₁) xor (a ∧ b₁)) xor (b₁ ∧ b₀) ≡
                           b₁ ∧ (b₀ xor (xt xor a))
phase-bit false false false false = refl
phase-bit false false false true  = refl
phase-bit false false true  false = refl
phase-bit false false true  true  = refl
phase-bit false true  false false = refl
phase-bit false true  false true  = refl
phase-bit false true  true  false = refl
phase-bit false true  true  true  = refl
phase-bit true  false false false = refl
phase-bit true  false false true  = refl
phase-bit true  false true  false = refl
phase-bit true  false true  true  = refl
phase-bit true  true  false false = refl
phase-bit true  true  false true  = refl
phase-bit true  true  true  false = refl
phase-bit true  true  true  true  = refl


------------------------------------------------------------------------
-- Summing two path variables

-- ζ^0, and 2 ζ^0.

one two : Amp
one = zpow 0ℤ
two = (+ 2) ·ᴬ one

-- ζ^(½·0) = 1 and ζ^(½·1) = -1.

zpow-½0 : zpow (½ * [ false ]ᶻ) ≐ one
zpow-½0 = zpow-≡ (*-zeroʳ ½)

zpow-½1 : zpow (½ * [ true ]ᶻ) ≐ -ᴬ one
zpow-½1 i = trans (zpow-≡ (*-identityʳ ½) i) (zpow-anti 0ℤ i)

private
  double : ∀ a → a + a ≡ (+ 2) * a
  double = solve 1 (λ a → a :+ a := con (+ 2) :* a) refl

-- For one value of y₂, the two values of y₁: 1 + (-1)^q.

pair : ∀ s q →
       ((if s then zpow (½ * [ q ]ᶻ) else 0ᴬ) +ᴬ
        (if s then zpow (½ * [ false ]ᶻ) else 0ᴬ)) ≐
       (if s then (if q then 0ᴬ else two) else 0ᴬ)
pair false q     i = refl
pair true  false i = trans (cong₂ _+_ (zpow-½0 i) (zpow-½0 i)) (double (one i))
pair true  true  i =
  trans (cong₂ _+_ (zpow-½1 i) (zpow-½0 i)) (+-inverseˡ (one i))

-- Then the two values of y₂: only y₂ = r survives.

outer : ∀ r sT sF →
        ((if sT then (if not r then 0ᴬ else two) else 0ᴬ) +ᴬ
         (if sF then (if r then 0ᴬ else two) else 0ᴬ)) ≐
        ((+ 2) ·ᴬ (if (if r then sT else sF) then one else 0ᴬ))
outer true  true  true  i = +-identityʳ (two i)
outer true  true  false i = +-identityʳ (two i)
outer true  false true  i = refl
outer true  false false i = refl
outer false true  true  i = +-identityˡ (two i)
outer false false true  i = +-identityˡ (two i)
outer false true  false i = refl
outer false false false i = refl

select : (s : Bool → Bool) (r : Bool) → (if r then s true else s false) ≡ s r
select s true  = refl
select s false = refl

-- The factor 2 left over is the circuit's normalisation, √2² (the
-- paper's [Elim] step): 2 = √2 · √2, by PathSum.AmpLinear's bookkeeping
-- rather than by unfolding √2 (which would compare rotations).

scale-two : ∀ a → (+ 2) ·ᴬ a ≐ scale 2 a
scale-two a i = trans (sym (scale-twice 1 a i)) (scale-+ 1 1 a i)
