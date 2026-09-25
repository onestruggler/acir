------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 2.7's well-formedness claim is false (Amy, QPL 2018)
--
-- Proposition 2.7 claims that the composite of two well-formed,
-- compatible path-sums is well formed.  Compatibility is vacuous here
-- (every input is a variable), and the claim fails for both notions
-- of well-formedness in play, on one qubit.
--
-- Definition 2.4: the operator is a partial isometry
-- (PathSum.PartialIsometry's PartialIsometric).  The projections
--
--    P₀ = |0⟩⟨0| = |x⟩ ↦ ½ Σ_y (-1)^(xy) |x⟩
--    P₊ = |+⟩⟨+| = |x⟩ ↦ ½ Σ_y |y⟩
--
-- (normalisation 1/√2^2, one path variable each) are partial
-- isometries, but P₀ then P₊ is P₊P₀ = (1/√2)|+⟩⟨0|, whose only
-- non-zero singular value is 1/√2: it is not a partial isometry
-- (PartialIsometric-∘-fails).  It still has columns of norm at most 1
-- (P₊∘P₀-WellFormed).
--
-- The weaker notion that lemma 4.1 uses: every column has trace-form
-- norm at most 1 (PathSum.Isometry's WellFormed).  plus = |x⟩ ↦ |+⟩
-- and erase = |x⟩ ↦ |0⟩ both have columns of norm 1, but plus then
-- erase sends every |x⟩ to √2 |0⟩, a column of norm 2
-- (WellFormed-∘-fails).
--
-- Every matrix here is an integer matrix read against ζ⁰: an entry
-- is c · ζ⁰ for an integer c depending on the two bits.  The first
-- section reduces the Gram matrix of such a path-sum, its column norms
-- and definition 2.4 to integer arithmetic on those entries, where
-- the four matrices above are then checked by computation.  The
-- phase of P₀ is ½ x y: its entry from x = 1 is ζ^½ + ζ^0 = -1 + 1 = 0.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Compose.Counterexample (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Fin.Base using (zero)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_; _≤_; +≤+)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; *-identityˡ; *-identityʳ;
   *-zeroˡ; *-zeroʳ; *-comm; *-distribʳ-+; ≤-trans; ≤-reflexive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (_^_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; _=ᵇ_)
open import PathSum.AssignSum using (Σᶻ; Σᶻ-cong; Σᶻ-*; Σᶻ-suc; Σᶻ-zero)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using (hits-same; prop-2-7ʳ)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; -ᴬ_; _·ᴬ_; _≐_; zpow; zpow-anti; coeff; coeff-map;
   coeff-·ᴬ; Σᴮ; Σᴮ-cong; rot; rot-map; rot-exp; rot-0; rot-zpow)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; outBit-μ; eval-0ᴾ-val)
open import PathSum.Hermitian M₀ using (Σᵃ; Σᵃ-cong; inner-cong)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Norm M₀ using (‖_‖²; ‖‖²-cong; coeff-zpow0-0)
open import PathSum.PartialIsometry M₀ using (gram; PartialIsometric)
open import PathSum.Polynomial using (x[_]; y[_]; 0ᴾ; _·ᴾ_; μ; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ)
open import PathSum.Polynomial.Properties using (eval-·ᴾ)
open import PathSum.Reduction M using (½)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; ⊛-·ᴬˡ; ⊛-·ᴬʳ; ⊛-identityˡ; conj-·ᴬ; conj-zpow;
   ·ᴬ-cong; ·ᴬ-·ᴬ; ‖‖²-coeff0)

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    k m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  one : Amp
  one = zpow 0ℤ

  twice : ∀ a → a + a ≡ (+ 2) * a
  twice = solve 1 (λ a → a :+ a := con (+ 2) :* a) refl


------------------------------------------------------------------------
-- Integer matrices on one qubit

-- A sum over one bit.

Σ₁ : (Bool → ℤ) → ℤ
Σ₁ h = h false + h true

Σᶻ-bit : (h : Bool → ℤ) → Σᶻ (λ (z : Assign 1) → h (z zero)) ≡ Σ₁ h
Σᶻ-bit h = trans (Σᶻ-suc (λ z → h (z zero)))
  (cong₂ _+_ (Σᶻ-zero (λ _ → h false)) (Σᶻ-zero (λ _ → h true)))

-- Integer multiples of ζ⁰ multiply as integers, are their own
-- conjugates, and have the square of the integer as norm.

private
  real-⊛ : (p q : ℤ) → (p ·ᴬ one) ⊛ (q ·ᴬ one) ≐ (p * q) ·ᴬ one
  real-⊛ p q =
    ⊛-·ᴬˡ p one (q ·ᴬ one)
    ∙ ·ᴬ-cong p (⊛-·ᴬʳ q one one ∙ ·ᴬ-cong q (⊛-identityˡ one))
    ∙ ·ᴬ-·ᴬ p q one

  real-conj : (q : ℤ) → conj (q ·ᴬ one) ≐ q ·ᴬ one
  real-conj q = conj-·ᴬ q one ∙ ·ᴬ-cong q (conj-zpow 0ℤ)

  real-⊛-conj : (p q : ℤ) →
                (p ·ᴬ one) ⊛ conj (q ·ᴬ one) ≐ (p * q) ·ᴬ one
  real-⊛-conj p q =
    ⊛-cong {a = p ·ᴬ one} {a′ = p ·ᴬ one} (λ _ → refl) (real-conj q)
    ∙ real-⊛ p q

  coeff-real : (p : ℤ) → coeff (p ·ᴬ one) 0ℤ ≡ p
  coeff-real p = trans (coeff-·ᴬ p one 0ℤ)
    (trans (cong (p *_) coeff-zpow0-0) (*-identityʳ p))

  ‖real‖² : (p : ℤ) → ‖ p ·ᴬ one ‖² ≡ p * p
  ‖real‖² p = trans (sym (‖‖²-coeff0 (p ·ᴬ one)))
    (trans (coeff-map (real-⊛-conj p p) 0ℤ) (coeff-real (p * p)))

  Σᵃ-real : (f : Assign 1 → ℤ) → Σᵃ (λ z → f z ·ᴬ one) ≐ Σᶻ f ·ᴬ one
  Σᵃ-real f i = trans (Σᶻ-cong (λ z → *-comm (f z) (one i)))
    (trans (Σᶻ-* (one i) f) (*-comm (one i) (Σᶻ f)))

-- The Gram matrix of an integer matrix a, entrywise.

gᵃ : (Bool → Bool → ℤ) → Bool → Bool → ℤ
gᵃ a b b′ = Σ₁ (λ c → a b c * a b′ c)

-- A one-qubit path-sum whose entry from x to z is a (x₀) (z₀) · ζ⁰.

Real : PathSum 1 k m → (Bool → Bool → ℤ) → Set
Real ξ a = ∀ x z → amp ξ x z ≐ a (x zero) (z zero) ·ᴬ one

-- Its column norms, Gram matrix and definition 2.4, in integers.

real-WF : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
          ∀ x → Σᶻ (λ z → ‖ amp ξ x z ‖²) ≡ gᵃ a (x zero) (x zero)
real-WF ξ a re x = trans
  (Σᶻ-cong (λ z → trans
    (‖‖²-cong {amp ξ x z} {a (x zero) (z zero) ·ᴬ one} (re x z))
    (‖real‖² (a (x zero) (z zero)))))
  (Σᶻ-bit (λ c → a (x zero) c * a (x zero) c))

private
  gram-real : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
              ∀ x x′ → gram ξ x x′ ≐ gᵃ a (x zero) (x′ zero) ·ᴬ one
  gram-real ξ a re x x′ =
    inner-cong {ψ = amp ξ x} {ψ′ = λ z → a (x zero) (z zero) ·ᴬ one}
               {φ = amp ξ x′} {φ′ = λ z → a (x′ zero) (z zero) ·ᴬ one}
               (re x) (re x′)
    ∙ Σᵃ-cong (λ z → real-⊛-conj (a (x zero) (z zero)) (a (x′ zero) (z zero)))
    ∙ Σᵃ-real (λ z → a (x zero) (z zero) * a (x′ zero) (z zero))
    ∙ (λ i → cong (_* one i)
         (Σᶻ-bit (λ c → a (x zero) c * a (x′ zero) c)))

  -- Both sides of definition 2.4, as integer multiples of ζ⁰.

  square : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
           ∀ x x′ → Σᵃ (λ x″ → gram ξ x x″ ⊛ gram ξ x″ x′) ≐
                    Σ₁ (λ c → gᵃ a (x zero) c * gᵃ a c (x′ zero)) ·ᴬ one
  square ξ a re x x′ =
    Σᵃ-cong (λ x″ → ⊛-cong (gram-real ξ a re x x″) (gram-real ξ a re x″ x′)
                    ∙ real-⊛ (gᵃ a (x zero) (x″ zero))
                             (gᵃ a (x″ zero) (x′ zero)))
    ∙ Σᵃ-real (λ x″ → gᵃ a (x zero) (x″ zero) * gᵃ a (x″ zero) (x′ zero))
    ∙ (λ i → cong (_* one i)
         (Σᶻ-bit (λ c → gᵃ a (x zero) c * gᵃ a c (x′ zero))))

  scaled : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
           ∀ x x′ → (+ (2 ^ k)) ·ᴬ gram ξ x x′ ≐
                    ((+ (2 ^ k)) * gᵃ a (x zero) (x′ zero)) ·ᴬ one
  scaled {k = k} ξ a re x x′ =
    ·ᴬ-cong (+ (2 ^ k)) (gram-real ξ a re x x′)
    ∙ ·ᴬ-·ᴬ (+ (2 ^ k)) (gᵃ a (x zero) (x′ zero)) one

-- Definition 2.4 holds when the integer Gram matrix is 2^k times a
-- projection, and implies it.

real-PI : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
          (∀ b b′ → Σ₁ (λ c → gᵃ a b c * gᵃ a c b′) ≡
                    (+ (2 ^ k)) * gᵃ a b b′) →
          PartialIsometric ξ
real-PI ξ a re idem x x′ =
  square ξ a re x x′
  ∙ (λ i → cong (_* one i) (idem (x zero) (x′ zero)))
  ∙ ≐-sym (scaled ξ a re x x′)

real-PI⁻ : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
           PartialIsometric ξ →
           ∀ b b′ → Σ₁ (λ c → gᵃ a b c * gᵃ a c b′) ≡
                    (+ (2 ^ k)) * gᵃ a b b′
real-PI⁻ {k = k} ξ a re pi b b′ =
  trans (sym (coeff-real (Σ₁ (λ c → gᵃ a b c * gᵃ a c b′))))
    (trans (coeff-map (≐-sym (square ξ a re x x′) ∙ pi x x′
                       ∙ scaled ξ a re x x′) 0ℤ)
           (coeff-real ((+ (2 ^ k)) * gᵃ a b b′)))
  where
  x x′ : Assign 1
  x  _ = b
  x′ _ = b′


------------------------------------------------------------------------
-- The path-sums

-- |x⟩ ↦ 1/√2^k Σ_y |y⟩: every input goes to √2^(1-k) |+⟩.

toY : (k : ℕ) → PathSum 1 k 1
toY k = ⟨ 0ᴾ , (λ _ → μ y[ zero ]) ⟩

-- plus = |x⟩ ↦ |+⟩, and the projection P₊ = |+⟩⟨+| = |x⟩ ↦ ½ Σ_y |y⟩.

plus : PathSum 1 1 1
plus = toY 1

P₊ : PathSum 1 2 1
P₊ = toY 2

-- erase = |x⟩ ↦ |0⟩.

erase : PathSum 1 0 0
erase = ⟨ 0ᴾ , (λ _ → 0ᴾ) ⟩

-- The projection P₀ = |0⟩⟨0| = |x⟩ ↦ ½ Σ_y e^(2πi xy/2) |x⟩: the sum is
-- 2 at x = 0 and 0 at x = 1.

P₀ : PathSum 1 2 1
P₀ = ⟨ ½ ·ᴾ (μ x[ zero ] *ᴾ μ y[ zero ]) , (λ _ → μ x[ zero ]) ⟩


------------------------------------------------------------------------
-- Their matrices

-- One bit is read through its only wire.

private
  hits₁ : (ξ : PathSum 1 k m) (x : Assign 1) (y : Assign m) (z : Assign 1) →
          hits ξ x y z ≡ (outBit ξ x y zero =ᵇ z zero)
  hits₁ ξ x y z = trans (hits-same ξ x y z) (∧-identityʳ _)

-- toY k: every entry is ζ⁰, the path y = z being the only one to z.

private
  two : (c : Bool) →
        ((if (true =ᵇ c) then one else 0ᴬ) +ᴬ
         (if (false =ᵇ c) then one else 0ᴬ)) ≐ one
  two true  i = +-identityʳ (one i)
  two false i = +-identityˡ (one i)

amp-toY : (k : ℕ) (x z : Assign 1) → amp (toY k) x z ≐ one
amp-toY k x z =
  Σᴮ-cong (λ y → if-cong
    (trans (hits₁ (toY k) x y z)
           (cong (_=ᵇ z zero) (outBit-μ (toY k) x y zero y[ zero ] refl)))
    (zpow-≡ (eval-0ᴾ-val x y)))
  ∙ two (z zero)

aᵖ : Bool → Bool → ℤ
aᵖ _ _ = 1ℤ

real-toY : (k : ℕ) → Real (toY k) aᵖ
real-toY k x z = amp-toY k x z ∙ (λ i → sym (*-identityˡ (one i)))

-- erase: the entry to z is 1 when z = 0.

aᵉ : Bool → Bool → ℤ
aᵉ _ c = if c then 0ℤ else 1ℤ

private
  erase-at : (c : Bool) →
             (if (false =ᵇ c) then one else 0ᴬ) ≐ aᵉ false c ·ᴬ one
  erase-at true  i = sym (*-zeroˡ (one i))
  erase-at false i = sym (*-identityˡ (one i))

real-erase : Real erase aᵉ
real-erase x z = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits erase x y z then zpow (eval (phase erase) x y) else 0ᴬ) ≐
       aᵉ (x zero) (z zero) ·ᴬ one
  at y = if-cong (trans (hits₁ erase x y z)
                        (cong (λ e → odd e =ᵇ z zero) (eval-0ᴾ-val x y)))
                 (zpow-≡ (eval-0ᴾ-val x y))
         ∙ erase-at (z zero)

-- plus, then erase: both paths reach |0⟩.

aᵉᵖ : Bool → Bool → ℤ
aᵉᵖ b c = aᵉ b c + aᵉ b c

real-erase∘plus : Real (erase ∘ᴾ plus) aᵉᵖ
real-erase∘plus x z =
  prop-2-7ʳ erase plus x z
  ∙ Σᴮ-cong (λ y →
      rot-map (eval (phase plus) x y) (real-erase (outBit plus x y) z)
      ∙ rot-exp {eval (phase plus) x y} {0ℤ}
                (aᵉ (outBit plus x y zero) (z zero) ·ᴬ one)
                (eval-0ᴾ-val x y)
      ∙ rot-0 (aᵉ (outBit plus x y zero) (z zero) ·ᴬ one))
  ∙ (λ i → sym (*-distribʳ-+ (one i) (aᵉ (x zero) (z zero))
                                     (aᵉ (x zero) (z zero))))

-- P₀: the path from x to x has the phase ½ x y.

private
  eval-P₀ : (x : Assign 1) (y : Assign 1) →
            eval (phase P₀) x y ≡ ½ * ([ x zero ]ᶻ * [ y zero ]ᶻ)
  eval-P₀ x y = trans (eval-·ᴾ ½ (μ x[ zero ] *ᴾ μ y[ zero ]) x y)
    (cong (½ *_) (trans (eval-*ᴾ (μ x[ zero ]) (μ y[ zero ]) x y)
                        (cong₂ _*_ (eval-μᴾ x[ zero ] x y)
                                   (eval-μᴾ y[ zero ] x y))))

  -- The two paths from b: ζ^0 + ζ^0 = 2 at b = 0, ζ^½ + ζ^0 = 0 at
  -- b = 1.

  paths : (b : Bool) →
          (zpow (½ * ([ b ]ᶻ * 1ℤ)) +ᴬ zpow (½ * ([ b ]ᶻ * 0ℤ))) ≐
          (if b then 0ℤ else + 2) ·ᴬ one
  paths false =
    (λ i → cong₂ _+_ (zpow-≡ (*-zeroʳ ½) i) (zpow-≡ (*-zeroʳ ½) i))
    ∙ (λ i → twice (one i))
  paths true  =
    (λ i → cong₂ _+_
      ((zpow-≡ (trans (*-identityʳ ½) (sym (+-identityˡ ½)))
        ∙ zpow-anti 0ℤ) i)
      (zpow-≡ (*-zeroʳ ½) i))
    ∙ (λ i → trans (+-inverseˡ (one i)) (sym (*-zeroˡ (one i))))

  zeros : (0ᴬ +ᴬ 0ᴬ) ≐ 0ℤ ·ᴬ one
  zeros i = sym (*-zeroˡ (one i))

a₀ : Bool → Bool → ℤ
a₀ b c = if b then 0ℤ else (if c then 0ℤ else + 2)

real-P₀ : Real P₀ a₀
real-P₀ x z =
  Σᴮ-cong (λ y → if-cong
    (trans (hits₁ P₀ x y z)
           (cong (_=ᵇ z zero) (outBit-μ P₀ x y zero x[ zero ] refl)))
    (zpow-≡ (eval-P₀ x y)))
  ∙ at (x zero) (z zero)
  where
  at : (b c : Bool) →
       ((if (b =ᵇ c) then zpow (½ * ([ b ]ᶻ * 1ℤ)) else 0ᴬ) +ᴬ
        (if (b =ᵇ c) then zpow (½ * ([ b ]ᶻ * 0ℤ)) else 0ᴬ)) ≐ a₀ b c ·ᴬ one
  at false false = paths false
  at false true  = zeros
  at true  false = zeros
  at true  true  = paths true

-- P₀, then P₊: every path from x ends in the same column of P₊, so the
-- column of x is (the entry of P₀ at x, summed) times |+⟩.

a₁ : Bool → Bool → ℤ
a₁ b _ = if b then 0ℤ else + 2

real-P₊∘P₀ : Real (P₊ ∘ᴾ P₀) a₁
real-P₊∘P₀ x z =
  prop-2-7ʳ P₊ P₀ x z
  ∙ Σᴮ-cong (λ y →
      rot-map (eval (phase P₀) x y) (amp-toY 2 (outBit P₀ x y) z)
      ∙ rot-zpow (eval (phase P₀) x y) 0ℤ
      ∙ zpow-≡ (trans (+-identityʳ (eval (phase P₀) x y)) (eval-P₀ x y)))
  ∙ paths (x zero)


------------------------------------------------------------------------
-- The counterexamples

-- Definition 2.4: P₀ and P₊ are projections, and so partial isometries
-- (their integer Gram matrices are 4 times a projection); P₀ then P₊
-- is not, its Gram matrix squaring to 64 where 2^4 times it is 128.

private
  64≢128 : + 64 ≢ + 128
  64≢128 ()

PartialIsometric-∘-fails :
  PartialIsometric P₀ × PartialIsometric P₊ × ¬ PartialIsometric (P₊ ∘ᴾ P₀)
PartialIsometric-∘-fails =
  real-PI P₀ a₀ real-P₀ idem₀ ,
  real-PI P₊ aᵖ (real-toY 2) (λ _ _ → refl) ,
  (λ pi → 64≢128 (real-PI⁻ (P₊ ∘ᴾ P₀) a₁ real-P₊∘P₀ pi false false))
  where
  idem₀ : ∀ b b′ → Σ₁ (λ c → gᵃ a₀ b c * gᵃ a₀ c b′) ≡
                   (+ (2 ^ 2)) * gᵃ a₀ b b′
  idem₀ false false = refl
  idem₀ false true  = refl
  idem₀ true  false = refl
  idem₀ true  true  = refl

-- The composite is still WellFormed: its columns have norm 8 and 0,
-- within the budget 2^4.

P₊∘P₀-WellFormed : WellFormed (P₊ ∘ᴾ P₀)
P₊∘P₀-WellFormed x =
  ≤-trans (≤-reflexive (real-WF (P₊ ∘ᴾ P₀) a₁ real-P₊∘P₀ x)) (bound (x zero))
  where
  bound : (b : Bool) → gᵃ a₁ b b ≤ + (2 ^ 4)
  bound false = +≤+ (ℕ.m≤m+n 8 8)
  bound true  = +≤+ z≤n

-- WellFormed: plus and erase have columns of norm 1, plus then erase
-- a column of norm 4 against the budget 2^1.

private
  4≰2 : ¬ (+ 4 ≤ + 2)
  4≰2 (+≤+ (s≤s (s≤s ())))

WellFormed-∘-fails :
  WellFormed plus × WellFormed erase × ¬ WellFormed (erase ∘ᴾ plus)
WellFormed-∘-fails =
  (λ x → ≤-reflexive (real-WF plus aᵖ (real-toY 1) x)) ,
  (λ x → ≤-reflexive (real-WF erase aᵉ real-erase x)) ,
  (λ wf → 4≰2 (≤-trans (≤-reflexive (sym (real-WF (erase ∘ᴾ plus) aᵉᵖ
                                                  real-erase∘plus x₀)))
                       (wf x₀)))
  where
  x₀ : Assign 1
  x₀ _ = false
