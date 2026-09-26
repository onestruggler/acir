------------------------------------------------------------------------
-- Presentations of groups
--
-- The quantum Fourier transform is unitary (Amy, QPL 2018, example 2.2,
-- definition 2.4 and section 5.2)
--
-- Example 2.2 lists QFT_n : |x⟩ ↦ 1/√2^n Σ_y e^{2πi [x·y]/2^n} |y⟩
-- among the path-sums of common unitaries, and section 5.2 uses it as
-- the specification of a circuit.  PathSum.QFT.Spec builds it as
-- QFTˢ n, at the fixed precision of this development (phases are
-- numerators over 2^M, M = 3 + M₀).  This module shows that QFTˢ n is
-- unitary in the sense of PathSum.PartialIsometry.Unitary -- U†U = I
-- and UU† = I, the denominators cleared -- and that this holds exactly
-- when n ≤ M.  Two routes:
--
--  * Through the circuit.  ⟦ QFTC n ⟧ is the path-sum of a circuit
--    over {H, CNOT, R_k, R_k†}, so it is unitary, for every n
--    (QFTC-Unitary, from PathSum.CRK.Unitarity); unitarity is a
--    property of the operator (Unitary-≋), and QFT-≋ says the two
--    have the same operator when n + 1 ≤ M.  So QFTˢ n is unitary for
--    n + 1 ≤ M (QFTˢ-Unitary-circuit).
--
--  * Directly, which reaches n = M as well.  By QFTˢ-matrix the entry
--    of QFTˢ n from x to z is ζ^(2^(M-n) [x][z]), so the product of
--    the rows (or of the columns) at x and x′ is the character sum
--
--       χsum n d = Σ_{z ∈ Z₂^n} ζ^(2^(M-n) d [z]),   d = [x] - [x′].
--
--    Peeling the least significant bit of z gives
--    χsum (n+1) d = (1 + ζ^(2^(M-n-1) d)) · χsum n d (χsum-suc), and
--    χsum n d depends on d only modulo 2^n (χsum-mod).  Writing
--    [x] = [x_low] + 2^n x_top, induction on n shows
--    χsum n ([x] - [x′]) = 2^n [x = x′] (χsum-rows): the sum over the
--    low bits is 2^n or 0 by induction, and when the low bits agree
--    the remaining factor is 1 + ζ^(2^(M-1) (x_top - x′_top)), which
--    is 2 or 1 + (-1) = 0.  So QFTˢ n is isometric and coisometric --
--    unitary -- for every n ≤ M (QFTˢ-Unitary), and in particular
--    well-formed in the sense of definition 2.4
--    (QFTˢ-PartialIsometric, QFTˢ-WellFormed).
--
-- For n > M it is not: 2^(M ∸ n) is then 1 and the entry is
-- ζ^([x][z]), a 2^M-th root of unity, so the rows at x = 0 and at x′
-- the assignment with bit M alone set coincide, and two equal rows of
-- nonzero norm are not orthogonal (QFTˢ-not-Isometric).  Together:
-- QFTˢ n is unitary if and only if n ≤ M (QFTˢ-Unitary⇔) -- if and
-- only if it is the Fourier transform, as PathSum.QFT.Spec's header
-- says.  This is a fact about the fixed precision of this
-- development, not about the paper, whose dyadic arithmetic has no
-- such bound.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.QFT.Unitary (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-assoc; ∧-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; fromℕ<; inject₁)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; divides)
open import Data.Integer.Properties using
  (+-identityˡ; +-inverseˡ; +-inverseʳ; *-identityˡ; *-identityʳ;
   *-zeroʳ; *-comm; neg-involutive; pos-*; +-injective)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_; _≤_; _<_; _^_; s≤s; z≤n)
open import Data.Product.Base using (_,_; proj₁)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _=ᵇ_; same; same-refl; same-true)
open import PathSum.AssignSum using (_∷ᵃ_; Σᶻ-zero; Σᶻ-suc)
open import PathSum.Compose.Sum M₀ using (zpow-≡)
open import PathSum.CRK.Circuit M using (⟦_⟧; Rk-order; Rk-primitive)
open import PathSum.CRK.Controlled M₀ using (pow-half)
open import PathSum.CRK.Unitarity M₀ using (circuit-Unitary)
open import PathSum.Cyclotomic M₀ using
  (H; Amp; 0ᴬ; _+ᴬ_; _·ᴬ_; -ᴬ_; _≐_; zpow; zpow-anti; zpow-cong; 0ᶠ;
   zpow0-at-0)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Hermitian M₀ using (Σᵃ; Σᵃ-cong; [_]ᴬ; inner-cong)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.PartialIsometry M₀ using
  (Isometric; PartialIsometric; Isometric⇒PartialIsometric;
   Isometric⇒WellFormed)
open import PathSum.PartialIsometry.Unitary M₀ using
  (Coisometric; Unitary; Unitary-≋)
open import PathSum.QFT M₀ using (QFT-≋)
open import PathSum.QFT.Circuit M₀ using (QFTC)
open import PathSum.QFT.Spec M₀ using
  (bin; bin-≗; bin-top; QFTˢ; QFTˢ-matrix)
open import PathSum.Reduction M using (½)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; ⊛-distribʳ-+ᴬ; ⊛-·ᴬˡ; ⊛-·ᴬʳ; ·ᴬ-cong; ·ᴬ-·ᴬ;
   ⊛-zeroʳ; ⊛-identityˡ; zpow-⊛-zpow; conj-zpow)
open import PathSum.Ring.Laws M₀ using (⊛-Σᵃ; ⊛-identityʳ; +ᴬ-cong)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Through the circuit

-- The circuit's path-sum is unitary, for every n: it is a circuit over
-- {H, CNOT, R_k, R_k†}.

QFTC-Unitary : ∀ n → Unitary ⟦ QFTC n ⟧
QFTC-Unitary n = circuit-Unitary (QFTC n)

-- So is the specification, wherever the circuit implements it.

QFTˢ-Unitary-circuit : ∀ n → suc n ≤ M → Unitary (QFTˢ n)
QFTˢ-Unitary-circuit n le =
  Unitary-≋ ⟦ QFTC n ⟧ (QFTˢ n) (QFT-≋ n le) (QFTC-Unitary n)


------------------------------------------------------------------------
-- Sums over assignments, one bit at a time

private
  Σᵃ-suc : (f : Assign (suc n) → Amp) →
           Σᵃ f ≐ Σᵃ (λ g → f (false ∷ᵃ g)) +ᴬ Σᵃ (λ g → f (true ∷ᵃ g))
  Σᵃ-suc f i = Σᶻ-suc (λ z → f z i)

  -- A sum over no bits is its one term.  (The term is reached through
  -- an absurd pattern, so it is left for Agda to fill in.)

  Σᵃ-zero : (f : Assign 0 → Amp) {a : Amp} → (∀ v → f v ≐ a) → Σᵃ f ≐ a
  Σᵃ-zero f h i = trans (Σᶻ-zero (λ z → f z i)) (h _ i)


------------------------------------------------------------------------
-- The character sums

-- Σ_z ζ^(2^(M-n) d [z]), the product of two rows (or two columns) of
-- the Fourier matrix whose indices differ by d.  Exponents are written
-- out in full throughout, never through local abbreviations, so that
-- no two powers of ζ are compared by unfolding.

χsum : (n : ℕ) → ℤ → Amp
χsum n d = Σᵃ (λ (z : Assign n) → zpow (pow (M ∸ n) * (d * bin z)))

-- The least significant bit of z contributes a factor
-- 1 + ζ^(2^(M-n-1) d).

χsum-suc : ∀ n → suc n ≤ M → (d : ℤ) →
           χsum (suc n) d ≐
           (zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * d)) ⊛ χsum n d
χsum-suc n le d =
  Σᵃ-suc (λ z → zpow (pow (M ∸ suc n) * (d * bin z)))
  ∙ +ᴬ-cong
      (Σᵃ-cong (λ g → zpow-≡ (even g)))
      (Σᵃ-cong (λ g → zpow-≡ (odd g)
                      ∙ ≐-sym (zpow-⊛-zpow (pow (M ∸ suc n) * d)
                                           (pow (M ∸ n) * (d * bin g))))
       ∙ ≐-sym (⊛-Σᵃ (zpow (pow (M ∸ suc n) * d))
                     (λ g → zpow (pow (M ∸ n) * (d * bin g)))))
  ∙ +ᴬ-cong (≐-sym (⊛-identityˡ (χsum n d))) (λ _ → refl)
  ∙ ≐-sym (⊛-distribʳ-+ᴬ (zpow 0ℤ) (zpow (pow (M ∸ suc n) * d)) (χsum n d))
  where
  -- 2^(M-n) = 2^(M-n-1) · 2.

  half : pow (M ∸ n) ≡ pow (M ∸ suc n) * (+ 2)
  half = pow-half n le

  even : ∀ g → pow (M ∸ suc n) * (d * bin (false ∷ᵃ g)) ≡
               pow (M ∸ n) * (d * bin g)
  even g = trans
    (solve 3 (λ q d B → q :* (d :* (con 0ℤ :+ con (+ 2) :* B)) :=
                        (q :* con (+ 2)) :* (d :* B))
           refl (pow (M ∸ suc n)) d (bin g))
    (cong (λ q → q * (d * bin g)) (sym half))

  odd : ∀ g → pow (M ∸ suc n) * (d * bin (true ∷ᵃ g)) ≡
              pow (M ∸ suc n) * d + pow (M ∸ n) * (d * bin g)
  odd g = trans
    (solve 3 (λ q d B → q :* (d :* (con 1ℤ :+ con (+ 2) :* B)) :=
                        q :* d :+ (q :* con (+ 2)) :* (d :* B))
           refl (pow (M ∸ suc n)) d (bin g))
    (cong (λ q → pow (M ∸ suc n) * d + q * (d * bin g)) (sym half))

-- Only d modulo 2^n matters: 2^(M-n) · 2^n = 2^M.

χsum-mod : ∀ n → n ≤ M → {d d′ : ℤ} → pow n ∣ (d - d′) →
           χsum n d ≐ χsum n d′
χsum-mod n le {d} {d′} (divides t eq) = Σᵃ-cong (λ z →
  zpow-cong {e = pow (M ∸ n) * (d * bin z)} {e′ = pow (M ∸ n) * (d′ * bin z)}
            (divides (t * bin z) (step (pow (M ∸ n)) (bin z) (Rk-order le))))
  where
  step : ∀ p B → p * pow n ≡ pow M →
         p * (d * B) - p * (d′ * B) ≡ (t * B) * pow M
  step p B pq = trans
    (solve 4 (λ p d d′ B → p :* (d :* B) :- p :* (d′ :* B) :=
                           (p :* (d :- d′)) :* B) refl p d d′ B)
    (trans (cong (λ e → (p * e) * B) eq)
      (trans (solve 4 (λ p t q B → (p :* (t :* q)) :* B :=
                                   (t :* B) :* (p :* q))
                      refl p t (pow n) B)
             (cong ((t * B) *_) pq)))


------------------------------------------------------------------------
-- Two rows of the Fourier matrix

private
  -- Comparing two assignments: the low bits, then the top one.

  same-top : (x x′ : Assign (suc n)) →
             same x x′ ≡
             same (λ i → x (inject₁ i)) (λ i → x′ (inject₁ i)) ∧
             (x (fromℕ n) =ᵇ x′ (fromℕ n))
  same-top {zero}  x x′ = ∧-identityʳ (x zero =ᵇ x′ zero)
  same-top {suc n} x x′ = trans
    (cong ((x zero =ᵇ x′ zero) ∧_)
          (same-top (λ i → x (suc i)) (λ i → x′ (suc i))))
    (sym (∧-assoc (x zero =ᵇ x′ zero)
                  (same (λ i → x (suc (inject₁ i)))
                        (λ i → x′ (suc (inject₁ i))))
                  (x (fromℕ (suc n)) =ᵇ x′ (fromℕ (suc n)))))

  double : ∀ t → t + t ≡ (+ 2) * t
  double = solve 1 (λ t → t :+ t := con (+ 2) :* t) refl

  *-1≡ : ∀ t → t * -1ℤ ≡ - t
  *-1≡ = solve 1 (λ t → t :* con -1ℤ := :- t) refl

  -- ζ^(±½) = -1, ½ being 2^(M-1) = H.

  zpow-½ : zpow ½ ≐ -ᴬ zpow 0ℤ
  zpow-½ i = trans (zpow-≡ {a = ½} {b = 0ℤ + (+ H)} refl i) (zpow-anti 0ℤ i)

  zpow-neg½ : zpow (- ½) ≐ -ᴬ zpow 0ℤ
  zpow-neg½ i = trans (sym (neg-involutive (zpow (- ½) i)))
    (cong -_ (trans (sym (zpow-anti (- ½) i))
                    (zpow-≡ {a = - ½ + (+ H)} {b = 0ℤ} (+-inverseˡ ½) i)))

  -- 1 + ζ^(½ (a - b)) is 2 when the bits agree, 1 - 1 = 0 when they
  -- differ.

  factor : ∀ a b → zpow 0ℤ +ᴬ zpow (½ * ([ a ]ᶻ - [ b ]ᶻ)) ≐
                   (+ 2) ·ᴬ [ a =ᵇ b ]ᴬ
  factor true  true  i = trans
    (cong (_+_ (zpow 0ℤ i))
          (zpow-≡ {a = ½ * ([ true ]ᶻ - [ true ]ᶻ)} {b = 0ℤ} (*-zeroʳ ½) i))
    (double (zpow 0ℤ i))
  factor false false i = trans
    (cong (_+_ (zpow 0ℤ i))
          (zpow-≡ {a = ½ * ([ false ]ᶻ - [ false ]ᶻ)} {b = 0ℤ}
                  (*-zeroʳ ½) i))
    (double (zpow 0ℤ i))
  factor true  false i = trans
    (cong (_+_ (zpow 0ℤ i))
          (trans (zpow-≡ {a = ½ * ([ true ]ᶻ - [ false ]ᶻ)} {b = ½}
                         (*-identityʳ ½) i)
                 (zpow-½ i)))
    (+-inverseʳ (zpow 0ℤ i))
  factor false true  i = trans
    (cong (_+_ (zpow 0ℤ i))
          (trans (zpow-≡ {a = ½ * ([ false ]ᶻ - [ true ]ᶻ)} {b = - ½}
                         (*-1≡ ½) i)
                 (zpow-neg½ i)))
    (+-inverseʳ (zpow 0ℤ i))

  -- With the low bits equal, [x] - [x′] = 2^n (x_top - x′_top), and
  -- 2^(M-n-1) · 2^n = ½.

  top-exponent : ∀ n → suc n ≤ M → (x x′ : Assign (suc n)) →
                 (∀ i → x (inject₁ i) ≡ x′ (inject₁ i)) →
                 pow (M ∸ suc n) * (bin x - bin x′) ≡
                 ½ * ([ x (fromℕ n) ]ᶻ - [ x′ (fromℕ n) ]ᶻ)
  top-exponent n le x x′ low = trans
    (cong₂ (λ a b → pow (M ∸ suc n) * (a - b)) (bin-top x) (bin-top x′))
    (trans (cong (λ B → pow (M ∸ suc n) *
                        ((B + pow n * [ x (fromℕ n) ]ᶻ) -
                         (bin (λ i → x′ (inject₁ i)) +
                          pow n * [ x′ (fromℕ n) ]ᶻ)))
                 (bin-≗ low))
      (trans (solve 5 (λ p q B a a′ →
                p :* ((B :+ q :* a) :- (B :+ q :* a′)) :=
                (p :* q) :* (a :- a′))
              refl (pow (M ∸ suc n)) (pow n) (bin (λ i → x′ (inject₁ i)))
                   [ x (fromℕ n) ]ᶻ [ x′ (fromℕ n) ]ᶻ)
             (cong (λ h → h * ([ x (fromℕ n) ]ᶻ - [ x′ (fromℕ n) ]ᶻ))
                   (Rk-primitive (s≤s z≤n) le))))

  -- [x] - [x′] = ([x_low] - [x′_low]) + 2^n (x_top - x′_top).

  low-split : ∀ n (x x′ : Assign (suc n)) →
              (bin x - bin x′) -
              (bin (λ i → x (inject₁ i)) - bin (λ i → x′ (inject₁ i))) ≡
              ([ x (fromℕ n) ]ᶻ - [ x′ (fromℕ n) ]ᶻ) * pow n
  low-split n x x′ = trans
    (cong₂ (λ a b → (a - b) - (bin (λ i → x (inject₁ i)) -
                               bin (λ i → x′ (inject₁ i))))
           (bin-top x) (bin-top x′))
    (solve 5 (λ B B′ q a a′ →
       ((B :+ q :* a) :- (B′ :+ q :* a′)) :- (B :- B′) :=
       (a :- a′) :* q)
     refl (bin (λ i → x (inject₁ i))) (bin (λ i → x′ (inject₁ i)))
          (pow n) [ x (fromℕ n) ]ᶻ [ x′ (fromℕ n) ]ᶻ)

-- The product of the rows at x and x′: 2^n [x = x′].  By induction on
-- n, splitting x at its most significant bit.

χsum-rows : ∀ n → n ≤ M → (x x′ : Assign n) →
            χsum n (bin x - bin x′) ≐ (+ (2 ^ n)) ·ᴬ [ same x x′ ]ᴬ
χsum-rows zero    le x x′ =
  Σᵃ-zero (λ z → zpow (pow (M ∸ 0) * ((bin x - bin x′) * bin z)))
          (λ v → zpow-≡ {a = pow (M ∸ 0) * ((bin x - bin x′) * bin v)}
                        {b = 0ℤ}
                        (*-zeroʳ (pow M)))
  ∙ (λ i → sym (*-identityˡ (zpow 0ℤ i)))
χsum-rows (suc n) le x x′ =
  χsum-suc n le (bin x - bin x′)
  ∙ ⊛-cong {a = zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′))}
           {a′ = zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′))}
           (λ _ → refl)
           (χsum-mod n le′ {d = bin x - bin x′}
                     {d′ = bin (λ i → x (inject₁ i)) -
                           bin (λ i → x′ (inject₁ i))}
                     (divides ([ x (fromℕ n) ]ᶻ - [ x′ (fromℕ n) ]ᶻ)
                              (low-split n x x′))
            ∙ χsum-rows n le′ (λ i → x (inject₁ i)) (λ i → x′ (inject₁ i)))
  ∙ finish (same (λ i → x (inject₁ i)) (λ i → x′ (inject₁ i))) refl
  where
  le′ = ℕ.<⇒≤ le

  -- The low bits decide first.

  same≡ : ∀ {b} → same (λ i → x (inject₁ i)) (λ i → x′ (inject₁ i)) ≡ b →
          same x x′ ≡ b ∧ (x (fromℕ n) =ᵇ x′ (fromℕ n))
  same≡ e = trans (same-top x x′)
                  (cong (_∧ (x (fromℕ n) =ᵇ x′ (fromℕ n))) e)

  finish : ∀ b → same (λ i → x (inject₁ i)) (λ i → x′ (inject₁ i)) ≡ b →
           (zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′))) ⊛
           ((+ (2 ^ n)) ·ᴬ [ b ]ᴬ) ≐
           (+ (2 ^ suc n)) ·ᴬ [ same x x′ ]ᴬ
  finish false e =
    ⊛-cong {a = zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′))}
           {a′ = zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′))}
           {b′ = 0ᴬ} (λ _ → refl) (λ j → *-zeroʳ (+ (2 ^ n)))
    ∙ ⊛-zeroʳ (zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′)))
    ∙ (λ i → sym (trans (cong (λ c → (+ (2 ^ suc n)) * [ c ]ᴬ i) (same≡ e))
                        (*-zeroʳ (+ (2 ^ suc n)))))
  finish true e =
    ⊛-cong {a = zpow 0ℤ +ᴬ zpow (pow (M ∸ suc n) * (bin x - bin x′))}
           {a′ = (+ 2) ·ᴬ [ x (fromℕ n) =ᵇ x′ (fromℕ n) ]ᴬ}
           (+ᴬ-cong {a = zpow 0ℤ} {a′ = zpow 0ℤ} (λ _ → refl)
                    (zpow-≡ (top-exponent n le x x′ (same-true _ _ e)))
            ∙ factor (x (fromℕ n)) (x′ (fromℕ n)))
           (λ _ → refl)
    ∙ ⊛-·ᴬˡ (+ 2) [ x (fromℕ n) =ᵇ x′ (fromℕ n) ]ᴬ
            ((+ (2 ^ n)) ·ᴬ zpow 0ℤ)
    ∙ ·ᴬ-cong (+ 2) (⊛-·ᴬʳ (+ (2 ^ n)) [ x (fromℕ n) =ᵇ x′ (fromℕ n) ]ᴬ
                           (zpow 0ℤ))
    ∙ ·ᴬ-·ᴬ (+ 2) (+ (2 ^ n))
            ([ x (fromℕ n) =ᵇ x′ (fromℕ n) ]ᴬ ⊛ zpow 0ℤ)
    ∙ (λ i → cong₂ _*_ (sym (pos-* 2 (2 ^ n)))
        (trans (⊛-identityʳ [ x (fromℕ n) =ᵇ x′ (fromℕ n) ]ᴬ i)
               (cong (λ c → [ c ]ᴬ i) (sym (same≡ e)))))


------------------------------------------------------------------------
-- The transform is unitary, for n ≤ M

private
  -- ζ^a · conj ζ^b = ζ^(a - b).

  zpow-⊛-conj : ∀ a b → zpow a ⊛ conj (zpow b) ≐ zpow (a - b)
  zpow-⊛-conj a b =
    ⊛-cong {a = zpow a} {a′ = zpow a} (λ _ → refl) (conj-zpow b)
    ∙ zpow-⊛-zpow a (- b)

  rows-term : ∀ p X X′ Z → p * (X * Z) - p * (X′ * Z) ≡ p * ((X - X′) * Z)
  rows-term = solve 4 (λ p X X′ Z → p :* (X :* Z) :- p :* (X′ :* Z) :=
                                    p :* ((X :- X′) :* Z)) refl

  cols-term : ∀ p X Z Z′ → p * (X * Z) - p * (X * Z′) ≡ p * ((Z - Z′) * X)
  cols-term = solve 4 (λ p X Z Z′ → p :* (X :* Z) :- p :* (X :* Z′) :=
                                    p :* ((Z :- Z′) :* X)) refl

-- U†U = I: the rows are orthogonal, of norm 2^n.

QFTˢ-Isometric : ∀ n → n ≤ M → Isometric (QFTˢ n)
QFTˢ-Isometric n le x x′ =
  inner-cong {ψ = amp (QFTˢ n) x}
             {ψ′ = λ z → zpow (pow (M ∸ n) * (bin x * bin z))}
             {φ = amp (QFTˢ n) x′}
             {φ′ = λ z → zpow (pow (M ∸ n) * (bin x′ * bin z))}
             (QFTˢ-matrix x) (QFTˢ-matrix x′)
  ∙ Σᵃ-cong (λ z →
      zpow-⊛-conj (pow (M ∸ n) * (bin x * bin z))
                  (pow (M ∸ n) * (bin x′ * bin z))
      ∙ zpow-≡ (rows-term (pow (M ∸ n)) (bin x) (bin x′) (bin z)))
  ∙ χsum-rows n le x x′

-- UU† = I: the columns likewise, the matrix being symmetric.

QFTˢ-Coisometric : ∀ n → n ≤ M → Coisometric (QFTˢ n)
QFTˢ-Coisometric n le z z′ =
  inner-cong {ψ = λ x → amp (QFTˢ n) x z}
             {ψ′ = λ x → zpow (pow (M ∸ n) * (bin x * bin z))}
             {φ = λ x → amp (QFTˢ n) x z′}
             {φ′ = λ x → zpow (pow (M ∸ n) * (bin x * bin z′))}
             (λ x → QFTˢ-matrix x z) (λ x → QFTˢ-matrix x z′)
  ∙ Σᵃ-cong (λ x →
      zpow-⊛-conj (pow (M ∸ n) * (bin x * bin z))
                  (pow (M ∸ n) * (bin x * bin z′))
      ∙ zpow-≡ (cols-term (pow (M ∸ n)) (bin x) (bin z) (bin z′)))
  ∙ χsum-rows n le z z′

QFTˢ-Unitary : ∀ n → n ≤ M → Unitary (QFTˢ n)
QFTˢ-Unitary n le = QFTˢ-Isometric n le , QFTˢ-Coisometric n le

-- Definition 2.4: the transform is a well-formed path-sum, and its
-- columns have the norms PathSum.Isometry's WellFormed bounds.

QFTˢ-PartialIsometric : ∀ n → n ≤ M → PartialIsometric (QFTˢ n)
QFTˢ-PartialIsometric n le =
  Isometric⇒PartialIsometric (QFTˢ n) (QFTˢ-Isometric n le)

QFTˢ-WellFormed : ∀ n → n ≤ M → WellFormed (QFTˢ n)
QFTˢ-WellFormed n le = Isometric⇒WellFormed (QFTˢ n) (QFTˢ-Isometric n le)


------------------------------------------------------------------------
-- Beyond the precision it is not

-- The assignment with bit i alone set.

unit : Fin n → Assign n
unit zero    zero    = true
unit zero    (suc j) = false
unit (suc i) zero    = false
unit (suc i) (suc j) = unit i j

private
  zeros : Assign n
  zeros _ = false

  bin-zeros : ∀ n → bin (zeros {n}) ≡ 0ℤ
  bin-zeros zero    = refl
  bin-zeros (suc n) = cong (λ b → 0ℤ + (+ 2) * b) (bin-zeros n)

  same-zeros-unit : (i : Fin n) → same zeros (unit i) ≡ false
  same-zeros-unit zero    = refl
  same-zeros-unit (suc i) = same-zeros-unit i

bin-unit : (i : Fin n) → bin (unit i) ≡ pow (toℕ i)
bin-unit {suc n} zero    = cong (λ b → 1ℤ + (+ 2) * b) (bin-zeros n)
bin-unit {suc n} (suc i) = trans
  (cong (λ b → 0ℤ + (+ 2) * b) (bin-unit i))
  (trans (+-identityˡ ((+ 2) * pow (toℕ i)))
    (trans (*-comm (+ 2) (pow (toℕ i))) (sym (pow-suc (toℕ i)))))

-- For n > M the rows at 0 and at the assignment with bit M set are
-- equal, since ζ^(2^M) = 1, and two equal rows cannot be orthogonal.

QFTˢ-not-Isometric : ∀ n → M < n → ¬ Isometric (QFTˢ n)
QFTˢ-not-Isometric n lt iso =
  ℕ.<-irrefl refl (ℕ.<-≤-trans (ℕ.m^n>0 2 n) ≤0)
  where
  bin-x′ : bin (unit (fromℕ< lt)) ≡ pow M
  bin-x′ = trans (bin-unit (fromℕ< lt)) (cong pow (Fin.toℕ-fromℕ< lt))

  rows : ∀ z → amp (QFTˢ n) (unit (fromℕ< lt)) z ≐ amp (QFTˢ n) zeros z
  rows z = QFTˢ-matrix (unit (fromℕ< lt)) z
    ∙ zpow-cong {e = pow (M ∸ n) * (bin (unit (fromℕ< lt)) * bin z)}
                {e′ = pow (M ∸ n) * (bin (zeros {n}) * bin z)}
                (divides (pow (M ∸ n) * bin z) eq)
    ∙ ≐-sym (QFTˢ-matrix zeros z)
    where
    eq : pow (M ∸ n) * (bin (unit (fromℕ< lt)) * bin z) -
         pow (M ∸ n) * (bin (zeros {n}) * bin z) ≡
         (pow (M ∸ n) * bin z) * pow M
    eq = trans (cong₂ (λ a b → pow (M ∸ n) * (a * bin z) -
                               pow (M ∸ n) * (b * bin z))
                      bin-x′ (bin-zeros n))
               (solve 3 (λ p q Z → p :* (q :* Z) :- p :* (con 0ℤ :* Z) :=
                                   (p :* Z) :* q)
                      refl (pow (M ∸ n)) (pow M) (bin z))

  -- Read at the constant coefficient: 2^n = 0.

  2^n≡0 : + (2 ^ n) ≡ 0ℤ
  2^n≡0 =
    trans (sym (*-identityʳ (+ (2 ^ n))))
    (trans (cong ((+ (2 ^ n)) *_) (sym zpow0-at-0))
    (trans (cong (λ c → (+ (2 ^ n)) * [ c ]ᴬ 0ᶠ)
                 (sym (same-refl (zeros {n}))))
    (trans (sym (iso zeros zeros 0ᶠ))
    (trans (inner-cong {ψ = amp (QFTˢ n) zeros} {ψ′ = amp (QFTˢ n) zeros}
                       {φ = amp (QFTˢ n) zeros}
                       {φ′ = amp (QFTˢ n) (unit (fromℕ< lt))}
                       (λ _ _ → refl) (λ z → ≐-sym (rows z)) 0ᶠ)
    (trans (iso zeros (unit (fromℕ< lt)) 0ᶠ)
    (trans (cong (λ c → (+ (2 ^ n)) * [ c ]ᴬ 0ᶠ)
                 (same-zeros-unit (fromℕ< lt)))
           (*-zeroʳ (+ (2 ^ n)))))))))

  ≤0 : 2 ^ n ≤ 0
  ≤0 = ℕ.≤-reflexive (+-injective 2^n≡0)

-- So the transform is unitary exactly at the sizes where it is the
-- Fourier transform.

QFTˢ-Unitary⇔ : ∀ n → Unitary (QFTˢ n) ⇔ n ≤ M
QFTˢ-Unitary⇔ n = mk⇔
  (λ u → ℕ.≮⇒≥ (λ M<n → QFTˢ-not-Isometric n M<n (proj₁ u)))
  (QFTˢ-Unitary n)
