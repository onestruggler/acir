------------------------------------------------------------------------
-- Presentations of groups
--
-- The Hermitian product of columns
--
-- A column of the operator of a path-sum is a function from output
-- assignments to amplitudes, and the entries of U†U are Hermitian
-- products of two columns, Σ_z ψ(z)·conj φ(z).  This module supplies
-- that product in Z[ζ], with the multiplication and conjugation of
-- PathSum.Ring.
--
-- Σᵃ sums amplitudes over all assignments, coordinate by coordinate,
-- through the opaque integer sum Σᶻ of PathSum.AssignSum, so it
-- inherits Σᶻ's ways of being taken apart: at one point, and at one
-- bit.  As there, an assignment is a function, the ones a sum visits
-- are only pointwise equal to a given one, and the lemmas that meet an
-- arbitrary assignment ask the summand to respect pointwise equality.
--
-- inner ψ φ = Σ_z ψ(z) · conj (φ z) is the Hermitian product.  It is
-- Hermitian (conj (inner ψ φ) = inner φ ψ); its constant coefficient
-- at ψ = φ is Σ_z ‖ψ z‖², the trace-form norm of the column that
-- PathSum.Isometry's WellFormed bounds; it is unchanged when both
-- columns are multiplied by the same phase at every z -- which is what
-- the diagonal gates S and CZ do -- and the basis columns
-- z ↦ [x = z] are orthonormal for it.  Normalising both columns by
-- √2^j multiplies it by 2^j, √2 being real.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; _^_)

module PathSum.Hermitian (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; -1ℤ; +_; -_; _+_; _*_; _≤_)
open import Data.Integer.Properties using
  (-1*i≡-i; +-identityʳ; *-identityˡ; *-assoc; pos-*; +-monoʳ-≤; ≤-refl;
   ≤-trans; ≤-reflexive)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Assign using (same; same-refl; same-≗; _[_≔_]; _=ᵇ_)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-+; Σᶻ-*; Σᶻ-0; Σᶻ-point; Σᶻ-at; Σᶻ-≥0)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _·ᴬ_; _≐_; zpow; coeff; Class; pos; neg; classify; rot;
   scale; Respects)
open import PathSum.Norm M₀ using (‖_‖²; coeff-at⁺; coeff-at⁻)
open import PathSum.Ring M₀

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- Sums of amplitudes over assignments

Σᵃ : ((Fin k → Bool) → Amp) → Amp
Σᵃ f i = Σᶻ (λ z → f z i)

-- Linearity, coordinate by coordinate.

Σᵃ-cong : {f g : (Fin k → Bool) → Amp} → (∀ z → f z ≐ g z) → Σᵃ f ≐ Σᵃ g
Σᵃ-cong f≐g i = Σᶻ-cong (λ z → f≐g z i)

Σᵃ-+ : (f g : (Fin k → Bool) → Amp) →
       Σᵃ (λ z → f z +ᴬ g z) ≐ Σᵃ f +ᴬ Σᵃ g
Σᵃ-+ f g i = Σᶻ-+ (λ z → f z i) (λ z → g z i)

Σᵃ-·ᴬ : (c : ℤ) (f : (Fin k → Bool) → Amp) →
        Σᵃ (λ z → c ·ᴬ f z) ≐ c ·ᴬ Σᵃ f
Σᵃ-·ᴬ c f i = Σᶻ-* c (λ z → f z i)

Σᵃ-0 : Σᵃ {k} (λ _ → 0ᴬ) ≐ 0ᴬ
Σᵃ-0 {k} i = Σᶻ-0 {k}

-- Splitting off one point, and pairing the two values of one bit.  A
-- masked amplitude, read at a coordinate, is the masked coordinate.

private
  if-at : ∀ b (A : Amp) i → (if b then 0ᴬ else A) i ≡ (if b then 0ℤ else A i)
  if-at true  A i = refl
  if-at false A i = refl

Σᵃ-point : (f : (Fin k → Bool) → Amp) → Respects f → ∀ x →
           Σᵃ f ≐ f x +ᴬ Σᵃ (λ z → if same x z then 0ᴬ else f z)
Σᵃ-point f resp x i = trans
  (Σᶻ-point (λ z → f z i) (λ g h g≗h → resp g h g≗h i) x)
  (cong (λ t → f x i + t)
        (Σᶻ-cong (λ z → sym (if-at (same x z) (f z) i))))

Σᵃ-at : (i : Fin k) (f : (Fin k → Bool) → Amp) → Respects f →
        Σᵃ f ≐ Σᵃ (λ z → if z i then 0ᴬ
                         else (f (z [ i ≔ false ]) +ᴬ f (z [ i ≔ true ])))
Σᵃ-at i f resp w = trans
  (Σᶻ-at i (λ z → f z w) (λ g h g≗h → resp g h g≗h w))
  (Σᶻ-cong (λ z → sym (if-at (z i)
    (f (z [ i ≔ false ]) +ᴬ f (z [ i ≔ true ])) w)))

-- Negation, and a term of a non-negative sum bounded by the sum.

Σᶻ-neg : (f : (Fin k → Bool) → ℤ) → Σᶻ (λ z → - f z) ≡ - Σᶻ f
Σᶻ-neg f = trans (Σᶻ-cong (λ z → sym (-1*i≡-i (f z))))
                 (trans (Σᶻ-* -1ℤ f) (-1*i≡-i (Σᶻ f)))

private
  if-≥0 : ∀ b {t} → 0ℤ ≤ t → 0ℤ ≤ (if b then 0ℤ else t)
  if-≥0 true  _   = ≤-refl
  if-≥0 false t≥0 = t≥0

Σᶻ-term≤ : (f : (Fin k → Bool) → ℤ) → RespectsZ f →
           (∀ z → 0ℤ ≤ f z) → ∀ x → f x ≤ Σᶻ f
Σᶻ-term≤ f resp f≥0 x = ≤-trans
  (≤-trans (≤-reflexive (sym (+-identityʳ (f x))))
           (+-monoʳ-≤ (f x) (Σᶻ-≥0 (λ z → if same x z then 0ℤ else f z)
                                    (λ z → if-≥0 (same x z) (f≥0 z)))))
  (≤-reflexive (sym (Σᶻ-point f resp x)))

-- A sum of amplitudes has, at every exponent, the sum of the
-- coefficients; hence conjugation commutes with it.

coeff-Σᵃ : (f : (Fin k → Bool) → Amp) → ∀ w →
           coeff (Σᵃ f) w ≡ Σᶻ (λ z → coeff (f z) w)
coeff-Σᵃ f w = go (classify w)
  where
  go : Class w → coeff (Σᵃ f) w ≡ Σᶻ (λ z → coeff (f z) w)
  go (pos i d) = trans (coeff-at⁺ (Σᵃ f) w i d)
    (Σᶻ-cong (λ z → sym (coeff-at⁺ (f z) w i d)))
  go (neg i d) = trans (coeff-at⁻ (Σᵃ f) w i d)
    (trans (sym (Σᶻ-neg (λ z → f z i)))
           (Σᶻ-cong (λ z → sym (coeff-at⁻ (f z) w i d))))

conj-Σᵃ : (f : (Fin k → Bool) → Amp) → conj (Σᵃ f) ≐ Σᵃ (λ z → conj (f z))
conj-Σᵃ f i = coeff-Σᵃ f (- (+ toℕ i))


------------------------------------------------------------------------
-- Basis indicators

-- [ b ]ᴬ is 1 or 0.  The column δ x of PathSum.CircuitSemantics is
-- definitionally z ↦ [ same x z ]ᴬ.

[_]ᴬ : Bool → Amp
[ b ]ᴬ = if b then zpow 0ℤ else 0ᴬ

[]ᴬ-resp : (x : Fin k → Bool) → Respects (λ z → [ same x z ]ᴬ)
[]ᴬ-resp x g h g≗h i = cong (λ b → [ b ]ᴬ i) (same-≗ (λ _ → refl) g≗h)

private
  zpow-exp : ∀ {e e′} → e ≡ e′ → zpow e ≐ zpow e′
  zpow-exp refl _ = refl

  =ᵇ-sym : ∀ a b → (a =ᵇ b) ≡ (b =ᵇ a)
  =ᵇ-sym true  true  = refl
  =ᵇ-sym true  false = refl
  =ᵇ-sym false true  = refl
  =ᵇ-sym false false = refl

  same-sym : (x z : Fin k → Bool) → same x z ≡ same z x
  same-sym {ℕ.zero}  x z = refl
  same-sym {ℕ.suc k} x z = cong₂ _∧_ (=ᵇ-sym (x zero) (z zero))
    (same-sym (λ j → x (suc j)) (λ j → z (suc j)))

conj-[]ᴬ : ∀ b → conj [ b ]ᴬ ≐ [ b ]ᴬ
conj-[]ᴬ true  i =
  trans (conj-zpow 0ℤ i) (zpow-exp {e = - 0ℤ} {e′ = 0ℤ} refl i)
conj-[]ᴬ false i = conj-0ᴬ i

-- Summing the product of the indicators of x = z and of z = x′ over z
-- leaves the indicator of x = x′: the term z = x is it, and every
-- other term vanishes.

Σᵃ-[]ᴬ-⊛ : (x x′ : Fin k → Bool) →
           Σᵃ (λ z → [ same x z ]ᴬ ⊛ [ same z x′ ]ᴬ) ≐ [ same x x′ ]ᴬ
Σᵃ-[]ᴬ-⊛ {k} x x′ i =
  trans (Σᵃ-point f resp x i)
    (trans (cong₂ _+_ (at-x i) (rest i)) (+-identityʳ ([ same x x′ ]ᴬ i)))
  where
  f : (Fin k → Bool) → Amp
  f z = [ same x z ]ᴬ ⊛ [ same z x′ ]ᴬ

  resp : Respects f
  resp g h g≗h = ⊛-cong ([]ᴬ-resp x g h g≗h)
    (λ j → cong (λ b → [ b ]ᴬ j) (same-≗ g≗h (λ _ → refl)))

  at-x : f x ≐ [ same x x′ ]ᴬ
  at-x j = trans
    (⊛-cong {a = [ same x x ]ᴬ} {a′ = zpow 0ℤ}
            (λ l → cong (λ b → [ b ]ᴬ l) (same-refl x)) (λ _ → refl) j)
    (⊛-identityˡ [ same x x′ ]ᴬ j)

  off : ∀ b c → (if b then 0ᴬ else ([ b ]ᴬ ⊛ c)) ≐ 0ᴬ
  off true  c _ = refl
  off false c   = ⊛-zeroˡ c

  rest : Σᵃ (λ z → if same x z then 0ᴬ else f z) ≐ 0ᴬ
  rest j = trans (Σᵃ-cong (λ z → off (same x z) [ same z x′ ]ᴬ) j)
                 (Σᵃ-0 j)


------------------------------------------------------------------------
-- The Hermitian product

inner : ((Fin k → Bool) → Amp) → ((Fin k → Bool) → Amp) → Amp
inner ψ φ = Σᵃ (λ z → ψ z ⊛ conj (φ z))

inner-cong : {ψ ψ′ φ φ′ : (Fin k → Bool) → Amp} →
             (∀ z → ψ z ≐ ψ′ z) → (∀ z → φ z ≐ φ′ z) →
             inner ψ φ ≐ inner ψ′ φ′
inner-cong ψ≐ψ′ φ≐φ′ = Σᵃ-cong (λ z → ⊛-cong (ψ≐ψ′ z) (conj-cong (φ≐φ′ z)))

-- Hermitian symmetry, term by term.

inner-herm : (ψ φ : (Fin k → Bool) → Amp) → conj (inner ψ φ) ≐ inner φ ψ
inner-herm ψ φ i = trans (conj-Σᵃ (λ z → ψ z ⊛ conj (φ z)) i)
  (Σᵃ-cong (λ z → ⊛-conj-herm (ψ z) (φ z)) i)

-- The constant coefficient of the product of a column with itself is
-- the sum of the trace-form norms of its entries.

inner-coeff0 : (ψ : (Fin k → Bool) → Amp) →
               coeff (inner ψ ψ) 0ℤ ≡ Σᶻ (λ z → ‖ ψ z ‖²)
inner-coeff0 ψ = trans (coeff-Σᵃ (λ z → ψ z ⊛ conj (ψ z)) 0ℤ)
  (Σᶻ-cong (λ z → ‖‖²-coeff0 (ψ z)))

-- A diagonal phase, the same on both columns, cancels.

inner-phase : (e : (Fin k → Bool) → ℤ) (ψ φ : (Fin k → Bool) → Amp) →
              inner (λ z → rot (e z) (ψ z)) (λ z → rot (e z) (φ z)) ≐
              inner ψ φ
inner-phase e ψ φ = Σᵃ-cong (λ z → ⊛-conj-rot (e z) (ψ z) (φ z))

-- The basis columns are orthonormal.

inner-basis : (x x′ : Fin k → Bool) →
              inner (λ z → [ same x z ]ᴬ) (λ z → [ same x′ z ]ᴬ) ≐
              [ same x x′ ]ᴬ
inner-basis x x′ i = trans
  (Σᵃ-cong (λ z → ⊛-cong {a = [ same x z ]ᴬ} {a′ = [ same x z ]ᴬ}
    (λ _ → refl)
    (λ j → trans (conj-[]ᴬ (same x′ z) j)
                 (cong (λ b → [ b ]ᴬ j) (same-sym x′ z)))) i)
  (Σᵃ-[]ᴬ-⊛ x x′ i)

-- The normalisation √2^j on both columns multiplies the product by
-- 2^j: √2 is real and √2 · √2 = 2 (PathSum.Ring's ⊛-conj-√2).

inner-scale : ∀ j (ψ φ : (Fin k → Bool) → Amp) →
              inner (λ z → scale j (ψ z)) (λ z → scale j (φ z)) ≐
              (+ (2 ^ j)) ·ᴬ inner ψ φ
inner-scale ℕ.zero    ψ φ i = sym (*-identityˡ (inner ψ φ i))
inner-scale (ℕ.suc j) ψ φ i =
  trans (Σᵃ-cong (λ z → ⊛-conj-√2 (scale j (ψ z)) (scale j (φ z))) i)
    (trans (Σᵃ-·ᴬ (+ 2) (λ z → scale j (ψ z) ⊛ conj (scale j (φ z))) i)
      (trans (cong (λ t → (+ 2) * t) (inner-scale j ψ φ i))
        (trans (sym (*-assoc (+ 2) (+ (2 ^ j)) (inner ψ φ i)))
               (cong (λ t → t * inner ψ φ i) (sym (pos-* 2 (2 ^ j)))))))
