------------------------------------------------------------------------
-- Presentations of groups
--
-- Definition 2.4: isometric and partially isometric path-sums (Amy,
-- QPL 2018)
--
-- Definition 2.4 calls a path-sum well-formed when its operator U_ξ is
-- a (partial) isometry.  The entries of U_ξ are amp ξ x z / √2^k, the
-- entry amp ξ x z lying in Z[ζ] (PathSum.Denotation), so the
-- definition is stated for the unnormalised operator Ũ = √2^k · U_ξ,
-- with the denominators cleared: U†U = Ũ†Ũ / 2^k, √2 being real
-- (PathSum.Ring's conj-√2).  Complex conjugation is ζ ↦ ζ⁻¹ on Z[ζ],
-- which is PathSum.Ring's conj; that Z[ζ] embeds in C with conj going
-- to complex conjugation is the same informal step as reading ≋ as
-- equality of operators.  Clearing the denominators loses nothing:
-- both properties are invariant under ≋ (Isometric-≋,
-- PartialIsometric-≋), path-sums with the same operator having
-- proportional Gram matrices (gram-≋), so they are properties of U_ξ
-- and not of the way ξ writes it.
--
-- gram ξ x x′ = Σ_z amp ξ x z · conj (amp ξ x′ z) is the entry of
-- Ũ†Ũ at (x′ , x), that is, of its transpose.
--
--   * Isometric ξ: gram ξ x x′ = 2^k [x = x′], which is U†U = I (the
--     identity matrix is its own transpose).
--   * PartialIsometric ξ: Σ_x″ gram ξ x x″ · gram ξ x″ x′ = 2^k gram ξ x x′,
--     which is (U†U)² = U†U, U†U being a projection -- the standard
--     definition of a partial isometry.  The square of a transpose is
--     the transpose of the square, so the transposed Gram matrix is
--     idempotent exactly when U†U is.  (That this is equivalent to
--     UU†U = U is not formalised.)
--
-- An isometry is a partial isometry (Isometric⇒PartialIsometric).
--
-- The column norms that PathSum.Isometry's WellFormed bounds are the
-- diagonal of the Gram matrix read at its constant coefficient:
-- Σ_z ‖amp ξ x z‖² is the constant coefficient t of G_xx = gram ξ x x
-- (gram-diag), ‖·‖² being the trace form.  For an isometric path-sum
-- t = 2^k, and WellFormed holds with equality.  For a partial isometry
-- an elementary quadratic argument bounds t, with no appeal to the
-- embeddings of Q(ζ) into C:
--
--   t² ≤ ‖G_xx‖² ≤ Σ_x″ ‖G_xx″‖² = ct (Σ_x″ G_xx″ · G_x″x) = 2^k · t,
--
-- ct being the constant coefficient.  The first step holds because
-- a₀² is one of the terms of the trace form ‖a‖² (coeff0²≤‖‖²); the
-- second because the other terms are squares; the equality because
-- ‖a‖² is the constant coefficient of a · ā (PathSum.Ring) and
-- G_x″x = conj G_xx″ (gram-herm); and the last step is idempotency.
-- So t ≤ 2^k (PartialIsometric⇒WellFormed), and lemma 4.1 holds under
-- definition 2.4 itself, proper partial isometries included
-- (lemma-4-1-partial) -- and so under the reading of section 4.1,
-- "well-formed (i.e. isometric)" (lemma-4-1-isometric).
--
-- WellFormed does not imply definition 2.4: ½·id, with k = 2, no path
-- variables, phase 0 and outputs the inputs, has columns of norm
-- 1 ≤ 2^2 but U†U = ¼·I, which is not a projection (argued here, not
-- formalised).  So PathSum.Isometry's lemma-4-1, stated under
-- WellFormed, remains the strongest form of the lemma, and the two
-- forms here are corollaries of it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; _^_; z≤n)

module PathSum.PartialIsometry (M₀ : ℕ) where

open import Data.Bool.Base using (true; if_then_else_)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; _*_; _≤_; +≤+; +0; +[1+_]; -[1+_])
open import Data.Integer.Properties using
  (*-identityʳ; *-cancelˡ-≡; *-cancelʳ-≤-pos; ≤-trans; ≤-reflexive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Assign using (same; same-refl)
open import PathSum.AssignSum using (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-≥0)
open import PathSum.Base using (PathSum; phase; idPS)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; _·ᴬ_; zpow; coeff; coeff-map; coeff-·ᴬ; scale; Σᴮ-cong)
open import PathSum.Denotation M₀ using (Assign; amp; hits-≗³; _≋_)
open import PathSum.Hermitian M₀
open import PathSum.Isometry M₀ using (WellFormed; Restriction-id; lemma-4-1)
open import PathSum.Norm M₀ using
  (‖_‖²; ‖‖²-cong; ‖‖²-≥0; coeff-zpow0-0)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Ring M₀

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The Gram matrix

-- The Hermitian product of the columns of x and x′: the entry of Ũ†Ũ
-- at (x′ , x).

gram : PathSum n k m → Assign n → Assign n → Amp
gram ξ x x′ = inner (amp ξ x) (amp ξ x′)

-- Definition 2.4, with denominators cleared.

Isometric : PathSum n k m → Set
Isometric {n = n} {k = k} ξ =
  ∀ (x x′ : Assign n) → gram ξ x x′ ≐ (+ (2 ^ k)) ·ᴬ [ same x x′ ]ᴬ

PartialIsometric : PathSum n k m → Set
PartialIsometric {n = n} {k = k} ξ =
  ∀ (x x′ : Assign n) →
  Σᵃ (λ x″ → gram ξ x x″ ⊛ gram ξ x″ x′) ≐ (+ (2 ^ k)) ·ᴬ gram ξ x x′


------------------------------------------------------------------------
-- Properties of the Gram matrix

-- Only the values of the input are read.  The implicit assignments of
-- hits-≗³ and eval-cong are not inferable through `hits`, so they are
-- given.

amp-≗ˣ : (ξ : PathSum n k m) {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
         ∀ z → amp ξ x z ≐ amp ξ x′ z
amp-≗ˣ ξ {x} {x′} x≗x′ z = Σᴮ-cong (λ y i →
  cong₂ (λ b e → (if b then zpow e else 0ᴬ) i)
    (hits-≗³ ξ {x} {x′} {y} {y} {z} {z} x≗x′ (λ _ → refl) (λ _ → refl))
    (eval-cong (phase ξ) {x} {x′} {y} {y} x≗x′ (λ _ → refl)))

gram-resp : (ξ : PathSum n k m) (x : Assign n) {x″ x‴ : Assign n} →
            (∀ i → x″ i ≡ x‴ i) → gram ξ x x″ ≐ gram ξ x x‴
gram-resp ξ x x″≗x‴ =
  inner-cong {ψ = amp ξ x} {ψ′ = amp ξ x} (λ _ _ → refl) (amp-≗ˣ ξ x″≗x‴)

-- The Gram matrix is Hermitian, and its diagonal, read at the
-- constant coefficient, is the trace-form norm of a column.

gram-herm : (ξ : PathSum n k m) (x x′ : Assign n) →
            conj (gram ξ x x′) ≐ gram ξ x′ x
gram-herm ξ x x′ = inner-herm (amp ξ x) (amp ξ x′)

gram-diag : (ξ : PathSum n k m) (x : Assign n) →
            coeff (gram ξ x x) 0ℤ ≡ Σᶻ (λ z → ‖ amp ξ x z ‖²)
gram-diag ξ x = inner-coeff0 (amp ξ x)


------------------------------------------------------------------------
-- Isometries are well-formed

-- The column of x has norm 2^k: the constant coefficient of
-- 2^k · [x = x] = 2^k · ζ^0.

private
  coeff-[true]ᴬ : coeff [ true ]ᴬ 0ℤ ≡ 1ℤ
  coeff-[true]ᴬ = trans (cong (λ A → coeff A 0ℤ) unfold)
    (trans (coeff-exp (zpow 0ℤ) 0ℤ (+ 0) refl) coeff-zpow0-0)
    where
    unfold : [ true ]ᴬ ≡ zpow 0ℤ
    unfold = refl

Isometric⇒unit-columns : (ξ : PathSum n k m) → Isometric ξ →
                         ∀ x → Σᶻ (λ z → ‖ amp ξ x z ‖²) ≡ + (2 ^ k)
Isometric⇒unit-columns {k = k} ξ iso x =
  trans (sym (gram-diag ξ x))
    (trans (coeff-map (iso x x) 0ℤ)
      (trans (coeff-·ᴬ (+ (2 ^ k)) [ same x x ]ᴬ 0ℤ)
        (trans (cong (λ b → (+ (2 ^ k)) * coeff [ b ]ᴬ 0ℤ) (same-refl x))
          (trans (cong ((+ (2 ^ k)) *_) coeff-[true]ᴬ)
                 (*-identityʳ (+ (2 ^ k)))))))

Isometric⇒WellFormed : (ξ : PathSum n k m) → Isometric ξ → WellFormed ξ
Isometric⇒WellFormed ξ iso x = ≤-reflexive (Isometric⇒unit-columns ξ iso x)

-- Lemma 4.1 under the paper's hypothesis, read as in section 4.1:
-- for an isometric path-sum, ξ ≡ |x⟩ ↦ |x⟩ exactly when its isometry
-- restriction is.

lemma-4-1-isometric : (ξ : PathSum n k m) → Isometric ξ →
                      (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1-isometric ξ iso = lemma-4-1 ξ (Isometric⇒WellFormed ξ iso)


------------------------------------------------------------------------
-- Isometries are partial isometries

-- A factor c on both sides of every product of a sum comes out
-- twice.

private
  Σᵃ-⊛-·ᴬ : (c : ℤ) (A B : Assign n → Amp) →
            Σᵃ (λ x″ → (c ·ᴬ A x″) ⊛ (c ·ᴬ B x″)) ≐
            c ·ᴬ (c ·ᴬ Σᵃ (λ x″ → A x″ ⊛ B x″))
  Σᵃ-⊛-·ᴬ c A B i =
    trans (Σᵃ-cong step i)
      (trans (Σᵃ-·ᴬ c (λ x″ → c ·ᴬ (A x″ ⊛ B x″)) i)
             (cong (λ t → c * t) (Σᵃ-·ᴬ c (λ x″ → A x″ ⊛ B x″) i)))
    where
    step : ∀ x″ → (c ·ᴬ A x″) ⊛ (c ·ᴬ B x″) ≐ c ·ᴬ (c ·ᴬ (A x″ ⊛ B x″))
    step x″ j = trans (⊛-·ᴬˡ c (A x″) (c ·ᴬ B x″) j)
                      (·ᴬ-cong c (⊛-·ᴬʳ c (A x″) (B x″)) j)

-- If U†U = I then (U†U)² = U†U: with the Gram matrix 2^k times the
-- identity, its square is 2^k · 2^k times the square of the identity,
-- which is the identity again (Σᵃ-[]ᴬ-⊛).

Isometric⇒PartialIsometric : (ξ : PathSum n k m) → Isometric ξ →
                             PartialIsometric ξ
Isometric⇒PartialIsometric {k = k} ξ iso x x′ i =
  trans (Σᵃ-cong (λ x″ → ⊛-cong (iso x x″) (iso x″ x′)) i)
    (trans (Σᵃ-⊛-·ᴬ c (λ x″ → [ same x x″ ]ᴬ) (λ x″ → [ same x″ x′ ]ᴬ) i)
      (cong (λ t → c * t)
        (trans (cong (λ t → c * t) (Σᵃ-[]ᴬ-⊛ x x′ i))
               (sym (iso x x′ i)))))
  where
  c : ℤ
  c = + (2 ^ k)


------------------------------------------------------------------------
-- Partial isometries are well-formed

-- The quadratic step: a non-negative t with t² ≤ b·t is at most b.

quad : ∀ (t : ℤ) (b : ℕ) → 0ℤ ≤ t → t * t ≤ (+ b) * t → t ≤ + b
quad +0         b _  _  = +≤+ z≤n
quad +[1+ j ]   b _  tt = *-cancelʳ-≤-pos +[1+ j ] (+ b) +[1+ j ] tt
quad -[1+ j ]   b () _

-- Definition 2.4 bounds the columns.  Let G be the Gram matrix and t
-- the constant coefficient of its diagonal entry G_xx, which is the
-- column norm Σ_z ‖amp ξ x z‖² that WellFormed bounds (gram-diag).
-- The constant coefficient of an entry squared is at most its norm
-- (coeff0²≤‖‖²), and one term of a non-negative sum at most the sum,
-- so t² ≤ ‖G_xx‖² ≤ Σ_x″ ‖G_xx″‖².  That sum is the constant
-- coefficient of Σ_x″ G_xx″ · conj G_xx″, which Hermitian symmetry
-- turns into the diagonal entry of G², and idempotency makes it
-- 2^k · t.  So t² ≤ 2^k · t, and t ≤ 2^k.

PartialIsometric⇒WellFormed : (ξ : PathSum n k m) → PartialIsometric ξ →
                              WellFormed ξ
PartialIsometric⇒WellFormed {n = n} {k = k} ξ pi x =
  ≤-trans (≤-reflexive (sym diag)) (quad t (2 ^ k) t≥0 t²≤)
  where
  g : Assign n → Amp
  g x″ = gram ξ x x″

  t : ℤ
  t = coeff (g x) 0ℤ

  diag : t ≡ Σᶻ (λ z → ‖ amp ξ x z ‖²)
  diag = gram-diag ξ x

  -- The diagonal entry of G², its second factor read by Hermitian
  -- symmetry.

  square : Σᵃ (λ x″ → g x″ ⊛ conj (g x″)) ≐ (+ (2 ^ k)) ·ᴬ g x
  square i = trans
    (Σᵃ-cong (λ x″ → ⊛-cong {a = g x″} {a′ = g x″}
                              (λ _ → refl) (gram-herm ξ x x″)) i)
    (pi x x i)

  sum-sq : Σᶻ (λ x″ → ‖ g x″ ‖²) ≡ (+ (2 ^ k)) * t
  sum-sq = trans (sym (Σᶻ-cong (λ x″ → ‖‖²-coeff0 (g x″))))
    (trans (sym (coeff-Σᵃ (λ x″ → g x″ ⊛ conj (g x″)) 0ℤ))
      (trans (coeff-map square 0ℤ) (coeff-·ᴬ (+ (2 ^ k)) (g x) 0ℤ)))

  resp : RespectsZ (λ x″ → ‖ g x″ ‖²)
  resp u v u≗v = ‖‖²-cong (gram-resp ξ x u≗v)

  t²≤ : t * t ≤ (+ (2 ^ k)) * t
  t²≤ = ≤-trans (coeff0²≤‖‖² (g x))
    (≤-trans (Σᶻ-term≤ (λ x″ → ‖ g x″ ‖²) resp (λ x″ → ‖‖²-≥0 (g x″)) x)
             (≤-reflexive sum-sq))

  t≥0 : 0ℤ ≤ t
  t≥0 = ≤-trans (Σᶻ-≥0 (λ z → ‖ amp ξ x z ‖²) (λ z → ‖‖²-≥0 (amp ξ x z)))
                (≤-reflexive (sym diag))

-- Lemma 4.1 under definition 2.4 itself.

lemma-4-1-partial : (ξ : PathSum n k m) → PartialIsometric ξ →
                    (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1-partial ξ pi = lemma-4-1 ξ (PartialIsometric⇒WellFormed ξ pi)


------------------------------------------------------------------------
-- Definition 2.4 is a property of the operator

-- Isometric and PartialIsometric are stated on the entries amp ξ x z,
-- the normalisation 1/√2^k cleared.  They depend only on the operator
-- that ≋ compares: ξ ≋ ζ says √2^k′ · amp ξ = √2^k · amp ζ entrywise,
-- and normalising both columns by √2^j multiplies their product by
-- 2^j (inner-scale), so equivalent path-sums have proportional Gram
-- matrices, and powers of 2 cancel.

gram-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
         ∀ x x′ → (+ (2 ^ k′)) ·ᴬ gram ξ x x′ ≐ (+ (2 ^ k)) ·ᴬ gram ζ x x′
gram-≋ {k = k} {k′ = k′} ξ ζ eq x x′ i =
  trans (sym (inner-scale k′ (amp ξ x) (amp ξ x′) i))
    (trans (inner-cong {ψ = λ z → scale k′ (amp ξ x z)}
                       {ψ′ = λ z → scale k (amp ζ x z)}
                       {φ = λ z → scale k′ (amp ξ x′ z)}
                       {φ′ = λ z → scale k (amp ζ x′ z)}
                       (eq x) (eq x′) i)
           (inner-scale k (amp ζ x) (amp ζ x′) i))

private
  cancel : ∀ j {s t : ℤ} → (+ (2 ^ j)) * s ≡ (+ (2 ^ j)) * t → s ≡ t
  cancel j {s} {t} = *-cancelˡ-≡ (+ (2 ^ j)) s t {{ℕ.m^n≢0 2 j}}

  swap : ∀ p q t → p * (q * t) ≡ q * (p * t)
  swap = solve 3 (λ p q t → p :* (q :* t) := q :* (p :* t)) refl

  swap₂ : ∀ p q t → q * (q * (p * t)) ≡ p * (q * (q * t))
  swap₂ = solve 3 (λ p q t → q :* (q :* (p :* t)) := p :* (q :* (q :* t)))
                  refl

Isometric-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
              Isometric ξ → Isometric ζ
Isometric-≋ {k = k} {k′ = k′} ξ ζ eq iso x x′ i = cancel k
  (trans (sym (gram-≋ ξ ζ eq x x′ i))
    (trans (cong (λ t → (+ (2 ^ k′)) * t) (iso x x′ i))
           (swap (+ (2 ^ k′)) (+ (2 ^ k)) ([ same x x′ ]ᴬ i))))

-- For idempotency the factor appears squared: 2^k · 2^k times the
-- square of ζ's Gram matrix is the square of 2^k′ times ξ's.

PartialIsometric-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
                     PartialIsometric ξ → PartialIsometric ζ
PartialIsometric-≋ {n = n} {k = k} {k′ = k′} ξ ζ eq pi x x′ i =
  cancel k (cancel k
    (trans (sym (Σᵃ-⊛-·ᴬ a (gram ζ x) (λ x″ → gram ζ x″ x′) i))
      (trans (Σᵃ-cong (λ x″ → ⊛-cong (back x x″) (back x″ x′)) i)
        (trans (Σᵃ-⊛-·ᴬ a′ (gram ξ x) (λ x″ → gram ξ x″ x′) i)
          (trans (cong (λ t → a′ * (a′ * t)) (pi x x′ i))
            (trans (swap₂ a a′ (gram ξ x x′ i))
              (trans (cong (λ t → a * (a′ * t)) (gram-≋ ξ ζ eq x x′ i))
                     (cong (λ t → a * t)
                           (swap a′ a (gram ζ x x′ i))))))))))
  where
  a a′ : ℤ
  a  = + (2 ^ k)
  a′ = + (2 ^ k′)

  back : ∀ u v → a ·ᴬ gram ζ u v ≐ a′ ·ᴬ gram ξ u v
  back u v j = sym (gram-≋ ξ ζ eq u v j)
