------------------------------------------------------------------------
-- Presentations of groups
--
-- Definition E.1's permutation, as a permutation
--
-- Equation (65) says that H_[a,b] H_[c,d] is the standard pair
-- H_[0,1] H_[3,2] with Definition E.1's word on each side.  Its
-- semantic content, given `Conjugate`, is what that word *is*: a
-- signed permutation carrying a, b, c, d to 0, 1, 3, 2, with no sign
-- at any of the four.
--
-- The word is four transpositions, built from the outside in:
--
--     π₃ = (d 2)      ρ₃ = π₃              ρ₃ 2 = d
--     π₂ = (c , ρ₃ 3) ρ₂ = π₂ ∘ ρ₃         ρ₂ 3 = c ,  ρ₂ 2 = d
--     π₁ = (b , ρ₂ 1) ρ₁ = π₁ ∘ ρ₂         ρ₁ 1 = b ,  ρ₁ 3 = c , ρ₁ 2 = d
--     π₀ = (a , ρ₁ 0) ρ₀ = π₀ ∘ ρ₁         ρ₀ 0 = a ,  ρ₀ 1 = b , ρ₀ 3 = c , ρ₀ 2 = d
--
-- and the word's own permutation is π₃ π₂ π₁ π₀, which is ρ₀ backwards.
-- Every step is the same: the new transposition sends its numeral where
-- it should, and leaves the earlier images alone because ρ is injective
-- and the numerals differ.  The signs sit at ρᵢ 4, which is none of
-- those images for the same reason.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≡ᵇ_)
open import Data.Nat.Properties using (_≟_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Examples.Groups.Real-Clifford+CH.Encoding using (τ)

------------------------------------------------------------------------
-- Boolean equality on numerals

≡ᵇ-refl : ∀ (u : ℕ) → (u ≡ᵇ u) ≡ true
≡ᵇ-refl zero    = Eq.refl
≡ᵇ-refl (suc u) = ≡ᵇ-refl u

≡ᵇ-t : ∀ (u v : ℕ) → u ≡ v → (u ≡ᵇ v) ≡ true
≡ᵇ-t u v Eq.refl = ≡ᵇ-refl u

≡ᵇ-f : ∀ (u v : ℕ) → u ≢ v → (u ≡ᵇ v) ≡ false
≡ᵇ-f zero    zero    ne = ⊥-elim (ne Eq.refl)
≡ᵇ-f zero    (suc v) ne = Eq.refl
≡ᵇ-f (suc u) zero    ne = Eq.refl
≡ᵇ-f (suc u) (suc v) ne = ≡ᵇ-f u v (λ e → ne (Eq.cong suc e))

------------------------------------------------------------------------
-- The transposition of two numerals

τ-k : ∀ (k i : ℕ) → τ k i k ≡ i
τ-k k i rewrite ≡ᵇ-refl k = Eq.refl

τ-i : ∀ (k i : ℕ) → τ k i i ≡ k
τ-i k i = go (i ≟ k)
  where
  go : Dec (i ≡ k) → τ k i i ≡ k
  go (yes e)  rewrite ≡ᵇ-t i k e = e
  go (no  ne) rewrite ≡ᵇ-f i k ne | ≡ᵇ-refl i = Eq.refl

τ-o : ∀ (k i v : ℕ) → v ≢ k → v ≢ i → τ k i v ≡ v
τ-o k i v nk ni rewrite ≡ᵇ-f v k nk | ≡ᵇ-f v i ni = Eq.refl

τ-mem : ∀ (k i v : ℕ) → (τ k i v ≡ i) ⊎ (τ k i v ≡ k) ⊎ (τ k i v ≡ v)
τ-mem k i v = go (v ≟ k)
  where
  go : Dec (v ≡ k) → (τ k i v ≡ i) ⊎ (τ k i v ≡ k) ⊎ (τ k i v ≡ v)
  go (yes Eq.refl) = inj₁ (τ-k k i)
  go (no  nk)      = go′ (v ≟ i)
    where
    go′ : Dec (v ≡ i) → (τ k i v ≡ i) ⊎ (τ k i v ≡ k) ⊎ (τ k i v ≡ v)
    go′ (yes Eq.refl) = inj₂ (inj₁ (τ-i k i))
    go′ (no  ni)      = inj₂ (inj₂ (τ-o k i v nk ni))

τ-invol : ∀ (k i v : ℕ) → τ k i (τ k i v) ≡ v
τ-invol k i v = go (v ≟ k)
  where
  go : Dec (v ≡ k) → τ k i (τ k i v) ≡ v
  go (yes Eq.refl) = Eq.trans (Eq.cong (τ k i) (τ-k k i)) (τ-i k i)
  go (no  nk)      = go′ (v ≟ i)
    where
    go′ : Dec (v ≡ i) → τ k i (τ k i v) ≡ v
    go′ (yes Eq.refl) = Eq.trans (Eq.cong (τ k i) (τ-i k i)) (τ-k k i)
    go′ (no  ni)      = Eq.trans (Eq.cong (τ k i) (τ-o k i v nk ni))
                                 (τ-o k i v nk ni)

τ-inj : ∀ (k i : ℕ) {u v : ℕ} → τ k i u ≡ τ k i v → u ≡ v
τ-inj k i {u} {v} e =
  Eq.trans (Eq.sym (τ-invol k i u))
           (Eq.trans (Eq.cong (τ k i) e) (τ-invol k i v))

τ-< : ∀ {N : ℕ} (k i v : ℕ) → k < N → i < N → v < N → τ k i v < N
τ-< {N} k i v bk bi bv with τ-mem k i v
... | inj₁ e             = Eq.subst (_< N) (Eq.sym e) bi
... | inj₂ (inj₁ e)      = Eq.subst (_< N) (Eq.sym e) bk
... | inj₂ (inj₂ e)      = Eq.subst (_< N) (Eq.sym e) bv

------------------------------------------------------------------------
-- The four transpositions of Definition E.1
--
-- Named exactly as the word's own `let` bindings, so that `i₂`, `i₁`,
-- `i₀` and the four `m`s below are those of `Encoding.Σ` on the nose.

module Sigma (a b c d : ℕ)
             (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d)
             (bc : b ≢ c) (bd : b ≢ d) (cd : c ≢ d)
  where

  ρ₃ : ℕ → ℕ
  ρ₃ v = τ d 2 v

  i₂ : ℕ
  i₂ = ρ₃ 3

  ρ₂ : ℕ → ℕ
  ρ₂ v = τ c i₂ (ρ₃ v)

  i₁ : ℕ
  i₁ = ρ₂ 1

  ρ₁ : ℕ → ℕ
  ρ₁ v = τ b i₁ (ρ₂ v)

  i₀ : ℕ
  i₀ = ρ₁ 0

  ρ₀ : ℕ → ℕ
  ρ₀ v = τ a i₀ (ρ₁ v)

  m₃ m₂ m₁ m₀ : ℕ
  m₃ = ρ₃ 4
  m₂ = ρ₂ 4
  m₁ = ρ₁ 4
  m₀ = ρ₀ 4

  ----------------------------------------------------------------------
  -- Each is injective, being a composite of transpositions

  ρ₃-inj : ∀ {u v : ℕ} → ρ₃ u ≡ ρ₃ v → u ≡ v
  ρ₃-inj = τ-inj d 2

  ρ₂-inj : ∀ {u v : ℕ} → ρ₂ u ≡ ρ₂ v → u ≡ v
  ρ₂-inj e = ρ₃-inj (τ-inj c i₂ e)

  ρ₁-inj : ∀ {u v : ℕ} → ρ₁ u ≡ ρ₁ v → u ≡ v
  ρ₁-inj e = ρ₂-inj (τ-inj b i₁ e)

  ρ₀-inj : ∀ {u v : ℕ} → ρ₀ u ≡ ρ₀ v → u ≡ v
  ρ₀-inj e = ρ₁-inj (τ-inj a i₀ e)

  ----------------------------------------------------------------------
  -- Where the numerals go

  private
    ≢sym : ∀ {u v : ℕ} → u ≢ v → v ≢ u
    ≢sym ne e = ne (Eq.sym e)

  ρ₃-2 : ρ₃ 2 ≡ d
  ρ₃-2 = τ-i d 2

  ρ₂-3 : ρ₂ 3 ≡ c
  ρ₂-3 = τ-i c i₂

  private
    -- The new transposition does not see an image already placed: it
    -- would force two numerals to agree.
    d≢i₂ : d ≢ i₂
    d≢i₂ e with ρ₃-inj {2} {3} (Eq.trans ρ₃-2 e)
    ... | ()

  ρ₂-2 : ρ₂ 2 ≡ d
  ρ₂-2 = Eq.trans (Eq.cong (τ c i₂) ρ₃-2) (τ-o c i₂ d (≢sym cd) d≢i₂)

  ρ₁-1 : ρ₁ 1 ≡ b
  ρ₁-1 = τ-i b i₁

  private
    c≢i₁ : c ≢ i₁
    c≢i₁ e with ρ₂-inj {3} {1} (Eq.trans ρ₂-3 e)
    ... | ()

    d≢i₁ : d ≢ i₁
    d≢i₁ e with ρ₂-inj {2} {1} (Eq.trans ρ₂-2 e)
    ... | ()

  ρ₁-3 : ρ₁ 3 ≡ c
  ρ₁-3 = Eq.trans (Eq.cong (τ b i₁) ρ₂-3) (τ-o b i₁ c (≢sym bc) c≢i₁)

  ρ₁-2 : ρ₁ 2 ≡ d
  ρ₁-2 = Eq.trans (Eq.cong (τ b i₁) ρ₂-2) (τ-o b i₁ d (≢sym bd) d≢i₁)

  ρ₀-0 : ρ₀ 0 ≡ a
  ρ₀-0 = τ-i a i₀

  private
    b≢i₀ : b ≢ i₀
    b≢i₀ e with ρ₁-inj {1} {0} (Eq.trans ρ₁-1 e)
    ... | ()

    c≢i₀ : c ≢ i₀
    c≢i₀ e with ρ₁-inj {3} {0} (Eq.trans ρ₁-3 e)
    ... | ()

    d≢i₀ : d ≢ i₀
    d≢i₀ e with ρ₁-inj {2} {0} (Eq.trans ρ₁-2 e)
    ... | ()

  ρ₀-1 : ρ₀ 1 ≡ b
  ρ₀-1 = Eq.trans (Eq.cong (τ a i₀) ρ₁-1) (τ-o a i₀ b (≢sym ab) b≢i₀)

  ρ₀-3 : ρ₀ 3 ≡ c
  ρ₀-3 = Eq.trans (Eq.cong (τ a i₀) ρ₁-3) (τ-o a i₀ c (≢sym ac) c≢i₀)

  ρ₀-2 : ρ₀ 2 ≡ d
  ρ₀-2 = Eq.trans (Eq.cong (τ a i₀) ρ₁-2) (τ-o a i₀ d (≢sym ad) d≢i₀)

  ----------------------------------------------------------------------
  -- Where the word's own permutation sends a, b, c and d
  --
  -- The letters act in the order π₀, π₁, π₂, π₃, so the word's
  -- permutation is ρ₀ read backwards.  `a` goes to i₀ and then unwinds
  -- through the three later transpositions; b, c and d are not seen by
  -- the earlier ones.

  π₀ π₁ π₂ π₃ : ℕ → ℕ
  π₃ = τ d 2
  π₂ = τ c i₂
  π₁ = τ b i₁
  π₀ = τ a i₀

  prmΣ : ℕ → ℕ
  prmΣ v = π₃ (π₂ (π₁ (π₀ v)))

  prmΣ-a : prmΣ a ≡ 0
  prmΣ-a =
    Eq.trans (Eq.cong (λ z → π₃ (π₂ (π₁ z))) (τ-k a i₀))
    (Eq.trans (Eq.cong (λ z → π₃ (π₂ z)) (τ-invol b i₁ (ρ₂ 0)))
    (Eq.trans (Eq.cong π₃ (τ-invol c i₂ (ρ₃ 0))) (τ-invol d 2 0)))

  prmΣ-b : prmΣ b ≡ 1
  prmΣ-b =
    Eq.trans (Eq.cong (λ z → π₃ (π₂ (π₁ z))) (τ-o a i₀ b (≢sym ab) b≢i₀))
    (Eq.trans (Eq.cong (λ z → π₃ (π₂ z)) (τ-k b i₁))
    (Eq.trans (Eq.cong π₃ (τ-invol c i₂ (ρ₃ 1))) (τ-invol d 2 1)))

  prmΣ-c : prmΣ c ≡ 3
  prmΣ-c =
    Eq.trans (Eq.cong (λ z → π₃ (π₂ (π₁ z))) (τ-o a i₀ c (≢sym ac) c≢i₀))
    (Eq.trans (Eq.cong (λ z → π₃ (π₂ z)) (τ-o b i₁ c (≢sym bc) c≢i₁))
    (Eq.trans (Eq.cong π₃ (τ-k c i₂)) (τ-invol d 2 3)))

  prmΣ-d : prmΣ d ≡ 2
  prmΣ-d =
    Eq.trans (Eq.cong (λ z → π₃ (π₂ (π₁ z))) (τ-o a i₀ d (≢sym ad) d≢i₀))
    (Eq.trans (Eq.cong (λ z → π₃ (π₂ z)) (τ-o b i₁ d (≢sym bd) d≢i₁))
    (Eq.trans (Eq.cong π₃ (τ-o c i₂ d (≢sym cd) d≢i₂)) (τ-k d 2)))

  ----------------------------------------------------------------------
  -- And where its four signs are not
  --
  -- The k-th sign sits at ρ_k 4, and the point the k-th letter is
  -- reached at is ρ_k of one of 0, 1, 2, 3.

  private
    off₀ : ∀ (k : ℕ) → k ≢ 4 → ρ₀ k ≢ m₀
    off₀ k nk e = nk (ρ₀-inj {k} {4} e)

    off₁ : ∀ (k : ℕ) → k ≢ 4 → ρ₁ k ≢ m₁
    off₁ k nk e = nk (ρ₁-inj {k} {4} e)

    off₂ : ∀ (k : ℕ) → k ≢ 4 → ρ₂ k ≢ m₂
    off₂ k nk e = nk (ρ₂-inj {k} {4} e)

    off₃ : ∀ (k : ℕ) → k ≢ 4 → ρ₃ k ≢ m₃
    off₃ k nk e = nk (ρ₃-inj {k} {4} e)

  -- The four points the letters are reached at, on each of a, b, c, d.
  -- (`p₀ v = v`, `p₁ v = π₀ v`, `p₂ v = π₁ (π₀ v)`, `p₃ v = π₂ (π₁ (π₀ v))`.)

  sgn₀-a : a ≢ m₀
  sgn₀-a = Eq.subst (_≢ m₀) ρ₀-0 (off₀ 0 (λ ()))

  sgn₁-a : π₀ a ≢ m₁
  sgn₁-a = Eq.subst (_≢ m₁) (Eq.sym (τ-k a i₀)) (off₁ 0 (λ ()))

  sgn₂-a : π₁ (π₀ a) ≢ m₂
  sgn₂-a = Eq.subst (_≢ m₂) (Eq.sym step) (off₂ 0 (λ ()))
    where
    step : π₁ (π₀ a) ≡ ρ₂ 0
    step = Eq.trans (Eq.cong π₁ (τ-k a i₀)) (τ-invol b i₁ (ρ₂ 0))

  sgn₃-a : π₂ (π₁ (π₀ a)) ≢ m₃
  sgn₃-a = Eq.subst (_≢ m₃) (Eq.sym step) (off₃ 0 (λ ()))
    where
    step : π₂ (π₁ (π₀ a)) ≡ ρ₃ 0
    step = Eq.trans (Eq.cong (λ z → π₂ (π₁ z)) (τ-k a i₀))
             (Eq.trans (Eq.cong π₂ (τ-invol b i₁ (ρ₂ 0))) (τ-invol c i₂ (ρ₃ 0)))

  sgn₀-b : b ≢ m₀
  sgn₀-b = Eq.subst (_≢ m₀) ρ₀-1 (off₀ 1 (λ ()))

  sgn₁-b : π₀ b ≢ m₁
  sgn₁-b = Eq.subst (_≢ m₁) (Eq.sym step) (off₁ 1 (λ ()))
    where
    step : π₀ b ≡ ρ₁ 1
    step = Eq.trans (τ-o a i₀ b (≢sym ab) b≢i₀) (Eq.sym ρ₁-1)

  sgn₂-b : π₁ (π₀ b) ≢ m₂
  sgn₂-b = Eq.subst (_≢ m₂) (Eq.sym step) (off₂ 1 (λ ()))
    where
    step : π₁ (π₀ b) ≡ ρ₂ 1
    step = Eq.trans (Eq.cong π₁ (τ-o a i₀ b (≢sym ab) b≢i₀)) (τ-k b i₁)

  sgn₃-b : π₂ (π₁ (π₀ b)) ≢ m₃
  sgn₃-b = Eq.subst (_≢ m₃) (Eq.sym step) (off₃ 1 (λ ()))
    where
    step : π₂ (π₁ (π₀ b)) ≡ ρ₃ 1
    step = Eq.trans (Eq.cong (λ z → π₂ (π₁ z)) (τ-o a i₀ b (≢sym ab) b≢i₀))
             (Eq.trans (Eq.cong π₂ (τ-k b i₁)) (τ-invol c i₂ (ρ₃ 1)))

  sgn₀-c : c ≢ m₀
  sgn₀-c = Eq.subst (_≢ m₀) ρ₀-3 (off₀ 3 (λ ()))

  sgn₁-c : π₀ c ≢ m₁
  sgn₁-c = Eq.subst (_≢ m₁) (Eq.sym step) (off₁ 3 (λ ()))
    where
    step : π₀ c ≡ ρ₁ 3
    step = Eq.trans (τ-o a i₀ c (≢sym ac) c≢i₀) (Eq.sym ρ₁-3)

  sgn₂-c : π₁ (π₀ c) ≢ m₂
  sgn₂-c = Eq.subst (_≢ m₂) (Eq.sym step) (off₂ 3 (λ ()))
    where
    step : π₁ (π₀ c) ≡ ρ₂ 3
    step = Eq.trans (Eq.cong π₁ (τ-o a i₀ c (≢sym ac) c≢i₀))
             (Eq.trans (τ-o b i₁ c (≢sym bc) c≢i₁) (Eq.sym ρ₂-3))

  sgn₃-c : π₂ (π₁ (π₀ c)) ≢ m₃
  sgn₃-c = Eq.subst (_≢ m₃) (Eq.sym step) (off₃ 3 (λ ()))
    where
    step : π₂ (π₁ (π₀ c)) ≡ ρ₃ 3
    step = Eq.trans (Eq.cong (λ z → π₂ (π₁ z)) (τ-o a i₀ c (≢sym ac) c≢i₀))
             (Eq.trans (Eq.cong π₂ (τ-o b i₁ c (≢sym bc) c≢i₁)) (τ-k c i₂))

  sgn₀-d : d ≢ m₀
  sgn₀-d = Eq.subst (_≢ m₀) ρ₀-2 (off₀ 2 (λ ()))

  sgn₁-d : π₀ d ≢ m₁
  sgn₁-d = Eq.subst (_≢ m₁) (Eq.sym step) (off₁ 2 (λ ()))
    where
    step : π₀ d ≡ ρ₁ 2
    step = Eq.trans (τ-o a i₀ d (≢sym ad) d≢i₀) (Eq.sym ρ₁-2)

  sgn₂-d : π₁ (π₀ d) ≢ m₂
  sgn₂-d = Eq.subst (_≢ m₂) (Eq.sym step) (off₂ 2 (λ ()))
    where
    step : π₁ (π₀ d) ≡ ρ₂ 2
    step = Eq.trans (Eq.cong π₁ (τ-o a i₀ d (≢sym ad) d≢i₀))
             (Eq.trans (τ-o b i₁ d (≢sym bd) d≢i₁) (Eq.sym ρ₂-2))

  sgn₃-d : π₂ (π₁ (π₀ d)) ≢ m₃
  sgn₃-d = Eq.subst (_≢ m₃) (Eq.sym step) (off₃ 2 (λ ()))
    where
    step : π₂ (π₁ (π₀ d)) ≡ ρ₃ 2
    step = Eq.trans (Eq.cong (λ z → π₂ (π₁ z)) (τ-o a i₀ d (≢sym ad) d≢i₀))
             (Eq.trans (Eq.cong π₂ (τ-o b i₁ d (≢sym bd) d≢i₁))
               (Eq.trans (τ-o c i₂ d (≢sym cd) d≢i₂) (Eq.sym ρ₃-2)))

  ----------------------------------------------------------------------
  -- Bounds
  --
  -- Every index in play is one of a, b, c, d or a numeral below 5.

  module Bounds {N : ℕ} (ba : a < N) (bb : b < N) (bc′ : c < N) (bd′ : d < N)
                (b0 : 0 < N) (b1 : 1 < N) (b2 : 2 < N) (b3 : 3 < N) (b4 : 4 < N)
    where

    i₂< : i₂ < N
    i₂< = τ-< d 2 3 bd′ b2 b3

    m₃< : m₃ < N
    m₃< = τ-< d 2 4 bd′ b2 b4

    i₁< : i₁ < N
    i₁< = τ-< c i₂ (ρ₃ 1) bc′ i₂< (τ-< d 2 1 bd′ b2 b1)

    m₂< : m₂ < N
    m₂< = τ-< c i₂ m₃ bc′ i₂< m₃<

    i₀< : i₀ < N
    i₀< = τ-< b i₁ (ρ₂ 0) bb i₁<
            (τ-< c i₂ (ρ₃ 0) bc′ i₂< (τ-< d 2 0 bd′ b2 b0))

    m₁< : m₁ < N
    m₁< = τ-< b i₁ m₂ bb i₁< m₂<

    m₀< : m₀ < N
    m₀< = τ-< a i₀ m₁ ba i₀< m₁<
