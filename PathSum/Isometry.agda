------------------------------------------------------------------------
-- Presentations of groups
--
-- Isometry restrictions (Amy, QPL 2018, lemma 4.1)
--
-- The isometry restriction ξ|f(x,y)=x of a path-sum keeps only the
-- paths that carry an input x back to x itself.  What it sums at x,
-- the powers ζ^P(x,y) over the paths y with f(x,y) = x, is exactly the
-- unnormalised diagonal entry amp ξ x x, so "ξ|f(x,y)=x ≡ |x⟩ ↦ |x⟩"
-- says that every diagonal entry of U_ξ is 1: amp ξ x x = √2^k ζ^0.
-- That is Restriction-id below.  Lemma 4.1 says that for a
-- well-formed path-sum this already makes ξ the identity, and the
-- reason is a budget: a column of a (partial) isometry has norm at
-- most 1, a diagonal entry equal to 1 spends all of it, and so every
-- entry off the diagonal vanishes.
--
-- Definition 2.4 asks the operator of ξ to be a partial isometry.
-- Only the operator's entries are formalised (amp, in Z[ζ]; see
-- PathSum.Denotation), where adjoints and complex absolute values are
-- not available; what is available is the
-- trace form of PathSum.Norm, ‖a‖² = Tr(a·ā)/H, the average of |σ(a)|²
-- over the H embeddings σ of Q(ζ) into C.  The proof uses one fact
-- about the operator, a bound on the norms of its columns, and
-- WellFormed ξ is that bound read through the trace form: for every
-- input x, Σ_z ‖amp ξ x z‖² ≤ 2^k, that is, every column of U_ξ has
-- norm at most 1.
--
-- The paper's hypothesis implies this one, by the following argument,
-- which is prose and is not formalised.  If U = U_ξ is a partial
-- isometry then U†U is a projection P.  Every embedding σ, applied
-- entrywise, commutes with complex conjugation, Q(ζ) being abelian
-- over Q, so σ(U)†σ(U) = σ(P) is again a projection; and σ(√2) = ±√2,
-- √2 lying in Q(ζ).  Hence Σ_z |σ(amp ξ x z)|² = 2^k ⟨x|σ(P)|x⟩ lies
-- in [0 , 2^k] for every σ, and its average over the embeddings, which
-- is Σ_z ‖amp ξ x z‖², is at most 2^k.  So the hypothesis of
-- lemma-4-1⇐ below follows from the paper's, and the lemma is proved
-- here in a form at least as strong as the paper's -- granted that
-- argument, U_ξ read as the matrix of entries amp ξ x z / √2^k that
-- PathSum.Denotation compares, and for path-sums whose inputs are all
-- variables.  Constant inputs, which are what make an operator only
-- partial, cannot be expressed in PathSum.Base.
--
-- The proof of the converse splits the sum over the column at z = x.
-- The diagonal term is ‖√2^k ζ^0‖² = 2^k, the whole budget, so the
-- rest -- a sum of non-negative terms -- is at most 0, hence every
-- one of its terms is 0, and positive definiteness of the form makes
-- every off-diagonal entry 0.  The forward direction needs no
-- hypothesis: ξ ≋ idPS read on the diagonal is the restriction
-- condition.  For a diagonal path-sum, none of whose paths leaves its
-- input, the off-diagonal entries vanish for want of a path, and the
-- two conditions agree without any well-formedness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc; _^_)

module PathSum.Isometry (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_; _≤_)
open import Data.Integer.Properties using
  (+-assoc; +-identityˡ; +-inverseˡ; *-identityʳ;
   +-monoʳ-≤; ≤-refl; ≤-trans; ≤-reflexive; ≤-antisym)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Assign using (same; same-true; same-intro; same-≗)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-point; Σᶻ-≥0; Σᶻ-≡0)
open import PathSum.Base using (PathSum; phase; idPS)
open import PathSum.Cyclotomic M₀ using
  (0ᴬ; _≐_; Σᴮ-cong; Σᴮ-0; zpow; scale; scale-map; √2·-map; √2·-0ᴬ)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; amp-idPS; amp-≗; hits-elim; outBit-μ)
open import PathSum.Norm M₀ using
  (‖_‖²; ‖‖²-cong; ‖‖²-≥0; ‖‖²-zero; ‖‖²-scale; ‖zpow0‖²)
open import PathSum.Polynomial using (x[_]; eval)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Well-formedness, the restriction, and diagonal path-sums

-- Definition 2.4, in the form the proof uses: every column of U_ξ has
-- norm at most 1, measured by the trace form.  The column of x is
-- amp ξ x z / √2^k over all z, and the normalisation contributes 2^k
-- to its norm.

WellFormed : PathSum n k m → Set
WellFormed {k = k} ξ = ∀ x → Σᶻ (λ z → ‖ amp ξ x z ‖²) ≤ + (2 ^ k)

-- ξ|f(x,y)=x ≡ |x⟩ ↦ |x⟩: the restricted sum at x, which is the
-- diagonal entry amp ξ x x, is √2^k, the amplitude 1 once normalised.

Restriction-id : PathSum n k m → Set
Restriction-id {k = k} ξ = ∀ x → amp ξ x x ≐ scale k (zpow 0ℤ)

-- A path-sum none of whose paths leaves its input.

Diagonal : PathSum n k m → Set
Diagonal ξ = ∀ x y z → hits ξ x y z ≡ true → same x z ≡ true


------------------------------------------------------------------------
-- Entries that no path reaches

-- When no path from x hits z, every term of the sum defining the
-- entry from x to z is 0.

amp-no-path : (ξ : PathSum n k m) (x z : Assign n) →
              (∀ y → hits ξ x y z ≡ true → same x z ≡ true) →
              same x z ≡ false → amp ξ x z ≐ 0ᴬ
amp-no-path {m = m} ξ x z reach ne i =
  trans (Σᴮ-cong term i) (Σᴮ-0 {m} i)
  where
  term : ∀ y →
         (if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ) ≐ 0ᴬ
  term y with hits ξ x y z in h
  ... | true  = contradiction (trans (sym (reach y h)) ne) (λ ())
  ... | false = λ _ → refl

-- The identity is diagonal: its outputs are its input variables, so
-- its single path carries x to x.

idPS-diagonal : Diagonal (idPS {n})
idPS-diagonal x y z h = same-intro x z (λ w →
  trans (sym (outBit-μ idPS x y w x[ w ] refl)) (hits-elim idPS x y z h w))

private
  -- √2^j · 0 = 0.  (Denotation proves this too, privately.)

  scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    _ = refl
  scale-0ᴬ (suc j) w = trans (√2·-map (scale-0ᴬ j) w) (√2·-0ᴬ w)


------------------------------------------------------------------------
-- Being the identity, entry by entry

-- A path-sum is the identity once its diagonal entries are √2^k and
-- the others vanish.  On the diagonal, "same x z" makes z pointwise x;
-- off it, the identity's entry is 0 because its path does not reach z.

≋-id-intro : (ξ : PathSum n k m) → Restriction-id ξ →
             (∀ x z → same x z ≡ false → amp ξ x z ≐ 0ᴬ) →
             ξ ≋ idPS
≋-id-intro {k = k} ξ rid off x z = entry (same x z) refl
  where
  entry : ∀ b → same x z ≡ b → amp ξ x z ≐ scale k (amp idPS x z)
  entry true  eq i =
    trans (amp-≗ ξ x (λ w → sym (same-true x z eq w)) i)
      (trans (rid x i)
        (scale-map k (λ j → trans (sym (amp-idPS x j))
                                  (amp-≗ idPS x (same-true x z eq) j)) i))
  entry false eq i = trans (off x z eq i)
    (sym (trans (scale-map k (amp-no-path idPS x z
                                (λ y → idPS-diagonal x y z) eq) i)
                (scale-0ᴬ k i)))


------------------------------------------------------------------------
-- The budget of a column

private
  -- A masked term of a non-negative summand is non-negative.

  if-≥0 : ∀ b {t} → 0ℤ ≤ t → 0ℤ ≤ (if b then 0ℤ else t)
  if-≥0 true  _   = ≤-refl
  if-≥0 false t≥0 = t≥0

  -- Whatever a spends of a budget a, it has nothing left to spend.

  cancel≤ : ∀ a b → a + b ≤ a → b ≤ 0ℤ
  cancel≤ a b h = ≤-trans (≤-reflexive (sym drop))
    (≤-trans (+-monoʳ-≤ (- a) h) (≤-reflexive (+-inverseˡ a)))
    where
    drop : - a + (a + b) ≡ b
    drop = trans (sym (+-assoc (- a) a b))
                 (trans (cong (_+ b) (+-inverseˡ a)) (+-identityˡ b))

-- In a well-formed path-sum whose restriction is the identity, every
-- off-diagonal entry vanishes.  The column of x splits into its
-- diagonal term, which is 2^k, and the masked rest, which the budget
-- 2^k then bounds by 0; the rest is a sum of norms, so each of them
-- is 0, and a norm is 0 only at 0.

off-diagonal-0 : (ξ : PathSum n k m) → WellFormed ξ → Restriction-id ξ →
                 ∀ x z → same x z ≡ false → amp ξ x z ≐ 0ᴬ
off-diagonal-0 {n = n} {k = k} ξ wf rid x z ne =
  ‖‖²-zero (amp ξ x z)
    (trans (sym (cong (λ b → if b then 0ℤ else f z) ne))
           (Σᶻ-≡0 rest rest≥0 rest-resp Σrest≡0 z))
  where
  f : Assign n → ℤ
  f u = ‖ amp ξ x u ‖²

  f-resp : RespectsZ f
  f-resp u v u≗v = ‖‖²-cong (amp-≗ ξ x u≗v)

  rest : Assign n → ℤ
  rest u = if same x u then 0ℤ else f u

  rest≥0 : ∀ u → 0ℤ ≤ rest u
  rest≥0 u = if-≥0 (same x u) (‖‖²-≥0 (amp ξ x u))

  rest-resp : RespectsZ rest
  rest-resp u v u≗v = cong₂ (λ b t → if b then 0ℤ else t)
    (same-≗ (λ _ → refl) u≗v) (f-resp u v u≗v)

  -- The diagonal term is the whole budget.

  diag : f x ≡ + (2 ^ k)
  diag = trans (‖‖²-cong (rid x))
    (trans (‖‖²-scale k (zpow 0ℤ))
      (trans (cong (λ t → (+ (2 ^ k)) * t) ‖zpow0‖²)
             (*-identityʳ (+ (2 ^ k)))))

  split : Σᶻ f ≡ + (2 ^ k) + Σᶻ rest
  split = trans (Σᶻ-point f f-resp x) (cong (_+ Σᶻ rest) diag)

  spent : + (2 ^ k) + Σᶻ rest ≤ + (2 ^ k)
  spent = ≤-trans (≤-reflexive (sym split)) (wf x)

  Σrest≡0 : Σᶻ rest ≡ 0ℤ
  Σrest≡0 = ≤-antisym (cancel≤ (+ (2 ^ k)) (Σᶻ rest) spent)
                      (Σᶻ-≥0 rest rest≥0)


------------------------------------------------------------------------
-- Lemma 4.1

-- The forward direction is the equivalence read on the diagonal.

lemma-4-1⇒ : (ξ : PathSum n k m) → ξ ≋ idPS → Restriction-id ξ
lemma-4-1⇒ {k = k} ξ ξ≋id x i =
  trans (ξ≋id x x i) (scale-map k (amp-idPS x) i)

-- The converse is where well-formedness is spent.

lemma-4-1⇐ : (ξ : PathSum n k m) → WellFormed ξ → Restriction-id ξ →
             ξ ≋ idPS
lemma-4-1⇐ ξ wf rid = ≋-id-intro ξ rid (off-diagonal-0 ξ wf rid)

lemma-4-1 : (ξ : PathSum n k m) → WellFormed ξ →
            (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1 ξ wf = mk⇔ (lemma-4-1⇒ ξ) (lemma-4-1⇐ ξ wf)

-- A diagonal path-sum is its own isometry restriction: its
-- off-diagonal entries vanish for want of a path, and no
-- well-formedness is needed.

diagonal-≋ : (ξ : PathSum n k m) → Diagonal ξ →
             (ξ ≋ idPS ⇔ Restriction-id ξ)
diagonal-≋ ξ D = mk⇔ (lemma-4-1⇒ ξ)
  (λ rid → ≋-id-intro ξ rid (λ x z → amp-no-path ξ x z (λ y → D x y z)))
