------------------------------------------------------------------------
-- Presentations of groups
--
-- Composing after a contraction keeps a path-sum well formed
-- (Amy, QPL 2018, proposition 2.7)
--
-- Proposition 2.7 claims that composites of well-formed path-sums are
-- well formed; that is false (PathSum.Compose.Counterexample), and
-- PathSum.Compose.WellFormed proves what holds when the path-sum
-- composed after is an isometry (WellFormed-∘).  Its header leaves out
-- the generalisations to a contraction, or a partial isometry, after;
-- this module supplies both.
--
-- Contraction ξ says that the operator of ξ does not increase the
-- norm of any column, the norm being the trace form of PathSum.Norm
-- summed over the entries, ‖ψ‖ᶜ = Σ_z ‖ψ(z)‖² (the norm WellFormed
-- bounds), and the operator the unnormalised applyᴾ ξ of
-- PathSum.Compose.Properties, whence the factor 2^k:
--
--    ‖ applyᴾ ξ ψ ‖ᶜ ≤ 2^k ‖ψ‖ᶜ        for every column ψ .
--
-- (The trace form averages |σ(·)|² over the embeddings σ of Q(ζ), so
-- an operator that is a contraction in every embedding is one here,
-- by averaging; embeddings are not formalised, and neither is that
-- remark nor its converse.)
--
-- WellFormed-∘ᶜ: a WellFormed path-sum followed by a contraction is
-- WellFormed, since each column of ξ′ ∘ ξ is applyᴾ ξ′ applied to a
-- column of ξ (PathSum.Compose.Properties's prop-2-7ᶜ).
--
-- Both kinds of path-sum that definition 2.4 calls well formed are
-- contractions.  An isometry keeps the norm of every column exactly
-- (isometric-norm, hence Isometric⇒Contraction), so WellFormed-∘ is
-- the special case WellFormed-∘-isometric.  A partial isometry, with
-- Gram matrix G Hermitian and G² = 2^k G, is a contraction too
-- (PartialIsometric⇒Contraction): for the column χ = Σ_w ψ(w) G(w,·)
-- the norm ‖2^k ψ − χ‖ᶜ, which is not negative, works out to
-- 2^k (2^k ‖ψ‖ᶜ − q₀), q₀ the norm of the image of ψ.  Hence the
-- well-formedness half of proposition 2.7, corrected
-- (WellFormed-∘-partial): a WellFormed path-sum followed by a partial
-- isometry is WellFormed, and so, by PathSum.PartialIsometry's
-- PartialIsometric⇒WellFormed, is the composite of two partial
-- isometries (PartialIsometric-∘-WellFormed) -- WellFormed, the
-- property lemma 4.1 uses, though not a partial isometry itself
-- (PathSum.Compose.Counterexample).
--
-- The proofs expand the Hermitian product of Σ_w ψ(w)·A(w,·) with
-- itself into the quadratic form Σ_{w,w′} ψ(w) conj ψ(w′)
-- ⟨A(w,·), A(w′,·)⟩ of the Gram matrix of A (inner-Σ⊛, gram-form);
-- this needs the product of Z[ζ] to be commutative and associative,
-- which PathSum.Ring.Laws provides and PathSum.Compose.WellFormed did
-- not have.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Contraction (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; +_; -_; _+_; _*_; _≤_; +<+; Positive; positive)
open import Data.Integer.Properties using
  (+-comm; +-identityʳ; pos-*; +-monoʳ-≤; *-monoˡ-≤-nonNeg;
   *-cancelˡ-≤-pos; ≤-trans; ≤-reflexive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (_^_) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same)
open import PathSum.AssignSum using
  (Σᶻ; Σᶻ-zero; Σᶻ-suc; Σᶻ-cong; Σᶻ-+; Σᶻ-*; Σᶻ-≥0; _∷ᵃ_)
open import PathSum.Base using (PathSum)
open import PathSum.CircuitSemantics M₀ using (Column)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Matrix M₀ using (applyᴾ-matrix′)
open import PathSum.Compose.Properties M₀ using (applyᴾ; prop-2-7ᶜ)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ)
open import PathSum.Compose.WellFormed M₀ using (Σᵃ-Σᴮ; Σᴮ-·ᴬ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _-ᴬ_; -ᴬ_; _+ᴬ_; _·ᴬ_; _≐_; coeff; coeff-map; coeff-·ᴬ; Σᴮ;
   Σᴮ-cong; extend; Respects)
open import PathSum.Denotation M₀ using (Assign; amp; amp-≗)
open import PathSum.Hermitian M₀ using
  (Σᵃ; Σᵃ-cong; Σᵃ-·ᴬ; Σᶻ-neg; coeff-Σᵃ; [_]ᴬ; inner; inner-cong;
   inner-coeff0)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Norm M₀ using
  (⟪_,_⟫; ‖_‖²; ‖‖²-cong; ‖‖²-+; ⟪⟫-negʳ; ‖‖²-neg; ‖‖²-≥0)
open import PathSum.PartialIsometry M₀ using
  (gram; Isometric; PartialIsometric; gram-herm; amp-≗ˣ;
   PartialIsometric⇒WellFormed)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; ⊛-·ᴬˡ; ⊛-·ᴬʳ; ⊛-zeroʳ; conj-cong; conj-·ᴬ; ·ᴬ-cong;
   ⊛-conj-coeff0)
open import PathSum.Ring.Laws M₀ using
  (⊛-comm; ⊛-assoc; ⊛-identityʳ; conj-⊛; Σᴮ-⊛; ⊛-Σᴮ; conj-Σᴮ; Σᵃ-⊛)

open +-*-Solver using (solve; con; _:+_; :-_; _:*_; _:=_)

private
  variable
    n j k k′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- Powers of two.  (PathSum.Compose.WellFormed proves this too,
  -- privately.)

  pow-mult : ∀ k k′ → + (2 ^ k′) * + (2 ^ k) ≡ + (2 ^ (k ℕ+ k′))
  pow-mult k k′ = trans (sym (pos-* (2 ^ k′) (2 ^ k)))
    (cong +_ (trans (ℕ.*-comm (2 ^ k′) (2 ^ k))
                    (sym (ℕ.^-distribˡ-+-* 2 k k′))))


------------------------------------------------------------------------
-- Contractions

-- The trace-form norm of a column, squared: the quantity WellFormed
-- bounds for the columns of a path-sum.

‖_‖ᶜ : Column n → ℤ
‖ ψ ‖ᶜ = Σᶻ (λ z → ‖ ψ z ‖²)

-- The operator of ξ, normalised by 1/√2^k, does not increase norms.

Contraction : PathSum n k m → Set
Contraction {n = n} {k = k} ξ =
  ∀ (ψ : Column n) → Respects ψ → ‖ applyᴾ ξ ψ ‖ᶜ ≤ + (2 ^ k) * ‖ ψ ‖ᶜ

-- A WellFormed path-sum followed by a contraction is WellFormed: the
-- column of x of ξ′ ∘ ξ is the operator of ξ′ applied to that of ξ.

WellFormed-∘ᶜ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
                Contraction ξ′ → WellFormed ξ → WellFormed (ξ′ ∘ᴾ ξ)
WellFormed-∘ᶜ {k′ = k′} {k = k} ξ′ ξ contr wf x =
  ≤-trans (≤-reflexive column)
    (≤-trans (contr (amp ξ x) (λ z z′ zz → amp-≗ ξ x {z} {z′} zz))
      (≤-trans (*-monoˡ-≤-nonNeg (+ (2 ^ k′)) (wf x))
               (≤-reflexive (pow-mult k k′))))
  where
  column : Σᶻ (λ z → ‖ amp (ξ′ ∘ᴾ ξ) x z ‖²) ≡ ‖ applyᴾ ξ′ (amp ξ x) ‖ᶜ
  column = Σᶻ-cong (λ z → ‖‖²-cong (prop-2-7ᶜ ξ′ ξ x z))


------------------------------------------------------------------------
-- Sums over assignments

-- The recursive sum Σᴮ and the opaque one Σᵃ agree, for summands that
-- see assignments only through their values: both split on the head
-- bit, in the opposite order.

Σᴮ-Σᵃ : (f : (Fin j → Bool) → Amp) → Respects f → Σᴮ f ≐ Σᵃ f
Σᴮ-Σᵃ {j = ℕ.zero}  f resp i =
  trans (resp _ _ (λ ()) i) (sym (Σᶻ-zero (λ z → f z i)))
Σᴮ-Σᵃ {j = ℕ.suc j} f resp i =
  trans (cong₂ _+_ (Σᴮ-Σᵃ (λ g → f (extend true g)) (resp-ext true) i)
                   (Σᴮ-Σᵃ (λ g → f (extend false g)) (resp-ext false) i))
  (trans (+-comm (Σᶻ (λ g → f (extend true g) i))
                 (Σᶻ (λ g → f (extend false g) i)))
  (trans (cong₂ _+_ (Σᶻ-cong (λ g → head false g))
                    (Σᶻ-cong (λ g → head true g)))
         (sym (Σᶻ-suc (λ z → f z i)))))
  where
  ext≗ : ∀ b (g : Fin j → Bool) t → extend b g t ≡ (b ∷ᵃ g) t
  ext≗ b g zero    = refl
  ext≗ b g (suc t) = refl

  -- The two recursions build the same assignments, pointwise.

  head : ∀ b (g : Fin j → Bool) → f (extend b g) i ≡ f (b ∷ᵃ g) i
  head b g = resp (extend b g) (b ∷ᵃ g) (ext≗ b g) i

  resp-ext : ∀ b → Respects (λ g → f (extend b g))
  resp-ext b g h g≗h = resp (extend b g) (extend b h) at
    where
    at : ∀ t → extend b g t ≡ extend b h t
    at zero    = refl
    at (suc t) = g≗h t

-- The product passes into Σᵃ on the left.

⊛-Σᵃ : (a : Amp) (f : (Fin j → Bool) → Amp) →
       a ⊛ Σᵃ f ≐ Σᵃ (λ z → a ⊛ f z)
⊛-Σᵃ a f = ⊛-comm a (Σᵃ f) ∙ Σᵃ-⊛ f a ∙ Σᵃ-cong (λ z → ⊛-comm (f z) a)


------------------------------------------------------------------------
-- The quadratic form of a Gram matrix

private
  -- Four factors, regrouped: (a b) conj (c d) = (a conj c) (b conj d).

  regroup : ∀ a b c d → (a ⊛ b) ⊛ conj (c ⊛ d) ≐ (a ⊛ conj c) ⊛ (b ⊛ conj d)
  regroup a b c d =
    ⊛-cong {a = a ⊛ b} {a′ = a ⊛ b} ≐-refl (conj-⊛ c d)
    ∙ ⊛-assoc a b (conj c ⊛ conj d)
    ∙ ⊛-cong {a = a} {a′ = a} ≐-refl
        (≐-sym (⊛-assoc b (conj c) (conj d))
         ∙ ⊛-cong {b = conj d} {b′ = conj d} (⊛-comm b (conj c)) ≐-refl
         ∙ ⊛-assoc (conj c) b (conj d))
    ∙ ≐-sym (⊛-assoc a (conj c) (b ⊛ conj d))

-- The Hermitian product of the column Σ_w ψ(w)·A(w,·) with itself is
-- Σ_{w,w′} ψ(w) conj ψ(w′) ⟨A(w,·), A(w′,·)⟩.

inner-Σ⊛ : (ψ : Column n) (A : Assign n → Column n) →
           inner (λ z → Σᴮ (λ w → ψ w ⊛ A w z))
                 (λ z → Σᴮ (λ w → ψ w ⊛ A w z)) ≐
           Σᴮ (λ w → Σᴮ (λ w′ → (ψ w ⊛ conj (ψ w′)) ⊛ inner (A w) (A w′)))
inner-Σ⊛ {n = n} ψ A =
  Σᵃ-cong term
  ∙ Σᵃ-Σᴮ (λ z w → Σᴮ (λ w′ → T z w w′))
  ∙ Σᴮ-cong (λ w → Σᵃ-Σᴮ (λ z w′ → T z w w′)
                   ∙ Σᴮ-cong (λ w′ → pull w w′))
  where
  a : Assign n → Assign n → Amp
  a w z = ψ w ⊛ A w z

  T : Assign n → Assign n → Assign n → Amp
  T z w w′ = a w z ⊛ conj (a w′ z)

  term : ∀ z → Σᴮ (λ w → a w z) ⊛ conj (Σᴮ (λ w′ → a w′ z)) ≐
               Σᴮ (λ w → Σᴮ (λ w′ → T z w w′))
  term z =
    ⊛-cong {a = Σᴮ (λ w → a w z)} {a′ = Σᴮ (λ w → a w z)} ≐-refl
           (conj-Σᴮ (λ w′ → a w′ z))
    ∙ Σᴮ-⊛ (λ w → a w z) (Σᴮ (λ w′ → conj (a w′ z)))
    ∙ Σᴮ-cong (λ w → ⊛-Σᴮ (a w z) (λ w′ → conj (a w′ z)))

  pull : ∀ w w′ → Σᵃ (λ z → T z w w′) ≐
                 (ψ w ⊛ conj (ψ w′)) ⊛ inner (A w) (A w′)
  pull w w′ =
    Σᵃ-cong (λ z → regroup (ψ w) (A w z) (ψ w′) (A w′ z))
    ∙ ≐-sym (⊛-Σᵃ (ψ w ⊛ conj (ψ w′)) (λ z → A w z ⊛ conj (A w′ z)))

-- For the operator of a path-sum, A is its matrix and the product is
-- its Gram matrix.

gram-form : (ξ : PathSum n k m) (ψ : Column n) →
            inner (applyᴾ ξ ψ) (applyᴾ ξ ψ) ≐
            Σᴮ (λ w → Σᴮ (λ w′ → (ψ w ⊛ conj (ψ w′)) ⊛ gram ξ w w′))
gram-form ξ ψ =
  inner-cong {ψ = applyᴾ ξ ψ} {ψ′ = λ z → Σᴮ (λ w → ψ w ⊛ amp ξ w z)}
             {φ = applyᴾ ξ ψ} {φ′ = λ z → Σᴮ (λ w → ψ w ⊛ amp ξ w z)}
             (applyᴾ-matrix′ ξ ψ) (applyᴾ-matrix′ ξ ψ)
  ∙ inner-Σ⊛ ψ (amp ξ)


------------------------------------------------------------------------
-- Isometries are contractions

-- Against the Gram matrix 2^k·[w = w′] the form collapses to its
-- diagonal: an isometry multiplies the Hermitian product of a column
-- with itself by 2^k ...

isometric-form : (ξ : PathSum n k m) → Isometric ξ → (ψ : Column n) →
                 Respects ψ →
                 inner (applyᴾ ξ ψ) (applyᴾ ξ ψ) ≐ (+ (2 ^ k)) ·ᴬ inner ψ ψ
isometric-form {n = n} {k = k} ξ iso ψ resp =
  gram-form ξ ψ
  ∙ Σᴮ-cong (λ w →
      Σᴮ-cong (λ w′ → entry w w′)
      ∙ Σᴮ-·ᴬ c (λ w′ → if same w w′ then P w w′ else 0ᴬ)
      ∙ ·ᴬ-cong c (Σᴮ-δ w (P w) (resp-P w)))
  ∙ Σᴮ-·ᴬ c (λ w → P w w)
  ∙ ·ᴬ-cong c (Σᴮ-Σᵃ (λ w → P w w) resp-diag)
  where
  c : ℤ
  c = + (2 ^ k)

  P : Assign n → Assign n → Amp
  P w w′ = ψ w ⊛ conj (ψ w′)

  guard : ∀ b a → a ⊛ [ b ]ᴬ ≐ (if b then a else 0ᴬ)
  guard true  a = ⊛-identityʳ a
  guard false a = ⊛-zeroʳ a

  entry : ∀ w w′ → P w w′ ⊛ gram ξ w w′ ≐
                   c ·ᴬ (if same w w′ then P w w′ else 0ᴬ)
  entry w w′ =
    ⊛-cong {a = P w w′} {a′ = P w w′} ≐-refl (iso w w′)
    ∙ ⊛-·ᴬʳ c (P w w′) [ same w w′ ]ᴬ
    ∙ ·ᴬ-cong c (guard (same w w′) (P w w′))

  resp-P : ∀ w → Respects (P w)
  resp-P w g h g≗h =
    ⊛-cong {a = ψ w} {a′ = ψ w} ≐-refl (conj-cong (resp g h g≗h))

  resp-diag : Respects (λ w → P w w)
  resp-diag g h g≗h = ⊛-cong (resp g h g≗h) (conj-cong (resp g h g≗h))

-- ... so it multiplies the norm of every column by exactly 2^k ...

isometric-norm : (ξ : PathSum n k m) → Isometric ξ → (ψ : Column n) →
                 Respects ψ → ‖ applyᴾ ξ ψ ‖ᶜ ≡ + (2 ^ k) * ‖ ψ ‖ᶜ
isometric-norm {k = k} ξ iso ψ resp =
  trans (sym (inner-coeff0 (applyᴾ ξ ψ)))
    (trans (coeff-map (isometric-form ξ iso ψ resp) 0ℤ)
      (trans (coeff-·ᴬ (+ (2 ^ k)) (inner ψ ψ) 0ℤ)
             (cong (+ (2 ^ k) *_) (inner-coeff0 ψ))))

-- ... and is a contraction.  WellFormed-∘ of PathSum.Compose.WellFormed
-- is WellFormed-∘ᶜ at an isometry.

Isometric⇒Contraction : (ξ : PathSum n k m) → Isometric ξ → Contraction ξ
Isometric⇒Contraction ξ iso ψ resp =
  ≤-reflexive (isometric-norm ξ iso ψ resp)

WellFormed-∘-isometric : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
                         Isometric ξ′ → WellFormed ξ →
                         WellFormed (ξ′ ∘ᴾ ξ)
WellFormed-∘-isometric ξ′ ξ iso =
  WellFormed-∘ᶜ ξ′ ξ (Isometric⇒Contraction ξ′ iso)


------------------------------------------------------------------------
-- Partial isometries are contractions

private
  pos2^ : ∀ j → Positive (+ (2 ^ j))
  pos2^ j = positive (+<+ (ℕ.m^n>0 2 j))

  -- The norm of a difference, expanded with the trace form ⟪_,_⟫.

  ‖‖²-diff : ∀ u v →
             ‖ u -ᴬ v ‖² ≡ (‖ u ‖² + (+ 2) * (- ⟪ u , v ⟫)) + ‖ v ‖²
  ‖‖²-diff u v =
    trans (‖‖²-cong {u -ᴬ v} {u +ᴬ (-ᴬ v)} (λ _ → refl))
      (trans (‖‖²-+ u (-ᴬ v))
        (cong₂ (λ s t → (‖ u ‖² + (+ 2) * s) + t)
               (⟪⟫-negʳ u v) (‖‖²-neg v)))

  -- The same, summed over the entries of two columns.

  Σᶻ-expand : (A B C : Assign n → ℤ) →
              Σᶻ (λ z → (A z + (+ 2) * (- B z)) + C z) ≡
              (Σᶻ A + (+ 2) * (- Σᶻ B)) + Σᶻ C
  Σᶻ-expand A B C =
    trans (Σᶻ-+ (λ z → A z + (+ 2) * (- B z)) C)
      (cong (λ t → t + Σᶻ C)
        (trans (Σᶻ-+ A (λ z → (+ 2) * (- B z)))
          (cong (λ t → Σᶻ A + t)
            (trans (Σᶻ-* (+ 2) (λ z → - B z))
                   (cong ((+ 2) *_) (Σᶻ-neg B))))))

  -- 0 ≤ ‖2^k ψ − χ‖ᶜ, read through the expansion.

  settle : ∀ c x q → 0ℤ ≤ ((c * (c * x)) + (+ 2) * (- (c * q))) + c * q →
           c * q ≤ c * (c * x)
  settle c x q h =
    ≤-trans (≤-reflexive (sym (+-identityʳ (c * q))))
      (≤-trans (+-monoʳ-≤ (c * q) h) (≤-reflexive (ident c x q)))
    where
    ident : ∀ c x q →
            c * q + (((c * (c * x)) + (+ 2) * (- (c * q))) + c * q) ≡
            c * (c * x)
    ident = solve 3 (λ c x q →
      c :* q :+ (((c :* (c :* x)) :+ con (+ 2) :* (:- (c :* q))) :+ c :* q)
      := c :* (c :* x)) refl

-- A partial isometry does not increase norms.  With G the Gram matrix
-- of ξ, Hermitian and with G² = 2^k G, and q the form
-- Σ_{w,w′} ψ(w) conj ψ(w′) G(w,w′), the Hermitian product of the
-- operator's image of ψ with itself (gram-form): the column
-- χ = Σ_w ψ(w) G(w,·) has ⟨χ, χ⟩ = 2^k q (inner-Σ⊛, then G² = 2^k G)
-- and ⟨ψ, χ⟩ = q (G Hermitian), so at the constant coefficient
--
--    0 ≤ ‖2^k ψ − χ‖ᶜ = 2^(2k) ‖ψ‖ᶜ − 2·2^k q₀ + 2^k q₀ ,
--
-- which is q₀ ≤ 2^k ‖ψ‖ᶜ, q₀ being the norm of the image.

PartialIsometric⇒Contraction : (ξ : PathSum n k m) → PartialIsometric ξ →
                               Contraction ξ
PartialIsometric⇒Contraction {n = n} {k = k} ξ pi ψ resp =
  ≤-trans (≤-reflexive normφ)
    (*-cancelˡ-≤-pos q₀ (c * ‖ ψ ‖ᶜ) c {{pos2^ k}}
      (settle c ‖ ψ ‖ᶜ q₀
        (subst (0ℤ ≤_) expand
          (Σᶻ-≥0 (λ z → ‖ a z -ᴬ χ z ‖²) (λ z → ‖‖²-≥0 (a z -ᴬ χ z))))))
  where
  c : ℤ
  c = + (2 ^ k)

  G : Assign n → Assign n → Amp
  G = gram ξ

  P : Assign n → Assign n → Amp
  P w w′ = ψ w ⊛ conj (ψ w′)

  Q : Amp
  Q = Σᴮ (λ w → Σᴮ (λ w′ → P w w′ ⊛ G w w′))

  q₀ : ℤ
  q₀ = coeff Q 0ℤ

  χ : Column n
  χ u = Σᴮ (λ w → ψ w ⊛ G w u)

  a : Column n
  a z = c ·ᴬ ψ z

  -- ⟨χ, χ⟩ = 2^k q, by G² = 2^k G.

  idem : ∀ w w′ → inner (G w) (G w′) ≐ c ·ᴬ G w w′
  idem w w′ =
    Σᵃ-cong (λ u → ⊛-cong {a = G w u} {a′ = G w u} ≐-refl (gram-herm ξ w′ u))
    ∙ pi w w′

  χχ : inner χ χ ≐ c ·ᴬ Q
  χχ =
    inner-Σ⊛ ψ G
    ∙ Σᴮ-cong (λ w →
        Σᴮ-cong (λ w′ →
          ⊛-cong {a = P w w′} {a′ = P w w′} ≐-refl (idem w w′)
          ∙ ⊛-·ᴬʳ c (P w w′) (G w w′))
        ∙ Σᴮ-·ᴬ c (λ w′ → P w w′ ⊛ G w w′))
    ∙ Σᴮ-·ᴬ c (λ w → Σᴮ (λ w′ → P w w′ ⊛ G w w′))

  -- ⟨ψ, χ⟩ = q, G being Hermitian.

  per : ∀ u → ψ u ⊛ conj (χ u) ≐ Σᴮ (λ w → P u w ⊛ G u w)
  per u =
    ⊛-cong {a = ψ u} {a′ = ψ u} ≐-refl (conj-Σᴮ (λ w → ψ w ⊛ G w u))
    ∙ ⊛-Σᴮ (ψ u) (λ w → conj (ψ w ⊛ G w u))
    ∙ Σᴮ-cong (λ w →
        ⊛-cong {a = ψ u} {a′ = ψ u} ≐-refl (conj-⊛ (ψ w) (G w u))
        ∙ ≐-sym (⊛-assoc (ψ u) (conj (ψ w)) (conj (G w u)))
        ∙ ⊛-cong {a = P u w} {a′ = P u w} ≐-refl (gram-herm ξ w u))

  resp-u : Respects (λ u → Σᴮ (λ w → P u w ⊛ G u w))
  resp-u g h g≗h = Σᴮ-cong (λ w →
    ⊛-cong (⊛-cong {b = conj (ψ w)} {b′ = conj (ψ w)}
                   (resp g h g≗h) ≐-refl)
           (inner-cong {ψ = amp ξ g} {ψ′ = amp ξ h}
                       {φ = amp ξ w} {φ′ = amp ξ w}
                       (amp-≗ˣ ξ g≗h) (λ _ → ≐-refl)))

  ψχ : inner ψ χ ≐ Q
  ψχ = Σᵃ-cong per
       ∙ ≐-sym (Σᴮ-Σᵃ (λ u → Σᴮ (λ w → P u w ⊛ G u w)) resp-u)

  -- ⟨2^k ψ, 2^k ψ⟩ and ⟨2^k ψ, χ⟩.

  aa : inner a a ≐ c ·ᴬ (c ·ᴬ inner ψ ψ)
  aa =
    Σᵃ-cong (λ z →
      ⊛-cong {a = c ·ᴬ ψ z} {a′ = c ·ᴬ ψ z} ≐-refl (conj-·ᴬ c (ψ z))
      ∙ ⊛-·ᴬˡ c (ψ z) (c ·ᴬ conj (ψ z))
      ∙ ·ᴬ-cong c (⊛-·ᴬʳ c (ψ z) (conj (ψ z))))
    ∙ Σᵃ-·ᴬ c (λ z → c ·ᴬ (ψ z ⊛ conj (ψ z)))
    ∙ ·ᴬ-cong c (Σᵃ-·ᴬ c (λ z → ψ z ⊛ conj (ψ z)))

  aχ : inner a χ ≐ c ·ᴬ Q
  aχ = Σᵃ-cong (λ z → ⊛-·ᴬˡ c (ψ z) (conj (χ z)))
       ∙ Σᵃ-·ᴬ c (λ z → ψ z ⊛ conj (χ z))
       ∙ ·ᴬ-cong c ψχ

  -- The norms, at the constant coefficient.

  normφ : ‖ applyᴾ ξ ψ ‖ᶜ ≡ q₀
  normφ = trans (sym (inner-coeff0 (applyᴾ ξ ψ)))
                (coeff-map (gram-form ξ ψ) 0ℤ)

  norma : ‖ a ‖ᶜ ≡ c * (c * ‖ ψ ‖ᶜ)
  norma = trans (sym (inner-coeff0 a))
    (trans (coeff-map aa 0ℤ)
      (trans (coeff-·ᴬ c (c ·ᴬ inner ψ ψ) 0ℤ)
        (cong (c *_) (trans (coeff-·ᴬ c (inner ψ ψ) 0ℤ)
                            (cong (c *_) (inner-coeff0 ψ))))))

  normχ : ‖ χ ‖ᶜ ≡ c * q₀
  normχ = trans (sym (inner-coeff0 χ))
                (trans (coeff-map χχ 0ℤ) (coeff-·ᴬ c Q 0ℤ))

  cross : Σᶻ (λ z → ⟪ a z , χ z ⟫) ≡ c * q₀
  cross = trans (Σᶻ-cong (λ z → sym (⊛-conj-coeff0 (a z) (χ z))))
    (trans (sym (coeff-Σᵃ (λ z → a z ⊛ conj (χ z)) 0ℤ))
      (trans (coeff-map aχ 0ℤ) (coeff-·ᴬ c Q 0ℤ)))

  expand : Σᶻ (λ z → ‖ a z -ᴬ χ z ‖²) ≡
           ((c * (c * ‖ ψ ‖ᶜ)) + (+ 2) * (- (c * q₀))) + c * q₀
  expand =
    trans (Σᶻ-cong (λ z → ‖‖²-diff (a z) (χ z)))
      (trans (Σᶻ-expand (λ z → ‖ a z ‖²) (λ z → ⟪ a z , χ z ⟫)
                        (λ z → ‖ χ z ‖²))
             (cong₂ _+_ (cong₂ (λ s t → s + (+ 2) * (- t)) norma cross)
                        normχ))

-- Hence the well-formedness half of proposition 2.7, corrected: a
-- WellFormed path-sum followed by a partial isometry (definition 2.4)
-- is WellFormed -- though not a partial isometry in general
-- (PathSum.Compose.Counterexample).

WellFormed-∘-partial : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
                       PartialIsometric ξ′ → WellFormed ξ →
                       WellFormed (ξ′ ∘ᴾ ξ)
WellFormed-∘-partial ξ′ ξ pi =
  WellFormed-∘ᶜ ξ′ ξ (PartialIsometric⇒Contraction ξ′ pi)

-- Definition 2.4 on both sides: the composite of two partial
-- isometries is WellFormed.

PartialIsometric-∘-WellFormed : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
                                PartialIsometric ξ′ → PartialIsometric ξ →
                                WellFormed (ξ′ ∘ᴾ ξ)
PartialIsometric-∘-WellFormed ξ′ ξ pi′ pi =
  WellFormed-∘-partial ξ′ ξ pi′ (PartialIsometric⇒WellFormed ξ pi)
