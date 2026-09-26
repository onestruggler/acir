------------------------------------------------------------------------
-- Presentations of groups
--
-- Well-formedness under composition (Amy, QPL 2018, proposition 2.7)
--
-- Proposition 2.7 says: for well-formed, compatible path-sums ξ and ξ′,
-- ξ′ ∘ ξ is well formed, and U_{ξ′∘ξ} = U_ξ′ U_ξ.  The second half
-- holds with no hypotheses (PathSum.Compose.Properties).  The first
-- half is false.  Compatibility is vacuous here, every input being a
-- variable, and well-formedness is not preserved, neither in the sense
-- of definition 2.4 (the operator is a partial isometry,
-- PathSum.PartialIsometry's PartialIsometric) nor in the weaker sense
-- lemma 4.1 uses (every column has trace-form norm at most 1,
-- PathSum.Isometry's WellFormed).  PathSum.Compose.Counterexample
-- gives both counterexamples: two WellFormed path-sums on one qubit
-- whose composite is not, and the projections |0⟩⟨0| and |+⟩⟨+|, both
-- PartialIsometric, whose composite (1/√2)|+⟩⟨0| is not.
--
-- What does hold is proved here.
--
--   * WellFormed is a property of the operator: it is invariant under
--     ≋ (WellFormed-≋).  PathSum.PartialIsometry already shows this of
--     Isometric and PartialIsometric.
--
--   * The paper's footnote observes that in practice only unitaries
--     are composed.  Composing with an isometry is harmless: if ξ′ is
--     Isometric, the Gram matrix of ξ′ ∘ ξ is 2^k′ times that of ξ,
--     whatever ξ is (gram-∘).  So the composite of two isometries is
--     an isometry (Isometric-∘), and composing a partial isometry, or
--     a WellFormed path-sum, with an isometry after it gives a partial
--     isometry (PartialIsometric-∘), or a WellFormed path-sum
--     (WellFormed-∘).  In the second counterexample the path-sum
--     composed after is |+⟩⟨+|, a partial isometry but not an
--     isometry: for PartialIsometric-∘ -- the composite being a
--     partial isometry -- the hypothesis cannot be weakened to
--     definition 2.4.  (For WellFormed-∘ it can; see below.)
--
-- Not here: that a WellFormed path-sum followed by any partial
-- isometry, or any contraction, is still WellFormed.  Its proof needs
-- the product of Z[ζ] to be commutative and associative, and it is
-- PathSum.Compose.Contraction (WellFormed-∘ᶜ, WellFormed-∘-partial),
-- over PathSum.Ring.Laws.
--
-- gram-∘ is proved on paths, without the commutativity or
-- associativity of Z[ζ]'s product, which PathSum.Ring does not
-- provide.  By proposition 2.7 each column of ξ′ ∘ ξ is a sum over the
-- paths y of ξ of ζ^{P(x,y)} times a column of ξ′ (prop-2-7ʳ), and
-- each column of ξ is the same sum of basis columns (amp-Σδ).  The
-- Hermitian product of two such sums is the double sum over pairs of
-- paths of the products of the columns summed, rotated by
-- ζ^{P(x,y) - P(x′,y′)} (inner-Σrot).  Each product of two columns of
-- ξ′ is 2^k′ times that of the two basis columns, which is the
-- statement that ξ′ is an isometry, and summed back that is 2^k′ times
-- the Gram matrix of ξ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.WellFormed (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Integer.Base using
  (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_; _≤_; +<+; Positive; positive)
open import Data.Integer.Properties using
  (*-comm; *-distribˡ-+; pos-*; *-cancelˡ-≤-pos; *-monoˡ-≤-nonNeg;
   ≤-trans; ≤-reflexive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _^_) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same)
open import PathSum.AssignSum using (Σᶻ; Σᶻ-cong; Σᶻ-*)
open import PathSum.Base using (PathSum; phase)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Matrix M₀ using (sum-⊛; ⊛-sum)
open import PathSum.Compose.Properties M₀ using (amp-Σδ; prop-2-7ʳ)
open import PathSum.Cyclotomic M₀ using
  (Amp; _·ᴬ_; _≐_; coeff; coeff-map; coeff-·ᴬ; extend; Σᴮ;
   Σᴮ-cong; rot; rot-map; rot-·ᴬ; rot-Σᴮ; scale)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Hermitian M₀ using
  (Σᵃ; Σᵃ-cong; Σᵃ-+; Σᵃ-·ᴬ; coeff-Σᵃ; [_]ᴬ; inner; inner-cong;
   inner-basis)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Norm M₀ using (‖_‖²; ‖‖²-cong; ‖‖²-scale)
open import PathSum.PartialIsometry M₀ using
  (gram; Isometric; PartialIsometric; gram-diag)
open import PathSum.Polynomial using (eval)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; conj-+ᴬ; conj-rot; ⊛-rotˡ; ⊛-rotʳ; ⊛-·ᴬˡ; ⊛-·ᴬʳ;
   ·ᴬ-cong; ·ᴬ-·ᴬ)

open +-*-Solver using (solve; _:*_; _:=_)

private
  variable
    n j k k′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- Powers of two.

  pos2^ : ∀ j → Positive (+ (2 ^ j))
  pos2^ j = positive (+<+ (ℕ.m^n>0 2 j))

  pow-mult : ∀ k k′ → + (2 ^ k′) * + (2 ^ k) ≡ + (2 ^ (k ℕ+ k′))
  pow-mult k k′ = trans (sym (pos-* (2 ^ k′) (2 ^ k)))
    (cong +_ (trans (ℕ.*-comm (2 ^ k′) (2 ^ k))
                    (sym (ℕ.^-distribˡ-+-* 2 k k′))))


------------------------------------------------------------------------
-- WellFormed is a property of the operator

-- ξ ≋ ζ says √2^k′ · amp ξ = √2^k · amp ζ entrywise, so the norms of
-- the columns satisfy 2^k′ ‖ξ's‖ = 2^k ‖ζ's‖, and ξ's bound 2^k carries
-- over to ζ's bound 2^k′.

WellFormed-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
               WellFormed ξ → WellFormed ζ
WellFormed-≋ {n = n} {k = k} {k′ = k′} ξ ζ eq wf x =
  *-cancelˡ-≤-pos (Σᶻ (λ z → ‖ amp ζ x z ‖²)) (+ (2 ^ k′)) (+ (2 ^ k))
                  {{pos2^ k}} bound
  where
  entry : ∀ z → + (2 ^ k) * ‖ amp ζ x z ‖² ≡ + (2 ^ k′) * ‖ amp ξ x z ‖²
  entry z = trans (sym (‖‖²-scale k (amp ζ x z)))
    (trans (‖‖²-cong {scale k (amp ζ x z)} {scale k′ (amp ξ x z)}
                      (λ i → sym (eq x z i)))
           (‖‖²-scale k′ (amp ξ x z)))

  total : + (2 ^ k) * Σᶻ (λ z → ‖ amp ζ x z ‖²) ≡
          + (2 ^ k′) * Σᶻ (λ z → ‖ amp ξ x z ‖²)
  total = trans (sym (Σᶻ-* (+ (2 ^ k)) (λ z → ‖ amp ζ x z ‖²)))
    (trans (Σᶻ-cong entry) (Σᶻ-* (+ (2 ^ k′)) (λ z → ‖ amp ξ x z ‖²)))

  bound : + (2 ^ k) * Σᶻ (λ z → ‖ amp ζ x z ‖²) ≤ + (2 ^ k) * + (2 ^ k′)
  bound = ≤-trans (≤-reflexive total)
    (≤-trans (*-monoˡ-≤-nonNeg (+ (2 ^ k′)) (wf x))
             (≤-reflexive (*-comm (+ (2 ^ k′)) (+ (2 ^ k)))))


------------------------------------------------------------------------
-- Sums and conjugates

-- Conjugation, integer multiples and rotations pass through sums.

conj-Σᴮ : (f : (Fin j → Bool) → Amp) → conj (Σᴮ f) ≐ Σᴮ (λ y → conj (f y))
conj-Σᴮ {j = zero}  f _ = refl
conj-Σᴮ {j = suc j} f i = trans
  (conj-+ᴬ (Σᴮ (λ y → f (extend true y))) (Σᴮ (λ y → f (extend false y))) i)
  (cong₂ _+_ (conj-Σᴮ (λ y → f (extend true y)) i)
             (conj-Σᴮ (λ y → f (extend false y)) i))

Σᴮ-·ᴬ : (c : ℤ) (f : (Fin j → Bool) → Amp) →
        Σᴮ (λ y → c ·ᴬ f y) ≐ c ·ᴬ Σᴮ f
Σᴮ-·ᴬ {j = zero}  c f _ = refl
Σᴮ-·ᴬ {j = suc j} c f i = trans
  (cong₂ _+_ (Σᴮ-·ᴬ c (λ y → f (extend true y)) i)
             (Σᴮ-·ᴬ c (λ y → f (extend false y)) i))
  (sym (*-distribˡ-+ c (Σᴮ (λ y → f (extend true y)) i)
                       (Σᴮ (λ y → f (extend false y)) i)))

-- A sum over assignments of amplitudes exchanges with a sum over
-- paths, and commutes with rotations.

Σᵃ-Σᴮ : (F : Assign n → (Fin j → Bool) → Amp) →
        Σᵃ (λ z → Σᴮ (F z)) ≐ Σᴮ (λ y → Σᵃ (λ z → F z y))
Σᵃ-Σᴮ {j = zero}  F _ = refl
Σᵃ-Σᴮ {j = suc j} F i = trans
  (Σᵃ-+ (λ z → Σᴮ (λ y → F z (extend true y)))
        (λ z → Σᴮ (λ y → F z (extend false y))) i)
  (cong₂ _+_ (Σᵃ-Σᴮ (λ z y → F z (extend true y)) i)
             (Σᵃ-Σᴮ (λ z y → F z (extend false y)) i))

Σᵃ-rot : (e : ℤ) (f : Assign n → Amp) →
         Σᵃ (λ z → rot e (f z)) ≐ rot e (Σᵃ f)
Σᵃ-rot e f i = sym (coeff-Σᵃ f ((+ toℕ i) - e))


------------------------------------------------------------------------
-- Hermitian products of sums over paths

-- The product of Σ_y ζ^{e(y)} φ_y and Σ_y′ ζ^{e′(y′)} φ′_y′ is the double
-- sum of the products of φ_y and φ′_y′, rotated by e(y) - e′(y′).

inner-Σrot : (e : Assign m → ℤ) (e′ : Assign m′ → ℤ)
             (φ : Assign m → Column n) (φ′ : Assign m′ → Column n) →
             inner (λ z → Σᴮ (λ y → rot (e y) (φ y z)))
                   (λ z → Σᴮ (λ y′ → rot (e′ y′) (φ′ y′ z))) ≐
             Σᴮ (λ y → Σᴮ (λ y′ →
               rot (e y) (rot (- e′ y′) (inner (φ y) (φ′ y′)))))
inner-Σrot {m = m} {m′ = m′} {n = n} e e′ φ φ′ =
  Σᵃ-cong term
  ∙ Σᵃ-Σᴮ (λ z y → Σᴮ (λ y′ → T z y y′))
  ∙ Σᴮ-cong (λ y → Σᵃ-Σᴮ (λ z y′ → T z y y′)
                   ∙ Σᴮ-cong (λ y′ → pull y y′))
  where
  -- The product of the entries at z of the columns of two paths.
  T : Assign n → Assign m → Assign m′ → Amp
  T z y y′ = rot (e y) (rot (- e′ y′) (φ y z ⊛ conj (φ′ y′ z)))

  conjΣ : ∀ z → conj (Σᴮ (λ y′ → rot (e′ y′) (φ′ y′ z))) ≐
                Σᴮ (λ y′ → rot (- e′ y′) (conj (φ′ y′ z)))
  conjΣ z = conj-Σᴮ (λ y′ → rot (e′ y′) (φ′ y′ z))
            ∙ Σᴮ-cong (λ y′ → conj-rot (e′ y′) (φ′ y′ z))

  inside : ∀ z y →
           φ y z ⊛ Σᴮ (λ y′ → rot (- e′ y′) (conj (φ′ y′ z))) ≐
           Σᴮ (λ y′ → rot (- e′ y′) (φ y z ⊛ conj (φ′ y′ z)))
  inside z y =
    ⊛-sum (φ y z) (λ y′ → rot (- e′ y′) (conj (φ′ y′ z)))
    ∙ Σᴮ-cong (λ y′ → ⊛-rotʳ (- e′ y′) (φ y z) (conj (φ′ y′ z)))

  term : ∀ z → Σᴮ (λ y → rot (e y) (φ y z)) ⊛
                 conj (Σᴮ (λ y′ → rot (e′ y′) (φ′ y′ z))) ≐
               Σᴮ (λ y → Σᴮ (λ y′ → T z y y′))
  term z =
    ⊛-cong {a = Σᴮ (λ y → rot (e y) (φ y z))}
           {a′ = Σᴮ (λ y → rot (e y) (φ y z))} (λ _ → refl) (conjΣ z)
    ∙ sum-⊛ (λ y → rot (e y) (φ y z))
            (Σᴮ (λ y′ → rot (- e′ y′) (conj (φ′ y′ z))))
    ∙ Σᴮ-cong (λ y →
        ⊛-rotˡ (e y) (φ y z) (Σᴮ (λ y′ → rot (- e′ y′) (conj (φ′ y′ z))))
        ∙ rot-map (e y) (inside z y)
        ∙ rot-Σᴮ (e y) (λ y′ → rot (- e′ y′) (φ y z ⊛ conj (φ′ y′ z))))

  pull : ∀ y y′ → Σᵃ (λ z → T z y y′) ≐
                 rot (e y) (rot (- e′ y′) (inner (φ y) (φ′ y′)))
  pull y y′ =
    Σᵃ-rot (e y) (λ z → rot (- e′ y′) (φ y z ⊛ conj (φ′ y′ z)))
    ∙ rot-map (e y) (Σᵃ-rot (- e′ y′) (λ z → φ y z ⊛ conj (φ′ y′ z)))


------------------------------------------------------------------------
-- The Gram matrix of a composite

-- The Gram matrix of any path-sum, over pairs of its paths: a pair
-- contributes ζ^{P(x,y) - P(x′,y′)} when the two paths reach the same
-- state.

gram-paths : (ξ : PathSum n k m) (x x′ : Assign n) →
             gram ξ x x′ ≐
             Σᴮ (λ y → Σᴮ (λ y′ →
               rot (eval (phase ξ) x y)
                   (rot (- eval (phase ξ) x′ y′)
                        [ same (outBit ξ x y) (outBit ξ x′ y′) ]ᴬ)))
gram-paths ξ x x′ =
  inner-cong {ψ = amp ξ x}
             {ψ′ = λ z → Σᴮ (λ y → rot (eval (phase ξ) x y)
                                       (δ (outBit ξ x y) z))}
             {φ = amp ξ x′}
             {φ′ = λ z → Σᴮ (λ y′ → rot (eval (phase ξ) x′ y′)
                                        (δ (outBit ξ x′ y′) z))}
             (amp-Σδ ξ x) (amp-Σδ ξ x′)
  ∙ inner-Σrot (λ y → eval (phase ξ) x y) (λ y′ → eval (phase ξ) x′ y′)
               (λ y → δ (outBit ξ x y)) (λ y′ → δ (outBit ξ x′ y′))
  ∙ Σᴮ-cong (λ y → Σᴮ-cong (λ y′ → rot-map (eval (phase ξ) x y)
      (rot-map (- eval (phase ξ) x′ y′)
               (inner-basis (outBit ξ x y) (outBit ξ x′ y′)))))

-- The Gram matrix of ξ′ ∘ ξ, over pairs of paths of ξ: a pair
-- contributes the product of the columns of ξ′ at the states the two
-- paths reach.

gram-∘-paths : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
               (x x′ : Assign n) →
               gram (ξ′ ∘ᴾ ξ) x x′ ≐
               Σᴮ (λ y → Σᴮ (λ y′ →
                 rot (eval (phase ξ) x y)
                     (rot (- eval (phase ξ) x′ y′)
                          (gram ξ′ (outBit ξ x y) (outBit ξ x′ y′)))))
gram-∘-paths ξ′ ξ x x′ =
  inner-cong {ψ = amp (ξ′ ∘ᴾ ξ) x}
             {ψ′ = λ z → Σᴮ (λ y → rot (eval (phase ξ) x y)
                                       (amp ξ′ (outBit ξ x y) z))}
             {φ = amp (ξ′ ∘ᴾ ξ) x′}
             {φ′ = λ z → Σᴮ (λ y′ → rot (eval (phase ξ) x′ y′)
                                        (amp ξ′ (outBit ξ x′ y′) z))}
             (prop-2-7ʳ ξ′ ξ x) (prop-2-7ʳ ξ′ ξ x′)
  ∙ inner-Σrot (λ y → eval (phase ξ) x y) (λ y′ → eval (phase ξ) x′ y′)
               (λ y → amp ξ′ (outBit ξ x y))
               (λ y′ → amp ξ′ (outBit ξ x′ y′))

-- After an isometry, the Gram matrix is multiplied by 2^k′.

gram-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) → Isometric ξ′ →
         ∀ x x′ → gram (ξ′ ∘ᴾ ξ) x x′ ≐ (+ (2 ^ k′)) ·ᴬ gram ξ x x′
gram-∘ {k′ = k′} {m = m} ξ′ ξ iso x x′ =
  gram-∘-paths ξ′ ξ x x′
  ∙ Σᴮ-cong (λ y → Σᴮ-cong (λ y′ → pair y y′))
  ∙ Σᴮ-cong (λ y → Σᴮ-·ᴬ c (λ y′ → R y y′))
  ∙ Σᴮ-·ᴬ c (λ y → Σᴮ (λ y′ → R y y′))
  ∙ ·ᴬ-cong c (≐-sym (gram-paths ξ x x′))
  where
  c : ℤ
  c = + (2 ^ k′)

  R : Assign m → Assign m → Amp
  R y y′ = rot (eval (phase ξ) x y)
               (rot (- eval (phase ξ) x′ y′)
                    [ same (outBit ξ x y) (outBit ξ x′ y′) ]ᴬ)

  pair : ∀ y y′ →
         rot (eval (phase ξ) x y)
             (rot (- eval (phase ξ) x′ y′)
                  (gram ξ′ (outBit ξ x y) (outBit ξ x′ y′))) ≐
         c ·ᴬ R y y′
  pair y y′ =
    rot-map (eval (phase ξ) x y)
      (rot-map (- eval (phase ξ) x′ y′) (iso (outBit ξ x y) (outBit ξ x′ y′))
       ∙ rot-·ᴬ (- eval (phase ξ) x′ y′) c
                [ same (outBit ξ x y) (outBit ξ x′ y′) ]ᴬ)
    ∙ rot-·ᴬ (eval (phase ξ) x y) c
             (rot (- eval (phase ξ) x′ y′)
                  [ same (outBit ξ x y) (outBit ξ x′ y′) ]ᴬ)


------------------------------------------------------------------------
-- Composing with an isometry

-- Isometries compose: 2^k′ · 2^k = 2^(k + k′).

Isometric-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
              Isometric ξ′ → Isometric ξ → Isometric (ξ′ ∘ᴾ ξ)
Isometric-∘ {k′ = k′} {k = k} ξ′ ξ iso′ iso x x′ =
  gram-∘ ξ′ ξ iso′ x x′
  ∙ ·ᴬ-cong (+ (2 ^ k′)) (iso x x′)
  ∙ ·ᴬ-·ᴬ (+ (2 ^ k′)) (+ (2 ^ k)) [ same x x′ ]ᴬ
  ∙ (λ i → cong (λ t → t * [ same x x′ ]ᴬ i) (pow-mult k k′))

-- A partial isometry followed by an isometry is a partial isometry.

private
  -- A factor c on both sides of every product of a sum comes out
  -- twice.  (PathSum.PartialIsometry proves this too, privately.)

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

  regroup : ∀ c p g → c * (c * (p * g)) ≡ (c * p) * (c * g)
  regroup = solve 3 (λ c p g → c :* (c :* (p :* g)) := (c :* p) :* (c :* g))
                  refl

PartialIsometric-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
                     Isometric ξ′ → PartialIsometric ξ →
                     PartialIsometric (ξ′ ∘ᴾ ξ)
PartialIsometric-∘ {n = n} {k′ = k′} {k = k} ξ′ ξ iso pi x x′ =
  Σᵃ-cong (λ x″ → ⊛-cong (gram-∘ ξ′ ξ iso x x″) (gram-∘ ξ′ ξ iso x″ x′))
  ∙ Σᵃ-⊛-·ᴬ c (gram ξ x) (λ x″ → gram ξ x″ x′)
  ∙ ·ᴬ-cong c (·ᴬ-cong c (pi x x′))
  ∙ (λ i → trans (regroup c (+ (2 ^ k)) (gram ξ x x′ i))
                 (cong (λ t → t * (c * gram ξ x x′ i)) (pow-mult k k′)))
  ∙ ·ᴬ-cong (+ (2 ^ (k ℕ+ k′))) (≐-sym (gram-∘ ξ′ ξ iso x x′))
  where
  c : ℤ
  c = + (2 ^ k′)

-- A WellFormed path-sum followed by an isometry is WellFormed: the
-- norm of a column of the composite is the constant coefficient of a
-- diagonal entry of its Gram matrix, 2^k′ times that of ξ.

WellFormed-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
               Isometric ξ′ → WellFormed ξ → WellFormed (ξ′ ∘ᴾ ξ)
WellFormed-∘ {k′ = k′} {k = k} ξ′ ξ iso wf x =
  ≤-trans (≤-reflexive column)
    (≤-trans (*-monoˡ-≤-nonNeg (+ (2 ^ k′)) (wf x))
             (≤-reflexive (pow-mult k k′)))
  where
  column : Σᶻ (λ z → ‖ amp (ξ′ ∘ᴾ ξ) x z ‖²) ≡
           + (2 ^ k′) * Σᶻ (λ z → ‖ amp ξ x z ‖²)
  column = trans (sym (gram-diag (ξ′ ∘ᴾ ξ) x))
    (trans (coeff-map (gram-∘ ξ′ ξ iso x x) 0ℤ)
      (trans (coeff-·ᴬ (+ (2 ^ k′)) (gram ξ x x) 0ℤ)
             (cong (+ (2 ^ k′) *_) (gram-diag ξ x))))
