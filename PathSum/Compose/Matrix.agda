------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 2.7 as a product of matrices over Z[ζ]
--
-- With the product ⊛ of Z[ζ] from PathSum.Ring, proposition 2.7 of
-- Amy's QPL 2018 paper can be stated as the paper states it: the matrix
-- of ξ′ ∘ ξ is the product of the matrices of ξ′ and ξ.  A matrix here
-- is an entry function on pairs of basis states, A x z being the entry
-- from x to z, so that amp ξ is the matrix of U_ξ with its
-- normalisation cleared; (B ⊙ A) x z = Σ_w A x w · B w z is the matrix
-- of "A, then B".  prop-2-7 is amp (ξ′ ∘ᴾ ξ) = amp ξ′ ⊙ amp ξ, entry
-- by entry, with no hypothesis and nothing to adjust: the
-- normalisations add, 1/√2^(k+k′) = 1/√2^k · 1/√2^k′.  prop-2-7′ is the
-- same with each product in the other order, Σ_w U_ξ′(w,z) · U_ξ(x,w),
-- which is the entry of the operator product U_ξ′ U_ξ as it is usually
-- written.  applyᴾ-matrix identifies the operator applyᴾ ξ of
-- PathSum.Compose.Properties with the matrix of ξ acting on a column.
--
-- PathSum.Ring does not prove ⊛ commutative or associative, and
-- neither is needed.  The two orders are proved separately, and both
-- come down to multiplying by ζ^e on one side being rot e: on the left
-- that is Ring's zpow-⊛, on the right it follows from Ring's ⊛-rotʳ
-- once ζ^0 is a right unit (⊛-unitʳ), which is derived here from
-- Ring's Hermitian symmetry conj (a · conj b) = b · conj a at b = ζ^0,
-- ζ^0 being its own conjugate:
--
--   a · ζ^0 = conj (conj (a · conj ζ^0)) = conj (ζ^0 · conj a) = a.
--
-- The rest is that sums and guards pass through a product on either
-- side (sum-⊛, ⊛-sum, if-⊛, ⊛-if), from Ring's distributivity over +ᴬ
-- and its zero laws, and that the row of U_ξ at x, multiplied against
-- a column, collapses to one term per path (row-collapse).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Matrix (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; -_; _+_)
open import Data.Integer.Properties using (+-identityʳ)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong₂)

open import PathSum.Base using (PathSum; phase)
open import PathSum.CircuitSemantics M₀ using (Column)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using
  (amp-≗ˣ; hits-same; prop-2-7ʳ; applyᴾ)
open import PathSum.Compose.Sum M₀ using (Σᴮ-swap; Σᴮ-δ; if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; extend; Σᴮ; Σᴮ-cong; zpow; rot; rot-map; rot-zpow;
   Respects)
open import PathSum.Denotation M₀ using (Assign; hits; amp; outBit)
open import PathSum.Polynomial using (eval)
open import PathSum.Ring M₀ using
  (_⊛_; ⊛-cong; ⊛-distribˡ-+ᴬ; ⊛-distribʳ-+ᴬ; ⊛-zeroˡ; ⊛-zeroʳ;
   ⊛-identityˡ; zpow-⊛; ⊛-rotʳ; conj; conj-cong; conj-involutive;
   conj-zpow; ⊛-conj-herm)

private
  variable
    n k k′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The product against sums, guards and powers of ζ

-- A sum passes through a product on either side.  Each step names the
-- unfolding of Σᴮ (⊛-cong at refl), so that the two sides of every
-- conversion are products of the same factors.

sum-⊛ : (f : (Fin k → Bool) → Amp) (b : Amp) →
        Σᴮ f ⊛ b ≐ Σᴮ (λ y → f y ⊛ b)
sum-⊛ {k = zero}  f b _ = refl
sum-⊛ {k = suc k} f b =
  ⊛-cong {a = Σᴮ f}
         {a′ = Σᴮ (λ y → f (extend true y)) +ᴬ
               Σᴮ (λ y → f (extend false y))}
         {b = b} {b′ = b} (λ _ → refl) ≐-refl
  ∙ ⊛-distribʳ-+ᴬ (Σᴮ (λ y → f (extend true y)))
                  (Σᴮ (λ y → f (extend false y))) b
  ∙ (λ i → cong₂ _+_ (sum-⊛ (λ y → f (extend true y)) b i)
                     (sum-⊛ (λ y → f (extend false y)) b i))

⊛-sum : (a : Amp) (f : (Fin k → Bool) → Amp) →
        a ⊛ Σᴮ f ≐ Σᴮ (λ y → a ⊛ f y)
⊛-sum {k = zero}  a f _ = refl
⊛-sum {k = suc k} a f =
  ⊛-cong {a = a} {a′ = a} {b = Σᴮ f}
         {b′ = Σᴮ (λ y → f (extend true y)) +ᴬ
               Σᴮ (λ y → f (extend false y))}
         ≐-refl (λ _ → refl)
  ∙ ⊛-distribˡ-+ᴬ a (Σᴮ (λ y → f (extend true y)))
                    (Σᴮ (λ y → f (extend false y)))
  ∙ (λ i → cong₂ _+_ (⊛-sum a (λ y → f (extend true y)) i)
                     (⊛-sum a (λ y → f (extend false y)) i))

-- A guard passes through a product on either side.

if-⊛ : (c : Bool) (a b : Amp) →
       (if c then a else 0ᴬ) ⊛ b ≐ (if c then a ⊛ b else 0ᴬ)
if-⊛ true  a b _ = refl
if-⊛ false a b   = ⊛-zeroˡ b

⊛-if : (c : Bool) (a b : Amp) →
       a ⊛ (if c then b else 0ᴬ) ≐ (if c then a ⊛ b else 0ᴬ)
⊛-if true  a b _ = refl
⊛-if false a b   = ⊛-zeroʳ a

-- ζ^0 is a unit on the right as well: it is its own conjugate, and
-- Hermitian symmetry moves it to the left, where it is Ring's unit.

⊛-unitʳ : ∀ a → a ⊛ zpow 0ℤ ≐ a
⊛-unitʳ a =
  ⊛-cong {a = a} {a′ = a} {b = zpow 0ℤ} {b′ = conj (zpow 0ℤ)} ≐-refl
         (≐-sym (conj-zpow 0ℤ ∙ zpow-≡ {a = - 0ℤ} {b = 0ℤ} refl))
  ∙ ≐-sym (conj-involutive (a ⊛ conj (zpow 0ℤ)))
  ∙ conj-cong (⊛-conj-herm a (zpow 0ℤ) ∙ ⊛-identityˡ (conj a))
  ∙ conj-involutive a

-- Multiplying by ζ^e on the right is rotating by e (on the left it is
-- Ring's zpow-⊛).

⊛-zpow : ∀ e a → a ⊛ zpow e ≐ rot e a
⊛-zpow e a =
  ⊛-cong {a = a} {a′ = a} {b = zpow e} {b′ = rot e (zpow 0ℤ)} ≐-refl
         (≐-sym (rot-zpow e 0ℤ ∙ zpow-≡ (+-identityʳ e)))
  ∙ ⊛-rotʳ e a (zpow 0ℤ)
  ∙ rot-map e (⊛-unitʳ a)


------------------------------------------------------------------------
-- Entries of U_ξ as multipliers

-- Multiplying by the entry of U_ξ from x to w, on either side, is
-- rotating by the phase of each path from x that hits w.

amp-⊛ : (ξ : PathSum n k m) (x w : Assign n) (b : Amp) →
        amp ξ x w ⊛ b ≐
        Σᴮ (λ y → if hits ξ x y w then rot (eval (phase ξ) x y) b else 0ᴬ)
amp-⊛ ξ x w b =
  sum-⊛ (λ y → if hits ξ x y w then zpow (eval (phase ξ) x y) else 0ᴬ) b
  ∙ Σᴮ-cong (λ y →
      if-⊛ (hits ξ x y w) (zpow (eval (phase ξ) x y)) b
      ∙ if-cong {p = hits ξ x y w} refl (zpow-⊛ (eval (phase ξ) x y) b))

⊛-amp : (a : Amp) (ξ : PathSum n k m) (x w : Assign n) →
        a ⊛ amp ξ x w ≐
        Σᴮ (λ y → if hits ξ x y w then rot (eval (phase ξ) x y) a else 0ᴬ)
⊛-amp a ξ x w =
  ⊛-sum a (λ y → if hits ξ x y w then zpow (eval (phase ξ) x y) else 0ᴬ)
  ∙ Σᴮ-cong (λ y →
      ⊛-if (hits ξ x y w) a (zpow (eval (phase ξ) x y))
      ∙ if-cong {p = hits ξ x y w} refl (⊛-zpow (eval (phase ξ) x y) a))

-- The row of U_ξ at x against a column C: summed over w, the paths
-- from x that hit w collapse, each onto C at the state it hits.

row-collapse : (ξ : PathSum n k m) (x : Assign n) (C : Column n) →
               Respects C →
               Σᴮ (λ w → Σᴮ (λ y → if hits ξ x y w
                                   then rot (eval (phase ξ) x y) (C w)
                                   else 0ᴬ)) ≐
               Σᴮ (λ y → rot (eval (phase ξ) x y) (C (outBit ξ x y)))
row-collapse ξ x C resp =
  Σᴮ-swap (λ w y → if hits ξ x y w
                   then rot (eval (phase ξ) x y) (C w) else 0ᴬ)
  ∙ Σᴮ-cong (λ y →
      Σᴮ-cong (λ w → if-cong (hits-same ξ x y w) ≐-refl)
      ∙ Σᴮ-δ (outBit ξ x y) (λ w → rot (eval (phase ξ) x y) (C w))
             (λ g h g≗h → rot-map (eval (phase ξ) x y) (resp g h g≗h)))


------------------------------------------------------------------------
-- Matrices

-- The operator applyᴾ ξ is the matrix of ξ acting on a column,
-- Σ_w U_ξ(w, z) · ψ(w), with the factors in either order.

applyᴾ-matrix : (ξ : PathSum n k m) (ψ : Column n) (z : Assign n) →
                applyᴾ ξ ψ z ≐ Σᴮ (λ w → amp ξ w z ⊛ ψ w)
applyᴾ-matrix ξ ψ z = Σᴮ-cong (λ w → ≐-sym (amp-⊛ ξ w z (ψ w)))

applyᴾ-matrix′ : (ξ : PathSum n k m) (ψ : Column n) (z : Assign n) →
                 applyᴾ ξ ψ z ≐ Σᴮ (λ w → ψ w ⊛ amp ξ w z)
applyᴾ-matrix′ ξ ψ z = Σᴮ-cong (λ w → ≐-sym (⊛-amp (ψ w) ξ w z))

-- The matrix of "A, then B".

infixr 9 _⊙_

_⊙_ : (Assign n → Assign n → Amp) → (Assign n → Assign n → Amp) →
      (Assign n → Assign n → Amp)
(B ⊙ A) x z = Σᴮ (λ w → A x w ⊛ B w z)

-- Proposition 2.7: U_{ξ′∘ξ} = U_ξ′ U_ξ, as a product of matrices over
-- Z[ζ], exactly and unnormalised.  Both sides are, by prop-2-7ʳ and by
-- amp-⊛ with row-collapse, Σ_y ζ^{P(x,y)} · U_ξ′(f(x,y), z).

prop-2-7 : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x z : Assign n) →
           amp (ξ′ ∘ᴾ ξ) x z ≐ (amp ξ′ ⊙ amp ξ) x z
prop-2-7 ξ′ ξ x z =
  prop-2-7ʳ ξ′ ξ x z
  ∙ ≐-sym (row-collapse ξ x (λ w → amp ξ′ w z)
                        (λ g h g≗h → amp-≗ˣ ξ′ g≗h z))
  ∙ ≐-sym (Σᴮ-cong (λ w → amp-⊛ ξ x w (amp ξ′ w z)))

-- The same, with each product written U_ξ′(w, z) · U_ξ(x, w).

prop-2-7′ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x z : Assign n) →
            amp (ξ′ ∘ᴾ ξ) x z ≐ Σᴮ (λ w → amp ξ′ w z ⊛ amp ξ x w)
prop-2-7′ ξ′ ξ x z =
  prop-2-7ʳ ξ′ ξ x z
  ∙ ≐-sym (row-collapse ξ x (λ w → amp ξ′ w z)
                        (λ g h g≗h → amp-≗ˣ ξ′ g≗h z))
  ∙ ≐-sym (Σᴮ-cong (λ w → ⊛-amp (amp ξ′ w z) ξ x w))
