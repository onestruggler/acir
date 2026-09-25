------------------------------------------------------------------------
-- Presentations of groups
--
-- Exchanging two blocks of wires (Amy, QPL 2018, remark 2.8)
--
-- Remark 2.8 gives two examples of circuits that are equal up to the
-- laws of symmetric monoidal categories, and that path-sums identify:
-- the bifunctoriality law (PathSum.Compose.Tensor) and the naturality
-- of SWAP,
--
--    SWAP ∘ (f ⊗ id) ≡ (id ⊗ f) ∘ SWAP .
--
-- Here SWAP exchanges two blocks of n wires, |x₁ x₂⟩ ↦ |x₂ x₁⟩: the
-- path-sum swapᴾ n has no path variables, phase 0, and its output on
-- each wire is the input on the corresponding wire of the other block.
-- It is natural in both factors,
--
--    swapᴾ ∘ (ξ₁ ⊗ ξ₂) ≋ (ξ₂ ⊗ ξ₁) ∘ swapᴾ      (swap-natural),
--
-- whose amplitudes agree exactly (amp-swap-natural): on concatenated
-- states both sides sum ζ^{P₁(x₁,y₁) + P₂(x₂,y₂)} over the paths y₁ of
-- ξ₁ from x₁ to z₂ and y₂ of ξ₂ from x₂ to z₁, in the two orders.  The
-- remark's picture is the case ξ₂ = id (remark-2-8-swap).  SWAP is
-- also its own inverse (swap-involutive).
--
-- As for the interchange law, these hold up to ≋ and not as equations,
-- although the remark says "strictly equal": the two sides of
-- swap-natural have normalisations (k₁ + k₂) + 0 and k₂ + k₁ and path
-- variables in different orders.  A SWAP of blocks of different sizes
-- is not expressible, since a path-sum here has as many outputs as
-- inputs, of one type; nor are the other symmetric monoidal laws
-- (associativity of ⊗ᴾ, the hexagon) formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Swap (M₀ : ℕ) where

open import Data.Bool.Base using (if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_)
open import Data.Integer.Properties using (+-comm; +-identityʳ)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Data.Sum.Base using ([_,_]′)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; idPS)
open import PathSum.Compose using (_⊗ᴾ_; _∘ᴾ_)
open import PathSum.Compose.Gates M₀ using (≋-amp; amp-ext)
open import PathSum.Compose.Properties M₀ using
  (eval-∘; outBit-∘; hits-same; amp-≗ˣ; prop-2-7ʳ)
open import PathSum.Compose.Sum M₀ using
  (_++ᵃ_; ++ᵃ-↑ˡ; ++ᵃ-↑ʳ; Σᴮ-++; Σᴮ-swap; if-cong; zpow-≡; rot-if)
open import PathSum.Compose.Tensor M₀ using
  (takeᵃ; dropᵃ; by-blocks; same-++; eval-⊗; outBit-⊗; hits-⊗;
   amp-blocks)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; zpow; rot; rot-map; rot-exp; rot-0)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; _≋_; outBit-μ; eval-0ᴾ-val)
open import PathSum.Polynomial using (x[_]; 0ᴾ; μ; eval)

private
  variable
    n k k₁ k₂ m m₁ m₂ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- SWAP

-- The permutation of the wires exchanging the two blocks.

swapᶠ : ∀ n → Fin (n ℕ+ n) → Fin (n ℕ+ n)
swapᶠ n w = [ (λ i → n ↑ʳ i) , (λ i → i ↑ˡ n) ]′ (splitAt n w)

swapᶠ-↑ˡ : ∀ n (i : Fin n) → swapᶠ n (i ↑ˡ n) ≡ n ↑ʳ i
swapᶠ-↑ˡ n i = cong [ (λ i′ → n ↑ʳ i′) , (λ i′ → i′ ↑ˡ n) ]′
                    (splitAt-↑ˡ n i n)

swapᶠ-↑ʳ : ∀ n (i : Fin n) → swapᶠ n (n ↑ʳ i) ≡ i ↑ˡ n
swapᶠ-↑ʳ n i = cong [ (λ i′ → n ↑ʳ i′) , (λ i′ → i′ ↑ˡ n) ]′
                    (splitAt-↑ʳ n n i)

swapᶠ-involutive : ∀ n (w : Fin (n ℕ+ n)) → swapᶠ n (swapᶠ n w) ≡ w
swapᶠ-involutive n = by-blocks n n
  (λ i → trans (cong (swapᶠ n) (swapᶠ-↑ˡ n i)) (swapᶠ-↑ʳ n i))
  (λ i → trans (cong (swapᶠ n) (swapᶠ-↑ʳ n i)) (swapᶠ-↑ˡ n i))

-- SWAP, |x₁ x₂⟩ ↦ |x₂ x₁⟩: no path variables, phase 0, and each output
-- the input on the other block.

swapᴾ : ∀ n → PathSum (n ℕ+ n) 0 0
swapᴾ n = ⟨ 0ᴾ , (λ w → μ x[ swapᶠ n w ]) ⟩

outBit-swap : ∀ n (x : Assign (n ℕ+ n)) (y : Assign 0) (w : Fin (n ℕ+ n)) →
              outBit (swapᴾ n) x y w ≡ x (swapᶠ n w)
outBit-swap n x y w = outBit-μ (swapᴾ n) x y w x[ swapᶠ n w ] refl

outBit-swap-++ : ∀ n (a b : Assign n) (y : Assign 0) (w : Fin (n ℕ+ n)) →
                 outBit (swapᴾ n) (a ++ᵃ b) y w ≡ (b ++ᵃ a) w
outBit-swap-++ n a b y = by-blocks n n
  (λ i → trans (outBit-swap n (a ++ᵃ b) y (i ↑ˡ n))
    (trans (cong (a ++ᵃ b) (swapᶠ-↑ˡ n i))
           (trans (++ᵃ-↑ʳ a b i) (sym (++ᵃ-↑ˡ b a i)))))
  (λ i → trans (outBit-swap n (a ++ᵃ b) y (n ↑ʳ i))
    (trans (cong (a ++ᵃ b) (swapᶠ-↑ʳ n i))
           (trans (++ᵃ-↑ˡ a b i) (sym (++ᵃ-↑ʳ b a i)))))

-- Its amplitude from x₁ x₂ to z₁ z₂ is 1 when x₂ = z₁ and x₁ = z₂, and
-- 0 otherwise.

amp-swap : ∀ n (a b c d : Assign n) →
           amp (swapᴾ n) (a ++ᵃ b) (c ++ᵃ d) ≐
           (if same b c ∧ same a d then zpow 0ℤ else 0ᴬ)
amp-swap n a b c d = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits (swapᴾ n) (a ++ᵃ b) y (c ++ᵃ d)
        then zpow (eval (phase (swapᴾ n)) (a ++ᵃ b) y) else 0ᴬ) ≐
       (if same b c ∧ same a d then zpow 0ℤ else 0ᴬ)
  at y = if-cong
    (trans (hits-same (swapᴾ n) (a ++ᵃ b) y (c ++ᵃ d))
      (trans (same-≗ {x = outBit (swapᴾ n) (a ++ᵃ b) y} {x′ = b ++ᵃ a}
                     {z = c ++ᵃ d} {z′ = c ++ᵃ d}
                     (outBit-swap-++ n a b y) (λ _ → refl))
             (same-++ b a c d)))
    (zpow-≡ (eval-0ᴾ-val (a ++ᵃ b) y))

-- SWAP is its own inverse.

swap-involutive : ∀ n → (swapᴾ n ∘ᴾ swapᴾ n) ≋ idPS {n ℕ+ n}
swap-involutive n =
  ≋-amp (swapᴾ n ∘ᴾ swapᴾ n) (idPS {n ℕ+ n}) refl
        (amp-ext (swapᴾ n ∘ᴾ swapᴾ n) (idPS {n ℕ+ n}) zero-phase
                 same-outputs)
  where
  zero-phase : ∀ x y → eval (phase (swapᴾ n ∘ᴾ swapᴾ n)) x y ≡
                       eval (phase (idPS {n ℕ+ n})) x y
  zero-phase x y = trans (eval-∘ (swapᴾ n) (swapᴾ n) x (λ ()) y)
    (trans (cong₂ _+_ (eval-0ᴾ-val {m = 0} x (λ ()))
                      (eval-0ᴾ-val (outBit (swapᴾ n) x (λ ())) y))
           (sym (eval-0ᴾ-val x y)))

  same-outputs : ∀ x y w → outBit (swapᴾ n ∘ᴾ swapᴾ n) x y w ≡
                           outBit (idPS {n ℕ+ n}) x y w
  same-outputs x y w = trans (outBit-∘ (swapᴾ n) (swapᴾ n) x (λ ()) y w)
    (trans (outBit-swap n (outBit (swapᴾ n) x (λ ())) y w)
    (trans (outBit-swap n x (λ ()) (swapᶠ n w))
    (trans (cong x (swapᶠ-involutive n w))
           (sym (outBit-μ idPS x y w x[ w ] refl)))))


------------------------------------------------------------------------
-- Naturality

-- At concatenated states both sides are the double sum, over the paths
-- y₁ of ξ₁ and y₂ of ξ₂, of ζ^{P₁(x₁,y₁) + P₂(x₂,y₂)} guarded by y₂
-- reaching z₁ and y₁ reaching z₂.  On the left the composite's paths
-- are ξ₁ ⊗ ξ₂'s, and SWAP only reads where they end; on the right SWAP
-- exchanges the inputs, and ξ₂ ⊗ ξ₁ sums over y₂ first.

private
  natural-at : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂)
               (x₁ z₁ x₂ z₂ : Assign n) →
               amp (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
               amp ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂)
  natural-at {n = n} {m₁ = m₁} {m₂ = m₂} ξ₁ ξ₂ x₁ z₁ x₂ z₂ =
    prop-2-7ʳ (swapᴾ n) (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂)
    ∙ Σᴮ-++ m₁ m₂ (λ Y → rot (eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) Y)
                             (amp (swapᴾ n)
                                  (outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) Y)
                                  (z₁ ++ᵃ z₂)))
    ∙ Σᴮ-cong (λ y₁ → Σᴮ-cong (λ y₂ → left y₁ y₂))
    ∙ Σᴮ-swap (λ y₁ y₂ → if hits ξ₂ x₂ y₂ z₁ ∧ hits ξ₁ x₁ y₁ z₂
                         then zpow (eval (phase ξ₂) x₂ y₂ +
                                    eval (phase ξ₁) x₁ y₁)
                         else 0ᴬ)
    ∙ ≐-sym (Σᴮ-cong (λ y₂ → Σᴮ-cong (λ y₁ →
        if-cong (hits-⊗ ξ₂ ξ₁ x₂ z₁ x₁ z₂ y₂ y₁)
                (zpow-≡ (eval-⊗ ξ₂ ξ₁ x₂ x₁ y₂ y₁)))))
    ∙ ≐-sym (Σᴮ-++ m₂ m₁
        (λ Y → if hits (ξ₂ ⊗ᴾ ξ₁) (x₂ ++ᵃ x₁) Y (z₁ ++ᵃ z₂)
               then zpow (eval (phase (ξ₂ ⊗ᴾ ξ₁)) (x₂ ++ᵃ x₁) Y) else 0ᴬ))
    ∙ ≐-sym (swapped (λ ()))
    ∙ ≐-sym (prop-2-7ʳ (ξ₂ ⊗ᴾ ξ₁) (swapᴾ n) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂))
    where
    left : (y₁ : Assign m₁) (y₂ : Assign m₂) →
           rot (eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
               (amp (swapᴾ n) (outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
                    (z₁ ++ᵃ z₂)) ≐
           (if hits ξ₂ x₂ y₂ z₁ ∧ hits ξ₁ x₁ y₁ z₂
            then zpow (eval (phase ξ₂) x₂ y₂ + eval (phase ξ₁) x₁ y₁)
            else 0ᴬ)
    left y₁ y₂ =
      rot-exp {eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂)}
              {eval (phase ξ₁) x₁ y₁ + eval (phase ξ₂) x₂ y₂}
              (amp (swapᴾ n) (outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
                   (z₁ ++ᵃ z₂))
              (eval-⊗ ξ₁ ξ₂ x₁ x₂ y₁ y₂)
      ∙ rot-map (eval (phase ξ₁) x₁ y₁ + eval (phase ξ₂) x₂ y₂)
          (amp-≗ˣ (swapᴾ n)
                  {outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂)}
                  {outBit ξ₁ x₁ y₁ ++ᵃ outBit ξ₂ x₂ y₂}
                  (outBit-⊗ ξ₁ ξ₂ x₁ x₂ y₁ y₂) (z₁ ++ᵃ z₂)
           ∙ amp-swap n (outBit ξ₁ x₁ y₁) (outBit ξ₂ x₂ y₂) z₁ z₂)
      ∙ rot-if (same (outBit ξ₂ x₂ y₂) z₁ ∧ same (outBit ξ₁ x₁ y₁) z₂)
               (eval (phase ξ₁) x₁ y₁ + eval (phase ξ₂) x₂ y₂) 0ℤ
      ∙ if-cong (sym (cong₂ _∧_ (hits-same ξ₂ x₂ y₂ z₁)
                                (hits-same ξ₁ x₁ y₁ z₂)))
                (zpow-≡ (trans (+-identityʳ (eval (phase ξ₁) x₁ y₁ +
                                             eval (phase ξ₂) x₂ y₂))
                               (+-comm (eval (phase ξ₁) x₁ y₁)
                                       (eval (phase ξ₂) x₂ y₂))))

    -- SWAP has a single path, which exchanges the inputs.
    swapped : (y : Assign 0) →
              rot (eval (phase (swapᴾ n)) (x₁ ++ᵃ x₂) y)
                  (amp (ξ₂ ⊗ᴾ ξ₁) (outBit (swapᴾ n) (x₁ ++ᵃ x₂) y)
                       (z₁ ++ᵃ z₂)) ≐
              amp (ξ₂ ⊗ᴾ ξ₁) (x₂ ++ᵃ x₁) (z₁ ++ᵃ z₂)
    swapped y =
      rot-exp {eval (phase (swapᴾ n)) (x₁ ++ᵃ x₂) y} {0ℤ}
              (amp (ξ₂ ⊗ᴾ ξ₁) (outBit (swapᴾ n) (x₁ ++ᵃ x₂) y) (z₁ ++ᵃ z₂))
              (eval-0ᴾ-val (x₁ ++ᵃ x₂) y)
      ∙ rot-0 (amp (ξ₂ ⊗ᴾ ξ₁) (outBit (swapᴾ n) (x₁ ++ᵃ x₂) y)
                   (z₁ ++ᵃ z₂))
      ∙ amp-≗ˣ (ξ₂ ⊗ᴾ ξ₁) {outBit (swapᴾ n) (x₁ ++ᵃ x₂) y} {x₂ ++ᵃ x₁}
               (outBit-swap-++ n x₁ x₂ y) (z₁ ++ᵃ z₂)

amp-swap-natural : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂)
                   (x z : Assign (n ℕ+ n)) →
                   amp (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) x z ≐
                   amp ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n) x z
amp-swap-natural {n = n} ξ₁ ξ₂ x z =
  amp-blocks n n (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) x z
  ∙ natural-at ξ₁ ξ₂ (takeᵃ n x) (takeᵃ n z) (dropᵃ n x) (dropᵃ n z)
  ∙ ≐-sym (amp-blocks n n ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n) x z)

swap-natural : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂) →
               (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) ≋ ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)
swap-natural {n = n} {k₁ = k₁} {k₂ = k₂} ξ₁ ξ₂ =
  ≋-amp (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)
        (trans (ℕ.+-identityʳ (k₁ ℕ+ k₂)) (ℕ.+-comm k₁ k₂))
        (amp-swap-natural ξ₁ ξ₂)

-- The law drawn in remark 2.8: ξ on the upper wires, then SWAP, is
-- SWAP, then ξ on the lower wires.

remark-2-8-swap : (ξ : PathSum n k m) →
                  (swapᴾ n ∘ᴾ (ξ ⊗ᴾ idPS {n})) ≋ ((idPS {n} ⊗ᴾ ξ) ∘ᴾ swapᴾ n)
remark-2-8-swap {n = n} ξ = swap-natural ξ (idPS {n})
