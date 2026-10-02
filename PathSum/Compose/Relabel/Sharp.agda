------------------------------------------------------------------------
-- Presentations of groups
--
-- Where definition 2.6 lifts outputs, congruence is the best one gets
-- (Amy, QPL 2018, remark 2.8)
--
-- PathSum.Compose.Relabel proves the drawn form of bifunctoriality, in
-- either order and the two orders against each other (⊗-sequentialᴿ,
-- ⊗-sequential′ᴿ, remark-2-8ᴿ), and conjugation by SWAP
-- (swap-conjugateᴿ) up to renaming with the outputs congruent modulo 2
-- (≈ᴿ), not equal as integers (≡ᴿ), and PathSum.Compose.Monoidal does
-- the same for the naturality of SWAP and the left identity law.  The
-- reason given there: definition 2.6 substitutes into the second
-- path-sum the lifts of the first one's outputs, which agree with those
-- outputs modulo 2 only, so an output that passes through a wire where
-- the other path-sum acts as the identity, or through SWAP, comes out
-- as a bit, while on the other side it is the original integer
-- polynomial.
--
-- Here that is shown to be a real limit, not an artefact of the
-- proofs: for a path-sum on one wire whose output is 3 x₀ (three,
-- read modulo 2 as x₀, so as the identity), none of those four laws
-- holds as ≡ᴿ under any renaming (sequential-sharp, sequential′-sharp,
-- remark-2-8-sharp, swap-conjugate-sharp).  At the input 1, on the
-- wire three acts on, one side's output takes a bit as its value -- the
-- lift of three's output, or the identity's output there -- and the
-- other side's takes 3, and equality up to renaming would make the two
-- values equal (≡ᴿ preserves values along the renamed path).  The
-- path-sums have no path variables, so no renaming can help.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Relabel.Sharp (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Permutation using (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
open import Data.Integer.Base using (ℤ; +_; 0ℤ; 1ℤ; _*_)
open import Data.Integer.Properties using (*-identityʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; ⟨_,_⟩; out; idPS)
open import PathSum.Compose using (_⊗ᴾ_; _∘ᴾ_)
open import PathSum.Compose.Monoidal M₀ using
  (eval-out-⊗ˡ; eval-out-⊗ʳ; eval-out-∘-blocks)
open import PathSum.Compose.Swap M₀ using (swapᴾ; swapᶠ)
open import PathSum.Compose.Tensor M₀ using (takeᵃ; dropᵃ; outBit-⊗ˡ)
open import PathSum.Denotation M₀ using
  (Assign; outBit; outBit-μ; eval-μ-val)
open import PathSum.Permute using
  (renumberᴾ; eval-renumberᴾ; relabel; eval-relabelᴾ; _≡ᴿ⟨_⟩_; out≡)
open import PathSum.Permute.Blocks using (braidᵖ; braidᶠ)
open import PathSum.Polynomial using (0ᴾ; μ; x[_]; _·ᴾ_; eval)
open import PathSum.Polynomial.Properties using (eval-·ᴾ; eval-ext)

private
  variable
    n k k′ m m′ : ℕ


------------------------------------------------------------------------
-- Values along a renaming

-- Equality up to renaming preserves the values of the outputs, along
-- the renamed path.

out-values : {ξ : PathSum n k m} {π : Permutation m m′}
             {ζ : PathSum n k′ m′} → ξ ≡ᴿ⟨ π ⟩ ζ →
             ∀ w x y → eval (out ζ w) x y ≡
                       eval (out ξ w) x (λ j → y (π ⟨$⟩ʳ j))
out-values {ξ = ξ} {π} {ζ} r w x y =
  trans (sym (eval-ext (renumberᴾ π (out ξ w)) (out ζ w) (out≡ r w) x y))
        (eval-renumberᴾ π (out ξ w) x y)


------------------------------------------------------------------------
-- Outputs worth three

-- 3 x_w takes the value 3 where x_w is 1, and a bit is never 3.

private
  eval-3 : (w : Fin n) (x : Assign n) (y : Assign m) → x w ≡ true →
           eval ((+ 3) ·ᴾ μ x[ w ]) x y ≡ + 3
  eval-3 w x y h =
    trans (eval-·ᴾ (+ 3) (μ x[ w ]) x y)
    (trans (cong (+ 3 *_) (trans (eval-μ-val x[ w ] x y)
                                 (cong (λ b → if b then 1ℤ else 0ℤ) h)))
           (*-identityʳ (+ 3)))

  bit≢3 : (b : Bool) → (if b then 1ℤ else 0ℤ) ≡ + 3 → ∀ {A : Set} → A
  bit≢3 true  ()
  bit≢3 false ()

  ones : ∀ {n} → Assign n
  ones _ = true

  none : Assign 0
  none ()

-- One wire, output 3 x₀: the identity, read modulo 2.

three : PathSum 1 0 0
three = ⟨ 0ᴾ , (λ _ → (+ 3) ·ᴾ μ x[ zero ]) ⟩

-- Two wires, outputs 3 x₀ and 3 x₁.

three₂ : PathSum 2 0 0
three₂ = ⟨ 0ᴾ , (λ w → (+ 3) ·ᴾ μ x[ w ]) ⟩


------------------------------------------------------------------------
-- The drawn form of bifunctoriality is not ≡ᴿ

-- (ξ₁ ⊗ id) ∘ (id ⊗ ξ₂) against ξ₁ ⊗ ξ₂, at ξ₁ the identity on no
-- wires and ξ₂ = three: on the left the lower wire carries the lift of
-- three's output, a bit; on the right three's output, 3 at the input 1.

sequential-sharp :
  (π : Permutation 0 0) →
  ¬ (((idPS {0} ⊗ᴾ idPS {1}) ∘ᴾ (idPS {0} ⊗ᴾ three)) ≡ᴿ⟨ π ⟩
     (idPS {0} ⊗ᴾ three))
sequential-sharp π r = bit≢3 (F zero) (trans (sym left) (trans (sym mid) right))
  where
  A = idPS {0} ⊗ᴾ three
  B = idPS {0} ⊗ᴾ idPS {1}

  y′ : Assign 0
  y′ j = none (π ⟨$⟩ʳ j)

  F : Assign 1
  F = outBit A ones (takeᵃ {n₁ = 0} 0 y′)

  left : eval (out (B ∘ᴾ A) zero) ones y′ ≡ (if F zero then 1ℤ else 0ℤ)
  left = trans (eval-out-∘-blocks B A ones y′ zero)
    (trans (eval-out-⊗ʳ (idPS {0}) (idPS {1}) F (dropᵃ 0 y′) zero)
           (eval-μ-val x[ zero ] (dropᵃ 0 F) (dropᵃ 0 (dropᵃ 0 y′))))

  mid : eval (out A zero) ones none ≡ eval (out (B ∘ᴾ A) zero) ones y′
  mid = out-values {ξ = B ∘ᴾ A} {π = π} {ζ = A} r zero ones none

  right : eval (out A zero) ones none ≡ + 3
  right = trans (eval-out-⊗ʳ (idPS {0}) three ones none zero)
                (eval-3 zero (dropᵃ {n₂ = 1} 0 ones) (dropᵃ {n₂ = 0} 0 none) refl)


-- The other order, (id ⊗ ξ₂) ∘ (ξ₁ ⊗ id) against ξ₁ ⊗ ξ₂, at ξ₁ = three
-- and ξ₂ the identity on no wires: on the left the identity, acting
-- second, carries the lift of three's output, a bit; on the right
-- three's output, 3 at the input 1.

sequential′-sharp :
  (π : Permutation 0 0) →
  ¬ (((idPS {1} ⊗ᴾ idPS {0}) ∘ᴾ (three ⊗ᴾ idPS {0})) ≡ᴿ⟨ π ⟩
     (three ⊗ᴾ idPS {0}))
sequential′-sharp π r =
  bit≢3 (F zero) (trans (sym left) (trans (sym mid) right))
  where
  A = three ⊗ᴾ idPS {0}
  B = idPS {1} ⊗ᴾ idPS {0}

  y′ : Assign 0
  y′ j = none (π ⟨$⟩ʳ j)

  F : Assign 1
  F = outBit A ones (takeᵃ {n₁ = 0} 0 y′)

  left : eval (out (B ∘ᴾ A) zero) ones y′ ≡ (if F zero then 1ℤ else 0ℤ)
  left = trans (eval-out-∘-blocks B A ones y′ zero)
    (trans (eval-out-⊗ˡ (idPS {1}) (idPS {0}) F (dropᵃ 0 y′) zero)
           (eval-μ-val x[ zero ] (takeᵃ {n₁ = 1} 0 F)
                       (takeᵃ {n₁ = 0} 0 (dropᵃ 0 y′))))

  mid : eval (out A zero) ones none ≡ eval (out (B ∘ᴾ A) zero) ones y′
  mid = out-values {ξ = B ∘ᴾ A} {π = π} {ζ = A} r zero ones none

  right : eval (out A zero) ones none ≡ + 3
  right = trans (eval-out-⊗ˡ three (idPS {0}) ones none zero)
                (eval-3 zero (takeᵃ {n₁ = 1} 0 ones) (takeᵃ {n₁ = 0} 0 none)
                        refl)

-- The two orders against each other, at the same ξ₁ and ξ₂: three acts
-- second on the left, on the input itself, so its output is 3 there; it
-- acts first on the right, and the identity after it leaves a bit.

remark-2-8-sharp :
  (π : Permutation 0 0) →
  ¬ (((three ⊗ᴾ idPS {0}) ∘ᴾ (idPS {1} ⊗ᴾ idPS {0})) ≡ᴿ⟨ π ⟩
     ((idPS {1} ⊗ᴾ idPS {0}) ∘ᴾ (three ⊗ᴾ idPS {0})))
remark-2-8-sharp π r = bit≢3 (G zero) (trans (sym left) (trans mid right))
  where
  -- The right-hand side: three, then the identity.
  A₂ = three ⊗ᴾ idPS {0}
  B₂ = idPS {1} ⊗ᴾ idPS {0}

  -- The left-hand side: the identity, then three.
  A₁ = idPS {1} ⊗ᴾ idPS {0}
  B₁ = three ⊗ᴾ idPS {0}

  y′ : Assign 0
  y′ j = none (π ⟨$⟩ʳ j)

  G : Assign 1
  G = outBit A₂ ones (takeᵃ {n₁ = 0} 0 none)

  F : Assign 1
  F = outBit A₁ ones (takeᵃ {n₁ = 0} 0 y′)

  -- The identity, acting first, leaves the input 1.
  F1 : F zero ≡ true
  F1 = trans (outBit-⊗ˡ (idPS {1}) (idPS {0}) ones
                         (takeᵃ {n₁ = 0} 0 y′) zero)
             (outBit-μ (idPS {1}) (takeᵃ {n₁ = 1} 0 ones)
                       (takeᵃ {n₁ = 0} 0 (takeᵃ {n₁ = 0} 0 y′)) zero x[ zero ]
                       refl)

  left : eval (out (B₂ ∘ᴾ A₂) zero) ones none ≡
         (if G zero then 1ℤ else 0ℤ)
  left = trans (eval-out-∘-blocks B₂ A₂ ones none zero)
    (trans (eval-out-⊗ˡ (idPS {1}) (idPS {0}) G (dropᵃ 0 none) zero)
           (eval-μ-val x[ zero ] (takeᵃ {n₁ = 1} 0 G)
                       (takeᵃ {n₁ = 0} 0 (dropᵃ 0 none))))

  mid : eval (out (B₂ ∘ᴾ A₂) zero) ones none ≡
        eval (out (B₁ ∘ᴾ A₁) zero) ones y′
  mid = out-values {ξ = B₁ ∘ᴾ A₁} {π = π} {ζ = B₂ ∘ᴾ A₂} r zero ones none

  right : eval (out (B₁ ∘ᴾ A₁) zero) ones y′ ≡ + 3
  right = trans (eval-out-∘-blocks B₁ A₁ ones y′ zero)
    (trans (eval-out-⊗ˡ three (idPS {0}) F (dropᵃ 0 y′) zero)
           (eval-3 zero (takeᵃ {n₁ = 1} 0 F) (takeᵃ {n₁ = 0} 0 (dropᵃ 0 y′))
                   F1))


------------------------------------------------------------------------
-- Conjugation by SWAP is not ≡ᴿ

-- SWAP, three₂, SWAP against three₂ relabelled along the braiding: on
-- the left each output is the lift of one of three₂'s, a bit; on the
-- right three₂'s, 3 at the input 11.

swap-conjugate-sharp :
  (π : Permutation 0 0) →
  ¬ (((swapᴾ 1 ∘ᴾ three₂) ∘ᴾ swapᴾ 1) ≡ᴿ⟨ π ⟩ relabel (braidᵖ 1 1) three₂)
swap-conjugate-sharp π r =
  bit≢3 (G (swapᶠ 1 zero)) (trans (sym left) (trans (sym mid) right))
  where
  A = swapᴾ 1 ∘ᴾ three₂

  y′ : Assign 0
  y′ j = none (π ⟨$⟩ʳ j)

  X : Assign 2
  X = outBit (swapᴾ 1) ones (takeᵃ {n₁ = 0} 0 y′)

  G : Assign 2
  G = outBit three₂ X (takeᵃ {n₁ = 0} 0 (dropᵃ 0 y′))

  left : eval (out (A ∘ᴾ swapᴾ 1) zero) ones y′ ≡
         (if G (swapᶠ 1 zero) then 1ℤ else 0ℤ)
  left = trans (eval-out-∘-blocks A (swapᴾ 1) ones y′ zero)
    (trans (eval-out-∘-blocks (swapᴾ 1) three₂ X (dropᵃ 0 y′) zero)
           (eval-μ-val x[ swapᶠ 1 zero ] G
                       (dropᵃ {n₂ = 0} 0 (dropᵃ 0 y′))))

  mid : eval (out (relabel (braidᵖ 1 1) three₂) zero) ones none ≡
        eval (out (A ∘ᴾ swapᴾ 1) zero) ones y′
  mid = out-values {ξ = A ∘ᴾ swapᴾ 1} {π = π}
                   {ζ = relabel (braidᵖ 1 1) three₂} r zero ones none

  right : eval (out (relabel (braidᵖ 1 1) three₂) zero) ones none ≡ + 3
  right = trans (eval-relabelᴾ (braidᵖ 1 1)
                   (out three₂ (braidᵖ 1 1 ⟨$⟩ˡ zero)) ones none)
                (eval-3 (braidᵖ 1 1 ⟨$⟩ˡ zero) (λ i → ones (braidᶠ 1 1 i))
                        none refl)
