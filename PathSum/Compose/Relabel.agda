------------------------------------------------------------------------
-- Presentations of groups
--
-- Relabelling against composition, conjugation by SWAP, the drawn
-- form of bifunctoriality, and the second hexagon, up to renaming the
-- path variables (Amy, QPL 2018, remark 2.8)
--
-- PathSum.Compose.Monoidal proves the symmetric monoidal laws of
-- path-sums up to a renaming of their path variables (PathSum.Permute's
-- ≡ᴿ, or PathSum.Permute.Sound's ≈ᴿ where outputs agree modulo 2
-- only).  This module adds four facts about how the structure maps --
-- relabellings of the wires -- interact with the two compositions, and
-- the pictures of remark 2.8 in the form they are drawn.
--
--  * Relabelling is functorial over both compositions, exactly:
--
--      relabel σ (ξ′ ∘ ξ) ≡ᴿ⟨ id ⟩ relabel σ ξ′ ∘ relabel σ ξ
--                                                    (relabel-∘ᴾ),
--      relabel (σ ⊕ τ) (ξ₁ ⊗ ξ₂) ≡ᴿ⟨ id ⟩ relabel σ ξ₁ ⊗ relabel τ ξ₂
--                                                    (relabel-⊗ᴾ).
--
--    No renaming of the path variables, no cast, and the outputs are
--    equal as integers, not only modulo 2: definition 2.6 feeds ξ′ the
--    lifts of ξ's outputs, and relabelling only renames the input
--    variables of the lifted polynomials and moves them between wires,
--    so the lifts are lifts of the relabelled outputs, coefficient for
--    coefficient (both sides take, at every point, the same bit as
--    value).  Neither needs ≈ᴿ.
--
--  * Conjugation by SWAP is relabelling along the braiding:
--
--      (swapᴾ n ∘ ξ) ∘ swapᴾ n ≈ᴿ⟨ unitʳᵖ m ⟩ relabel (braidᵖ n n) ξ
--                                                 (swap-conjugateᴿ),
--
--    the renaming the cast m + 0 ↔ m that SWAP's lack of path
--    variables leaves.  Here the outputs agree modulo 2 only (≈ᴿ): on
--    the left SWAP's outputs, single variables, have ξ's lifted
--    outputs substituted -- bits -- while on the right ξ's outputs are
--    kept as they are, any integers of the same parity.
--
--  * The drawn form of bifunctoriality, PathSum.Compose.Tensor's
--    ⊗-sequential and ⊗-sequential′, up to renaming:
--
--      (ξ₁ ⊗ id) ∘ (id ⊗ ξ₂) ≈ᴿ⟨ seqᵖ m₁ m₂ ⟩ ξ₁ ⊗ ξ₂ (⊗-sequentialᴿ),
--      (id ⊗ ξ₂) ∘ (ξ₁ ⊗ id) ≈ᴿ⟨ seq′ᵖ m₁ m₂ ⟩ ξ₁ ⊗ ξ₂
--                                                   (⊗-sequential′ᴿ),
--
--    and so the two orders against each other (remark-2-8ᴿ, by
--    PathSum.Permute.Congruence's ≈ᴿ-trans and ≈ᴿ-sym).  The renamings:
--    in the first order ξ₂'s path variables come first, so seqᵖ is the
--    exchange of the two blocks (after dropping the identity's empty
--    block, the cast along +-identityʳ); in the second they are already
--    in order, and seq′ᵖ is the cast alone.  Again modulo 2 on the
--    outputs: the wires a path-sum crosses as the identity carry the
--    lift of the other's outputs.
--
--  * The second hexagon, PathSum.Permute.Hexagon's hexagon′,
--    transported to path-sums: relabelling along either side of it
--    gives the same path-sum, coefficient by coefficient (hexagon′ᴿ,
--    hexagon′-≋).
--
-- Every ≡ᴿ and ≈ᴿ gives ≋ (PathSum.Permute.Sound.≡ᴿ⇒≋, ≈ᴿ⇒≋).  The ≋
-- forms of the new laws are stated (relabel-∘ᴾ-≋, relabel-⊗ᴾ-≋,
-- swap-conjugate-≋, hexagon′-≋); those of the drawn form of
-- bifunctoriality were already PathSum.Compose.Tensor's ⊗-sequential,
-- ⊗-sequential′ and remark-2-8.  PathSum.Compose.Relabel.Sharp shows,
-- by a counterexample to each, that none of the four ≈ᴿ laws here
-- (swap-conjugateᴿ, ⊗-sequentialᴿ, ⊗-sequential′ᴿ, remark-2-8ᴿ) can be
-- strengthened to ≡ᴿ under any renaming.  Every proof is by values, as
-- in
-- PathSum.Compose.Monoidal: both sides are evaluated block by block,
-- the blocks matched through the block lemmas of the bijections
-- (PathSum.Permute.Blocks), and Möbius uniqueness turns equal values
-- (or equal bits) into equal (or congruent) coefficients.  No
-- polynomial is computed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Relabel (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Permutation using
  (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ; id; flip; _∘ₚ_)
open import Data.Integer.Base using (ℤ; _+_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Compose using (_⊗ᴾ_; _∘ᴾ_)
open import PathSum.Compose.Monoidal M₀ using
  (eval-out-⊗ˡ; eval-out-⊗ʳ; eval-∘-blocks; eval-out-∘-blocks;
   outBit-∘-blocks)
open import PathSum.Compose.Swap M₀ using (swapᴾ; outBit-swap)
open import PathSum.Compose.Tensor M₀ using
  (takeᵃ; dropᵃ; eval-⊗-blocks; outBit-⊗ˡ; outBit-⊗ʳ)
open import PathSum.Denotation M₀ using
  (Assign; outBit; _≋_; outBit-μ; eval-0ᴾ-val)
open import PathSum.Permute using
  (relabel; relabelᴾ; eval-relabelᴾ; _≡ᴿ⟨_⟩_; ≡ᴿ-by-values; ≡ᴿ-trans;
   ≡ᴿ-sym; ≡ᴿ-cong; relabel-∘; relabel-cong; relabel-≡ᴿ)
open import PathSum.Permute.Blocks using
  (blocks; assocᵖ; unitʳᵖ; braidᵖ; braidᶠ; _⊕ᵖ_; ⊕-1; ⊕-2; unitʳ-1;
   braid-1; braid-2)
open import PathSum.Permute.Congruence M₀ using (≈ᴿ-sym; ≈ᴿ-trans)
open import PathSum.Permute.Hexagon using (hexagon′)
open import PathSum.Permute.Sound M₀ using
  (_≈ᴿ⟨_⟩_; ≈ᴿ-by-values; ≈ᴿ⇒≋; ≡ᴿ⇒≋; outBit-relabel)
open import PathSum.Polynomial using (x[_]; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Properties using (eval-cong)

private
  variable
    n n′ n₁ n₂ n₁′ n₂′ k k′ k₁ k₂ m m′ m₁ m₂ : ℕ

  -- Outputs read the input and the path only through their values.
  outBit-≗ : (ξ : PathSum n k m) {x x′ : Assign n} {y y′ : Assign m} →
             (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
             ∀ w → outBit ξ x y w ≡ outBit ξ x′ y′ w
  outBit-≗ ξ hx hy w = cong odd (eval-cong (out ξ w) hx hy)


------------------------------------------------------------------------
-- Relabelling is functorial over sequential composition

-- The bits relabel σ ξ leaves, read back through σ, are ξ's at the
-- input read through σ.

private
  bits : (σ : Permutation n n′) (ξ : PathSum n k m) (x : Assign n′)
         (y : Assign m) (i : Fin n) →
         outBit (relabel σ ξ) x y (σ ⟨$⟩ʳ i) ≡
         outBit ξ (λ i′ → x (σ ⟨$⟩ʳ i′)) y i
  bits σ ξ x y i = trans (outBit-relabel σ ξ x y (σ ⟨$⟩ʳ i))
                         (cong (outBit ξ (λ i′ → x (σ ⟨$⟩ʳ i′)) y) (inverseˡ σ))

relabel-∘ᴾ : (σ : Permutation n n′) (ξ′ : PathSum n k′ m′)
             (ξ : PathSum n k m) →
             relabel σ (ξ′ ∘ᴾ ξ) ≡ᴿ⟨ id ⟩ (relabel σ ξ′ ∘ᴾ relabel σ ξ)
relabel-∘ᴾ {n = n} {n′ = n′} {m′ = m′} {m = m} σ ξ′ ξ =
  ≡ᴿ-by-values (relabel σ (ξ′ ∘ᴾ ξ)) (relabel σ ξ′ ∘ᴾ relabel σ ξ) id refl
               ph ou
  where
  xσ : Assign n′ → Assign n
  xσ x i = x (σ ⟨$⟩ʳ i)

  ph : ∀ (x : Assign n′) (Y : Assign (m ℕ+ m′)) →
       eval (phase (relabel σ (ξ′ ∘ᴾ ξ))) x (λ j → Y (id ⟨$⟩ʳ j)) ≡
       eval (phase (relabel σ ξ′ ∘ᴾ relabel σ ξ)) x Y
  ph x Y =
    trans (eval-relabelᴾ σ (phase (ξ′ ∘ᴾ ξ)) x Y)
    (trans (eval-∘-blocks ξ′ ξ (xσ x) Y)
    (sym (trans (eval-∘-blocks (relabel σ ξ′) (relabel σ ξ) x Y)
         (cong₂ _+_
           (eval-relabelᴾ σ (phase ξ) x (takeᵃ m′ Y))
           (trans (eval-relabelᴾ σ (phase ξ′)
                    (outBit (relabel σ ξ) x (takeᵃ m′ Y)) (dropᵃ m Y))
                  (eval-cong (phase ξ′) (bits σ ξ x (takeᵃ m′ Y))
                             (λ _ → refl)))))))

  ou : ∀ w (x : Assign n′) (Y : Assign (m ℕ+ m′)) →
       eval (out (relabel σ (ξ′ ∘ᴾ ξ)) w) x (λ j → Y (id ⟨$⟩ʳ j)) ≡
       eval (out (relabel σ ξ′ ∘ᴾ relabel σ ξ) w) x Y
  ou w x Y =
    trans (eval-relabelᴾ σ (out (ξ′ ∘ᴾ ξ) (σ ⟨$⟩ˡ w)) x Y)
    (trans (eval-out-∘-blocks ξ′ ξ (xσ x) Y (σ ⟨$⟩ˡ w))
    (sym (trans (eval-out-∘-blocks (relabel σ ξ′) (relabel σ ξ) x Y w)
         (trans (eval-relabelᴾ σ (out ξ′ (σ ⟨$⟩ˡ w))
                   (outBit (relabel σ ξ) x (takeᵃ m′ Y)) (dropᵃ m Y))
                (eval-cong (out ξ′ (σ ⟨$⟩ˡ w)) (bits σ ξ x (takeᵃ m′ Y))
                           (λ _ → refl))))))

relabel-∘ᴾ-≋ : (σ : Permutation n n′) (ξ′ : PathSum n k′ m′)
               (ξ : PathSum n k m) →
               relabel σ (ξ′ ∘ᴾ ξ) ≋ (relabel σ ξ′ ∘ᴾ relabel σ ξ)
relabel-∘ᴾ-≋ σ ξ′ ξ =
  ≡ᴿ⇒≋ {ξ = relabel σ (ξ′ ∘ᴾ ξ)} {π = id}
       {ζ = relabel σ ξ′ ∘ᴾ relabel σ ξ} (relabel-∘ᴾ σ ξ′ ξ)


------------------------------------------------------------------------
-- Relabelling is functorial over parallel composition

relabel-⊗ᴾ : (σ : Permutation n₁ n₁′) (τ : Permutation n₂ n₂′)
             (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
             relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂) ≡ᴿ⟨ id ⟩
             (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂)
relabel-⊗ᴾ {n₁ = n₁} {n₁′ = n₁′} {n₂ = n₂} {n₂′ = n₂′} {m₁ = m₁} {m₂ = m₂}
           σ τ ξ₁ ξ₂ =
  ≡ᴿ-by-values (relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂)) (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂)
               id refl ph ou
  where
  -- The input read through σ ⊕ τ, block by block.
  up : (x : Assign (n₁′ ℕ+ n₂′)) (i : Fin n₁) →
       x ((σ ⊕ᵖ τ) ⟨$⟩ʳ (i ↑ˡ n₂)) ≡ takeᵃ n₂′ x (σ ⟨$⟩ʳ i)
  up x i = cong x (⊕-1 (σ ⟨$⟩ʳ_) (τ ⟨$⟩ʳ_) i)

  down : (x : Assign (n₁′ ℕ+ n₂′)) (j : Fin n₂) →
         x ((σ ⊕ᵖ τ) ⟨$⟩ʳ (n₁ ↑ʳ j)) ≡ dropᵃ n₁′ x (τ ⟨$⟩ʳ j)
  down x j = cong x (⊕-2 (σ ⟨$⟩ʳ_) (τ ⟨$⟩ʳ_) j)

  ph : ∀ (x : Assign (n₁′ ℕ+ n₂′)) (y : Assign (m₁ ℕ+ m₂)) →
       eval (phase (relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂))) x (λ j → y (id ⟨$⟩ʳ j)) ≡
       eval (phase (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂)) x y
  ph x y =
    trans (eval-relabelᴾ (σ ⊕ᵖ τ) (phase (ξ₁ ⊗ᴾ ξ₂)) x y)
    (trans (eval-⊗-blocks ξ₁ ξ₂ (λ i → x ((σ ⊕ᵖ τ) ⟨$⟩ʳ i)) y)
    (trans (cong₂ _+_
      (trans (eval-cong (phase ξ₁) (up x) (λ _ → refl))
             (sym (eval-relabelᴾ σ (phase ξ₁) (takeᵃ n₂′ x) (takeᵃ m₂ y))))
      (trans (eval-cong (phase ξ₂) (down x) (λ _ → refl))
             (sym (eval-relabelᴾ τ (phase ξ₂) (dropᵃ n₁′ x) (dropᵃ m₁ y)))))
    (sym (eval-⊗-blocks (relabel σ ξ₁) (relabel τ ξ₂) x y))))

  ou : ∀ w (x : Assign (n₁′ ℕ+ n₂′)) (y : Assign (m₁ ℕ+ m₂)) →
       eval (out (relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂)) w) x (λ j → y (id ⟨$⟩ʳ j)) ≡
       eval (out (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂) w) x y
  ou w x y = blocks n₁′ n₂′ {P} one two w
    where
    X : Assign (n₁ ℕ+ n₂)
    X i = x ((σ ⊕ᵖ τ) ⟨$⟩ʳ i)

    P : Fin (n₁′ ℕ+ n₂′) → Set
    P v = eval (out (relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂)) v) x y ≡
          eval (out (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂) v) x y

    one : ∀ i → P (i ↑ˡ n₂′)
    one i =
      trans (eval-relabelᴾ (σ ⊕ᵖ τ)
               (out (ξ₁ ⊗ᴾ ξ₂) ((σ ⊕ᵖ τ) ⟨$⟩ˡ (i ↑ˡ n₂′))) x y)
      (trans (cong (λ v → eval (out (ξ₁ ⊗ᴾ ξ₂) v) X y)
                   (⊕-1 (σ ⟨$⟩ˡ_) (τ ⟨$⟩ˡ_) i))
      (trans (eval-out-⊗ˡ ξ₁ ξ₂ X y (σ ⟨$⟩ˡ i))
      (trans (eval-cong (out ξ₁ (σ ⟨$⟩ˡ i)) (up x) (λ _ → refl))
             (sym (trans (eval-out-⊗ˡ (relabel σ ξ₁) (relabel τ ξ₂) x y i)
                         (eval-relabelᴾ σ (out ξ₁ (σ ⟨$⟩ˡ i))
                                        (takeᵃ n₂′ x) (takeᵃ m₂ y)))))))

    two : ∀ j → P (n₁′ ↑ʳ j)
    two j =
      trans (eval-relabelᴾ (σ ⊕ᵖ τ)
               (out (ξ₁ ⊗ᴾ ξ₂) ((σ ⊕ᵖ τ) ⟨$⟩ˡ (n₁′ ↑ʳ j))) x y)
      (trans (cong (λ v → eval (out (ξ₁ ⊗ᴾ ξ₂) v) X y)
                   (⊕-2 (σ ⟨$⟩ˡ_) (τ ⟨$⟩ˡ_) j))
      (trans (eval-out-⊗ʳ ξ₁ ξ₂ X y (τ ⟨$⟩ˡ j))
      (trans (eval-cong (out ξ₂ (τ ⟨$⟩ˡ j)) (down x) (λ _ → refl))
             (sym (trans (eval-out-⊗ʳ (relabel σ ξ₁) (relabel τ ξ₂) x y j)
                         (eval-relabelᴾ τ (out ξ₂ (τ ⟨$⟩ˡ j))
                                        (dropᵃ n₁′ x) (dropᵃ m₁ y)))))))

relabel-⊗ᴾ-≋ : (σ : Permutation n₁ n₁′) (τ : Permutation n₂ n₂′)
               (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
               relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂) ≋ (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂)
relabel-⊗ᴾ-≋ σ τ ξ₁ ξ₂ =
  ≡ᴿ⇒≋ {ξ = relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂)} {π = id}
       {ζ = relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂} (relabel-⊗ᴾ σ τ ξ₁ ξ₂)


------------------------------------------------------------------------
-- Conjugation by SWAP

-- SWAP, then ξ, then SWAP again, is ξ with its two blocks of wires
-- exchanged: relabelled along the braiding.  The path variables are
-- ξ's, in a block of m + 0.

swap-conjugateᴿ : (ξ : PathSum (n ℕ+ n) k m) →
                  ((swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n) ≈ᴿ⟨ unitʳᵖ m ⟩
                  relabel (braidᵖ n n) ξ
swap-conjugateᴿ {n = n} {k = k} {m = m} ξ =
  ≈ᴿ-by-values ((swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n) (relabel (braidᵖ n n) ξ)
               (unitʳᵖ m) (ℕ.+-identityʳ k) ph ob
  where
  A = swapᴾ n ∘ᴾ ξ

  module At (x : Assign (n ℕ+ n)) (y : Assign m) where
    Y : Assign (m ℕ+ 0)
    Y j = y (unitʳᵖ m ⟨$⟩ʳ j)

    -- The input after the first SWAP: the two blocks exchanged.
    X : Assign (n ℕ+ n)
    X = outBit (swapᴾ n) x (takeᵃ {n₁ = 0} (m ℕ+ 0) Y)

    xs : ∀ i → X i ≡ x (braidᶠ n n i)
    xs i = outBit-swap n x (takeᵃ {n₁ = 0} (m ℕ+ 0) Y) i

    -- ξ's path: the block of m + 0, read through the cast.
    ys : ∀ j → takeᵃ 0 (dropᵃ 0 Y) j ≡ y j
    ys j = cong y (unitʳ-1 m j)

  ph : ∀ (x : Assign (n ℕ+ n)) (y : Assign m) →
       eval (phase ((swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n)) x
            (λ j → y (unitʳᵖ m ⟨$⟩ʳ j)) ≡
       eval (phase (relabel (braidᵖ n n) ξ)) x y
  ph x y =
    trans (eval-∘-blocks A (swapᴾ n) x Y)
    (trans (cong₂ _+_ (eval-0ᴾ-val x (takeᵃ {n₁ = 0} (m ℕ+ 0) Y))
                      (eval-∘-blocks (swapᴾ n) ξ X (dropᵃ 0 Y)))
    (trans (+-identityˡ _)
    (trans (cong₂ _+_ (eval-cong (phase ξ) xs ys)
                      (eval-0ᴾ-val (outBit ξ X (takeᵃ 0 (dropᵃ 0 Y)))
                                   (dropᵃ m (dropᵃ 0 Y))))
    (trans (+-identityʳ _)
           (sym (eval-relabelᴾ (braidᵖ n n) (phase ξ) x y))))))
    where
    open At x y

  ob : ∀ w (x : Assign (n ℕ+ n)) (y : Assign m) →
       outBit ((swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n) x (λ j → y (unitʳᵖ m ⟨$⟩ʳ j)) w ≡
       outBit (relabel (braidᵖ n n) ξ) x y w
  ob w x y =
    trans (outBit-∘-blocks A (swapᴾ n) x Y w)
    (trans (outBit-∘-blocks (swapᴾ n) ξ X (dropᵃ 0 Y) w)
    (trans (outBit-swap n (outBit ξ X (takeᵃ 0 (dropᵃ 0 Y)))
                        (dropᵃ m (dropᵃ 0 Y)) w)
    (trans (outBit-≗ ξ xs ys (braidᶠ n n w))
           (sym (outBit-relabel (braidᵖ n n) ξ x y w)))))
    where
    open At x y

swap-conjugate-≋ : (ξ : PathSum (n ℕ+ n) k m) →
                   ((swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n) ≋ relabel (braidᵖ n n) ξ
swap-conjugate-≋ {n = n} {m = m} ξ =
  ≈ᴿ⇒≋ {ξ = (swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n} {π = unitʳᵖ m}
       {ζ = relabel (braidᵖ n n) ξ} (swap-conjugateᴿ {n = n} ξ)


------------------------------------------------------------------------
-- The drawn form of bifunctoriality

-- The renamings.  First ξ₂ (on the lower wires), then ξ₁: ξ₂'s path
-- variables come first, so the blocks are exchanged, after dropping
-- the empty block of the identity.  First ξ₁, then ξ₂: the order is
-- already ξ₁'s then ξ₂'s, and only the cast is left.

seqᵖ : ∀ m₁ m₂ → Permutation (m₂ ℕ+ (m₁ ℕ+ 0)) (m₁ ℕ+ m₂)
seqᵖ m₁ m₂ = (id {m₂} ⊕ᵖ unitʳᵖ m₁) ∘ₚ braidᵖ m₂ m₁

seq′ᵖ : ∀ m₁ m₂ → Permutation ((m₁ ℕ+ 0) ℕ+ m₂) (m₁ ℕ+ m₂)
seq′ᵖ m₁ m₂ = unitʳᵖ m₁ ⊕ᵖ id {m₂}

-- ξ₂ on the lower wires, then ξ₁ on the upper ones, is ξ₁ ⊗ ξ₂.

⊗-sequentialᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
                ((ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂)) ≈ᴿ⟨ seqᵖ m₁ m₂ ⟩
                (ξ₁ ⊗ᴾ ξ₂)
⊗-sequentialᴿ {n₁ = n₁} {k₁ = k₁} {m₁ = m₁} {n₂ = n₂} {k₂ = k₂} {m₂ = m₂}
              ξ₁ ξ₂ =
  ≈ᴿ-by-values (B ∘ᴾ A) (ξ₁ ⊗ᴾ ξ₂) (seqᵖ m₁ m₂)
    (trans (cong (k₂ ℕ+_) (ℕ.+-identityʳ k₁)) (ℕ.+-comm k₂ k₁)) ph ob
  where
  A = idPS {n₁} ⊗ᴾ ξ₂
  B = ξ₁ ⊗ᴾ idPS {n₂}

  module At (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) where
    Y : Assign (m₂ ℕ+ (m₁ ℕ+ 0))
    Y j = y (seqᵖ m₁ m₂ ⟨$⟩ʳ j)

    -- A's path, B's path, and the bits A leaves.
    P₁ : Assign m₂
    P₁ = takeᵃ (m₁ ℕ+ 0) Y

    P₂ : Assign (m₁ ℕ+ 0)
    P₂ = dropᵃ m₂ Y

    F : Assign (n₁ ℕ+ n₂)
    F = outBit A x P₁

    p₁ : ∀ j → P₁ j ≡ dropᵃ m₁ y j
    p₁ j = cong y (trans (cong (braidᶠ m₂ m₁)
                               (⊕-1 (id {m₂} ⟨$⟩ʳ_) (unitʳᵖ m₁ ⟨$⟩ʳ_) j))
                         (braid-1 m₂ m₁ j))

    p₂ : ∀ i → takeᵃ 0 P₂ i ≡ takeᵃ m₂ y i
    p₂ i = cong y (trans (cong (braidᶠ m₂ m₁)
                    (trans (⊕-2 (id {m₂} ⟨$⟩ʳ_) (unitʳᵖ m₁ ⟨$⟩ʳ_) (i ↑ˡ 0))
                           (cong (m₂ ↑ʳ_) (unitʳ-1 m₁ i))))
                         (braid-2 m₂ m₁ i))

    -- On the upper wires the identity leaves the input; on the lower
    -- ones ξ₂'s bits.
    f₁ : ∀ i → takeᵃ n₂ F i ≡ takeᵃ n₂ x i
    f₁ i = trans (outBit-⊗ˡ (idPS {n₁}) ξ₂ x P₁ i)
                 (outBit-μ (idPS {n₁}) (takeᵃ n₂ x) (takeᵃ m₂ P₁) i x[ i ] refl)

    f₂ : ∀ j → dropᵃ n₁ F j ≡ outBit ξ₂ (dropᵃ n₁ x) (dropᵃ m₁ y) j
    f₂ j = trans (outBit-⊗ʳ (idPS {n₁}) ξ₂ x P₁ j)
                 (outBit-≗ ξ₂ (λ _ → refl) p₁ j)

  ph : ∀ (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) →
       eval (phase (B ∘ᴾ A)) x (λ j → y (seqᵖ m₁ m₂ ⟨$⟩ʳ j)) ≡
       eval (phase (ξ₁ ⊗ᴾ ξ₂)) x y
  ph x y =
    trans (eval-∘-blocks B A x Y)
    (trans (cong₂ _+_ (eval-⊗-blocks (idPS {n₁}) ξ₂ x P₁)
                      (eval-⊗-blocks ξ₁ (idPS {n₂}) F P₂))
    (trans (cong₂ _+_
             (cong₂ _+_ (eval-0ᴾ-val (takeᵃ n₂ x) (takeᵃ {n₁ = 0} m₂ P₁))
                        (eval-cong (phase ξ₂) (λ _ → refl) p₁))
             (cong₂ _+_ (eval-cong (phase ξ₁) f₁ p₂)
                        (eval-0ᴾ-val (dropᵃ n₁ F) (dropᵃ {n₂ = 0} m₁ P₂))))
    (trans (cong₂ _+_ (+-identityˡ b) (+-identityʳ a))
    (trans (+-comm b a)
           (sym (eval-⊗-blocks ξ₁ ξ₂ x y))))))
    where
    open At x y

    a b : ℤ
    a = eval (phase ξ₁) (takeᵃ n₂ x) (takeᵃ m₂ y)
    b = eval (phase ξ₂) (dropᵃ n₁ x) (dropᵃ m₁ y)

  ob : ∀ w (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) →
       outBit (B ∘ᴾ A) x (λ j → y (seqᵖ m₁ m₂ ⟨$⟩ʳ j)) w ≡
       outBit (ξ₁ ⊗ᴾ ξ₂) x y w
  ob w x y = blocks n₁ n₂ {Q} one two w
    where
    open At x y

    Q : Fin (n₁ ℕ+ n₂) → Set
    Q v = outBit (B ∘ᴾ A) x Y v ≡ outBit (ξ₁ ⊗ᴾ ξ₂) x y v

    one : ∀ i → Q (i ↑ˡ n₂)
    one i =
      trans (outBit-∘-blocks B A x Y (i ↑ˡ n₂))
      (trans (outBit-⊗ˡ ξ₁ (idPS {n₂}) F P₂ i)
      (trans (outBit-≗ ξ₁ f₁ p₂ i)
             (sym (outBit-⊗ˡ ξ₁ ξ₂ x y i))))

    two : ∀ j → Q (n₁ ↑ʳ j)
    two j =
      trans (outBit-∘-blocks B A x Y (n₁ ↑ʳ j))
      (trans (outBit-⊗ʳ ξ₁ (idPS {n₂}) F P₂ j)
      (trans (outBit-μ (idPS {n₂}) (dropᵃ n₁ F) (dropᵃ m₁ P₂) j x[ j ] refl)
      (trans (f₂ j)
             (sym (outBit-⊗ʳ ξ₁ ξ₂ x y j)))))

-- ξ₁ on the upper wires, then ξ₂ on the lower ones, is ξ₁ ⊗ ξ₂.

⊗-sequential′ᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
                 ((idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})) ≈ᴿ⟨ seq′ᵖ m₁ m₂ ⟩
                 (ξ₁ ⊗ᴾ ξ₂)
⊗-sequential′ᴿ {n₁ = n₁} {k₁ = k₁} {m₁ = m₁} {n₂ = n₂} {k₂ = k₂} {m₂ = m₂}
               ξ₁ ξ₂ =
  ≈ᴿ-by-values (B ∘ᴾ A) (ξ₁ ⊗ᴾ ξ₂) (seq′ᵖ m₁ m₂)
    (cong (_ℕ+ k₂) (ℕ.+-identityʳ k₁)) ph ob
  where
  A = ξ₁ ⊗ᴾ idPS {n₂}
  B = idPS {n₁} ⊗ᴾ ξ₂

  module At (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) where
    Y : Assign ((m₁ ℕ+ 0) ℕ+ m₂)
    Y j = y (seq′ᵖ m₁ m₂ ⟨$⟩ʳ j)

    P₁ : Assign (m₁ ℕ+ 0)
    P₁ = takeᵃ m₂ Y

    P₂ : Assign m₂
    P₂ = dropᵃ (m₁ ℕ+ 0) Y

    F : Assign (n₁ ℕ+ n₂)
    F = outBit A x P₁

    p₁ : ∀ i → takeᵃ 0 P₁ i ≡ takeᵃ m₂ y i
    p₁ i = cong y (trans (⊕-1 (unitʳᵖ m₁ ⟨$⟩ʳ_) (id {m₂} ⟨$⟩ʳ_) (i ↑ˡ 0))
                         (cong (_↑ˡ m₂) (unitʳ-1 m₁ i)))

    p₂ : ∀ j → P₂ j ≡ dropᵃ m₁ y j
    p₂ j = cong y (⊕-2 (unitʳᵖ m₁ ⟨$⟩ʳ_) (id {m₂} ⟨$⟩ʳ_) j)

    -- On the upper wires ξ₁'s bits; on the lower ones the identity
    -- leaves the input.
    f₁ : ∀ i → takeᵃ n₂ F i ≡ outBit ξ₁ (takeᵃ n₂ x) (takeᵃ m₂ y) i
    f₁ i = trans (outBit-⊗ˡ ξ₁ (idPS {n₂}) x P₁ i)
                 (outBit-≗ ξ₁ (λ _ → refl) p₁ i)

    f₂ : ∀ j → dropᵃ n₁ F j ≡ dropᵃ n₁ x j
    f₂ j = trans (outBit-⊗ʳ ξ₁ (idPS {n₂}) x P₁ j)
                 (outBit-μ (idPS {n₂}) (dropᵃ n₁ x) (dropᵃ m₁ P₁) j x[ j ] refl)

  ph : ∀ (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) →
       eval (phase (B ∘ᴾ A)) x (λ j → y (seq′ᵖ m₁ m₂ ⟨$⟩ʳ j)) ≡
       eval (phase (ξ₁ ⊗ᴾ ξ₂)) x y
  ph x y =
    trans (eval-∘-blocks B A x Y)
    (trans (cong₂ _+_ (eval-⊗-blocks ξ₁ (idPS {n₂}) x P₁)
                      (eval-⊗-blocks (idPS {n₁}) ξ₂ F P₂))
    (trans (cong₂ _+_
             (cong₂ _+_ (eval-cong (phase ξ₁) (λ _ → refl) p₁)
                        (eval-0ᴾ-val (dropᵃ n₁ x) (dropᵃ {n₂ = 0} m₁ P₁)))
             (cong₂ _+_ (eval-0ᴾ-val (takeᵃ n₂ F) (takeᵃ {n₁ = 0} m₂ P₂))
                        (eval-cong (phase ξ₂) f₂ p₂)))
    (trans (cong₂ _+_ (+-identityʳ a) (+-identityˡ b))
           (sym (eval-⊗-blocks ξ₁ ξ₂ x y)))))
    where
    open At x y

    a b : ℤ
    a = eval (phase ξ₁) (takeᵃ n₂ x) (takeᵃ m₂ y)
    b = eval (phase ξ₂) (dropᵃ n₁ x) (dropᵃ m₁ y)

  ob : ∀ w (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) →
       outBit (B ∘ᴾ A) x (λ j → y (seq′ᵖ m₁ m₂ ⟨$⟩ʳ j)) w ≡
       outBit (ξ₁ ⊗ᴾ ξ₂) x y w
  ob w x y = blocks n₁ n₂ {Q} one two w
    where
    open At x y

    Q : Fin (n₁ ℕ+ n₂) → Set
    Q v = outBit (B ∘ᴾ A) x Y v ≡ outBit (ξ₁ ⊗ᴾ ξ₂) x y v

    one : ∀ i → Q (i ↑ˡ n₂)
    one i =
      trans (outBit-∘-blocks B A x Y (i ↑ˡ n₂))
      (trans (outBit-⊗ˡ (idPS {n₁}) ξ₂ F P₂ i)
      (trans (outBit-μ (idPS {n₁}) (takeᵃ n₂ F) (takeᵃ m₂ P₂) i x[ i ] refl)
      (trans (f₁ i)
             (sym (outBit-⊗ˡ ξ₁ ξ₂ x y i)))))

    two : ∀ j → Q (n₁ ↑ʳ j)
    two j =
      trans (outBit-∘-blocks B A x Y (n₁ ↑ʳ j))
      (trans (outBit-⊗ʳ (idPS {n₁}) ξ₂ F P₂ j)
      (trans (outBit-≗ ξ₂ f₂ p₂ j)
             (sym (outBit-⊗ʳ ξ₁ ξ₂ x y j))))

-- The two orders against each other: remark 2.8's picture.

remark-2-8ᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
              ((ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂))
              ≈ᴿ⟨ seqᵖ m₁ m₂ ∘ₚ flip (seq′ᵖ m₁ m₂) ⟩
              ((idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂}))
remark-2-8ᴿ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ =
  ≈ᴿ-trans {ξ = (ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂)} {π = seqᵖ m₁ m₂}
           {ζ = ξ₁ ⊗ᴾ ξ₂} {ρ = flip (seq′ᵖ m₁ m₂)}
           {χ = (idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})}
    (⊗-sequentialᴿ ξ₁ ξ₂)
    (≈ᴿ-sym {ξ = (idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})}
            {π = seq′ᵖ m₁ m₂} {ζ = ξ₁ ⊗ᴾ ξ₂} (⊗-sequential′ᴿ ξ₁ ξ₂))


------------------------------------------------------------------------
-- The second hexagon, for path-sums

-- Relabelling in three steps is relabelling along the composite.

private
  relabel³ : ∀ {o₁ o₂ o₃ o₄} (ρ : Permutation o₁ o₂) (σ : Permutation o₂ o₃)
             (τ : Permutation o₃ o₄) (ξ : PathSum o₁ k m) →
             relabel τ (relabel σ (relabel ρ ξ)) ≡ᴿ⟨ id ⟩
             relabel ((ρ ∘ₚ σ) ∘ₚ τ) ξ
  relabel³ ρ σ τ ξ = ≡ᴿ-cong (λ _ → refl)
    (≡ᴿ-trans (relabel-≡ᴿ τ (relabel-∘ ρ σ ξ)) (relabel-∘ (ρ ∘ₚ σ) τ ξ))

-- Moving c in front of a + b, along either side of the second hexagon.

hexagon′ᴿ : ∀ a b c (ξ : PathSum (a ℕ+ (b ℕ+ c)) k m) →
            relabel (flip (assocᵖ c a b))
              (relabel (braidᵖ (a ℕ+ b) c) (relabel (flip (assocᵖ a b c)) ξ))
            ≡ᴿ⟨ id ⟩
            relabel (braidᵖ a c ⊕ᵖ id {b})
              (relabel (flip (assocᵖ a c b)) (relabel (id {a} ⊕ᵖ braidᵖ b c) ξ))
hexagon′ᴿ a b c ξ = ≡ᴿ-cong (λ _ → refl)
  (≡ᴿ-trans (relabel³ (flip (assocᵖ a b c)) (braidᵖ (a ℕ+ b) c)
                      (flip (assocᵖ c a b)) ξ)
  (≡ᴿ-trans (relabel-cong
              {σ = (flip (assocᵖ a b c) ∘ₚ braidᵖ (a ℕ+ b) c) ∘ₚ
                   flip (assocᵖ c a b)}
              {τ = ((id {a} ⊕ᵖ braidᵖ b c) ∘ₚ flip (assocᵖ a c b)) ∘ₚ
                   (braidᵖ a c ⊕ᵖ id {b})}
              (hexagon′ a b c) ξ)
            (≡ᴿ-sym (relabel³ (id {a} ⊕ᵖ braidᵖ b c) (flip (assocᵖ a c b))
                              (braidᵖ a c ⊕ᵖ id {b}) ξ))))

hexagon′-≋ : ∀ a b c (ξ : PathSum (a ℕ+ (b ℕ+ c)) k m) →
             relabel (flip (assocᵖ c a b))
               (relabel (braidᵖ (a ℕ+ b) c) (relabel (flip (assocᵖ a b c)) ξ))
             ≋
             relabel (braidᵖ a c ⊕ᵖ id {b})
               (relabel (flip (assocᵖ a c b)) (relabel (id {a} ⊕ᵖ braidᵖ b c) ξ))
hexagon′-≋ a b c ξ =
  ≡ᴿ⇒≋ {ξ = relabel (flip (assocᵖ c a b))
               (relabel (braidᵖ (a ℕ+ b) c) (relabel (flip (assocᵖ a b c)) ξ))}
       {π = id}
       {ζ = relabel (braidᵖ a c ⊕ᵖ id {b})
              (relabel (flip (assocᵖ a c b)) (relabel (id {a} ⊕ᵖ braidᵖ b c) ξ))}
       (hexagon′ᴿ a b c ξ)
