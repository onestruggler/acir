------------------------------------------------------------------------
-- Presentations of groups
--
-- The symmetric monoidal laws of path-sums, up to renaming their path
-- variables (Amy, QPL 2018, remark 2.8)
--
-- Remark 2.8: "circuits which are equivalent up to symmetric monoidal
-- laws are strictly equal in the path-sum picture.  For instance, the
-- bifunctoriality law and the naturality of SWAP ... are both equality
-- in the path-sum framework."  PathSum.Compose.Tensor and
-- PathSum.Compose.Swap prove those two examples up to ≋.  Here every
-- law of a symmetric monoidal category is proved for path-sums in the
-- strongest form available: equality of the path-sums up to a renaming
-- of their path variables (PathSum.Permute's ≡ᴿ, or ≈ᴿ where outputs
-- agree only modulo 2), and hence ≋.
--
-- The objects are numbers of wires, ⊗ᴾ adds them, and a path-sum on n
-- wires is a morphism n → n.  The structure maps -- the associator,
-- the unitors, the braiding -- are bijections of the wires between the
-- two sides (PathSum.Permute.Blocks), and act on a path-sum by
-- relabelling its wires (PathSum.Permute.relabel: inputs renamed,
-- outputs moved).  So a law relating path-sums on (n₁ + n₂) + n₃ and
-- n₁ + (n₂ + n₃) wires is stated after re-indexing the first along the
-- cast between them; ≋, which relates path-sums on the same wires, then
-- applies.
--
-- The laws, each with the renaming of the path variables it needs.
--
--    ⊗-assocᴿ   relabel α ((ξ₁ ⊗ ξ₂) ⊗ ξ₃) ≡ᴿ⟨ α ⟩ ξ₁ ⊗ (ξ₂ ⊗ ξ₃)
--               α the casts along +-assoc, of wires and of paths;
--    ⊗-unitˡᴿ   idPS {0} ⊗ ξ ≡ᴿ⟨ id ⟩ ξ                (0 + n is n);
--    ⊗-unitʳᴿ   relabel ρ (ξ ⊗ idPS {0}) ≡ᴿ⟨ ρ ⟩ ξ
--               ρ the casts along +-identityʳ;
--    ⊗-braidᴿ   relabel β (ξ₁ ⊗ ξ₂) ≡ᴿ⟨ β ⟩ ξ₂ ⊗ ξ₁
--               β the exchange of the blocks, of wires and of paths --
--               the naturality of the symmetry;
--    braid-braidᴿ, hexagonᴿ, pentagonᴿ, triangleᴿ: relabelling along
--               either side of a coherence diagram gives the same
--               path-sum, coefficient by coefficient (≡ᴿ⟨ id ⟩): the
--               symmetry is involutive, and the hexagon, pentagon and
--               triangle commute (they do already as bijections of
--               wires, PathSum.Permute.Blocks);
--    ⊗-idPSᴿ    idPS ⊗ idPS ≡ᴿ⟨ id ⟩ idPS;
--
-- and remark 2.8's two examples, with composition:
--
--    ⊗-interchangeᴿ  (ξ₁ ⊗ ξ₂) ∘ (ζ₁ ⊗ ζ₂) ≡ᴿ⟨ shuffle ⟩
--                    (ξ₁ ∘ ζ₁) ⊗ (ξ₂ ∘ ζ₂), the middle blocks of
--                    path variables exchanged -- bifunctoriality;
--    swap-naturalᴿ   SWAP ∘ (ξ₁ ⊗ ξ₂) ≈ᴿ⟨ β ⟩ (ξ₂ ⊗ ξ₁) ∘ SWAP --
--                    the naturality of SWAP, for the SWAP path-sum of
--                    PathSum.Compose.Swap;
--
-- and the category laws of ∘ᴾ that PathSum.Compose.Laws proves up to
-- ≋: ∘ᴾ-identityʳᴿ (≡ᴿ⟨ id ⟩), ∘ᴾ-identityˡᴿ (≈ᴿ, a cast) and
-- ∘ᴾ-assocᴿ (≡ᴿ, a cast).  Every one gives ≋ by ≡ᴿ⇒≋ or ≈ᴿ⇒≋; the ≋
-- forms of most are stated (⊗-assoc-≋, ⊗-unitˡ-≋, ⊗-unitʳ-≋,
-- ⊗-braid-≋, braid-braid-≋, hexagon-≋, ⊗-interchange-≋,
-- swap-natural-≋, ∘ᴾ-assoc-≋), and the rest are one application of
-- those two lemmas away.
--
-- So every law holds syntactically, up to renaming: none needs ≋'s
-- freedom to change the paths themselves (as [HH] or [Elim] do).  What
-- "strictly equal" comes to.  (1) The renaming of the path variables:
-- a trivial cast for the associator, the unitors and ∘ᴾ's laws, but a
-- genuine permutation for the braiding, the interchange law and SWAP,
-- because a path-sum lists its path variables block by block in the
-- order of its construction.  (2) Equality coefficient by coefficient,
-- as functions are not identified without function extensionality,
-- with normalisations equal only as numbers ((k₁ + k₂) + k₃ against
-- k₁ + (k₂ + k₃)).  (3) The phases agree exactly, as integers -- more
-- than the modulo 2^M that ≋ needs -- and so do the outputs, except
-- where a composite with SWAP or with idPS on the left substitutes the
-- lifted outputs of definition 2.6 (PathSum.Compose): the lift f̄
-- agrees with f modulo 2 only, so swap-naturalᴿ and ∘ᴾ-identityˡᴿ hold
-- with the outputs congruent modulo 2 (≈ᴿ), which is how outputs are
-- read.
--
-- Every proof is by values: both sides are evaluated block by block
-- (eval-⊗-blocks and the output lemmas below for ⊗ᴾ, eval-∘-blocks for
-- ∘ᴾ), the blocks are matched through the block lemmas of the
-- bijections, and Möbius uniqueness turns equal values into equal
-- coefficients (≡ᴿ-by-values, ≈ᴿ-by-values).  No polynomial is
-- computed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Monoidal (M₀ : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Permutation using
  (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_; id; flip; _∘ₚ_)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_)
open import Data.Integer.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Compose using (⊗ˡ; ⊗ʳ; feed; _⊗ᴾ_; _∘ᴾ_)
open import PathSum.Compose.Properties M₀ using (eval-∘; eval-feed)
open import PathSum.Compose.Sum M₀ using (_++ᵃ_; ++ᵃ-split)
open import PathSum.Compose.Swap M₀ using
  (swapᴾ; swapᶠ; swapᶠ-↑ˡ; swapᶠ-↑ʳ; outBit-swap)
open import PathSum.Compose.Tensor M₀ using
  (takeᵃ; dropᵃ; out-⊗ˡ; out-⊗ʳ; eval-⊗-blocks; outBit-⊗ˡ; outBit-⊗ʳ)
open import PathSum.Denotation M₀ using
  (Assign; outBit; _≋_; outBit-μ; eval-0ᴾ-val; eval-μ-val)
open import PathSum.Permute using
  (relabel; relabelᴾ; eval-relabelᴾ; _≡ᴿ⟨_⟩_; ≡ᴿ-by-values; ≡ᴿ-trans;
   ≡ᴿ-sym; ≡ᴿ-cong; relabel-id; relabel-∘; relabel-cong; relabel-≡ᴿ)
open import PathSum.Permute.Blocks using
  (blocks; assocᵖ; unitʳᵖ; braidᵖ; braidᶠ; _⊕ᵖ_; shuffleᵖ; shuffleᶠ;
   assoc-1; assoc-2; assoc-3; assoc⁻¹-1; assoc⁻¹-2; assoc⁻¹-3; unitʳ-1;
   unitʳ⁻¹-1; braid-1; braid-2; braid-involutive; shuffle-1; shuffle-2;
   shuffle-3; shuffle-4; hexagon; pentagon; triangle)
open import PathSum.Permute.Sound M₀ using
  (_≈ᴿ⟨_⟩_; ≈ᴿ-by-values; ≈ᴿ⇒≋; ≡ᴿ⇒≋)
open import PathSum.Polynomial using (x[_]; eval)
open import PathSum.Polynomial.Bind using (eval-bind; eval-rename; odd)
open import PathSum.Polynomial.Properties using (eval-cong)

private
  variable
    o₁ o₂ o₃ o₄ n n₁ n₂ n₃ k k′ k″ k₁ k₂ k₃ m m′ m″ m₁ m₂ m₃ j₁ j₂ l₁ l₂ : ℕ


------------------------------------------------------------------------
-- The outputs of a tensor, along any path

-- The output on an upper wire is the upper path-sum's, read on the
-- upper blocks of the input and the path; likewise below.

eval-out-⊗ˡ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
              (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) (i : Fin n₁) →
              eval (out (ξ₁ ⊗ᴾ ξ₂) (i ↑ˡ n₂)) x y ≡
              eval (out ξ₁ i) (takeᵃ n₂ x) (takeᵃ m₂ y)
eval-out-⊗ˡ {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ x y i =
  trans (cong (λ P → eval P x y) (out-⊗ˡ ξ₁ ξ₂ i))
        (eval-rename (⊗ˡ n₂ m₂) (out ξ₁ i) x y)

eval-out-⊗ʳ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
              (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) (i : Fin n₂) →
              eval (out (ξ₁ ⊗ᴾ ξ₂) (n₁ ↑ʳ i)) x y ≡
              eval (out ξ₂ i) (dropᵃ n₁ x) (dropᵃ m₁ y)
eval-out-⊗ʳ {n₁ = n₁} {m₁ = m₁} ξ₁ ξ₂ x y i =
  trans (cong (λ P → eval P x y) (out-⊗ʳ ξ₁ ξ₂ i))
        (eval-rename (⊗ʳ n₁ m₁) (out ξ₂ i) x y)


------------------------------------------------------------------------
-- Associativity

-- The three blocks of either bracketing are the same blocks of the
-- wires and of the paths, read through the cast; the phases add in
-- either order.

⊗-assocᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
           (ξ₃ : PathSum n₃ k₃ m₃) →
           relabel (assocᵖ n₁ n₂ n₃) ((ξ₁ ⊗ᴾ ξ₂) ⊗ᴾ ξ₃) ≡ᴿ⟨ assocᵖ m₁ m₂ m₃ ⟩
           (ξ₁ ⊗ᴾ (ξ₂ ⊗ᴾ ξ₃))
⊗-assocᴿ {n₁ = n₁} {k₁ = k₁} {m₁ = m₁} {n₂ = n₂} {k₂ = k₂} {m₂ = m₂}
         {n₃ = n₃} {k₃ = k₃} {m₃ = m₃} ξ₁ ξ₂ ξ₃ =
  ≡ᴿ-by-values (relabel α A) B α′ (ℕ.+-assoc k₁ k₂ k₃) ph ou
  where
  A = (ξ₁ ⊗ᴾ ξ₂) ⊗ᴾ ξ₃
  B = ξ₁ ⊗ᴾ (ξ₂ ⊗ᴾ ξ₃)
  α = assocᵖ n₁ n₂ n₃
  α′ = assocᵖ m₁ m₂ m₃

  ph : ∀ (x : Assign (n₁ ℕ+ (n₂ ℕ+ n₃))) (y : Assign (m₁ ℕ+ (m₂ ℕ+ m₃))) →
       eval (phase (relabel α A)) x (λ j → y (α′ ⟨$⟩ʳ j)) ≡
       eval (phase B) x y
  ph x y =
    trans (eval-relabelᴾ α (phase A) x Y)
    (trans (eval-⊗-blocks (ξ₁ ⊗ᴾ ξ₂) ξ₃ X Y)
    (trans (cong (_+ L₃) (eval-⊗-blocks ξ₁ ξ₂ (takeᵃ n₃ X) (takeᵃ m₃ Y)))
    (trans (cong₂ _+_ (cong₂ _+_ e₁ e₂) e₃)
    (trans (+-assoc a₁ a₂ a₃)
           (sym (trans (eval-⊗-blocks ξ₁ (ξ₂ ⊗ᴾ ξ₃) x y)
                       (cong (a₁ +_) (eval-⊗-blocks ξ₂ ξ₃ (dropᵃ n₁ x)
                                                         (dropᵃ m₁ y)))))))))
    where
    X : Assign ((n₁ ℕ+ n₂) ℕ+ n₃)
    X i = x (α ⟨$⟩ʳ i)

    Y : Assign ((m₁ ℕ+ m₂) ℕ+ m₃)
    Y j = y (α′ ⟨$⟩ʳ j)

    L₃ a₁ a₂ a₃ : ℤ
    L₃ = eval (phase ξ₃) (dropᵃ (n₁ ℕ+ n₂) X) (dropᵃ (m₁ ℕ+ m₂) Y)
    a₁ = eval (phase ξ₁) (takeᵃ (n₂ ℕ+ n₃) x) (takeᵃ (m₂ ℕ+ m₃) y)
    a₂ = eval (phase ξ₂) (takeᵃ n₃ (dropᵃ n₁ x)) (takeᵃ m₃ (dropᵃ m₁ y))
    a₃ = eval (phase ξ₃) (dropᵃ n₂ (dropᵃ n₁ x)) (dropᵃ m₂ (dropᵃ m₁ y))

    e₁ : eval (phase ξ₁) (takeᵃ n₂ (takeᵃ n₃ X)) (takeᵃ m₂ (takeᵃ m₃ Y)) ≡ a₁
    e₁ = eval-cong (phase ξ₁) (λ i → cong x (assoc-1 n₁ n₂ n₃ i))
                              (λ j → cong y (assoc-1 m₁ m₂ m₃ j))

    e₂ : eval (phase ξ₂) (dropᵃ n₁ (takeᵃ n₃ X)) (dropᵃ m₁ (takeᵃ m₃ Y)) ≡ a₂
    e₂ = eval-cong (phase ξ₂) (λ i → cong x (assoc-2 n₁ n₂ n₃ i))
                              (λ j → cong y (assoc-2 m₁ m₂ m₃ j))

    e₃ : L₃ ≡ a₃
    e₃ = eval-cong (phase ξ₃) (λ i → cong x (assoc-3 n₁ n₂ n₃ i))
                              (λ j → cong y (assoc-3 m₁ m₂ m₃ j))

  ou : ∀ w (x : Assign (n₁ ℕ+ (n₂ ℕ+ n₃))) (y : Assign (m₁ ℕ+ (m₂ ℕ+ m₃))) →
       eval (out (relabel α A) w) x (λ j → y (α′ ⟨$⟩ʳ j)) ≡
       eval (out B w) x y
  ou w x y =
    blocks n₁ (n₂ ℕ+ n₃) {P} one (blocks n₂ n₃ {λ v → P (n₁ ↑ʳ v)} two three) w
    where
    X : Assign ((n₁ ℕ+ n₂) ℕ+ n₃)
    X i = x (α ⟨$⟩ʳ i)

    Y : Assign ((m₁ ℕ+ m₂) ℕ+ m₃)
    Y j = y (α′ ⟨$⟩ʳ j)

    P : Fin (n₁ ℕ+ (n₂ ℕ+ n₃)) → Set
    P v = eval (out (relabel α A) v) x Y ≡ eval (out B v) x y

    at : ∀ v → eval (out (relabel α A) v) x Y ≡ eval (out A (α ⟨$⟩ˡ v)) X Y
    at v = eval-relabelᴾ α (out A (α ⟨$⟩ˡ v)) x Y

    one : ∀ i → eval (out (relabel α A) (i ↑ˡ (n₂ ℕ+ n₃))) x Y ≡
                eval (out B (i ↑ˡ (n₂ ℕ+ n₃))) x y
    one i = trans (at (i ↑ˡ (n₂ ℕ+ n₃)))
      (trans (cong (λ v → eval (out A v) X Y) (assoc⁻¹-1 n₁ n₂ n₃ i))
      (trans (eval-out-⊗ˡ (ξ₁ ⊗ᴾ ξ₂) ξ₃ X Y (i ↑ˡ n₂))
      (trans (eval-out-⊗ˡ ξ₁ ξ₂ (takeᵃ n₃ X) (takeᵃ m₃ Y) i)
      (trans (eval-cong (out ξ₁ i) (λ i′ → cong x (assoc-1 n₁ n₂ n₃ i′))
                                   (λ j → cong y (assoc-1 m₁ m₂ m₃ j)))
             (sym (eval-out-⊗ˡ ξ₁ (ξ₂ ⊗ᴾ ξ₃) x y i))))))

    two : ∀ j → eval (out (relabel α A) (n₁ ↑ʳ (j ↑ˡ n₃))) x Y ≡
                eval (out B (n₁ ↑ʳ (j ↑ˡ n₃))) x y
    two j = trans (at (n₁ ↑ʳ (j ↑ˡ n₃)))
      (trans (cong (λ v → eval (out A v) X Y) (assoc⁻¹-2 n₁ n₂ n₃ j))
      (trans (eval-out-⊗ˡ (ξ₁ ⊗ᴾ ξ₂) ξ₃ X Y (n₁ ↑ʳ j))
      (trans (eval-out-⊗ʳ ξ₁ ξ₂ (takeᵃ n₃ X) (takeᵃ m₃ Y) j)
      (trans (eval-cong (out ξ₂ j) (λ i → cong x (assoc-2 n₁ n₂ n₃ i))
                                   (λ j′ → cong y (assoc-2 m₁ m₂ m₃ j′)))
      (sym (trans (eval-out-⊗ʳ ξ₁ (ξ₂ ⊗ᴾ ξ₃) x y (j ↑ˡ n₃))
                  (eval-out-⊗ˡ ξ₂ ξ₃ (dropᵃ n₁ x) (dropᵃ m₁ y) j)))))))

    three : ∀ l → eval (out (relabel α A) (n₁ ↑ʳ (n₂ ↑ʳ l))) x Y ≡
                  eval (out B (n₁ ↑ʳ (n₂ ↑ʳ l))) x y
    three l = trans (at (n₁ ↑ʳ (n₂ ↑ʳ l)))
      (trans (cong (λ v → eval (out A v) X Y) (assoc⁻¹-3 n₁ n₂ n₃ l))
      (trans (eval-out-⊗ʳ (ξ₁ ⊗ᴾ ξ₂) ξ₃ X Y l)
      (trans (eval-cong (out ξ₃ l) (λ i → cong x (assoc-3 n₁ n₂ n₃ i))
                                   (λ j → cong y (assoc-3 m₁ m₂ m₃ j)))
      (sym (trans (eval-out-⊗ʳ ξ₁ (ξ₂ ⊗ᴾ ξ₃) x y (n₂ ↑ʳ l))
                  (eval-out-⊗ʳ ξ₂ ξ₃ (dropᵃ n₁ x) (dropᵃ m₁ y) l))))))

⊗-assoc-≋ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
            (ξ₃ : PathSum n₃ k₃ m₃) →
            relabel (assocᵖ n₁ n₂ n₃) ((ξ₁ ⊗ᴾ ξ₂) ⊗ᴾ ξ₃) ≋ (ξ₁ ⊗ᴾ (ξ₂ ⊗ᴾ ξ₃))
⊗-assoc-≋ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} {n₃ = n₃} {m₃ = m₃}
          ξ₁ ξ₂ ξ₃ =
  ≡ᴿ⇒≋ {ξ = relabel (assocᵖ n₁ n₂ n₃) ((ξ₁ ⊗ᴾ ξ₂) ⊗ᴾ ξ₃)}
       {π = assocᵖ m₁ m₂ m₃} {ζ = ξ₁ ⊗ᴾ (ξ₂ ⊗ᴾ ξ₃)} (⊗-assocᴿ ξ₁ ξ₂ ξ₃)


------------------------------------------------------------------------
-- The unit laws

-- On the left the empty block is no block at all: 0 + n is n, and the
-- identity on no wires adds the phase 0.

⊗-unitˡᴿ : (ξ : PathSum n k m) → (idPS {0} ⊗ᴾ ξ) ≡ᴿ⟨ id ⟩ ξ
⊗-unitˡᴿ {n = n} {m = m} ξ = ≡ᴿ-by-values (idPS {0} ⊗ᴾ ξ) ξ id refl ph ou
  where
  ph : ∀ (x : Assign n) (y : Assign m) →
       eval (phase (idPS {0} ⊗ᴾ ξ)) x (λ j → y (id ⟨$⟩ʳ j)) ≡
       eval (phase ξ) x y
  ph x y = trans (eval-⊗-blocks (idPS {0}) ξ x y)
    (trans (cong (_+ eval (phase ξ) x y)
                 (eval-0ᴾ-val (takeᵃ n x) (takeᵃ m y)))
           (+-identityˡ (eval (phase ξ) x y)))

  ou : ∀ w (x : Assign n) (y : Assign m) →
       eval (out (idPS {0} ⊗ᴾ ξ) w) x (λ j → y (id ⟨$⟩ʳ j)) ≡
       eval (out ξ w) x y
  ou w x y = eval-out-⊗ʳ (idPS {0}) ξ x y w

⊗-unitˡ-≋ : (ξ : PathSum n k m) → (idPS {0} ⊗ᴾ ξ) ≋ ξ
⊗-unitˡ-≋ ξ = ≡ᴿ⇒≋ {ξ = idPS {0} ⊗ᴾ ξ} {π = id} {ζ = ξ} (⊗-unitˡᴿ ξ)

-- On the right the cast along +-identityʳ, of the wires and of the
-- paths.

⊗-unitʳᴿ : (ξ : PathSum n k m) →
           relabel (unitʳᵖ n) (ξ ⊗ᴾ idPS {0}) ≡ᴿ⟨ unitʳᵖ m ⟩ ξ
⊗-unitʳᴿ {n = n} {k = k} {m = m} ξ =
  ≡ᴿ-by-values (relabel (unitʳᵖ n) (ξ ⊗ᴾ idPS {0})) ξ (unitʳᵖ m)
               (ℕ.+-identityʳ k) ph ou
  where
  ph : ∀ (x : Assign n) (y : Assign m) →
       eval (phase (relabel (unitʳᵖ n) (ξ ⊗ᴾ idPS {0}))) x
            (λ j → y (unitʳᵖ m ⟨$⟩ʳ j)) ≡
       eval (phase ξ) x y
  ph x y =
    trans (eval-relabelᴾ (unitʳᵖ n) (phase (ξ ⊗ᴾ idPS {0})) x Y)
    (trans (eval-⊗-blocks ξ (idPS {0}) X Y)
    (trans (cong₂ _+_ (eval-cong (phase ξ) (λ i → cong x (unitʳ-1 n i))
                                           (λ j → cong y (unitʳ-1 m j)))
                      (eval-0ᴾ-val (dropᵃ n X) (dropᵃ m Y)))
           (+-identityʳ (eval (phase ξ) x y))))
    where
    X : Assign (n ℕ+ 0)
    X i = x (unitʳᵖ n ⟨$⟩ʳ i)

    Y : Assign (m ℕ+ 0)
    Y j = y (unitʳᵖ m ⟨$⟩ʳ j)

  ou : ∀ w (x : Assign n) (y : Assign m) →
       eval (out (relabel (unitʳᵖ n) (ξ ⊗ᴾ idPS {0})) w) x
            (λ j → y (unitʳᵖ m ⟨$⟩ʳ j)) ≡
       eval (out ξ w) x y
  ou w x y =
    trans (eval-relabelᴾ (unitʳᵖ n) (out (ξ ⊗ᴾ idPS {0}) (unitʳᵖ n ⟨$⟩ˡ w))
                         x Y)
    (trans (cong (λ v → eval (out (ξ ⊗ᴾ idPS {0}) v) X Y) (unitʳ⁻¹-1 n w))
    (trans (eval-out-⊗ˡ ξ (idPS {0}) X Y w)
           (eval-cong (out ξ w) (λ i → cong x (unitʳ-1 n i))
                                (λ j → cong y (unitʳ-1 m j)))))
    where
    X : Assign (n ℕ+ 0)
    X i = x (unitʳᵖ n ⟨$⟩ʳ i)

    Y : Assign (m ℕ+ 0)
    Y j = y (unitʳᵖ m ⟨$⟩ʳ j)

⊗-unitʳ-≋ : (ξ : PathSum n k m) → relabel (unitʳᵖ n) (ξ ⊗ᴾ idPS {0}) ≋ ξ
⊗-unitʳ-≋ {n = n} {m = m} ξ =
  ≡ᴿ⇒≋ {ξ = relabel (unitʳᵖ n) (ξ ⊗ᴾ idPS {0})} {π = unitʳᵖ m} {ζ = ξ}
       (⊗-unitʳᴿ ξ)

-- The tensor of identities is the identity.

⊗-idPSᴿ : ∀ n₁ n₂ → (idPS {n₁} ⊗ᴾ idPS {n₂}) ≡ᴿ⟨ id ⟩ idPS {n₁ ℕ+ n₂}
⊗-idPSᴿ n₁ n₂ =
  ≡ᴿ-by-values (idPS {n₁} ⊗ᴾ idPS {n₂}) (idPS {n₁ ℕ+ n₂}) id refl ph ou
  where
  ph : ∀ (x : Assign (n₁ ℕ+ n₂)) (y : Assign 0) →
       eval (phase (idPS {n₁} ⊗ᴾ idPS {n₂})) x (λ j → y (id ⟨$⟩ʳ j)) ≡
       eval (phase (idPS {n₁ ℕ+ n₂})) x y
  ph x y = trans (eval-⊗-blocks (idPS {n₁}) (idPS {n₂}) x y)
    (trans (cong₂ _+_ (eval-0ᴾ-val (takeᵃ n₂ x) (takeᵃ 0 y))
                      (eval-0ᴾ-val (dropᵃ n₁ x) (dropᵃ 0 y)))
           (sym (eval-0ᴾ-val x y)))

  ou : ∀ w (x : Assign (n₁ ℕ+ n₂)) (y : Assign 0) →
       eval (out (idPS {n₁} ⊗ᴾ idPS {n₂}) w) x (λ j → y (id ⟨$⟩ʳ j)) ≡
       eval (out (idPS {n₁ ℕ+ n₂}) w) x y
  ou w x y = blocks n₁ n₂
    (λ i → trans (eval-out-⊗ˡ (idPS {n₁}) (idPS {n₂}) x y i)
             (trans (eval-μ-val x[ i ] (takeᵃ n₂ x) (takeᵃ 0 y))
                    (sym (eval-μ-val x[ i ↑ˡ n₂ ] x y))))
    (λ j → trans (eval-out-⊗ʳ (idPS {n₁}) (idPS {n₂}) x y j)
             (trans (eval-μ-val x[ j ] (dropᵃ n₁ x) (dropᵃ 0 y))
                    (sym (eval-μ-val x[ n₁ ↑ʳ j ] x y))))
    w


------------------------------------------------------------------------
-- The symmetry

-- Naturality: relabelling ξ₁ ⊗ ξ₂ along the exchange of the blocks
-- gives ξ₂ ⊗ ξ₁, once its paths are exchanged too.

⊗-braidᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
           relabel (braidᵖ n₁ n₂) (ξ₁ ⊗ᴾ ξ₂) ≡ᴿ⟨ braidᵖ m₁ m₂ ⟩ (ξ₂ ⊗ᴾ ξ₁)
⊗-braidᴿ {n₁ = n₁} {k₁ = k₁} {m₁ = m₁} {n₂ = n₂} {k₂ = k₂} {m₂ = m₂}
         ξ₁ ξ₂ =
  ≡ᴿ-by-values (relabel σ (ξ₁ ⊗ᴾ ξ₂)) (ξ₂ ⊗ᴾ ξ₁) σ′ (ℕ.+-comm k₁ k₂) ph ou
  where
  σ = braidᵖ n₁ n₂
  σ′ = braidᵖ m₁ m₂

  ph : ∀ (x : Assign (n₂ ℕ+ n₁)) (y : Assign (m₂ ℕ+ m₁)) →
       eval (phase (relabel σ (ξ₁ ⊗ᴾ ξ₂))) x (λ j → y (σ′ ⟨$⟩ʳ j)) ≡
       eval (phase (ξ₂ ⊗ᴾ ξ₁)) x y
  ph x y =
    trans (eval-relabelᴾ σ (phase (ξ₁ ⊗ᴾ ξ₂)) x Y)
    (trans (eval-⊗-blocks ξ₁ ξ₂ X Y)
    (trans (cong₂ _+_ e₁ e₂)
    (trans (+-comm b₁ b₂) (sym (eval-⊗-blocks ξ₂ ξ₁ x y)))))
    where
    X : Assign (n₁ ℕ+ n₂)
    X i = x (braidᶠ n₁ n₂ i)

    Y : Assign (m₁ ℕ+ m₂)
    Y j = y (braidᶠ m₁ m₂ j)

    b₁ b₂ : ℤ
    b₁ = eval (phase ξ₁) (dropᵃ n₂ x) (dropᵃ m₂ y)
    b₂ = eval (phase ξ₂) (takeᵃ n₁ x) (takeᵃ m₁ y)

    e₁ : eval (phase ξ₁) (takeᵃ n₂ X) (takeᵃ m₂ Y) ≡ b₁
    e₁ = eval-cong (phase ξ₁) (λ i → cong x (braid-1 n₁ n₂ i))
                              (λ j → cong y (braid-1 m₁ m₂ j))

    e₂ : eval (phase ξ₂) (dropᵃ n₁ X) (dropᵃ m₁ Y) ≡ b₂
    e₂ = eval-cong (phase ξ₂) (λ i → cong x (braid-2 n₁ n₂ i))
                              (λ j → cong y (braid-2 m₁ m₂ j))

  ou : ∀ w (x : Assign (n₂ ℕ+ n₁)) (y : Assign (m₂ ℕ+ m₁)) →
       eval (out (relabel σ (ξ₁ ⊗ᴾ ξ₂)) w) x (λ j → y (σ′ ⟨$⟩ʳ j)) ≡
       eval (out (ξ₂ ⊗ᴾ ξ₁) w) x y
  ou w x y = blocks n₂ n₁ {P} one two w
    where
    X : Assign (n₁ ℕ+ n₂)
    X i = x (braidᶠ n₁ n₂ i)

    Y : Assign (m₁ ℕ+ m₂)
    Y j = y (braidᶠ m₁ m₂ j)

    P : Fin (n₂ ℕ+ n₁) → Set
    P v = eval (out (relabel σ (ξ₁ ⊗ᴾ ξ₂)) v) x Y ≡ eval (out (ξ₂ ⊗ᴾ ξ₁) v) x y

    at : ∀ v → eval (out (relabel σ (ξ₁ ⊗ᴾ ξ₂)) v) x Y ≡
               eval (out (ξ₁ ⊗ᴾ ξ₂) (braidᶠ n₂ n₁ v)) X Y
    at v = eval-relabelᴾ σ (out (ξ₁ ⊗ᴾ ξ₂) (σ ⟨$⟩ˡ v)) x Y

    one : ∀ i → eval (out (relabel σ (ξ₁ ⊗ᴾ ξ₂)) (i ↑ˡ n₁)) x Y ≡
                eval (out (ξ₂ ⊗ᴾ ξ₁) (i ↑ˡ n₁)) x y
    one i = trans (at (i ↑ˡ n₁))
      (trans (cong (λ v → eval (out (ξ₁ ⊗ᴾ ξ₂) v) X Y) (braid-1 n₂ n₁ i))
      (trans (eval-out-⊗ʳ ξ₁ ξ₂ X Y i)
      (trans (eval-cong (out ξ₂ i) (λ j → cong x (braid-2 n₁ n₂ j))
                                   (λ j → cong y (braid-2 m₁ m₂ j)))
             (sym (eval-out-⊗ˡ ξ₂ ξ₁ x y i)))))

    two : ∀ j → eval (out (relabel σ (ξ₁ ⊗ᴾ ξ₂)) (n₂ ↑ʳ j)) x Y ≡
                eval (out (ξ₂ ⊗ᴾ ξ₁) (n₂ ↑ʳ j)) x y
    two j = trans (at (n₂ ↑ʳ j))
      (trans (cong (λ v → eval (out (ξ₁ ⊗ᴾ ξ₂) v) X Y) (braid-2 n₂ n₁ j))
      (trans (eval-out-⊗ˡ ξ₁ ξ₂ X Y j)
      (trans (eval-cong (out ξ₁ j) (λ i → cong x (braid-1 n₁ n₂ i))
                                   (λ i → cong y (braid-1 m₁ m₂ i)))
             (sym (eval-out-⊗ʳ ξ₂ ξ₁ x y j)))))

⊗-braid-≋ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
            relabel (braidᵖ n₁ n₂) (ξ₁ ⊗ᴾ ξ₂) ≋ (ξ₂ ⊗ᴾ ξ₁)
⊗-braid-≋ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ =
  ≡ᴿ⇒≋ {ξ = relabel (braidᵖ n₁ n₂) (ξ₁ ⊗ᴾ ξ₂)} {π = braidᵖ m₁ m₂}
       {ζ = ξ₂ ⊗ᴾ ξ₁} (⊗-braidᴿ ξ₁ ξ₂)


------------------------------------------------------------------------
-- Coherence, for path-sums

-- Relabelling in steps is relabelling along the composite.

private
  relabel² : (ρ : Permutation o₁ o₂) (σ : Permutation o₂ o₃)
             (ξ : PathSum o₁ k m) →
             relabel σ (relabel ρ ξ) ≡ᴿ⟨ id ⟩ relabel (ρ ∘ₚ σ) ξ
  relabel² ρ σ ξ = relabel-∘ ρ σ ξ

  relabel³ : (ρ : Permutation o₁ o₂) (σ : Permutation o₂ o₃)
             (τ : Permutation o₃ o₄) (ξ : PathSum o₁ k m) →
             relabel τ (relabel σ (relabel ρ ξ)) ≡ᴿ⟨ id ⟩
             relabel ((ρ ∘ₚ σ) ∘ₚ τ) ξ
  relabel³ ρ σ τ ξ = ≡ᴿ-cong (λ _ → refl)
    (≡ᴿ-trans (relabel-≡ᴿ τ (relabel-∘ ρ σ ξ)) (relabel-∘ (ρ ∘ₚ σ) τ ξ))

-- The symmetry is involutive: exchanging the blocks twice gives the
-- path-sum back.

braid-braidᴿ : ∀ n₁ n₂ (ξ : PathSum (n₁ ℕ+ n₂) k m) →
               relabel (braidᵖ n₂ n₁) (relabel (braidᵖ n₁ n₂) ξ) ≡ᴿ⟨ id ⟩ ξ
braid-braidᴿ n₁ n₂ ξ = ≡ᴿ-cong (λ _ → refl)
  (≡ᴿ-trans (relabel-∘ (braidᵖ n₁ n₂) (braidᵖ n₂ n₁) ξ)
  (≡ᴿ-trans (relabel-cong {σ = braidᵖ n₁ n₂ ∘ₚ braidᵖ n₂ n₁} {τ = id}
                          (braid-involutive n₁ n₂) ξ)
            (relabel-id ξ)))

braid-braid-≋ : ∀ n₁ n₂ (ξ : PathSum (n₁ ℕ+ n₂) k m) →
                relabel (braidᵖ n₂ n₁) (relabel (braidᵖ n₁ n₂) ξ) ≋ ξ
braid-braid-≋ n₁ n₂ ξ =
  ≡ᴿ⇒≋ {ξ = relabel (braidᵖ n₂ n₁) (relabel (braidᵖ n₁ n₂) ξ)} {π = id}
       {ζ = ξ} (braid-braidᴿ n₁ n₂ ξ)

-- The hexagon: relabelling along either side of it.

hexagonᴿ : ∀ a b c (ξ : PathSum ((a ℕ+ b) ℕ+ c) k m) →
           relabel (assocᵖ b c a)
             (relabel (braidᵖ a (b ℕ+ c)) (relabel (assocᵖ a b c) ξ))
           ≡ᴿ⟨ id ⟩
           relabel (id {b} ⊕ᵖ braidᵖ a c)
             (relabel (assocᵖ b a c) (relabel (braidᵖ a b ⊕ᵖ id {c}) ξ))
hexagonᴿ a b c ξ = ≡ᴿ-cong (λ _ → refl)
  (≡ᴿ-trans (relabel³ (assocᵖ a b c) (braidᵖ a (b ℕ+ c)) (assocᵖ b c a) ξ)
  (≡ᴿ-trans (relabel-cong
              {σ = (assocᵖ a b c ∘ₚ braidᵖ a (b ℕ+ c)) ∘ₚ assocᵖ b c a}
              {τ = ((braidᵖ a b ⊕ᵖ id {c}) ∘ₚ assocᵖ b a c) ∘ₚ
                   (id {b} ⊕ᵖ braidᵖ a c)}
              (hexagon a b c) ξ)
            (≡ᴿ-sym (relabel³ (braidᵖ a b ⊕ᵖ id {c}) (assocᵖ b a c)
                              (id {b} ⊕ᵖ braidᵖ a c) ξ))))

hexagon-≋ : ∀ a b c (ξ : PathSum ((a ℕ+ b) ℕ+ c) k m) →
            relabel (assocᵖ b c a)
              (relabel (braidᵖ a (b ℕ+ c)) (relabel (assocᵖ a b c) ξ)) ≋
            relabel (id {b} ⊕ᵖ braidᵖ a c)
              (relabel (assocᵖ b a c) (relabel (braidᵖ a b ⊕ᵖ id {c}) ξ))
hexagon-≋ a b c ξ =
  ≡ᴿ⇒≋ {ξ = relabel (assocᵖ b c a)
               (relabel (braidᵖ a (b ℕ+ c)) (relabel (assocᵖ a b c) ξ))}
       {π = id}
       {ζ = relabel (id {b} ⊕ᵖ braidᵖ a c)
              (relabel (assocᵖ b a c) (relabel (braidᵖ a b ⊕ᵖ id {c}) ξ))}
       (hexagonᴿ a b c ξ)

-- The pentagon and the triangle.

pentagonᴿ : ∀ a b c d (ξ : PathSum (((a ℕ+ b) ℕ+ c) ℕ+ d) k m) →
            relabel (assocᵖ a b (c ℕ+ d)) (relabel (assocᵖ (a ℕ+ b) c d) ξ)
            ≡ᴿ⟨ id ⟩
            relabel (id {a} ⊕ᵖ assocᵖ b c d)
              (relabel (assocᵖ a (b ℕ+ c) d)
                (relabel (assocᵖ a b c ⊕ᵖ id {d}) ξ))
pentagonᴿ a b c d ξ = ≡ᴿ-cong (λ _ → refl)
  (≡ᴿ-trans (relabel² (assocᵖ (a ℕ+ b) c d) (assocᵖ a b (c ℕ+ d)) ξ)
  (≡ᴿ-trans (relabel-cong
              {σ = assocᵖ (a ℕ+ b) c d ∘ₚ assocᵖ a b (c ℕ+ d)}
              {τ = ((assocᵖ a b c ⊕ᵖ id {d}) ∘ₚ assocᵖ a (b ℕ+ c) d) ∘ₚ
                   (id {a} ⊕ᵖ assocᵖ b c d)}
              (pentagon a b c d) ξ)
            (≡ᴿ-sym (relabel³ (assocᵖ a b c ⊕ᵖ id {d}) (assocᵖ a (b ℕ+ c) d)
                              (id {a} ⊕ᵖ assocᵖ b c d) ξ))))

triangleᴿ : ∀ a b (ξ : PathSum ((a ℕ+ 0) ℕ+ b) k m) →
            relabel (id {a} ⊕ᵖ id {b}) (relabel (assocᵖ a 0 b) ξ) ≡ᴿ⟨ id ⟩
            relabel (unitʳᵖ a ⊕ᵖ id {b}) ξ
triangleᴿ a b ξ = ≡ᴿ-cong (λ _ → refl)
  (≡ᴿ-trans (relabel² (assocᵖ a 0 b) (id {a} ⊕ᵖ id {b}) ξ)
            (relabel-cong {σ = assocᵖ a 0 b ∘ₚ (id {a} ⊕ᵖ id {b})}
                          {τ = unitʳᵖ a ⊕ᵖ id {b}}
                          (triangle a b) ξ))


------------------------------------------------------------------------
-- Sequential composition, along any path

-- A path of ξ′ ∘ᴾ ξ is a path of ξ (its first block) followed by one of
-- ξ′ (its second); PathSum.Compose.Properties reads the composite on
-- paths written as concatenations, and these read it on any.

eval-∘-blocks : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x : Assign n)
                (Y : Assign (m ℕ+ m′)) →
                eval (phase (ξ′ ∘ᴾ ξ)) x Y ≡
                eval (phase ξ) x (takeᵃ m′ Y) +
                eval (phase ξ′) (outBit ξ x (takeᵃ m′ Y)) (dropᵃ m Y)
eval-∘-blocks {m′ = m′} {m = m} ξ′ ξ x Y =
  trans (eval-cong (phase (ξ′ ∘ᴾ ξ)) {x} {x} {Y}
                   {_++ᵃ_ {m} {m′} (takeᵃ m′ Y) (dropᵃ m Y)}
                   (λ _ → refl) (λ j → sym (++ᵃ-split m m′ Y j)))
        (eval-∘ ξ′ ξ x (takeᵃ m′ Y) (dropᵃ m Y))

eval-out-∘-blocks : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
                    (x : Assign n) (Y : Assign (m ℕ+ m′)) (w : Fin n) →
                    eval (out (ξ′ ∘ᴾ ξ) w) x Y ≡
                    eval (out ξ′ w) (outBit ξ x (takeᵃ m′ Y)) (dropᵃ m Y)
eval-out-∘-blocks {m′ = m′} {m = m} ξ′ ξ x Y w =
  trans (eval-cong (out (ξ′ ∘ᴾ ξ) w) {x} {x} {Y}
                   {_++ᵃ_ {m} {m′} (takeᵃ m′ Y) (dropᵃ m Y)}
                   (λ _ → refl) (λ j → sym (++ᵃ-split m m′ Y j)))
        (eval-bind (out ξ′ w) (feed ξ) x
                   (_++ᵃ_ {m} {m′} (takeᵃ m′ Y) (dropᵃ m Y))
                   (outBit ξ x (takeᵃ m′ Y)) (dropᵃ m Y)
                   (eval-feed ξ x (takeᵃ m′ Y) (dropᵃ m Y)))

outBit-∘-blocks : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
                  (x : Assign n) (Y : Assign (m ℕ+ m′)) (w : Fin n) →
                  outBit (ξ′ ∘ᴾ ξ) x Y w ≡
                  outBit ξ′ (outBit ξ x (takeᵃ m′ Y)) (dropᵃ m Y) w
outBit-∘-blocks ξ′ ξ x Y w = cong odd (eval-out-∘-blocks ξ′ ξ x Y w)

private
  outBit-≗ : (ξ : PathSum n k m) {x x′ : Assign n} {y y′ : Assign m} →
             (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
             ∀ w → outBit ξ x y w ≡ outBit ξ x′ y′ w
  outBit-≗ ξ hx hy w = cong odd (eval-cong (out ξ w) hx hy)

  middle4 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  middle4 a b c d =
    trans (+-assoc a b (c + d))
    (trans (cong (a +_) (trans (sym (+-assoc b c d))
                        (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
           (sym (+-assoc a c (b + d))))

  middle4ℕ : ∀ a b c d → (a ℕ+ b) ℕ+ (c ℕ+ d) ≡ (a ℕ+ c) ℕ+ (b ℕ+ d)
  middle4ℕ a b c d =
    trans (ℕ.+-assoc a b (c ℕ+ d))
    (trans (cong (a ℕ+_) (trans (sym (ℕ.+-assoc b c d))
                         (trans (cong (_ℕ+ d) (ℕ.+-comm b c))
                                (ℕ.+-assoc c b d))))
           (sym (ℕ.+-assoc a c (b ℕ+ d))))


------------------------------------------------------------------------
-- Bifunctoriality

-- The interchange law, PathSum.Compose.Tensor's ⊗-interchange, as an
-- equality up to renaming.  On the left the path variables are those
-- of ζ₁ and ζ₂, then those of ξ₁ and ξ₂; on the right those of ζ₁ and
-- ξ₁, then those of ζ₂ and ξ₂: the renaming exchanges the two middle
-- blocks.  The phases are P_ζ₁ + P_ζ₂ + P_ξ₁ + P_ξ₂ on both sides, and
-- the outputs ξ₁'s and ξ₂'s at the bits ζ₁ and ζ₂ leave.

⊗-interchangeᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                 (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂) →
                 ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) ≡ᴿ⟨ shuffleᵖ l₁ l₂ m₁ m₂ ⟩
                 ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂))
⊗-interchangeᴿ {n₁ = n₁} {k₁ = k₁} {m₁ = m₁} {n₂ = n₂} {k₂ = k₂} {m₂ = m₂}
               {j₁ = j₁} {l₁ = l₁} {j₂ = j₂} {l₂ = l₂} ξ₁ ξ₂ ζ₁ ζ₂ =
  ≡ᴿ-by-values L R (shuffleᵖ l₁ l₂ m₁ m₂) (middle4ℕ j₁ j₂ k₁ k₂) ph ou
  where
  L = (ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)
  R = (ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂)

  -- The blocks of a path Y′ of the right-hand side, and of the
  -- corresponding path Y of the left-hand side.
  module At (x : Assign (n₁ ℕ+ n₂))
            (Y′ : Assign ((l₁ ℕ+ m₁) ℕ+ (l₂ ℕ+ m₂))) where
    Y : Assign ((l₁ ℕ+ l₂) ℕ+ (m₁ ℕ+ m₂))
    Y j = Y′ (shuffleᶠ l₁ l₂ m₁ m₂ j)

    Lp : Assign (l₁ ℕ+ l₂)
    Lp = takeᵃ (m₁ ℕ+ m₂) Y

    Rp : Assign (m₁ ℕ+ m₂)
    Rp = dropᵃ (l₁ ℕ+ l₂) Y

    A : Assign (l₁ ℕ+ m₁)
    A = takeᵃ (l₂ ℕ+ m₂) Y′

    B : Assign (l₂ ℕ+ m₂)
    B = dropᵃ (l₁ ℕ+ m₁) Y′

    x₁ : Assign n₁
    x₁ = takeᵃ n₂ x

    x₂ : Assign n₂
    x₂ = dropᵃ n₁ x

    F : Assign (n₁ ℕ+ n₂)
    F = outBit (ζ₁ ⊗ᴾ ζ₂) x Lp

    b1 : ∀ i → takeᵃ l₂ Lp i ≡ takeᵃ m₁ A i
    b1 i = cong Y′ (shuffle-1 l₁ l₂ m₁ m₂ i)

    b2 : ∀ j → dropᵃ l₁ Lp j ≡ takeᵃ m₂ B j
    b2 j = cong Y′ (shuffle-2 l₁ l₂ m₁ m₂ j)

    b3 : ∀ j → takeᵃ m₂ Rp j ≡ dropᵃ l₁ A j
    b3 j = cong Y′ (shuffle-3 l₁ l₂ m₁ m₂ j)

    b4 : ∀ j → dropᵃ m₁ Rp j ≡ dropᵃ l₂ B j
    b4 j = cong Y′ (shuffle-4 l₁ l₂ m₁ m₂ j)

    f1 : ∀ i → takeᵃ n₂ F i ≡ outBit ζ₁ x₁ (takeᵃ m₁ A) i
    f1 i = trans (outBit-⊗ˡ ζ₁ ζ₂ x Lp i) (outBit-≗ ζ₁ (λ _ → refl) b1 i)

    f2 : ∀ j → dropᵃ n₁ F j ≡ outBit ζ₂ x₂ (takeᵃ m₂ B) j
    f2 j = trans (outBit-⊗ʳ ζ₁ ζ₂ x Lp j) (outBit-≗ ζ₂ (λ _ → refl) b2 j)

  ph : ∀ (x : Assign (n₁ ℕ+ n₂)) (Y′ : Assign ((l₁ ℕ+ m₁) ℕ+ (l₂ ℕ+ m₂))) →
       eval (phase L) x (λ j → Y′ (shuffleᵖ l₁ l₂ m₁ m₂ ⟨$⟩ʳ j)) ≡
       eval (phase R) x Y′
  ph x Y′ =
    trans (eval-∘-blocks (ξ₁ ⊗ᴾ ξ₂) (ζ₁ ⊗ᴾ ζ₂) x Y)
    (trans (cong₂ _+_ (eval-⊗-blocks ζ₁ ζ₂ x Lp) (eval-⊗-blocks ξ₁ ξ₂ F Rp))
    (trans (cong₂ _+_ (cong₂ _+_ z₁ z₂) (cong₂ _+_ c₁ c₂))
    (trans (middle4 a b c d)
           (sym (trans (eval-⊗-blocks (ξ₁ ∘ᴾ ζ₁) (ξ₂ ∘ᴾ ζ₂) x Y′)
                       (cong₂ _+_ (eval-∘-blocks ξ₁ ζ₁ x₁ A)
                                  (eval-∘-blocks ξ₂ ζ₂ x₂ B)))))))
    where
    open At x Y′

    a b c d : ℤ
    a = eval (phase ζ₁) x₁ (takeᵃ m₁ A)
    b = eval (phase ζ₂) x₂ (takeᵃ m₂ B)
    c = eval (phase ξ₁) (outBit ζ₁ x₁ (takeᵃ m₁ A)) (dropᵃ l₁ A)
    d = eval (phase ξ₂) (outBit ζ₂ x₂ (takeᵃ m₂ B)) (dropᵃ l₂ B)

    z₁ : eval (phase ζ₁) x₁ (takeᵃ l₂ Lp) ≡ a
    z₁ = eval-cong (phase ζ₁) (λ _ → refl) b1

    z₂ : eval (phase ζ₂) x₂ (dropᵃ l₁ Lp) ≡ b
    z₂ = eval-cong (phase ζ₂) (λ _ → refl) b2

    c₁ : eval (phase ξ₁) (takeᵃ n₂ F) (takeᵃ m₂ Rp) ≡ c
    c₁ = eval-cong (phase ξ₁) f1 b3

    c₂ : eval (phase ξ₂) (dropᵃ n₁ F) (dropᵃ m₁ Rp) ≡ d
    c₂ = eval-cong (phase ξ₂) f2 b4

  ou : ∀ w (x : Assign (n₁ ℕ+ n₂))
       (Y′ : Assign ((l₁ ℕ+ m₁) ℕ+ (l₂ ℕ+ m₂))) →
       eval (out L w) x (λ j → Y′ (shuffleᵖ l₁ l₂ m₁ m₂ ⟨$⟩ʳ j)) ≡
       eval (out R w) x Y′
  ou w x Y′ = blocks n₁ n₂ {P} one two w
    where
    open At x Y′

    P : Fin (n₁ ℕ+ n₂) → Set
    P v = eval (out L v) x Y ≡ eval (out R v) x Y′

    one : ∀ i → P (i ↑ˡ n₂)
    one i =
      trans (eval-out-∘-blocks (ξ₁ ⊗ᴾ ξ₂) (ζ₁ ⊗ᴾ ζ₂) x Y (i ↑ˡ n₂))
      (trans (eval-out-⊗ˡ ξ₁ ξ₂ F Rp i)
      (trans (eval-cong (out ξ₁ i) f1 b3)
             (sym (trans (eval-out-⊗ˡ (ξ₁ ∘ᴾ ζ₁) (ξ₂ ∘ᴾ ζ₂) x Y′ i)
                         (eval-out-∘-blocks ξ₁ ζ₁ x₁ A i)))))

    two : ∀ j → P (n₁ ↑ʳ j)
    two j =
      trans (eval-out-∘-blocks (ξ₁ ⊗ᴾ ξ₂) (ζ₁ ⊗ᴾ ζ₂) x Y (n₁ ↑ʳ j))
      (trans (eval-out-⊗ʳ ξ₁ ξ₂ F Rp j)
      (trans (eval-cong (out ξ₂ j) f2 b4)
             (sym (trans (eval-out-⊗ʳ (ξ₁ ∘ᴾ ζ₁) (ξ₂ ∘ᴾ ζ₂) x Y′ j)
                         (eval-out-∘-blocks ξ₂ ζ₂ x₂ B j)))))

⊗-interchange-≋ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                  (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂) →
                  ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) ≋ ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂))
⊗-interchange-≋ {m₁ = m₁} {m₂ = m₂} {l₁ = l₁} {l₂ = l₂} ξ₁ ξ₂ ζ₁ ζ₂ =
  ≡ᴿ⇒≋ {ξ = (ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)} {π = shuffleᵖ l₁ l₂ m₁ m₂}
       {ζ = (ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂)} (⊗-interchangeᴿ ξ₁ ξ₂ ζ₁ ζ₂)


------------------------------------------------------------------------
-- The naturality of SWAP

-- PathSum.Compose.Swap's swap-natural, as an equality up to renaming:
-- the paths of ξ₁ and ξ₂ (and none of SWAP's) on the left, those of
-- ξ₂ and ξ₁ on the right, so the renaming exchanges the two blocks
-- after dropping SWAP's empty one.  The outputs agree modulo 2 only:
-- on the left SWAP's outputs, single variables, have the lifted
-- outputs of ξ₁ ⊗ ξ₂ substituted (bits), on the right ξ₂ ⊗ ξ₁'s
-- outputs are read at the exchanged inputs (any integers of the same
-- parity).

swap-naturalᴿ : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂) →
                (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) ≈ᴿ⟨ unitʳᵖ (m₁ ℕ+ m₂) ∘ₚ braidᵖ m₁ m₂ ⟩
                ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)
swap-naturalᴿ {n = n} {k₁ = k₁} {m₁ = m₁} {k₂ = k₂} {m₂ = m₂} ξ₁ ξ₂ =
  ≈ᴿ-by-values (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n) π
    (trans (ℕ.+-identityʳ (k₁ ℕ+ k₂)) (ℕ.+-comm k₁ k₂)) ph ob
  where
  π = unitʳᵖ (m₁ ℕ+ m₂) ∘ₚ braidᵖ m₁ m₂

  module At (x : Assign (n ℕ+ n)) (y : Assign (m₂ ℕ+ m₁)) where
    Y : Assign ((m₁ ℕ+ m₂) ℕ+ 0)
    Y j = y (π ⟨$⟩ʳ j)

    Z : Assign (m₁ ℕ+ m₂)
    Z = takeᵃ 0 Y

    S : Assign (n ℕ+ n)
    S = outBit (swapᴾ n) x (takeᵃ (m₂ ℕ+ m₁) y)

    z1 : ∀ i → takeᵃ m₂ Z i ≡ dropᵃ m₂ y i
    z1 i = cong y (trans (cong (braidᶠ m₁ m₂) (unitʳ-1 (m₁ ℕ+ m₂) (i ↑ˡ m₂)))
                         (braid-1 m₁ m₂ i))

    z2 : ∀ j → dropᵃ m₁ Z j ≡ takeᵃ m₁ y j
    z2 j = cong y (trans (cong (braidᶠ m₁ m₂) (unitʳ-1 (m₁ ℕ+ m₂) (m₁ ↑ʳ j)))
                         (braid-2 m₁ m₂ j))

    s1 : ∀ i → takeᵃ n S i ≡ dropᵃ n x i
    s1 i = trans (outBit-swap n x (takeᵃ (m₂ ℕ+ m₁) y) (i ↑ˡ n))
                 (cong x (swapᶠ-↑ˡ n i))

    s2 : ∀ j → dropᵃ n S j ≡ takeᵃ n x j
    s2 j = trans (outBit-swap n x (takeᵃ (m₂ ℕ+ m₁) y) (n ↑ʳ j))
                 (cong x (swapᶠ-↑ʳ n j))

  ph : ∀ (x : Assign (n ℕ+ n)) (y : Assign (m₂ ℕ+ m₁)) →
       eval (phase (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂))) x (λ j → y (π ⟨$⟩ʳ j)) ≡
       eval (phase ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)) x y
  ph x y =
    trans (eval-∘-blocks (swapᴾ n) (ξ₁ ⊗ᴾ ξ₂) x Y)
    (trans (cong₂ _+_ (eval-⊗-blocks ξ₁ ξ₂ x Z)
                      (eval-0ᴾ-val (outBit (ξ₁ ⊗ᴾ ξ₂) x Z)
                                   (dropᵃ (m₁ ℕ+ m₂) Y)))
    (trans (+-identityʳ (p₁ + p₂))
    (trans (cong₂ _+_ (eval-cong (phase ξ₁) (λ _ → refl) z1)
                      (eval-cong (phase ξ₂) (λ _ → refl) z2))
    (trans (+-comm q₁ q₂)
    (sym (trans (eval-∘-blocks (ξ₂ ⊗ᴾ ξ₁) (swapᴾ n) x y)
         (trans (cong₂ _+_ (eval-0ᴾ-val x (takeᵃ {n₁ = 0} (m₂ ℕ+ m₁) y))
                           (eval-⊗-blocks ξ₂ ξ₁ S (dropᵃ 0 y)))
         (trans (+-identityˡ (r₂ + r₁))
                (cong₂ _+_ (eval-cong (phase ξ₂) s1 (λ _ → refl))
                           (eval-cong (phase ξ₁) s2 (λ _ → refl)))))))))))
    where
    open At x y

    p₁ p₂ q₁ q₂ r₁ r₂ : ℤ
    p₁ = eval (phase ξ₁) (takeᵃ n x) (takeᵃ m₂ Z)
    p₂ = eval (phase ξ₂) (dropᵃ n x) (dropᵃ m₁ Z)
    q₁ = eval (phase ξ₁) (takeᵃ n x) (dropᵃ m₂ y)
    q₂ = eval (phase ξ₂) (dropᵃ n x) (takeᵃ m₁ y)
    r₁ = eval (phase ξ₁) (dropᵃ n S) (dropᵃ m₂ (dropᵃ 0 y))
    r₂ = eval (phase ξ₂) (takeᵃ n S) (takeᵃ m₁ (dropᵃ 0 y))

  ob : ∀ w (x : Assign (n ℕ+ n)) (y : Assign (m₂ ℕ+ m₁)) →
       outBit (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) x (λ j → y (π ⟨$⟩ʳ j)) w ≡
       outBit ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n) x y w
  ob w x y = blocks n n {P} one two w
    where
    open At x y

    P : Fin (n ℕ+ n) → Set
    P v = outBit (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) x Y v ≡
          outBit ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n) x y v

    left : ∀ v → outBit (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) x Y v ≡
                 outBit (ξ₁ ⊗ᴾ ξ₂) x Z (swapᶠ n v)
    left v = trans (outBit-∘-blocks (swapᴾ n) (ξ₁ ⊗ᴾ ξ₂) x Y v)
                   (outBit-swap n (outBit (ξ₁ ⊗ᴾ ξ₂) x Z)
                                (dropᵃ (m₁ ℕ+ m₂) Y) v)

    one : ∀ i → P (i ↑ˡ n)
    one i =
      trans (left (i ↑ˡ n))
      (trans (cong (outBit (ξ₁ ⊗ᴾ ξ₂) x Z) (swapᶠ-↑ˡ n i))
      (trans (outBit-⊗ʳ ξ₁ ξ₂ x Z i)
      (trans (outBit-≗ ξ₂ (λ i′ → sym (s1 i′)) z2 i)
             (sym (trans (outBit-∘-blocks (ξ₂ ⊗ᴾ ξ₁) (swapᴾ n) x y (i ↑ˡ n))
                         (outBit-⊗ˡ ξ₂ ξ₁ S (dropᵃ 0 y) i))))))

    two : ∀ j → P (n ↑ʳ j)
    two j =
      trans (left (n ↑ʳ j))
      (trans (cong (outBit (ξ₁ ⊗ᴾ ξ₂) x Z) (swapᶠ-↑ʳ n j))
      (trans (outBit-⊗ˡ ξ₁ ξ₂ x Z j)
      (trans (outBit-≗ ξ₁ (λ i → sym (s2 i)) z1 j)
             (sym (trans (outBit-∘-blocks (ξ₂ ⊗ᴾ ξ₁) (swapᴾ n) x y (n ↑ʳ j))
                         (outBit-⊗ʳ ξ₂ ξ₁ S (dropᵃ 0 y) j))))))

swap-natural-≋ : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂) →
                 (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) ≋ ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)
swap-natural-≋ {n = n} {m₁ = m₁} {m₂ = m₂} ξ₁ ξ₂ =
  ≈ᴿ⇒≋ {ξ = swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)}
       {π = unitʳᵖ (m₁ ℕ+ m₂) ∘ₚ braidᵖ m₁ m₂}
       {ζ = (ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n} (swap-naturalᴿ ξ₁ ξ₂)


------------------------------------------------------------------------
-- The category laws of ∘ᴾ

-- PathSum.Compose.Laws proves these up to ≋.  On the right the
-- identity contributes no path variable and its outputs are the
-- inputs, so ξ ∘ idPS has ξ's coefficients exactly.

∘ᴾ-identityʳᴿ : (ξ : PathSum n k m) → (ξ ∘ᴾ idPS) ≡ᴿ⟨ id ⟩ ξ
∘ᴾ-identityʳᴿ {n = n} {m = m} ξ = ≡ᴿ-by-values (ξ ∘ᴾ idPS) ξ id refl ph ou
  where
  ids : ∀ (x : Assign n) (y : Assign m) i →
        outBit (idPS {n}) x (takeᵃ m y) i ≡ x i
  ids x y i = outBit-μ idPS x (takeᵃ m y) i x[ i ] refl

  ph : ∀ (x : Assign n) (y : Assign m) →
       eval (phase (ξ ∘ᴾ idPS)) x (λ j → y (id ⟨$⟩ʳ j)) ≡ eval (phase ξ) x y
  ph x y = trans (eval-∘-blocks ξ idPS x y)
    (trans (cong₂ _+_ (eval-0ᴾ-val x (takeᵃ m y))
                      (eval-cong (phase ξ) (ids x y) (λ _ → refl)))
           (+-identityˡ (eval (phase ξ) x y)))

  ou : ∀ w (x : Assign n) (y : Assign m) →
       eval (out (ξ ∘ᴾ idPS) w) x (λ j → y (id ⟨$⟩ʳ j)) ≡ eval (out ξ w) x y
  ou w x y = trans (eval-out-∘-blocks ξ idPS x y w)
                   (eval-cong (out ξ w) (ids x y) (λ _ → refl))

-- On the left the identity's outputs, single variables, have ξ's lifted
-- outputs substituted: bits, congruent to ξ's outputs modulo 2.

∘ᴾ-identityˡᴿ : (ξ : PathSum n k m) → (idPS ∘ᴾ ξ) ≈ᴿ⟨ unitʳᵖ m ⟩ ξ
∘ᴾ-identityˡᴿ {n = n} {k = k} {m = m} ξ =
  ≈ᴿ-by-values (idPS ∘ᴾ ξ) ξ (unitʳᵖ m) (ℕ.+-identityʳ k) ph ob
  where
  back : ∀ (y : Assign m) j → takeᵃ 0 (λ j′ → y (unitʳᵖ m ⟨$⟩ʳ j′)) j ≡ y j
  back y j = cong y (unitʳ-1 m j)

  ph : ∀ (x : Assign n) (y : Assign m) →
       eval (phase (idPS ∘ᴾ ξ)) x (λ j → y (unitʳᵖ m ⟨$⟩ʳ j)) ≡
       eval (phase ξ) x y
  ph x y =
    trans (eval-∘-blocks idPS ξ x Y)
    (trans (cong₂ _+_ (eval-cong (phase ξ) (λ _ → refl) (back y))
                      (eval-0ᴾ-val (outBit ξ x (takeᵃ 0 Y)) (dropᵃ m Y)))
           (+-identityʳ (eval (phase ξ) x y)))
    where
    Y : Assign (m ℕ+ 0)
    Y j = y (unitʳᵖ m ⟨$⟩ʳ j)

  ob : ∀ w (x : Assign n) (y : Assign m) →
       outBit (idPS ∘ᴾ ξ) x (λ j → y (unitʳᵖ m ⟨$⟩ʳ j)) w ≡ outBit ξ x y w
  ob w x y =
    trans (outBit-∘-blocks idPS ξ x Y w)
    (trans (outBit-μ idPS (outBit ξ x (takeᵃ 0 Y)) (dropᵃ m Y) w x[ w ] refl)
           (outBit-≗ ξ (λ _ → refl) (back y) w))
    where
    Y : Assign (m ℕ+ 0)
    Y j = y (unitʳᵖ m ⟨$⟩ʳ j)

-- Associativity: the path variables of ξ, ξ′ and ξ″ in the same
-- order, bracketed differently -- the cast along +-assoc.

∘ᴾ-assocᴿ : (ξ″ : PathSum n k″ m″) (ξ′ : PathSum n k′ m′)
            (ξ : PathSum n k m) →
            ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) ≡ᴿ⟨ flip (assocᵖ m m′ m″) ⟩ (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ))
∘ᴾ-assocᴿ {n = n} {k″ = k″} {m″ = m″} {k′ = k′} {m′ = m′} {k = k} {m = m}
          ξ″ ξ′ ξ =
  ≡ᴿ-by-values ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ)) (flip (assocᵖ m m′ m″))
               (sym (ℕ.+-assoc k k′ k″)) ph ou
  where
  module At (x : Assign n) (Y′ : Assign ((m ℕ+ m′) ℕ+ m″)) where
    Y : Assign (m ℕ+ (m′ ℕ+ m″))
    Y j = Y′ (assocᵖ m m′ m″ ⟨$⟩ˡ j)

    f : Assign n
    f = outBit ξ x (takeᵃ (m′ ℕ+ m″) Y)

    b1 : ∀ i → takeᵃ (m′ ℕ+ m″) Y i ≡ takeᵃ m′ (takeᵃ m″ Y′) i
    b1 i = cong Y′ (assoc⁻¹-1 m m′ m″ i)

    b2 : ∀ j → takeᵃ m″ (dropᵃ m Y) j ≡ dropᵃ m (takeᵃ m″ Y′) j
    b2 j = cong Y′ (assoc⁻¹-2 m m′ m″ j)

    b3 : ∀ l → dropᵃ m′ (dropᵃ m Y) l ≡ dropᵃ (m ℕ+ m′) Y′ l
    b3 l = cong Y′ (assoc⁻¹-3 m m′ m″ l)

    -- The bits ξ′ leaves, along the two bracketings.
    g : ∀ v → outBit ξ′ f (takeᵃ m″ (dropᵃ m Y)) v ≡
              outBit (ξ′ ∘ᴾ ξ) x (takeᵃ m″ Y′) v
    g v = trans (outBit-≗ ξ′ (outBit-≗ ξ (λ _ → refl) b1) b2 v)
                (sym (outBit-∘-blocks ξ′ ξ x (takeᵃ m″ Y′) v))

  ph : ∀ (x : Assign n) (Y′ : Assign ((m ℕ+ m′) ℕ+ m″)) →
       eval (phase ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ)) x
            (λ j → Y′ (flip (assocᵖ m m′ m″) ⟨$⟩ʳ j)) ≡
       eval (phase (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ))) x Y′
  ph x Y′ =
    trans (eval-∘-blocks (ξ″ ∘ᴾ ξ′) ξ x Y)
    (trans (cong (p +_) (eval-∘-blocks ξ″ ξ′ f (dropᵃ m Y)))
    (trans (cong₂ _+_ e₀ (cong₂ _+_ e₁ e₂))
    (trans (sym (+-assoc a b c))
           (sym (trans (eval-∘-blocks ξ″ (ξ′ ∘ᴾ ξ) x Y′)
                       (cong (_+ c) (eval-∘-blocks ξ′ ξ x (takeᵃ m″ Y′))))))))
    where
    open At x Y′

    p a b c : ℤ
    p = eval (phase ξ) x (takeᵃ (m′ ℕ+ m″) Y)
    a = eval (phase ξ) x (takeᵃ m′ (takeᵃ m″ Y′))
    b = eval (phase ξ′) (outBit ξ x (takeᵃ m′ (takeᵃ m″ Y′)))
                        (dropᵃ m (takeᵃ m″ Y′))
    c = eval (phase ξ″) (outBit (ξ′ ∘ᴾ ξ) x (takeᵃ m″ Y′))
                        (dropᵃ (m ℕ+ m′) Y′)

    e₀ : p ≡ a
    e₀ = eval-cong (phase ξ) (λ _ → refl) b1

    e₁ : eval (phase ξ′) f (takeᵃ m″ (dropᵃ m Y)) ≡ b
    e₁ = eval-cong (phase ξ′) (outBit-≗ ξ (λ _ → refl) b1) b2

    e₂ : eval (phase ξ″) (outBit ξ′ f (takeᵃ m″ (dropᵃ m Y)))
                         (dropᵃ m′ (dropᵃ m Y)) ≡ c
    e₂ = eval-cong (phase ξ″) g b3

  ou : ∀ w (x : Assign n) (Y′ : Assign ((m ℕ+ m′) ℕ+ m″)) →
       eval (out ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) w) x
            (λ j → Y′ (flip (assocᵖ m m′ m″) ⟨$⟩ʳ j)) ≡
       eval (out (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ)) w) x Y′
  ou w x Y′ =
    trans (eval-out-∘-blocks (ξ″ ∘ᴾ ξ′) ξ x Y w)
    (trans (eval-out-∘-blocks ξ″ ξ′ f (dropᵃ m Y) w)
    (trans (eval-cong (out ξ″ w) g b3)
           (sym (eval-out-∘-blocks ξ″ (ξ′ ∘ᴾ ξ) x Y′ w))))
    where
    open At x Y′

∘ᴾ-assoc-≋ : (ξ″ : PathSum n k″ m″) (ξ′ : PathSum n k′ m′)
             (ξ : PathSum n k m) →
             ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) ≋ (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ))
∘ᴾ-assoc-≋ {m″ = m″} {m′ = m′} {m = m} ξ″ ξ′ ξ =
  ≡ᴿ⇒≋ {ξ = (ξ″ ∘ᴾ ξ′) ∘ᴾ ξ} {π = flip (assocᵖ m m′ m″)}
       {ζ = ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ)} (∘ᴾ-assocᴿ ξ″ ξ′ ξ)
