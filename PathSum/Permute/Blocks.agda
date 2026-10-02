------------------------------------------------------------------------
-- Presentations of groups
--
-- The structure maps of the monoidal structure on wires, and their
-- coherence (Amy, QPL 2018, remark 2.8)
--
-- Path-sums on n wires compose in parallel, ⊗ᴾ putting a path-sum on
-- n₁ wires above one on n₂ (PathSum.Compose).  The structure maps of
-- the symmetric monoidal structure are bijections between the wires
-- of the two sides, and they act on path-sums by relabelling
-- (PathSum.Permute.relabel):
--
--    assocᵖ a b c : (a + b) + c ↔ a + (b + c)   the cast along +-assoc,
--    unitʳᵖ a     : a + 0 ↔ a                    the cast along
--                                                +-identityʳ (the left
--                                                unit 0 + a is a on
--                                                the nose),
--    braidᵖ a b   : a + b ↔ b + a                the exchange of the two
--                                                blocks,
--
-- with σ ⊕ᵖ τ, the two bijections side by side, for the maps of the
-- coherence diagrams, and shuffleᵖ a b c d : (a + b) + (c + d) ↔
-- (a + c) + (b + d), which exchanges the two middle blocks -- the
-- renaming of the path variables in the interchange law.  The block
-- lemmas say what each does to an index written as i ↑ˡ _ or _ ↑ʳ j.
--
-- The coherence of the structure is a property of these bijections
-- alone, proved here pointwise: the braiding is its own inverse
-- (braid-involutive), the hexagon commutes (hexagon), and so do the
-- pentagon and the triangle (pentagon, triangle: every map in them is
-- a cast or built from casts, so they keep the number toℕ of every
-- index).  PathSum.Compose.Monoidal transports them to path-sums.
-- Nothing here depends on M or mentions a path-sum.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Permute.Blocks where

open import Data.Fin.Base using (Fin; zero; suc; toℕ; cast; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Permutation using
  (Permutation; permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ; inverseʳ; cast-id)
open import Data.Fin.Properties using
  (toℕ-injective; toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Sum.Base using ([_,_]′)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

private
  variable
    a a′ a″ b b′ b″ c d : ℕ


------------------------------------------------------------------------
-- Blocks

-- Every index of a + b is in one of the two blocks.

blocks : ∀ a b {P : Fin (a + b) → Set} →
         (∀ i → P (i ↑ˡ b)) → (∀ j → P (a ↑ʳ j)) → ∀ w → P w
blocks zero    b     l r w       = r w
blocks (suc a) b     l r zero    = l zero
blocks (suc a) b {P} l r (suc w) =
  blocks a b {λ w′ → P (suc w′)} (λ i → l (suc i)) r w

-- A cast is determined by toℕ.

cast-≡ : ∀ {m n} .(e : m ≡ n) (w : Fin m) (w′ : Fin n) → toℕ w ≡ toℕ w′ →
         cast e w ≡ w′
cast-≡ e w w′ h = toℕ-injective (trans (toℕ-cast e w) h)


------------------------------------------------------------------------
-- The associator and the right unitor

assocᵖ : ∀ a b c → Permutation ((a + b) + c) (a + (b + c))
assocᵖ a b c = cast-id (ℕ.+-assoc a b c)

unitʳᵖ : ∀ a → Permutation (a + 0) a
unitʳᵖ a = cast-id (ℕ.+-identityʳ a)

-- Where the associator and its inverse send the three blocks.

assoc-1 : ∀ a b c (i : Fin a) →
          assocᵖ a b c ⟨$⟩ʳ ((i ↑ˡ b) ↑ˡ c) ≡ i ↑ˡ (b + c)
assoc-1 a b c i = cast-≡ _ _ _
  (trans (toℕ-↑ˡ (i ↑ˡ b) c) (trans (toℕ-↑ˡ i b) (sym (toℕ-↑ˡ i (b + c)))))

assoc-2 : ∀ a b c (j : Fin b) →
          assocᵖ a b c ⟨$⟩ʳ ((a ↑ʳ j) ↑ˡ c) ≡ a ↑ʳ (j ↑ˡ c)
assoc-2 a b c j = cast-≡ _ _ _
  (trans (toℕ-↑ˡ (a ↑ʳ j) c)
  (trans (toℕ-↑ʳ a j)
         (sym (trans (toℕ-↑ʳ a (j ↑ˡ c)) (cong (a +_) (toℕ-↑ˡ j c))))))

assoc-3 : ∀ a b c (k : Fin c) →
          assocᵖ a b c ⟨$⟩ʳ ((a + b) ↑ʳ k) ≡ a ↑ʳ (b ↑ʳ k)
assoc-3 a b c k = cast-≡ _ _ _
  (trans (toℕ-↑ʳ (a + b) k)
  (trans (ℕ.+-assoc a b (toℕ k))
         (sym (trans (toℕ-↑ʳ a (b ↑ʳ k)) (cong (a +_) (toℕ-↑ʳ b k))))))

assoc⁻¹-1 : ∀ a b c (i : Fin a) →
            assocᵖ a b c ⟨$⟩ˡ (i ↑ˡ (b + c)) ≡ (i ↑ˡ b) ↑ˡ c
assoc⁻¹-1 a b c i = cast-≡ _ _ _
  (trans (toℕ-↑ˡ i (b + c)) (sym (trans (toℕ-↑ˡ (i ↑ˡ b) c) (toℕ-↑ˡ i b))))

assoc⁻¹-2 : ∀ a b c (j : Fin b) →
            assocᵖ a b c ⟨$⟩ˡ (a ↑ʳ (j ↑ˡ c)) ≡ (a ↑ʳ j) ↑ˡ c
assoc⁻¹-2 a b c j = cast-≡ _ _ _
  (trans (toℕ-↑ʳ a (j ↑ˡ c))
  (trans (cong (a +_) (toℕ-↑ˡ j c))
         (sym (trans (toℕ-↑ˡ (a ↑ʳ j) c) (toℕ-↑ʳ a j)))))

assoc⁻¹-3 : ∀ a b c (k : Fin c) →
            assocᵖ a b c ⟨$⟩ˡ (a ↑ʳ (b ↑ʳ k)) ≡ (a + b) ↑ʳ k
assoc⁻¹-3 a b c k = cast-≡ _ _ _
  (trans (toℕ-↑ʳ a (b ↑ʳ k))
  (trans (cong (a +_) (toℕ-↑ʳ b k))
  (trans (sym (ℕ.+-assoc a b (toℕ k))) (sym (toℕ-↑ʳ (a + b) k)))))

-- The right unitor and its inverse.

unitʳ-1 : ∀ a (i : Fin a) → unitʳᵖ a ⟨$⟩ʳ (i ↑ˡ 0) ≡ i
unitʳ-1 a i = cast-≡ _ _ _ (toℕ-↑ˡ i 0)

unitʳ⁻¹-1 : ∀ a (i : Fin a) → unitʳᵖ a ⟨$⟩ˡ i ≡ i ↑ˡ 0
unitʳ⁻¹-1 a i = cast-≡ _ _ _ (sym (toℕ-↑ˡ i 0))


------------------------------------------------------------------------
-- The braiding

braidᶠ : ∀ a b → Fin (a + b) → Fin (b + a)
braidᶠ a b w = [ (λ i → b ↑ʳ i) , (λ j → j ↑ˡ a) ]′ (splitAt a w)

braid-1 : ∀ a b (i : Fin a) → braidᶠ a b (i ↑ˡ b) ≡ b ↑ʳ i
braid-1 a b i =
  cong [ (λ i′ → b ↑ʳ i′) , (λ j → j ↑ˡ a) ]′ (splitAt-↑ˡ a i b)

braid-2 : ∀ a b (j : Fin b) → braidᶠ a b (a ↑ʳ j) ≡ j ↑ˡ a
braid-2 a b j =
  cong [ (λ i → b ↑ʳ i) , (λ j′ → j′ ↑ˡ a) ]′ (splitAt-↑ʳ a b j)

-- Exchanging the blocks twice changes nothing.

braid-involutive : ∀ a b (w : Fin (a + b)) → braidᶠ b a (braidᶠ a b w) ≡ w
braid-involutive a b = blocks a b
  (λ i → trans (cong (braidᶠ b a) (braid-1 a b i)) (braid-2 b a i))
  (λ j → trans (cong (braidᶠ b a) (braid-2 a b j)) (braid-1 b a j))

braidᵖ : ∀ a b → Permutation (a + b) (b + a)
braidᵖ a b = permutation (braidᶠ a b) (braidᶠ b a)
                         (braid-involutive b a) (braid-involutive a b)


------------------------------------------------------------------------
-- Two bijections side by side

infixr 6 _⊕ᶠ_ _⊕ᵖ_

_⊕ᶠ_ : (Fin a → Fin a′) → (Fin b → Fin b′) → Fin (a + b) → Fin (a′ + b′)
_⊕ᶠ_ {a} {a′} {b} {b′} f g w =
  [ (λ i → f i ↑ˡ b′) , (λ j → a′ ↑ʳ g j) ]′ (splitAt a w)

⊕-1 : (f : Fin a → Fin a′) (g : Fin b → Fin b′) (i : Fin a) →
      (f ⊕ᶠ g) (i ↑ˡ b) ≡ f i ↑ˡ b′
⊕-1 {a} {a′} {b} {b′} f g i =
  cong [ (λ i′ → f i′ ↑ˡ b′) , (λ j → a′ ↑ʳ g j) ]′ (splitAt-↑ˡ a i b)

⊕-2 : (f : Fin a → Fin a′) (g : Fin b → Fin b′) (j : Fin b) →
      (f ⊕ᶠ g) (a ↑ʳ j) ≡ a′ ↑ʳ g j
⊕-2 {a} {a′} {b} {b′} f g j =
  cong [ (λ i → f i ↑ˡ b′) , (λ j′ → a′ ↑ʳ g j′) ]′ (splitAt-↑ʳ a b j)

private
  ⊕-inv : (f : Fin a → Fin a′) (g : Fin b → Fin b′)
          (f′ : Fin a′ → Fin a) (g′ : Fin b′ → Fin b) →
          (∀ i → f′ (f i) ≡ i) → (∀ j → g′ (g j) ≡ j) →
          ∀ w → (f′ ⊕ᶠ g′) ((f ⊕ᶠ g) w) ≡ w
  ⊕-inv {a} {a′} {b} {b′} f g f′ g′ ff gg = blocks a b
    (λ i → trans (cong (f′ ⊕ᶠ g′) (⊕-1 f g i))
                 (trans (⊕-1 f′ g′ (f i)) (cong (_↑ˡ b) (ff i))))
    (λ j → trans (cong (f′ ⊕ᶠ g′) (⊕-2 f g j))
                 (trans (⊕-2 f′ g′ (g j)) (cong (a ↑ʳ_) (gg j))))

_⊕ᵖ_ : Permutation a a′ → Permutation b b′ → Permutation (a + b) (a′ + b′)
σ ⊕ᵖ τ = permutation ((σ ⟨$⟩ʳ_) ⊕ᶠ (τ ⟨$⟩ʳ_)) ((σ ⟨$⟩ˡ_) ⊕ᶠ (τ ⟨$⟩ˡ_))
  (⊕-inv (σ ⟨$⟩ˡ_) (τ ⟨$⟩ˡ_) (σ ⟨$⟩ʳ_) (τ ⟨$⟩ʳ_)
         (λ i → inverseʳ σ) (λ j → inverseʳ τ))
  (⊕-inv (σ ⟨$⟩ʳ_) (τ ⟨$⟩ʳ_) (σ ⟨$⟩ˡ_) (τ ⟨$⟩ˡ_)
         (λ i → inverseˡ σ) (λ j → inverseˡ τ))


------------------------------------------------------------------------
-- Exchanging the middle blocks

shuffleᶠ : ∀ a b c d → Fin ((a + b) + (c + d)) → Fin ((a + c) + (b + d))
shuffleᶠ a b c d w =
  [ (λ u → [ (λ i → (i ↑ˡ c) ↑ˡ (b + d)) , (λ j → (a + c) ↑ʳ (j ↑ˡ d)) ]′
             (splitAt a u))
  , (λ v → [ (λ k → (a ↑ʳ k) ↑ˡ (b + d)) , (λ l → (a + c) ↑ʳ (b ↑ʳ l)) ]′
             (splitAt c v))
  ]′ (splitAt (a + b) w)

shuffle-1 : ∀ a b c d (i : Fin a) →
            shuffleᶠ a b c d ((i ↑ˡ b) ↑ˡ (c + d)) ≡ (i ↑ˡ c) ↑ˡ (b + d)
shuffle-1 a b c d i
  rewrite splitAt-↑ˡ (a + b) (i ↑ˡ b) (c + d) | splitAt-↑ˡ a i b = refl

shuffle-2 : ∀ a b c d (j : Fin b) →
            shuffleᶠ a b c d ((a ↑ʳ j) ↑ˡ (c + d)) ≡ (a + c) ↑ʳ (j ↑ˡ d)
shuffle-2 a b c d j
  rewrite splitAt-↑ˡ (a + b) (a ↑ʳ j) (c + d) | splitAt-↑ʳ a b j = refl

shuffle-3 : ∀ a b c d (k : Fin c) →
            shuffleᶠ a b c d ((a + b) ↑ʳ (k ↑ˡ d)) ≡ (a ↑ʳ k) ↑ˡ (b + d)
shuffle-3 a b c d k
  rewrite splitAt-↑ʳ (a + b) (c + d) (k ↑ˡ d) | splitAt-↑ˡ c k d = refl

shuffle-4 : ∀ a b c d (l : Fin d) →
            shuffleᶠ a b c d ((a + b) ↑ʳ (c ↑ʳ l)) ≡ (a + c) ↑ʳ (b ↑ʳ l)
shuffle-4 a b c d l
  rewrite splitAt-↑ʳ (a + b) (c + d) (c ↑ʳ l) | splitAt-↑ʳ c d l = refl

-- Exchanging the middle blocks twice changes nothing.

shuffle-involutive : ∀ a b c d (w : Fin ((a + b) + (c + d))) →
                     shuffleᶠ a c b d (shuffleᶠ a b c d w) ≡ w
shuffle-involutive a b c d = blocks (a + b) (c + d)
  (blocks a b
    (λ i → trans (cong (shuffleᶠ a c b d) (shuffle-1 a b c d i))
                 (shuffle-1 a c b d i))
    (λ j → trans (cong (shuffleᶠ a c b d) (shuffle-2 a b c d j))
                 (shuffle-3 a c b d j)))
  (blocks c d
    (λ k → trans (cong (shuffleᶠ a c b d) (shuffle-3 a b c d k))
                 (shuffle-2 a c b d k))
    (λ l → trans (cong (shuffleᶠ a c b d) (shuffle-4 a b c d l))
                 (shuffle-4 a c b d l)))

shuffleᵖ : ∀ a b c d → Permutation ((a + b) + (c + d)) ((a + c) + (b + d))
shuffleᵖ a b c d = permutation (shuffleᶠ a b c d) (shuffleᶠ a c b d)
  (shuffle-involutive a c b d) (shuffle-involutive a b c d)




------------------------------------------------------------------------
-- Coherence

-- The identity on a wires (with the size explicit, so that a map
-- built from it has its sizes determined).

idᶠ : ∀ a → Fin a → Fin a
idᶠ a i = i

-- The hexagon: from (a + b) + c to b + (c + a), associating then
-- moving a past b + c then associating is moving a past b, associating
-- and moving a past c.

hexagon : ∀ a b c (w : Fin ((a + b) + c)) →
          assocᵖ b c a ⟨$⟩ʳ (braidᶠ a (b + c) (assocᵖ a b c ⟨$⟩ʳ w)) ≡
          (idᶠ b ⊕ᶠ braidᶠ a c)
            (assocᵖ b a c ⟨$⟩ʳ ((braidᶠ a b ⊕ᶠ idᶠ c) w))
hexagon a b c = blocks (a + b) c (blocks a b one two) three
  where
  rhs : Fin ((a + b) + c) → Fin (b + (c + a))
  rhs w = (idᶠ b ⊕ᶠ braidᶠ a c) (assocᵖ b a c ⟨$⟩ʳ ((braidᶠ a b ⊕ᶠ idᶠ c) w))

  lhs : Fin ((a + b) + c) → Fin (b + (c + a))
  lhs w = assocᵖ b c a ⟨$⟩ʳ (braidᶠ a (b + c) (assocᵖ a b c ⟨$⟩ʳ w))

  one : ∀ i → lhs ((i ↑ˡ b) ↑ˡ c) ≡ rhs ((i ↑ˡ b) ↑ˡ c)
  one i =
    trans (cong (λ w → assocᵖ b c a ⟨$⟩ʳ braidᶠ a (b + c) w) (assoc-1 a b c i))
    (trans (cong (assocᵖ b c a ⟨$⟩ʳ_) (braid-1 a (b + c) i))
    (trans (assoc-3 b c a i)
    (sym (trans (cong (λ w → (idᶠ b ⊕ᶠ braidᶠ a c) (assocᵖ b a c ⟨$⟩ʳ w))
                      (trans (⊕-1 (braidᶠ a b) (idᶠ c) (i ↑ˡ b))
                             (cong (_↑ˡ c) (braid-1 a b i))))
         (trans (cong (idᶠ b ⊕ᶠ braidᶠ a c) (assoc-2 b a c i))
         (trans (⊕-2 (idᶠ b) (braidᶠ a c) (i ↑ˡ c))
                (cong (b ↑ʳ_) (braid-1 a c i))))))))

  two : ∀ j → lhs ((a ↑ʳ j) ↑ˡ c) ≡ rhs ((a ↑ʳ j) ↑ˡ c)
  two j =
    trans (cong (λ w → assocᵖ b c a ⟨$⟩ʳ braidᶠ a (b + c) w) (assoc-2 a b c j))
    (trans (cong (assocᵖ b c a ⟨$⟩ʳ_) (braid-2 a (b + c) (j ↑ˡ c)))
    (trans (assoc-1 b c a j)
    (sym (trans (cong (λ w → (idᶠ b ⊕ᶠ braidᶠ a c) (assocᵖ b a c ⟨$⟩ʳ w))
                      (trans (⊕-1 (braidᶠ a b) (idᶠ c) (a ↑ʳ j))
                             (cong (_↑ˡ c) (braid-2 a b j))))
         (trans (cong (idᶠ b ⊕ᶠ braidᶠ a c) (assoc-1 b a c j))
                (⊕-1 (idᶠ b) (braidᶠ a c) j))))))

  three : ∀ k → lhs ((a + b) ↑ʳ k) ≡ rhs ((a + b) ↑ʳ k)
  three k =
    trans (cong (λ w → assocᵖ b c a ⟨$⟩ʳ braidᶠ a (b + c) w) (assoc-3 a b c k))
    (trans (cong (assocᵖ b c a ⟨$⟩ʳ_) (braid-2 a (b + c) (b ↑ʳ k)))
    (trans (assoc-2 b c a k)
    (sym (trans (cong (λ w → (idᶠ b ⊕ᶠ braidᶠ a c) (assocᵖ b a c ⟨$⟩ʳ w))
                      (⊕-2 (braidᶠ a b) (idᶠ c) k))
         (trans (cong (idᶠ b ⊕ᶠ braidᶠ a c) (assoc-3 b a c k))
         (trans (⊕-2 (idᶠ b) (braidᶠ a c) (a ↑ʳ k))
                (cong (b ↑ʳ_) (braid-2 a c k))))))))

-- Maps that keep toℕ, side by side, keep toℕ.

⊕-toℕ : (f : Fin a → Fin a′) (g : Fin b → Fin b′) → a ≡ a′ →
        (∀ i → toℕ (f i) ≡ toℕ i) → (∀ j → toℕ (g j) ≡ toℕ j) →
        ∀ w → toℕ ((f ⊕ᶠ g) w) ≡ toℕ w
⊕-toℕ {a} {a′} {b} {b′} f g refl hf hg = blocks a b
  (λ i → trans (cong toℕ (⊕-1 f g i))
         (trans (toℕ-↑ˡ (f i) b′) (trans (hf i) (sym (toℕ-↑ˡ i b)))))
  (λ j → trans (cong toℕ (⊕-2 f g j))
         (trans (toℕ-↑ʳ a (g j)) (trans (cong (a +_) (hg j))
                                        (sym (toℕ-↑ʳ a j)))))

-- The pentagon: the two ways of reassociating ((a + b) + c) + d.

pentagon : ∀ a b c d (w : Fin (((a + b) + c) + d)) →
           assocᵖ a b (c + d) ⟨$⟩ʳ (assocᵖ (a + b) c d ⟨$⟩ʳ w) ≡
           (idᶠ a ⊕ᶠ (assocᵖ b c d ⟨$⟩ʳ_))
             (assocᵖ a (b + c) d ⟨$⟩ʳ
               (((assocᵖ a b c ⟨$⟩ʳ_) ⊕ᶠ idᶠ d) w))
pentagon a b c d w = toℕ-injective
  (trans (toℕ-cast _ (assocᵖ (a + b) c d ⟨$⟩ʳ w))
  (trans (toℕ-cast _ w)
  (sym (trans (⊕-toℕ (idᶠ a) (assocᵖ b c d ⟨$⟩ʳ_) refl (λ _ → refl)
                     (λ j → toℕ-cast _ j) _)
       (trans (toℕ-cast _ (((assocᵖ a b c ⟨$⟩ʳ_) ⊕ᶠ idᶠ d) w))
              (⊕-toℕ (assocᵖ a b c ⟨$⟩ʳ_) (idᶠ d) (ℕ.+-assoc a b c)
                     (λ i → toℕ-cast _ i) (λ _ → refl) w))))))

-- The triangle: from (a + 0) + b to a + b, associating then dropping
-- the unit on the left of b (0 + b is b on the nose) is dropping it on
-- the right of a.

triangle : ∀ a b (w : Fin ((a + 0) + b)) →
           (idᶠ a ⊕ᶠ idᶠ b) (assocᵖ a 0 b ⟨$⟩ʳ w) ≡
           ((unitʳᵖ a ⟨$⟩ʳ_) ⊕ᶠ idᶠ b) w
triangle a b w = toℕ-injective
  (trans (⊕-toℕ (idᶠ a) (idᶠ b) refl (λ _ → refl) (λ _ → refl) _)
  (trans (toℕ-cast _ w)
  (sym (⊕-toℕ (unitʳᵖ a ⟨$⟩ʳ_) (idᶠ b) (ℕ.+-identityʳ a)
              (λ i → toℕ-cast _ i) (λ _ → refl) w))))
