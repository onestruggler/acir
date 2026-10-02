------------------------------------------------------------------------
-- Presentations of groups
--
-- The second hexagon, on wires (Amy, QPL 2018, remark 2.8)
--
-- PathSum.Permute.Blocks proves the coherence of the symmetric
-- monoidal structure on wires -- the bijections between the wires of
-- the two sides -- with one orientation of the hexagon (hexagon):
-- moving a past b + c is moving a past b, then past c.  A braided
-- monoidal category has a second hexagon, built from the inverse
-- associator: moving c in front of a + b is moving it in front of b,
-- then in front of a,
--
--    α⁻¹_{c,a,b} ∘ γ_{a+b,c} ∘ α⁻¹_{a,b,c}
--      = (γ_{a,c} ⊕ 1_b) ∘ α⁻¹_{a,c,b} ∘ (1_a ⊕ γ_{b,c}),
--
-- from a + (b + c) to (c + a) + b.  In a symmetric category it follows
-- from the first and the involutivity of the braiding; here it is
-- proved directly, block by block, like the first (hexagon′).
-- PathSum.Compose.Relabel transports it to path-sums.  Nothing here
-- depends on M or mentions a path-sum.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Permute.Hexagon where

open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Permutation using (_⟨$⟩ˡ_)
open import Data.Nat.Base using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong)

open import PathSum.Permute.Blocks using
  (blocks; assocᵖ; braidᶠ; _⊕ᶠ_; idᶠ; ⊕-1; ⊕-2; braid-1; braid-2;
   assoc⁻¹-1; assoc⁻¹-2; assoc⁻¹-3)


------------------------------------------------------------------------
-- The second hexagon

-- From a + (b + c) to (c + a) + b: associating back, then moving c in
-- front of a + b, then associating back, is moving c in front of b,
-- associating back and moving c in front of a.

hexagon′ : ∀ a b c (w : Fin (a + (b + c))) →
           assocᵖ c a b ⟨$⟩ˡ (braidᶠ (a + b) c (assocᵖ a b c ⟨$⟩ˡ w)) ≡
           (braidᶠ a c ⊕ᶠ idᶠ b)
             (assocᵖ a c b ⟨$⟩ˡ ((idᶠ a ⊕ᶠ braidᶠ b c) w))
hexagon′ a b c = blocks a (b + c) one (blocks b c two three)
  where
  lhs : Fin (a + (b + c)) → Fin ((c + a) + b)
  lhs w = assocᵖ c a b ⟨$⟩ˡ (braidᶠ (a + b) c (assocᵖ a b c ⟨$⟩ˡ w))

  rhs : Fin (a + (b + c)) → Fin ((c + a) + b)
  rhs w = (braidᶠ a c ⊕ᶠ idᶠ b)
            (assocᵖ a c b ⟨$⟩ˡ ((idᶠ a ⊕ᶠ braidᶠ b c) w))

  one : ∀ i → lhs (i ↑ˡ (b + c)) ≡ rhs (i ↑ˡ (b + c))
  one i =
    trans (cong (λ v → assocᵖ c a b ⟨$⟩ˡ braidᶠ (a + b) c v)
                (assoc⁻¹-1 a b c i))
    (trans (cong (assocᵖ c a b ⟨$⟩ˡ_) (braid-1 (a + b) c (i ↑ˡ b)))
    (trans (assoc⁻¹-2 c a b i)
    (sym (trans (cong (λ v → (braidᶠ a c ⊕ᶠ idᶠ b) (assocᵖ a c b ⟨$⟩ˡ v))
                      (⊕-1 (idᶠ a) (braidᶠ b c) i))
         (trans (cong (braidᶠ a c ⊕ᶠ idᶠ b) (assoc⁻¹-1 a c b i))
         (trans (⊕-1 (braidᶠ a c) (idᶠ b) (i ↑ˡ c))
                (cong (_↑ˡ b) (braid-1 a c i))))))))

  two : ∀ j → lhs (a ↑ʳ (j ↑ˡ c)) ≡ rhs (a ↑ʳ (j ↑ˡ c))
  two j =
    trans (cong (λ v → assocᵖ c a b ⟨$⟩ˡ braidᶠ (a + b) c v)
                (assoc⁻¹-2 a b c j))
    (trans (cong (assocᵖ c a b ⟨$⟩ˡ_) (braid-1 (a + b) c (a ↑ʳ j)))
    (trans (assoc⁻¹-3 c a b j)
    (sym (trans (cong (λ v → (braidᶠ a c ⊕ᶠ idᶠ b) (assocᵖ a c b ⟨$⟩ˡ v))
                      (trans (⊕-2 (idᶠ a) (braidᶠ b c) (j ↑ˡ c))
                             (cong (a ↑ʳ_) (braid-1 b c j))))
         (trans (cong (braidᶠ a c ⊕ᶠ idᶠ b) (assoc⁻¹-3 a c b j))
                (⊕-2 (braidᶠ a c) (idᶠ b) j))))))

  three : ∀ k → lhs (a ↑ʳ (b ↑ʳ k)) ≡ rhs (a ↑ʳ (b ↑ʳ k))
  three k =
    trans (cong (λ v → assocᵖ c a b ⟨$⟩ˡ braidᶠ (a + b) c v)
                (assoc⁻¹-3 a b c k))
    (trans (cong (assocᵖ c a b ⟨$⟩ˡ_) (braid-2 (a + b) c k))
    (trans (assoc⁻¹-1 c a b k)
    (sym (trans (cong (λ v → (braidᶠ a c ⊕ᶠ idᶠ b) (assocᵖ a c b ⟨$⟩ˡ v))
                      (trans (⊕-2 (idᶠ a) (braidᶠ b c) (b ↑ʳ k))
                             (cong (a ↑ʳ_) (braid-2 b c k))))
         (trans (cong (braidᶠ a c ⊕ᶠ idᶠ b) (assoc⁻¹-2 a c b k))
         (trans (⊕-1 (braidᶠ a c) (idᶠ b) (a ↑ʳ k))
                (cong (_↑ˡ b) (braid-2 a c k))))))))
