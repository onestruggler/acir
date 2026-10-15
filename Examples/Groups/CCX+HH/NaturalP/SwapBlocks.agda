------------------------------------------------------------------------
-- Presentations of groups
--
-- The swap of wires 0 and 1 transposes the blocks of the two low bits.
--
-- A vector on 2 + k wires has four blocks R b₀ b₁, the coordinates
-- with bit 0 equal to b₀ and bit 1 equal to b₁ (two nested alternating
-- partitions).  The swap of the bottom two wires carries block (b₁, b₀)
-- to block (b₀, b₁) (`swap-blocks`).  So the swap moves a control on
-- wire 1 down to wire 0 (`swap-ctrl`, the semantic step of Ctrl's
-- CTRL₁), and passes an operator idle on both wires (`swap-idle`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.SwapBlocks where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Vec.Base using (Vec ; _∷_ ; [])
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
open Action isCommutativeRing-D adj-D ½ᴰ using (_!_ ; vec-ext)
open EmbedAction isCommutativeRing-D adj-D ½ᴰ using (restrict ; restrict-!)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (Partition ; select ; parallel ; restrict-ext ; parallel-cong ; parallel-id)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
open import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates
  using (bit ; contiguous-index ; alternating-index)
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (swap)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2
  using (Op ; pick ; parallel-select ; ctrlA)

private
  variable
    k : ℕ

-- The block of a vector on 2 + k wires with bit 0 = b₀ and bit 1 = b₁.
R : ∀ k → Bool → Bool → Vec D (2 * (2 * 2 ^ k)) → Vec D (2 ^ k)
R k b₀ b₁ v = restrict (select (alternating (2 ^ k)) b₁)
                (restrict (select (alternating (2 * 2 ^ k)) b₀) v)

-- R commutes with the top bit.
private
  index : ∀ k a b₀ b₁ (i : Fin (2 ^ k)) →
    ι (select (alternating (2 * 2 ^ suc k)) b₀)
      (ι (select (alternating (2 ^ suc k)) b₁) (ι (select (contiguous (2 ^ k)) a) i))
    ≡ ι (select (contiguous (2 ^ suc (suc k))) a)
        (ι (select (alternating (2 * 2 ^ k)) b₀) (ι (select (alternating (2 ^ k)) b₁) i))
  index k a b₀ b₁ i = FP.toℕ-injective (begin
    toℕ (ι (select (alternating (2 * 2 ^ suc k)) b₀)
      (ι (select (alternating (2 ^ suc k)) b₁) (ι (select (contiguous (2 ^ k)) a) i)))
      ≡⟨ alternating-index _ b₀ _ ⟩
    2 * toℕ (ι (select (alternating (2 ^ suc k)) b₁) (ι (select (contiguous (2 ^ k)) a) i)) + bit b₀
      ≡⟨ cong (λ x → 2 * x + bit b₀) (alternating-index _ b₁ _) ⟩
    2 * (2 * toℕ (ι (select (contiguous (2 ^ k)) a) i) + bit b₁) + bit b₀
      ≡⟨ cong (λ x → 2 * (2 * x + bit b₁) + bit b₀) (contiguous-index _ a i) ⟩
    2 * (2 * (2 ^ k * bit a + toℕ i) + bit b₁) + bit b₀
      ≡⟨ arith (2 ^ k) (bit a) (toℕ i) (bit b₁) (bit b₀) ⟩
    (2 * (2 * 2 ^ k)) * bit a + (2 * (2 * toℕ i + bit b₁) + bit b₀)
      ≡⟨ cong ((2 * (2 * 2 ^ k)) * bit a +_)
           (sym (trans (alternating-index _ b₀ _) (cong (λ x → 2 * x + bit b₀) (alternating-index _ b₁ i)))) ⟩
    (2 * (2 * 2 ^ k)) * bit a + toℕ (ι (select (alternating (2 * 2 ^ k)) b₀) (ι (select (alternating (2 ^ k)) b₁) i))
      ≡⟨ sym (contiguous-index _ a _) ⟩
    toℕ (ι (select (contiguous (2 ^ suc (suc k))) a)
        (ι (select (alternating (2 * 2 ^ k)) b₀) (ι (select (alternating (2 ^ k)) b₁) i))) ∎)
    where
    open ≡-Reasoning
    arith : ∀ p x i y z → 2 * (2 * (p * x + i) + y) + z ≡ (2 * (2 * p)) * x + (2 * (2 * i + y) + z)
    arith = solve-∀

  R-top : ∀ k a b₀ b₁ (v : Vec D (2 * (2 * 2 ^ suc k))) →
    restrict (select (contiguous (2 ^ k)) a) (R (suc k) b₀ b₁ v)
    ≡ R k b₀ b₁ (restrict (select (contiguous (2 ^ suc (suc k))) a) v)
  R-top k a b₀ b₁ v = vec-ext λ i →
    trans (restrict-! eC (restrict eB (restrict eA v)) i)
    (trans (restrict-! eB (restrict eA v) (ι eC i))
    (trans (restrict-! eA v (ι eB (ι eC i)))
    (trans (cong (v !_) (index k a b₀ b₁ i))
    (sym (trans (restrict-! eF (restrict eE (restrict eD v)) i)
         (trans (restrict-! eE (restrict eD v) (ι eF i))
                (restrict-! eD v (ι eE (ι eF i)))))))))
    where
    eA = select (alternating (2 * 2 ^ suc k)) b₀
    eB = select (alternating (2 ^ suc k)) b₁
    eC = select (contiguous (2 ^ k)) a
    eD = select (contiguous (2 ^ suc (suc k))) a
    eE = select (alternating (2 * 2 ^ k)) b₀
    eF = select (alternating (2 ^ k)) b₁

swap-blocks : ∀ k (v : Q.State (suc (suc k))) b₀ b₁ → R k b₀ b₁ (swap k v) ≡ R k b₁ b₀ v
swap-blocks zero (a ∷ b ∷ c ∷ d ∷ []) false false = refl
swap-blocks zero (a ∷ b ∷ c ∷ d ∷ []) false true  = refl
swap-blocks zero (a ∷ b ∷ c ∷ d ∷ []) true  false = refl
swap-blocks zero (a ∷ b ∷ c ∷ d ∷ []) true  true  = refl
swap-blocks (suc k) v b₀ b₁ = restrict-ext (contiguous (2 ^ k)) (at false) (at true)
  where
  at : ∀ a → restrict (select (contiguous (2 ^ k)) a) (R (suc k) b₀ b₁ (swap (suc k) v))
           ≡ restrict (select (contiguous (2 ^ k)) a) (R (suc k) b₁ b₀ v)
  at a = trans (R-top k a b₀ b₁ (swap (suc k) v))
    (trans (cong (R k b₀ b₁) (parallel-sel a))
    (trans (swap-blocks k _ b₀ b₁) (sym (R-top k a b₁ b₀ v))))
    where
    parallel-sel : ∀ a → restrict (select (contiguous (2 ^ suc (suc k))) a) (swap (suc k) v)
                       ≡ swap k (restrict (select (contiguous (2 ^ suc (suc k))) a) v)
    parallel-sel false = parallel-select (contiguous _) (swap k) (swap k) false v
    parallel-sel true  = parallel-select (contiguous _) (swap k) (swap k) true v

------------------------------------------------------------------------
-- Operators acting blockwise on the two low bits

-- f b₀ b₁ on the block with bit 0 = b₀ and bit 1 = b₁.
block₂ : ∀ k → (Bool → Bool → Op (2 ^ k)) → Op (2 * (2 * 2 ^ k))
block₂ k f = parallel (alternating (2 * 2 ^ k))
  (parallel (alternating (2 ^ k)) (f false false) (f false true))
  (parallel (alternating (2 ^ k)) (f true false) (f true true))

R-block₂ : ∀ k f b₀ b₁ v → R k b₀ b₁ (block₂ k f v) ≡ f b₀ b₁ (R k b₀ b₁ v)
R-block₂ k f false b₁ v = trans
  (cong (restrict (select (alternating (2 ^ k)) b₁))
    (parallel-select (alternating (2 * 2 ^ k)) P₀ P₁ false v))
  (trans (parallel-select (alternating (2 ^ k)) (f false false) (f false true) b₁
      (restrict (select (alternating (2 * 2 ^ k)) false) v))
    (pick-f b₁ (R k false b₁ v)))
  where
  P₀ = parallel (alternating (2 ^ k)) (f false false) (f false true)
  P₁ = parallel (alternating (2 ^ k)) (f true false) (f true true)
  pick-f : ∀ b x → pick (f false false) (f false true) b x ≡ f false b x
  pick-f false x = refl
  pick-f true  x = refl
R-block₂ k f true b₁ v = trans
  (cong (restrict (select (alternating (2 ^ k)) b₁))
    (parallel-select (alternating (2 * 2 ^ k)) P₀ P₁ true v))
  (trans (parallel-select (alternating (2 ^ k)) (f true false) (f true true) b₁
      (restrict (select (alternating (2 * 2 ^ k)) true) v))
    (pick-f b₁ (R k true b₁ v)))
  where
  P₀ = parallel (alternating (2 ^ k)) (f false false) (f false true)
  P₁ = parallel (alternating (2 ^ k)) (f true false) (f true true)
  pick-f : ∀ b x → pick (f true false) (f true true) b x ≡ f true b x
  pick-f false x = refl
  pick-f true  x = refl

-- Two vectors with the same four blocks are equal.
R-ext : ∀ k {u v : Vec D (2 * (2 * 2 ^ k))} →
  (∀ b₀ b₁ → R k b₀ b₁ u ≡ R k b₀ b₁ v) → u ≡ v
R-ext k e = restrict-ext (alternating (2 * 2 ^ k))
  (restrict-ext (alternating (2 ^ k)) (e false false) (e false true))
  (restrict-ext (alternating (2 ^ k)) (e true false) (e true true))

-- Conjugating by the swap exchanges the two low bits of the blocks.
swap-conj : ∀ k (f : Bool → Bool → Op (2 ^ k)) v →
  swap k (block₂ k f (swap k v)) ≡ block₂ k (λ a b → f b a) v
swap-conj k f v = R-ext k λ b₀ b₁ →
  trans (swap-blocks k (block₂ k f (swap k v)) b₀ b₁)
  (trans (R-block₂ k f b₁ b₀ (swap k v))
  (trans (cong (f b₁ b₀) (swap-blocks k v b₁ b₀))
    (sym (R-block₂ k (λ a b → f b a) b₀ b₁ v))))

block₂-id : ∀ k v → block₂ k (λ _ _ x → x) v ≡ v
block₂-id k v = trans
  (parallel-cong (alternating (2 * 2 ^ k))
    {f = parallel (alternating (2 ^ k)) (λ x → x) (λ x → x)} {f′ = λ x → x}
    {g = parallel (alternating (2 ^ k)) (λ x → x) (λ x → x)} {g′ = λ x → x}
    (parallel-id (alternating (2 ^ k))) (parallel-id (alternating (2 ^ k))) v)
  (parallel-id (alternating (2 * 2 ^ k)) v)

swap-invol : ∀ k v → swap k (swap k v) ≡ v
swap-invol k v = trans (cong (swap k) (sym (block₂-id k (swap k v))))
  (trans (swap-conj k (λ _ _ x → x) v) (block₂-id k v))

-- The swap moves a control on wire 1 down to wire 0, wire 1 then idle.
swap-ctrl : ∀ k (G : Op (2 ^ k)) v →
  swap k (Q.bottom {suc k} (ctrlA (2 ^ k) G) (swap k v))
  ≡ ctrlA (2 * 2 ^ k) (Q.bottom {k} G) v
swap-ctrl k G v = trans (swap-conj k (λ _ b → pick (λ x → x) G b) v)
  (parallel-cong (alternating (2 * 2 ^ k))
    {f = parallel (alternating (2 ^ k)) (λ x → x) (λ x → x)} {f′ = λ x → x}
    {g = Q.bottom {k} G} {g′ = Q.bottom {k} G}
    (parallel-id (alternating (2 ^ k))) (λ _ → refl) v)

-- The swap passes an operator idle on wires 0 and 1.
swap-idle : ∀ k (G : Op (2 ^ k)) v →
  swap k (Q.bottom {suc k} (Q.bottom {k} G) (swap k v)) ≡ Q.bottom {suc k} (Q.bottom {k} G) v
swap-idle k G v = swap-conj k (λ _ _ → G) v
