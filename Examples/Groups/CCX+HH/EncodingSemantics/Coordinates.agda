------------------------------------------------------------------------
-- Presentations of groups
--
-- Arithmetic of the binary block embeddings.  Inserting a bit at the
-- top and at the bottom commute, including at symbolic dimension.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.EncodingSemantics.Coordinates where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Fin.Base using (Fin ; toℕ ; zero ; suc)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; _+_ ; _*_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary

private variable m n k : ℕ

bit : Bool → ℕ
bit false = 0
bit true = 1

contiguous-index : ∀ m b i →
  toℕ (ι (select (contiguous m) b) i) ≡ m * bit b + toℕ i
contiguous-index m false i = FP.toℕ-combine {m = 2} {n = m} zero i
contiguous-index m true i = FP.toℕ-combine {m = 2} {n = m} (suc zero) i

columns-index : ∀ m b i →
  toℕ (ι (select (columns m) b) i) ≡ 2 * toℕ i + bit b
columns-index m false i = FP.toℕ-combine {m = m} {n = 2} i zero
columns-index m true i = FP.toℕ-combine {m = m} {n = 2} i (suc zero)

transport-index : (eq : n ≡ k) (p : Partition m n) → ∀ b i →
  toℕ (ι (select (subst (Partition m) eq p) b) i) ≡
  toℕ (ι (select p b) i)
transport-index refl p b i = refl

alternating-index : ∀ m b i →
  toℕ (ι (select (alternating m) b) i) ≡ 2 * toℕ i + bit b
alternating-index m b i = trans
  (transport-index (NP.*-comm m 2) (columns m) b i) (columns-index m b i)

-- q_a p_b i = s_b r_a i, with p/s alternating and q/r contiguous.
commute : ∀ m a b (i : Fin m) →
  ι (select (contiguous (2 * m)) a) (ι (select (alternating m) b) i) ≡
  ι (select (alternating (2 * m)) b) (ι (select (contiguous m) a) i)
commute m a b i = FP.toℕ-injective (begin
  toℕ (ι (select (contiguous (2 * m)) a) (ι (select (alternating m) b) i))
    ≡⟨ contiguous-index (2 * m) a _ ⟩
  (2 * m) * bit a + toℕ (ι (select (alternating m) b) i)
    ≡⟨ cong ((2 * m) * bit a +_) (alternating-index m b i) ⟩
  (2 * m) * bit a + (2 * toℕ i + bit b)
    ≡⟨ sym (NP.+-assoc ((2 * m) * bit a) (2 * toℕ i) (bit b)) ⟩
  ((2 * m) * bit a + 2 * toℕ i) + bit b
    ≡⟨ cong (λ x → (x + 2 * toℕ i) + bit b) (NP.*-assoc 2 m (bit a)) ⟩
  (2 * (m * bit a) + 2 * toℕ i) + bit b
    ≡⟨ cong (_+ bit b) (sym (NP.*-distribˡ-+ 2 (m * bit a) (toℕ i))) ⟩
  2 * (m * bit a + toℕ i) + bit b
    ≡⟨ cong (λ x → 2 * x + bit b) (sym (contiguous-index m a i)) ⟩
  2 * toℕ (ι (select (contiguous m) a) i) + bit b
    ≡⟨ sym (alternating-index (2 * m) b _) ⟩
  toℕ (ι (select (alternating (2 * m)) b) (ι (select (contiguous m) a) i)) ∎)
  where open ≡-Reasoning
