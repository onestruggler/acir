------------------------------------------------------------------------
-- Presentations of groups
--
-- The two coordinate partitions obtained by adding an idle qubit.
-- Contiguous halves add a most significant bit; interleaving adds a
-- least significant bit.  Wire zero is least significant.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.EncodingSemantics.Binary where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; combine ; remQuot ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; _*_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_×_ ; _,_ ; uncurry)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition

private
  variable m : ℕ

  row : Fin 2 → Emb m (2 * m)
  row b = record { ι = combine b ; mono = mono′ }
    where
    mono′ : ∀ {i j} → i < j → combine b i < combine b j
    mono′ {i} {j} p rewrite FP.toℕ-combine b i | FP.toℕ-combine b j =
      NP.+-monoʳ-< _ p

  column : Fin 2 → Emb m (m * 2)
  column b = record { ι = λ i → combine i b ; mono = FP.combine-monoˡ-< b b }

  choose-row : Fin 2 × Fin m → Fin m ⊎ Fin m
  choose-row (zero , i) = inj₁ i
  choose-row (suc zero , i) = inj₂ i

  choose-column : Fin m × Fin 2 → Fin m ⊎ Fin m
  choose-column (i , zero) = inj₁ i
  choose-column (i , suc zero) = inj₂ i

  row-cover : (p : Fin 2 × Fin m) →
    [ ι (row zero) , ι (row (suc zero)) ]′ (choose-row p) ≡ uncurry combine p
  row-cover (zero , i) = refl
  row-cover (suc zero , i) = refl

  column-cover : (p : Fin m × Fin 2) →
    [ ι (column zero) , ι (column (suc zero)) ]′ (choose-column p) ≡ uncurry combine p
  column-cover (i , zero) = refl
  column-cover (i , suc zero) = refl

contiguous : (m : ℕ) → Partition m (2 * m)
contiguous m = record
  { left = row zero
  ; right = row (suc zero)
  ; locate = λ x → choose-row (remQuot m x)
  ; locate-left = λ x → cong choose-row (FP.remQuot-combine zero x)
  ; locate-right = λ x → cong choose-row (FP.remQuot-combine (suc zero) x)
  ; cover = λ x → trans (row-cover (remQuot m x)) (FP.combine-remQuot m x)
  }

columns : (m : ℕ) → Partition m (m * 2)
columns m = record
  { left = column zero
  ; right = column (suc zero)
  ; locate = λ x → choose-column (remQuot 2 x)
  ; locate-left = λ x → cong choose-column (FP.remQuot-combine x zero)
  ; locate-right = λ x → cong choose-column (FP.remQuot-combine x (suc zero))
  ; cover = λ x → trans (column-cover {m} (remQuot {m} 2 x))
      (FP.combine-remQuot {m} 2 x)
  }

alternating : (m : ℕ) → Partition m (2 * m)
alternating m = subst (Partition m) (NP.*-comm m 2) (columns m)
