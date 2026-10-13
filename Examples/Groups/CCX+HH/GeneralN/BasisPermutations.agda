------------------------------------------------------------------------
-- Presentations of groups
--
-- Localized even permutations on basis levels.  Products of two
-- arbitrary exchanges are compiled into at most two three-cycles;
-- coincident and overlapping exchanges are included.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.BasisPermutations (n : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
import Data.Fin.Permutation.Components as PC
open import Data.Nat.Base using (_^_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong)
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Word.Base using (ε ; _•_)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.GeneralN.ThreeCycle as TC
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits)
open import Examples.Groups.CCX+HH.GeneralN.WirePermutations using (transpose-other)

module T = TC n
width = T.width
Level = Fin (2 ^ width)

swap : Level → Level → Level → Level
swap = PC.transpose

swap-first = PC.transpose[i,j,i]≡j
swap-second = PC.transpose[i,j,j]≡i
swap-other : ∀ {a b i : Level} → i ≢ a → i ≢ b → swap a b i ≡ i
swap-other = transpose-other

swap-sym : ∀ a b i → swap a b i ≡ swap b a i
swap-sym a b i = choose (i ≟ a)
  where
  choose : Dec (i ≡ a) → swap a b i ≡ swap b a i
  choose (yes refl) = trans (swap-first a b) (sym (swap-second b a))
  choose (no ia) = next (i ≟ b)
    where
    next : Dec (i ≡ b) → swap a b i ≡ swap b a i
    next (yes refl) = trans (swap-second a b) (sym (swap-first b a))
    next (no ib) = trans (swap-other ia ib) (sym (swap-other ib ia))

swap-involutive : ∀ a b i → swap a b (swap a b i) ≡ i
swap-involutive a b i = trans (cong (swap a b) (swap-sym a b i)) (PC.transpose-inverse a b)

tri : Level → Level → Level → Level → Level
tri a b c i = swap a c (swap a b i)

tri-first : ∀ a b c → a ≢ b → b ≢ c → tri a b c a ≡ b
tri-first a b c ab bc = trans (cong (swap a c) (swap-first a b))
  (swap-other (λ eq → ab (sym eq)) bc)
tri-second : ∀ a b c → tri a b c b ≡ c
tri-second a b c = trans (cong (swap a c) (swap-second a b)) (swap-first a c)
tri-third : ∀ a b c → a ≢ c → b ≢ c → tri a b c c ≡ a
tri-third a b c ac bc = trans
  (cong (swap a c) (swap-other (λ eq → ac (sym eq)) (λ eq → bc (sym eq))))
  (swap-second a c)
tri-other : ∀ a b c i → i ≢ a → i ≢ b → i ≢ c → tri a b c i ≡ i
tri-other a b c i ia ib ic = trans (cong (swap a c) (swap-other ia ib)) (swap-other ia ic)

record CircuitFor (f : Level → Level) : Set where
  field
    word : C.Circuit width
    correct : ∀ i → C.act word (bits width i) C.≈s bits width (f i)
open CircuitFor public

identity : CircuitFor (λ i → i)
identity = record { word = ε ; correct = λ i j → refl }

retarget : ∀ {f g} → (∀ i → f i ≡ g i) → CircuitFor f → CircuitFor g
retarget eq cf = record
  { word = word cf
  ; correct = λ i j → trans (correct cf i j) (cong (λ q → bits width q j) (eq i)) }

compose : ∀ {f g} → CircuitFor f → CircuitFor g → CircuitFor (λ i → f (g i))
compose cf cg = record
  { word = word cf • word cg
  ; correct = λ i j → trans (C.act-cong (word cf) (correct cg i) j) (correct cf ( _ ) j) }

three : ∀ a b c → a ≢ b → a ≢ c → b ≢ c → CircuitFor (tri a b c)
three a b c ab ac bc = record { word = T.Cycle.word witness ; correct = run }
  where
  witness = T.indexed a b c ab ac bc
  run : ∀ i → C.act (T.Cycle.word witness) (bits width i) C.≈s bits width (tri a b c i)
  run i = choose (i ≟ a)
    where
    choose : Dec (i ≡ a) → C.act (T.Cycle.word witness) (bits width i) C.≈s bits width (tri a b c i)
    choose (yes refl) j = trans (T.Cycle.first witness j)
      (cong (λ q → bits width q j) (sym (tri-first a b c ab bc)))
    choose (no ia) = next (i ≟ b)
      where
      next : Dec (i ≡ b) → C.act (T.Cycle.word witness) (bits width i) C.≈s bits width (tri a b c i)
      next (yes refl) j = trans (T.Cycle.second witness j)
        (cong (λ q → bits width q j) (sym (tri-second a b c)))
      next (no ib) = last (i ≟ c)
        where
        last : Dec (i ≡ c) → C.act (T.Cycle.word witness) (bits width i) C.≈s bits width (tri a b c i)
        last (yes refl) j = trans (T.Cycle.third witness j)
          (cong (λ q → bits width q j) (sym (tri-third a b c ac bc)))
        last (no ic) j = trans
          (T.Cycle.outside witness (bits width i) (T.bits-distinct ia) (T.bits-distinct ib) (T.bits-distinct ic) j)
          (cong (λ q → bits width q j) (sym (tri-other a b c i ia ib ic)))

private
  disjoint-factor : ∀ a b c d → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
    ∀ i → tri a b c (tri b c d i) ≡ swap a b (swap c d i)
  disjoint-factor a b c d ab ac ad bc bd cd i = choose (i ≟ a)
    where
    choose : Dec (i ≡ a) → tri a b c (tri b c d i) ≡ swap a b (swap c d i)
    choose (yes refl) = trans (cong (tri a b c) (tri-other b c d a ab ac ad))
      (trans (tri-first a b c ab bc)
        (sym (trans (cong (swap a b) (swap-other ac ad)) (swap-first a b))))
    choose (no ia) = next (i ≟ b)
      where
      next : Dec (i ≡ b) → tri a b c (tri b c d i) ≡ swap a b (swap c d i)
      next (yes refl) = trans (cong (tri a b c) (tri-first b c d bc cd))
        (trans (tri-third a b c ac bc)
          (sym (trans (cong (swap a b) (swap-other bc bd)) (swap-second a b))))
      next (no ib) = third (i ≟ c)
        where
        third : Dec (i ≡ c) → tri a b c (tri b c d i) ≡ swap a b (swap c d i)
        third (yes refl) = trans (cong (tri a b c) (tri-second b c d))
          (trans (tri-other a b c d (λ eq → ad (sym eq)) (λ eq → bd (sym eq)) (λ eq → cd (sym eq)))
            (sym (trans (cong (swap a b) (swap-first c d))
              (swap-other (λ eq → ad (sym eq)) (λ eq → bd (sym eq))))))
        third (no ic) = fourth (i ≟ d)
          where
          fourth : Dec (i ≡ d) → tri a b c (tri b c d i) ≡ swap a b (swap c d i)
          fourth (yes refl) = trans (cong (tri a b c) (tri-third b c d bd cd))
            (trans (tri-second a b c)
              (sym (trans (cong (swap a b) (swap-second c d))
                (swap-other (λ eq → ac (sym eq)) (λ eq → bc (sym eq))))))
          fourth (no id) = trans (cong (tri a b c) (tri-other b c d i ib ic id))
            (trans (tri-other a b c i ia ib ic)
              (sym (trans (cong (swap a b) (swap-other ic id)) (swap-other ia ib))))

pair : ∀ a b c d → a ≢ b → c ≢ d → CircuitFor (λ i → swap a b (swap c d i))
pair a b c d ab cd = first-case (c ≟ a)
  where
  first-case : Dec (c ≡ a) → CircuitFor (λ i → swap a b (swap c d i))
  first-case (yes refl) = last-case (d ≟ b)
    where
    last-case : Dec (d ≡ b) → CircuitFor (λ i → swap a b (swap a d i))
    last-case (yes refl) = retarget (λ i → sym (swap-involutive a b i)) identity
    last-case (no db) = three a d b cd ab db
  first-case (no ca) = second-case (c ≟ b)
    where
    second-case : Dec (c ≡ b) → CircuitFor (λ i → swap a b (swap c d i))
    second-case (yes refl) = last-case (d ≟ a)
      where
      last-case : Dec (d ≡ a) → CircuitFor (λ i → swap a b (swap b d i))
      last-case (yes refl) = retarget (λ i → sym (PC.transpose-inverse a b)) identity
      last-case (no da) = retarget (λ i → swap-sym b a (swap b d i))
        (three b d a cd (λ eq → ab (sym eq)) da)
    second-case (no cb) = third-case (d ≟ a)
      where
      third-case : Dec (d ≡ a) → CircuitFor (λ i → swap a b (swap c d i))
      third-case (yes refl) = retarget (λ i → cong (swap a b) (swap-sym a c i))
        (three a c b (λ eq → ca (sym eq)) ab cb)
      third-case (no da) = fourth-case (d ≟ b)
        where
        fourth-case : Dec (d ≡ b) → CircuitFor (λ i → swap a b (swap c d i))
        fourth-case (yes refl) = retarget
          (λ i → trans (swap-sym b a (swap b c i)) (cong (swap a b) (swap-sym b c i)))
          (three b c a (λ eq → cb (sym eq)) (λ eq → ab (sym eq)) ca)
        fourth-case (no db) = retarget
          (disjoint-factor a b c d ab (λ eq → ca (sym eq)) (λ eq → da (sym eq))
            (λ eq → cb (sym eq)) (λ eq → db (sym eq)) cd)
          (compose (three a b c ab (λ eq → ca (sym eq)) (λ eq → cb (sym eq)))
            (three b c d (λ eq → cb (sym eq)) (λ eq → db (sym eq)) cd))
