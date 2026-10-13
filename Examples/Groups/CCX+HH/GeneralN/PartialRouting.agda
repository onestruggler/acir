------------------------------------------------------------------------
-- Presentations of groups
--
-- Any injective finite list of basis levels can be routed to another
-- injective list, provided two target levels remain unused.  A list
-- of transpositions is paired into physical even permutations; an
-- unpaired transposition is absorbed by exchanging the two unused
-- target levels.  No additional qubits are introduced.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.PartialRouting (n : ℕ) where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_ ; suc-injective)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
import Examples.Groups.CCX+HH.GeneralN.BasisPermutations as BP
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits)

module P = BP n
open P using (Level ; width ; swap ; swap-first ; swap-other ; swap-involutive)

record Exchange : Set where
  constructor exchange
  field
    a b : Level
    different : a ≢ b
open Exchange

image : Exchange → Level → Level
image e = swap (a e) (b e)

apply : List Exchange → Level → Level
apply [] i = i
apply (e ∷ es) i = image e (apply es i)

apply-injective : ∀ es {i j} → apply es i ≡ apply es j → i ≡ j
apply-injective [] eq = eq
apply-injective (e ∷ es) {i} {j} eq = apply-injective es
  (trans (sym (swap-involutive (a e) (b e) (apply es i)))
    (trans (cong (image e) eq) (swap-involutive (a e) (b e) (apply es j))))

record Pins {k : ℕ} (xs ys : Fin k → Level) : Set where
  field
    exchanges : List Exchange
    correct : ∀ i → apply exchanges (xs i) ≡ ys i
open Pins public

pins : ∀ k (xs ys : Fin k → Level) →
  (∀ {i j} → xs i ≡ xs j → i ≡ j) →
  (∀ {i j} → ys i ≡ ys j → i ≡ j) → Pins xs ys
pins zero xs ys xi yi = record { exchanges = [] ; correct = λ () }
pins (suc k) xs ys xi yi = choose (current ≟ ys zero)
  where
  tail = pins k (λ i → xs (suc i)) (λ i → ys (suc i))
    (λ eq → suc-injective (xi eq)) (λ eq → suc-injective (yi eq))
  es = exchanges tail
  current = apply es (xs zero)

  choose : Dec (current ≡ ys zero) → Pins xs ys
  choose (yes eq) = record
    { exchanges = es
    ; correct = λ { zero → eq ; (suc i) → correct tail i }
    }
  choose (no ne) = record
    { exchanges = exchange current (ys zero) ne ∷ es
    ; correct = λ { zero → swap-first current (ys zero) ; (suc i) → preserved i }
    }
    where
    preserved : ∀ i → swap current (ys zero) (apply es (xs (suc i))) ≡ ys (suc i)
    preserved i = trans (swap-other
      (λ eq → impossible (xi (apply-injective es eq)))
      (λ eq → impossible (yi (trans (sym (correct tail i)) eq)))) (correct tail i)
      where
      impossible : suc i ≢ zero
      impossible ()

-- Pair adjacent letters.  The odd case retains exactly one pending
-- exchange, rather than asserting that an odd permutation is physical.
data Decoded (es : List Exchange) : Set where
  even : P.CircuitFor (apply es) → Decoded es
  odd : (e : Exchange) (f : Level → Level) → P.CircuitFor f →
    (∀ i → apply es i ≡ image e (f i)) → Decoded es

decode : ∀ es → Decoded es
decode [] = even P.identity
decode (e ∷ es) = extend (decode es)
  where
  extend : Decoded es → Decoded (e ∷ es)
  extend (even cf) = odd e (apply es) cf (λ i → refl)
  extend (odd d f cf eq) = even
    (P.retarget (λ i → cong (image e) (sym (eq i)))
      (P.compose (P.pair (a e) (b e) (a d) (b d) (different e) (different d)) cf))

module Complete (s t : Level) (st : s ≢ t) where

  record Completed (es : List Exchange) : Set where
    field
      word : C.Circuit width
      correct-away : ∀ i → apply es i ≢ s → apply es i ≢ t →
        C.act word (bits width i) C.≈s bits width (apply es i)
  open Completed public

  finish : ∀ es → Completed es
  finish es = choose (decode es)
    where
    choose : Decoded es → Completed es
    choose (even cf) = record { word = P.word cf ; correct-away = λ i _ _ → P.correct cf i }
    choose (odd e f cf eq) = record
      { word = P.word corrected
      ; correct-away = λ i is it j → trans (P.correct corrected i j)
          (cong (λ q → bits width q j)
            (trans (cong (swap s t) (sym (eq i))) (swap-other is it)))
      }
      where
      corrected = P.compose (P.pair s t (a e) (b e) st (different e)) cf

  record Route {k : ℕ} (xs ys : Fin k → Level) : Set where
    field
      word : C.Circuit width
      correct : ∀ i → C.act word (bits width (xs i)) C.≈s bits width (ys i)

  route : ∀ k (xs ys : Fin k → Level) →
    (∀ {i j} → xs i ≡ xs j → i ≡ j) →
    (∀ {i j} → ys i ≡ ys j → i ≡ j) →
    (∀ i → ys i ≢ s) → (∀ i → ys i ≢ t) → Route xs ys
  route k xs ys xi yi out-s out-t = record
    { word = Completed.word completed
    ; correct = λ i j → trans
        (Completed.correct-away completed (xs i)
          (λ eq → out-s i (trans (sym (Pins.correct p i)) eq))
          (λ eq → out-t i (trans (sym (Pins.correct p i)) eq)) j)
        (cong (λ q → bits width q j) (Pins.correct p i))
    }
    where
    p = pins k xs ys xi yi
    completed = finish (Pins.exchanges p)
