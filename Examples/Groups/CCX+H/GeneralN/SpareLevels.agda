------------------------------------------------------------------------
-- Presentations of groups
--
-- Construct spare levels without enumerating the computational basis.
-- Deleting k requested levels leaves a strictly increasing embedding
-- of the remaining lower bound.  Repeated requested levels are allowed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.SpareLevels where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _≤_ ; s≤s ; z≤n)
import Data.Nat.Properties as NP
open import Data.Product.Base using (Σ ; _,_)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_ ; punchIn ; punchOut ; toℕ)
import Data.Fin.Properties as FP
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map ; lookup)
open import Data.Vec.Properties using (lookup-map)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans)

private
  punchIn-mono-< : ∀ {n} a (i j : Fin n) → i < j → punchIn a i < punchIn a j
  punchIn-mono-< zero i j p = s≤s p
  punchIn-mono-< (suc a) zero zero ()
  punchIn-mono-< (suc a) zero (suc j) p = s≤s z≤n
  punchIn-mono-< (suc a) (suc i) zero ()
  punchIn-mono-< (suc a) (suc i) (suc j) (s≤s p) =
    s≤s (punchIn-mono-< a i j p)

  -- If the level being removed occurs again, exclude an arbitrary
  -- extra level.  This preserves the promised cardinality lower bound.
  lower : ∀ {n} → Fin (suc (suc n)) → Fin (suc (suc n)) → Fin (suc n)
  lower a x with a FP.≟ x
  ... | yes _ = zero
  ... | no ax = punchOut ax

  lower-correct : ∀ {n} (a x : Fin (suc (suc n))) → a ≢ x →
    punchIn a (lower a x) ≡ x
  lower-correct a x ax with a FP.≟ x
  ... | yes eq = ⊥-elim (ax eq)
  ... | no neq = FP.punchIn-punchOut neq

record Complement {k n : ℕ} (xs : Vec (Fin (suc (k + n))) k) : Set where
  field
    embed : Fin (suc n) → Fin (suc (k + n))
    increasing : ∀ i j → i < j → embed i < embed j
    outside : ∀ i j → embed i ≢ lookup xs j

complement : ∀ {k n} (xs : Vec (Fin (suc (k + n))) k) → Complement xs
complement [] = record
  { embed = λ i → i
  ; increasing = λ i j p → p
  ; outside = λ i ()
  }
complement {suc k} {n} (a ∷ xs) = record
  { embed = λ i → punchIn a (C.embed i)
  ; increasing = λ i j p → punchIn-mono-< a (C.embed i) (C.embed j)
      (C.increasing i j p)
  ; outside = apart
  }
  where
  lower′ : Fin (suc (suc (k + n))) → Fin (suc (k + n))
  lower′ = lower a

  module C = Complement (complement (map lower′ xs))

  lowered : ∀ x → a ≢ x → punchIn a (lower′ x) ≡ x
  lowered = lower-correct a

  apart : ∀ i j → punchIn a (C.embed i) ≢ lookup (a ∷ xs) j
  apart i zero = FP.punchInᵢ≢i a (C.embed i)
  apart i (suc j) eq with a FP.≟ lookup xs j
  ... | yes ax = FP.punchInᵢ≢i a (C.embed i) (trans eq (sym ax))
  ... | no ax = C.outside i j
    (trans (FP.punchIn-injective a (C.embed i) (lower′ (lookup xs j))
      (trans eq (sym (lowered (lookup xs j) ax))))
      (sym (lookup-map j lower′ xs)))

record TwoSpares {k n : ℕ} (xs : Vec (Fin n) k) : Set where
  field
    first second : Fin n
    ordered : first < second
    first-outside : ∀ j → first ≢ lookup xs j
    second-outside : ∀ j → second ≢ lookup xs j

two-spares : ∀ {n} (xs : Vec (Fin (6 + n)) 4) → TwoSpares xs
two-spares xs = record
  { first = C.embed zero
  ; second = C.embed (suc zero)
  ; ordered = C.increasing zero (suc zero) (s≤s z≤n)
  ; first-outside = C.outside zero
  ; second-outside = C.outside (suc zero)
  }
  where module C = Complement (complement xs)

-- The same construction for eight routed levels in an arbitrary
-- dimension satisfying the numerical bound.  Equality elimination
-- keeps the final finite indices in the caller's original dimension.
eight-spares : ∀ {n} (xs : Vec (Fin n) 8) → 10 ≤ n → TwoSpares xs
eight-spares {n} xs bound = choose (NP.m≤n⇒∃[o]m+o≡n bound)
  where
  build : ∀ m {n} → 10 + m ≡ n → (ys : Vec (Fin n) 8) → TwoSpares ys
  build m refl ys = record
    { first = C.embed zero
    ; second = C.embed (suc zero)
    ; ordered = C.increasing zero (suc zero) (s≤s z≤n)
    ; first-outside = C.outside zero
    ; second-outside = C.outside (suc zero)
    }
    where module C = Complement (complement ys)

  choose : (Σ ℕ λ m → 10 + m ≡ n) → TwoSpares xs
  choose (m , eq) = build m eq xs

------------------------------------------------------------------------
-- The spares are small

private
  punchIn-≤ : ∀ {n} (a : Fin (suc n)) (j : Fin n) → toℕ (punchIn a j) ≤ suc (toℕ j)
  punchIn-≤ zero    j       = NP.≤-refl
  punchIn-≤ (suc a) zero    = z≤n
  punchIn-≤ (suc a) (suc j) = s≤s (punchIn-≤ a j)

-- Removing k levels moves a level up by at most k.
embed-bound : ∀ {k n} (xs : Vec (Fin (suc (k + n))) k) (i : Fin (suc n)) →
  toℕ (Complement.embed (complement xs) i) ≤ toℕ i + k
embed-bound []       i = NP.m≤m+n (toℕ i) 0
embed-bound {suc k} {n} (a ∷ xs) i =
  NP.≤-trans (punchIn-≤ a (Complement.embed (complement (map (lower a) xs)) i))
    (NP.≤-trans (s≤s (embed-bound (map (lower a) xs) i)) (NP.≤-reflexive (sym (NP.+-suc (toℕ i) k))))

two-spares-first : ∀ {n} (xs : Vec (Fin (6 + n)) 4) → toℕ (TwoSpares.first (two-spares xs)) ≤ 4
two-spares-first xs = embed-bound xs zero

two-spares-second : ∀ {n} (xs : Vec (Fin (6 + n)) 4) → toℕ (TwoSpares.second (two-spares xs)) ≤ 5
two-spares-second xs = embed-bound xs (suc zero)
