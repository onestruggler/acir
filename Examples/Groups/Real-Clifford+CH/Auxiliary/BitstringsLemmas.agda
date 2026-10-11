------------------------------------------------------------------------
-- Presentations of groups
--
-- Facts about insertion and removal at a wire, decided equality of
-- bitstrings, and the enumeration of all bitstrings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Bool.Properties using (∧-comm ; ∨-comm)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqᵇ ; eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Decided equality of bitstrings

eqᵇ-refl : ∀ b → eqᵇ b b ≡ true
eqᵇ-refl true  = Eq.refl
eqᵇ-refl false = Eq.refl

eqB-refl : (x : Bits n) → eqB x x ≡ true
eqB-refl []       = Eq.refl
eqB-refl (b ∷ x) = Eq.trans (Eq.cong (_∧ eqB x x) (eqᵇ-refl b)) (eqB-refl x)

eqB-sound : (x y : Bits n) → eqB x y ≡ true → x ≡ y
eqB-sound []          []          _ = Eq.refl
eqB-sound (true ∷ x)  (true ∷ y)  e = Eq.cong (true ∷_) (eqB-sound x y e)
eqB-sound (false ∷ x) (false ∷ y) e = Eq.cong (false ∷_) (eqB-sound x y e)
eqB-sound (true ∷ x)  (false ∷ y) ()
eqB-sound (false ∷ x) (true ∷ y)  ()

eqB-complete : (x y : Bits n) → x ≡ y → eqB x y ≡ true
eqB-complete x .x Eq.refl = eqB-refl x

eqB-false : (x y : Bits n) → x ≢ y → eqB x y ≡ false
eqB-false x y ne with eqB x y in eq
... | true  = ⊥-elim (ne (eqB-sound x y eq))
... | false = Eq.refl

eqB-sym : (x y : Bits n) → eqB x y ≡ eqB y x
eqB-sym []          []          = Eq.refl
eqB-sym (a ∷ x)     (b ∷ y)     = Eq.cong₂ _∧_ (eqᵇ-sym a b) (eqB-sym x y)
  where
  eqᵇ-sym : ∀ a b → eqᵇ a b ≡ eqᵇ b a
  eqᵇ-sym true  true  = Eq.refl
  eqᵇ-sym true  false = Eq.refl
  eqᵇ-sym false true  = Eq.refl
  eqᵇ-sym false false = Eq.refl

------------------------------------------------------------------------
-- Insertion, removal and lookup at a wire i ≤ n

lookup-insert : ∀ i b (v : Bits n) → i ≤ n → lookupℕ i (insertℕ i b v) ≡ b
lookup-insert zero    b v       _       = Eq.refl
lookup-insert (suc i) b (c ∷ v) (s≤s p) = lookup-insert i b v p

remove-insert : ∀ i b (v : Bits n) → i ≤ n → removeℕ i (insertℕ i b v) ≡ v
remove-insert zero          b v         _             = Eq.refl
remove-insert (suc zero)    b (c ∷ v)   _             = Eq.refl
remove-insert (suc (suc i)) b (c ∷ c′ ∷ v) (s≤s p)    =
  Eq.cong (c ∷_) (remove-insert (suc i) b (c′ ∷ v) p)

insert-lookup-remove : ∀ i (x : Bits (suc n)) → i ≤ n → insertℕ i (lookupℕ i x) (removeℕ i x) ≡ x
insert-lookup-remove zero          (b ∷ x)         _       = Eq.refl
insert-lookup-remove (suc zero)    (b ∷ c ∷ x)     _       = Eq.refl
insert-lookup-remove (suc (suc i)) (b ∷ c ∷ x)     (s≤s p) =
  Eq.cong (b ∷_) (insert-lookup-remove (suc i) (c ∷ x) p)

-- Looking up below and above an insertion.
lookup-insert-below : ∀ i j b (v : Bits n) → j < i → i ≤ n → lookupℕ j (insertℕ i b v) ≡ lookupℕ j v
lookup-insert-below (suc i) zero    b (c ∷ v) _       _       = Eq.refl
lookup-insert-below (suc i) (suc j) b (c ∷ v) (s≤s p) (s≤s q) = lookup-insert-below i j b v p q

lookup-insert-above : ∀ i j b (v : Bits n) → i ≤ j → j < n → lookupℕ (suc j) (insertℕ i b v) ≡ lookupℕ j v
lookup-insert-above zero    j       b v       _       _       = Eq.refl
lookup-insert-above (suc i) (suc j) b (c ∷ v) (s≤s p) (s≤s q) = lookup-insert-above i j b v p q

-- Removing below an insertion.
remove-insert-below : ∀ i j b (v : Bits (suc n)) → j ≤ i → i ≤ n →
                      removeℕ j (insertℕ (suc i) b v) ≡ insertℕ i b (removeℕ j v)
remove-insert-below i       zero    b (c ∷ v)      _       _       = Eq.refl
remove-insert-below (suc i) (suc j) b (c ∷ c′ ∷ v) (s≤s p) (s≤s q) =
  Eq.cong (c ∷_) (remove-insert-below i j b (c′ ∷ v) p q)

-- Looking up below a removal.
lookup-remove-below : ∀ i j (x : Bits (suc n)) → j < i → i ≤ n → lookupℕ j (removeℕ i x) ≡ lookupℕ j x
lookup-remove-below (suc i) zero    (b ∷ c ∷ x) _       _       = Eq.refl
lookup-remove-below (suc i) (suc j) (b ∷ c ∷ x) (s≤s p) (s≤s q) = lookup-remove-below i j (c ∷ x) p q

-- Inserting at i then at j ≤ i is inserting at j then at i + 1.
insert-swap : ∀ i j b b′ (v : Bits n) → j ≤ i → i ≤ n →
              insertℕ j b′ (insertℕ i b v) ≡ insertℕ (suc i) b (insertℕ j b′ v)
insert-swap i       zero    b b′ v       _       _       = Eq.refl
insert-swap (suc i) (suc j) b b′ (c ∷ v) (s≤s p) (s≤s q) =
  Eq.cong (c ∷_) (insert-swap i j b b′ v p q)

------------------------------------------------------------------------
-- Membership and the enumeration of all bitstrings

infix 6 _∈ᵇ_
_∈ᵇ_ : Bits n → List (Bits n) → Bool
x ∈ᵇ []       = false
x ∈ᵇ (c ∷ cs) = eqB x c ∨ (x ∈ᵇ cs)

∈ᵇ-++ : (x : Bits n) (xs ys : List (Bits n)) → x ∈ᵇ (xs ++ ys) ≡ (x ∈ᵇ xs) ∨ (x ∈ᵇ ys)
∈ᵇ-++ x []       ys = Eq.refl
∈ᵇ-++ x (c ∷ xs) ys = Eq.trans (Eq.cong (eqB x c ∨_) (∈ᵇ-++ x xs ys)) (Eq.sym (∨-assoc′ (eqB x c) _ _))
  where
  ∨-assoc′ : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc′ true  b c = Eq.refl
  ∨-assoc′ false b c = Eq.refl

-- Membership in a map by cons: the head bit must agree.
∈ᵇ-map∷ : ∀ a (x : Bits n) (cs : List (Bits n)) → (a ∷ x) ∈ᵇ map (a ∷_) cs ≡ x ∈ᵇ cs
∈ᵇ-map∷ a x []       = Eq.refl
∈ᵇ-map∷ a x (c ∷ cs) = Eq.cong₂ _∨_ (Eq.cong (_∧ eqB x c) (eqᵇ-refl a)) (∈ᵇ-map∷ a x cs)

∈ᵇ-map∷-≢ : ∀ a b (x : Bits n) (cs : List (Bits n)) → a ≢ b → (a ∷ x) ∈ᵇ map (b ∷_) cs ≡ false
∈ᵇ-map∷-≢ a b x []       ne = Eq.refl
∈ᵇ-map∷-≢ a b x (c ∷ cs) ne = Eq.cong₂ _∨_ (Eq.cong (_∧ eqB x c) (eqᵇ-≢ a b ne)) (∈ᵇ-map∷-≢ a b x cs ne)
  where
  eqᵇ-≢ : ∀ a b → a ≢ b → eqᵇ a b ≡ false
  eqᵇ-≢ true  true  ne = ⊥-elim (ne Eq.refl)
  eqᵇ-≢ false false ne = ⊥-elim (ne Eq.refl)
  eqᵇ-≢ true  false _  = Eq.refl
  eqᵇ-≢ false true  _  = Eq.refl

-- Every string is enumerated.
∈-allBits : (x : Bits n) → x ∈ᵇ allBits n ≡ true
∈-allBits []          = Eq.refl
∈-allBits {suc n} (false ∷ x) =
  Eq.trans (∈ᵇ-++ (false ∷ x) (map (false ∷_) (allBits n)) (map (true ∷_) (allBits n)))
    (Eq.cong (_∨ ((false ∷ x) ∈ᵇ map (true ∷_) (allBits n)))
      (Eq.trans (∈ᵇ-map∷ false x (allBits n)) (∈-allBits x)))
∈-allBits {suc n} (true ∷ x) =
  Eq.trans (∈ᵇ-++ (true ∷ x) (map (false ∷_) (allBits n)) (map (true ∷_) (allBits n)))
    (Eq.trans (Eq.cong (_∨ ((true ∷ x) ∈ᵇ map (true ∷_) (allBits n))) (∈ᵇ-map∷-≢ true false x (allBits n) (λ ())))
      (Eq.trans (∈ᵇ-map∷ true x (allBits n)) (∈-allBits x)))

-- No string is enumerated twice: each element is absent from its tail.
Nodup : List (Bits n) → Set
Nodup []       = ⊤
Nodup (c ∷ cs) = (c ∈ᵇ cs ≡ false) × Nodup cs

private
  nodup-map : ∀ a (cs : List (Bits n)) → Nodup cs → Nodup (map (a ∷_) cs)
  nodup-map a []       _         = tt
  nodup-map a (c ∷ cs) (nc , nd) = Eq.trans (∈ᵇ-map∷ a c cs) nc , nodup-map a cs nd

  nodup-++ : (xs ys : List (Bits n)) → Nodup xs → Nodup ys →
             (∀ x → x ∈ᵇ xs ≡ true → x ∈ᵇ ys ≡ false) → Nodup (xs ++ ys)
  nodup-++ []       ys _         ny dis = ny
  nodup-++ (c ∷ xs) ys (nc , nx) ny dis =
    Eq.trans (∈ᵇ-++ c xs ys) (Eq.cong₂ _∨_ nc (dis c (Eq.cong (_∨ (c ∈ᵇ xs)) (eqB-refl c)))) ,
    nodup-++ xs ys nx ny (λ x p → dis x (Eq.cong (eqB x c ∨_) p ∙∙ ∨-true (eqB x c)))
    where
    _∙∙_ = Eq.trans
    ∨-true : ∀ a → a ∨ true ≡ true
    ∨-true true  = Eq.refl
    ∨-true false = Eq.refl

allBits-nodup : ∀ n → Nodup (allBits n)
allBits-nodup zero    = Eq.refl , tt
allBits-nodup (suc n) =
  nodup-++ (map (false ∷_) (allBits n)) (map (true ∷_) (allBits n))
    (nodup-map false (allBits n) (allBits-nodup n))
    (nodup-map true  (allBits n) (allBits-nodup n))
    dis
  where
  dis : ∀ x → x ∈ᵇ map (false ∷_) (allBits n) ≡ true → x ∈ᵇ map (true ∷_) (allBits n) ≡ false
  dis (false ∷ x) _ = ∈ᵇ-map∷-≢ false true x (allBits n) (λ ())
  dis (true ∷ x)  p = ⊥-elim (true≢false (Eq.trans (Eq.sym p) (∈ᵇ-map∷-≢ true false x (allBits n) (λ ()))))
    where
    true≢false : true ≢ false
    true≢false ()
