------------------------------------------------------------------------
-- Presentations of groups
--
-- The letters of the auxiliary generators as row operations
--
-- Checks8 decides Figure 8 on three qubits by comparing the stored
-- matrices of words over P.  Read as dense products of 8 × 8 tries,
-- every letter costs a product summing eight terms for each of its 64
-- entries.  But a sign letter negates a row, an exchange swaps two, and
-- a Hadamard letter replaces two rows by their sum and difference and
-- scales the others by √2: applied on the left of a trie of rows each
-- costs one operation per entry, as the gates do in Evaluation.
-- `negR-ok`, `swapR-ok` and `hadR-ok` say that each row operation is
-- the letter's operator (Auxiliary.Matrices) on the left, at every
-- width and for every pair of indices, equal or not.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Rows where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Evaluation
  using (Rows ; rix ; mapT ; zipT ; get-map ; get-zip ; _⊙ʳ_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices
  using (eqB ; negOp ; swapOp ; hadOp)

import Algebra.Properties.Ring as RingProps
open RingProps (CommutativeRing.ring +-*-commutativeRing) using (-‿distribˡ-*)

private
  variable
    k c : ℕ

------------------------------------------------------------------------
-- Equality of bit vectors, decided

eqB-≡ : (x y : Bits k) → eqB x y ≡ true → x ≡ y
eqB-≡ []          []          _ = Eq.refl
eqB-≡ (true ∷ x)  (true ∷ y)  e = Eq.cong (true ∷_) (eqB-≡ x y e)
eqB-≡ (false ∷ x) (false ∷ y) e = Eq.cong (false ∷_) (eqB-≡ x y e)
eqB-≡ (true ∷ x)  (false ∷ y) ()
eqB-≡ (false ∷ x) (true ∷ y)  ()

eqB-refl : (x : Bits k) → eqB x x ≡ true
eqB-refl []          = Eq.refl
eqB-refl (true ∷ x)  = eqB-refl x
eqB-refl (false ∷ x) = eqB-refl x

eqB-sym : (x y : Bits k) → eqB x y ≡ eqB y x
eqB-sym []          []          = Eq.refl
eqB-sym (true ∷ x)  (true ∷ y)  = eqB-sym x y
eqB-sym (false ∷ x) (false ∷ y) = eqB-sym x y
eqB-sym (true ∷ x)  (false ∷ y) = Eq.refl
eqB-sym (false ∷ x) (true ∷ y)  = Eq.refl

-- The delta as an indicator.
δ-ind : (i z : Bits k) → δb i z ≡ (if eqB z i then 1# else 0#)
δ-ind []          []          = Eq.refl
δ-ind (true ∷ i)  (true ∷ z)  = δ-ind i z
δ-ind (false ∷ i) (false ∷ z) = δ-ind i z
δ-ind (true ∷ i)  (false ∷ z) = Eq.refl
δ-ind (false ∷ i) (true ∷ z)  = Eq.refl

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  -- Two indices equal to one bit vector are equal.
  apart : (i j z : Bits k) → eqB j i ≡ false → eqB z i ≡ true → eqB z j ≡ true → ⊥
  apart i j z ji zi zj =
    true≢false (Eq.trans (Eq.sym (Eq.trans (Eq.cong₂ eqB (Eq.sym (eqB-≡ z j zj)) (Eq.sym (eqB-≡ z i zi)))
                                           (eqB-refl z)))
                         ji)

  if-true : ∀ {A : Set} {b} {t e : A} → b ≡ true → (if b then t else e) ≡ t
  if-true Eq.refl = Eq.refl

  if-false : ∀ {A : Set} {b} {t e : A} → b ≡ false → (if b then t else e) ≡ e
  if-false Eq.refl = Eq.refl

------------------------------------------------------------------------
-- Sums against deltas

  Σ-cδ : (a : 𝔽) (x : Bits k) (f : Bits k → 𝔽) → Σb (λ z → (a * δb x z) * f z) ≡ a * f x
  Σ-cδ a x f =
    Eq.trans (Σ-cong {f = λ z → (a * δb x z) * f z} {g = λ z → a * (δb x z * f z)}
                     (λ z → *-assoc a (δb x z) (f z)))
      (Eq.trans (Σ-scaleˡ a (λ z → δb x z * f z)) (Eq.cong (a *_) (Σ-δˡ x f)))

  Σ-δδ : (a : 𝔽) (i j : Bits k) (f : Bits k → 𝔽) →
         Σb (λ z → (δb i z + a * δb j z) * f z) ≡ f i + a * f j
  Σ-δδ a i j f =
    Eq.trans (Σ-cong {f = λ z → (δb i z + a * δb j z) * f z}
                     {g = λ z → δb i z * f z + (a * δb j z) * f z}
                     (λ z → *-distribʳ-+ (f z) (δb i z) (a * δb j z)))
      (Eq.trans (Σ-add (λ z → δb i z * f z) (λ z → (a * δb j z) * f z))
        (Eq.cong₂ _+_ (Σ-δˡ i f) (Σ-cδ a j f)))

  neg : ∀ a → -1# * a ≡ - a
  neg a = Eq.trans (Eq.sym (-‿distribˡ-* 1# a)) (-‿cong (*-identityˡ a))

------------------------------------------------------------------------
-- Operations on one row, every entry forced (Ring.strict)

negRow : ∀ c → Tab c 𝔽 → Tab c 𝔽
negRow c = mapT c (λ a → strict (- a))

scRow : ∀ c → 𝔽 → Tab c 𝔽 → Tab c 𝔽
scRow c s = mapT c (λ a → strict (s * a))

addRow subRow : ∀ c → Tab c 𝔽 → Tab c 𝔽 → Tab c 𝔽
addRow c = zipT c (λ a b → strict (a + b))
subRow c = zipT c (λ a b → strict (a - b))

------------------------------------------------------------------------
-- The three letters

-- A sign: the row at i negated.
negIf : ∀ c → Bool → Tab c 𝔽 → Tab c 𝔽
negIf c true  r = negRow c r
negIf c false r = r

negR : ∀ {k} c → Bits k → Rows k c → Rows k c
negR {k} c i R = tab k (λ x → negIf c (eqB x i) (get R x))

-- An exchange: the rows at i and j swapped (swapOp's index map).
σ : Bits k → Bits k → Bits k → Bits k
σ i j x = if eqB x i then j else if eqB x j then i else x

swapR : ∀ {k} c → Bits k → Bits k → Rows k c → Rows k c
swapR {k} c i j R = tab k (λ x → get R (σ i j x))

-- A Hadamard: at i the sum of the rows at i and j (just the row at i
-- if j = i), at j their difference, and √2 times the row elsewhere.
-- The flags are x = i, x = j and j = i.
hadRow : ∀ c → Bool → Bool → Bool → Tab c 𝔽 → Tab c 𝔽 → Tab c 𝔽 → Tab c 𝔽
hadRow c true  _     true  ri rj rx = ri
hadRow c true  _     false ri rj rx = addRow c ri rj
hadRow c false true  _     ri rj rx = subRow c ri rj
hadRow c false false _     ri rj rx = scRow c √2 rx

hadR : ∀ {k} c → Bits k → Bits k → Rows k c → Rows k c
hadR {k} c i j R =
  tab k (λ x → hadRow c (eqB x i) (eqB x j) (eqB j i) (get R i) (get R j) (get R x))

------------------------------------------------------------------------
-- Correctness: each row operation is its letter's operator on the left

negIf-ok : ∀ c b (r : Tab c 𝔽) y → get (negIf c b r) y ≡ (if b then -1# else 1#) * get r y
negIf-ok c true  r y =
  Eq.trans (get-map c (λ a → strict (- a)) r y)
    (Eq.trans (strict-id _) (Eq.sym (neg (get r y))))
negIf-ok c false r y = Eq.sym (*-identityˡ (get r y))

negR-ok : ∀ {k} c (i : Bits k) (R : Rows k c) x y →
          rix (negR c i R) x y ≡ (negOp i ⊙ʳ rix R) x y
negR-ok {k} c i R x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-tab k (λ u → negIf c (eqB u i) (get R u)) x))
    (Eq.trans (negIf-ok c (eqB x i) (get R x) y)
      (Eq.sym (Σ-cδ (if eqB x i then -1# else 1#) x (λ z → rix R z y))))

swapR-ok : ∀ {k} c (i j : Bits k) (R : Rows k c) x y →
           rix (swapR c i j R) x y ≡ (swapOp i j ⊙ʳ rix R) x y
swapR-ok {k} c i j R x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-tab k (λ u → get R (σ i j u)) x))
    (Eq.sym (Σ-δˡ (σ i j x) (λ z → rix R z y)))

-- The value of a Hadamard row, entry by entry.
hadVal : Bool → Bool → Bool → 𝔽 → 𝔽 → 𝔽 → 𝔽
hadVal true  _     true  a b r = a
hadVal true  _     false a b r = a + b
hadVal false true  _     a b r = a - b
hadVal false false _     a b r = √2 * r

hadRow-ok : ∀ c bi bj bji (ri rj rx : Tab c 𝔽) y →
            get (hadRow c bi bj bji ri rj rx) y ≡ hadVal bi bj bji (get ri y) (get rj y) (get rx y)
hadRow-ok c true  _     true  ri rj rx y = Eq.refl
hadRow-ok c true  _     false ri rj rx y =
  Eq.trans (get-zip c (λ a b → strict (a + b)) ri rj y) (strict-id _)
hadRow-ok c false true  _     ri rj rx y =
  Eq.trans (get-zip c (λ a b → strict (a - b)) ri rj y) (strict-id _)
hadRow-ok c false false _     ri rj rx y =
  Eq.trans (get-map c (λ a → strict (√2 * a)) rx y) (strict-id _)

private
  -- The coefficients of a Hadamard row as deltas.
  coef-ii : (i j z : Bits k) → eqB j i ≡ true →
            (if eqB z i then 1# else if eqB z j then 1# else 0#) ≡ δb i z + 0# * δb j z
  coef-ii i j z ji rewrite eqB-≡ j i ji | δ-ind i z with eqB z i
  ... | true  = Eq.refl
  ... | false = Eq.refl

  coef-ij : (i j z : Bits k) → eqB j i ≡ false →
            (if eqB z i then 1# else if eqB z j then 1# else 0#) ≡ δb i z + 1# * δb j z
  coef-ij i j z ji rewrite δ-ind i z | δ-ind j z with eqB z i in zi | eqB z j in zj
  ... | true  | true  = ⊥-elim (apart i j z ji zi zj)
  ... | true  | false = Eq.refl
  ... | false | true  = Eq.refl
  ... | false | false = Eq.refl

  coef-ji : (i j z : Bits k) → eqB j i ≡ false →
            (if eqB z i then 1# else if eqB z j then -1# else 0#) ≡ δb i z + -1# * δb j z
  coef-ji i j z ji rewrite δ-ind i z | δ-ind j z with eqB z i in zi | eqB z j in zj
  ... | true  | true  = ⊥-elim (apart i j z ji zi zj)
  ... | true  | false = Eq.refl
  ... | false | true  = Eq.refl
  ... | false | false = Eq.refl

  -- A sum against the row x of a Hadamard, given the coefficients.
  via : ∀ {k} (i j x : Bits k) (f : Bits k → 𝔽) (a : 𝔽) →
        (∀ z → hadOp i j x z ≡ δb i z + a * δb j z) →
        Σb (λ z → hadOp i j x z * f z) ≡ f i + a * f j
  via i j x f a e =
    Eq.trans (Σ-cong {f = λ z → hadOp i j x z * f z} {g = λ z → (δb i z + a * δb j z) * f z}
                     (λ z → Eq.cong (_* f z) (e z)))
             (Σ-δδ a i j f)

  -- The flags x = i, x = j and j = i are arguments with their
  -- equations, so that splitting on them leaves hadOp in the sum alone.
  had-sum′ : ∀ {k} (i j x : Bits k) (f : Bits k → 𝔽) bi bj bji →
             eqB x i ≡ bi → eqB x j ≡ bj → eqB j i ≡ bji →
             Σb (λ z → hadOp i j x z * f z) ≡ hadVal bi bj bji (f i) (f j) (f x)
  had-sum′ i j x f true _ true xi xj ji =
    Eq.trans (via i j x f 0# (λ z → Eq.trans (if-true xi) (coef-ii i j z ji)))
      (Eq.trans (Eq.cong (f i +_) (*-zeroˡ (f j))) (+-identityʳ (f i)))
  had-sum′ i j x f true _ false xi xj ji =
    Eq.trans (via i j x f 1# (λ z → Eq.trans (if-true xi) (coef-ij i j z ji)))
      (Eq.cong (f i +_) (*-identityˡ (f j)))
  had-sum′ i j x f false true _ xi xj ji =
    Eq.trans (via i j x f -1# (λ z → Eq.trans (if-false xi)
                                      (Eq.trans (if-true xj) (coef-ji i j z j≢i))))
      (Eq.cong (f i +_) (neg (f j)))
    where
    j≢i : eqB j i ≡ false
    j≢i = Eq.trans (Eq.cong (λ u → eqB u i) (Eq.sym (eqB-≡ x j xj))) xi
  had-sum′ i j x f false false _ xi xj ji =
    Eq.trans (Σ-cong {f = λ z → hadOp i j x z * f z} {g = λ z → (√2 * δb x z) * f z}
                     (λ z → Eq.cong (_* f z) (Eq.trans (if-false xi) (if-false xj))))
             (Σ-cδ √2 x f)

  had-sum : ∀ {k} (i j x : Bits k) (f : Bits k → 𝔽) →
            Σb (λ z → hadOp i j x z * f z) ≡ hadVal (eqB x i) (eqB x j) (eqB j i) (f i) (f j) (f x)
  had-sum i j x f = had-sum′ i j x f (eqB x i) (eqB x j) (eqB j i) Eq.refl Eq.refl Eq.refl

hadR-ok : ∀ {k} c (i j : Bits k) (R : Rows k c) x y →
          rix (hadR c i j R) x y ≡ (hadOp i j ⊙ʳ rix R) x y
hadR-ok {k} c i j R x y =
  Eq.trans (Eq.cong (λ t → get t y)
             (get-tab k (λ u → hadRow c (eqB u i) (eqB u j) (eqB j i) (get R i) (get R j) (get R u)) x))
    (Eq.trans (hadRow-ok c (eqB x i) (eqB x j) (eqB j i) (get R i) (get R j) (get R x) y)
      (Eq.sym (had-sum i j x (λ z → rix R z y))))

------------------------------------------------------------------------
-- Operators on the left of tries of rows

⊙ʳ-ext : ∀ (G : Op k) {R S : Bits k → Bits c → 𝔽} → (∀ x y → R x y ≡ S x y) →
         ∀ x y → (G ⊙ʳ R) x y ≡ (G ⊙ʳ S) x y
⊙ʳ-ext G {R} {S} e x y =
  Σ-cong {f = λ z → G x z * R z y} {g = λ z → G x z * S z y} (λ z → Eq.cong (G x z *_) (e z y))

⊙ʳ-assoc : (M N : Op k) (R : Bits k → Bits c → 𝔽) → ∀ x y →
           (M ⊙ʳ (N ⊙ʳ R)) x y ≡ ((M ⊙ N) ⊙ʳ R) x y
⊙ʳ-assoc M N R x y = begin
  Σb (λ z → M x z * Σb (λ w → N z w * R w y))
    ≡⟨ Σ-cong {f = λ z → M x z * Σb (λ w → N z w * R w y)}
              {g = λ z → Σb (λ w → (M x z * N z w) * R w y)}
              (λ z → Eq.trans (Eq.sym (Σ-scaleˡ (M x z) (λ w → N z w * R w y)))
                       (Σ-cong {f = λ w → M x z * (N z w * R w y)}
                               {g = λ w → (M x z * N z w) * R w y}
                               (λ w → Eq.sym (*-assoc (M x z) (N z w) (R w y))))) ⟩
  Σb (λ z → Σb (λ w → (M x z * N z w) * R w y))
    ≡⟨ Σ-swap (λ z w → (M x z * N z w) * R w y) ⟩
  Σb (λ w → Σb (λ z → (M x z * N z w) * R w y))
    ≡⟨ Σ-cong {f = λ w → Σb (λ z → (M x z * N z w) * R w y)}
              {g = λ w → Σb (λ z → M x z * N z w) * R w y}
              (λ w → Σ-scaleʳ (R w y) (λ z → M x z * N z w)) ⟩
  Σb (λ w → Σb (λ z → M x z * N z w) * R w y) ∎
  where open Eq.≡-Reasoning

⊙ʳ-id : (R : Bits k → Bits c → 𝔽) → ∀ x y → (Idₒ ⊙ʳ R) x y ≡ R x y
⊙ʳ-id R x y = Σ-δˡ x (λ z → R z y)
