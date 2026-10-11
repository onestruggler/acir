------------------------------------------------------------------------
-- Presentations of groups
--
-- The two smallest naturals a Hadamard letter misses
--
-- Equation (42) splits `H_[a,b] H_[c,d]` over `twoSmallest a b c d`,
-- the two smallest naturals not among its four indices, found by a
-- search with fuel 5 from 0.  Every use of (42) needs to know that
-- those two really do miss the four, and that they are indices — that
-- is, below 8, hence below every width.
--
-- Neither follows from the search on its own: it would have to be
-- known that four blocked values cannot fill six consecutive slots,
-- which is a pigeonhole.  `Avoid` supplies exactly that — deleting the
-- four from 0 … 7 leaves four, the first at most 4 and the second at
-- most 5 — and the search, which stops at the first unblocked value,
-- can only stop at or before one of those.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Small where

open import Data.Bool using (Bool ; true ; false ; _∨_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_ ; s≤s ; z≤n ; _≡ᵇ_)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; ≤-reflexive ; m≤n⇒m≤1+n ; m≤m+n ; m≤n+m
       ; +-identityʳ ; +-suc ; ≤∧≢⇒< ; ≤⇒≯ ; ≮⇒≥ ; _≟_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

open import Examples.Groups.Real-Clifford+CH.Encoding using (twoSmallest)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma using (≡ᵇ-t ; ≡ᵇ-f)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Avoid
  using (avoid4 ; module Four ; here ; there)

------------------------------------------------------------------------
-- `Encoding`'s own search, repeated
--
-- `free` is private there; the two definitions agree by reduction.

blk : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
blk a b c d v = (v ≡ᵇ a) ∨ (v ≡ᵇ b) ∨ (v ≡ᵇ c) ∨ (v ≡ᵇ d)

fr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
fr zero       v a b c d = v
fr (suc fuel) v a b c d =
  if blk a b c d v then fr fuel (suc v) a b c d else v

ts≡ : ∀ (a b c d : ℕ) →
      twoSmallest a b c d
      ≡ (fr 5 0 a b c d , fr 5 (suc (fr 5 0 a b c d)) a b c d)
ts≡ a b c d = Eq.refl

------------------------------------------------------------------------
-- Reading the blocking test

private
  t≢f : true ≢ false
  t≢f ()

  ∨-f : ∀ (x y : Bool) → (x ∨ y) ≡ false → (x ≡ false) × (y ≡ false)
  ∨-f false y e = Eq.refl , e

  ne-of : ∀ (u w : ℕ) → (u ≡ᵇ w) ≡ false → u ≢ w
  ne-of u w hf e = t≢f (Eq.trans (Eq.sym (≡ᵇ-t u w e)) hf)

blk-f : ∀ (a b c d v : ℕ) → v ≢ a → v ≢ b → v ≢ c → v ≢ d →
        blk a b c d v ≡ false
blk-f a b c d v na nb nc nd
  rewrite ≡ᵇ-f v a na | ≡ᵇ-f v b nb | ≡ᵇ-f v c nc | ≡ᵇ-f v d nd = Eq.refl

blk-≢ : ∀ (a b c d v : ℕ) → blk a b c d v ≡ false →
        (v ≢ a) × (v ≢ b) × (v ≢ c) × (v ≢ d)
blk-≢ a b c d v h =
    ne-of v a (proj₁ one)
  , ne-of v b (proj₁ two)
  , ne-of v c (proj₁ three)
  , ne-of v d (proj₂ three)
  where
  one : ((v ≡ᵇ a) ≡ false) × (((v ≡ᵇ b) ∨ (v ≡ᵇ c) ∨ (v ≡ᵇ d)) ≡ false)
  one = ∨-f _ _ h

  two : ((v ≡ᵇ b) ≡ false) × (((v ≡ᵇ c) ∨ (v ≡ᵇ d)) ≡ false)
  two = ∨-f _ _ (proj₂ one)

  three : ((v ≡ᵇ c) ≡ false) × ((v ≡ᵇ d) ≡ false)
  three = ∨-f _ _ (proj₂ two)

------------------------------------------------------------------------
-- What the search does

-- It never goes back, and never past its fuel.
fr-≥ : ∀ (k v a b c d : ℕ) → v ≤ fr k v a b c d
fr-≥ zero    v a b c d = ≤-refl
fr-≥ (suc k) v a b c d with blk a b c d v
... | true  = ≤-trans (m≤n⇒m≤1+n ≤-refl) (fr-≥ k (suc v) a b c d)
... | false = ≤-refl

fr-≤ : ∀ (k v a b c d : ℕ) → fr k v a b c d ≤ v + k
fr-≤ zero    v a b c d = ≤-reflexive (Eq.sym (+-identityʳ v))
fr-≤ (suc k) v a b c d with blk a b c d v
... | true  = ≤-trans (fr-≤ k (suc v) a b c d)
                      (≤-reflexive (Eq.sym (+-suc v k)))
... | false = m≤m+n v (suc k)

-- Everything it passed was blocked.
fr-low : ∀ (k v a b c d w : ℕ) → v ≤ w → w < fr k v a b c d →
         blk a b c d w ≡ true
fr-low zero    v a b c d w le lt = ⊥-elim (≤⇒≯ le lt)
fr-low (suc k) v a b c d w le lt = go (blk a b c d v) Eq.refl lt
  where
  go : ∀ (t : Bool) → blk a b c d v ≡ t →
       w < (if t then fr k (suc v) a b c d else v) → blk a b c d w ≡ true
  go true  eq lt′ = dec (v ≟ w)
    where
    dec : Dec (v ≡ w) → blk a b c d w ≡ true
    dec (yes e) = Eq.subst (λ u → blk a b c d u ≡ true) e eq
    dec (no ne) = fr-low k (suc v) a b c d w (≤∧≢⇒< le ne) lt′
  go false eq lt′ = ⊥-elim (≤⇒≯ le lt′)

-- And where it stopped early it stopped on an unblocked value.
fr-stop : ∀ (k v a b c d : ℕ) → fr k v a b c d < v + k →
          blk a b c d (fr k v a b c d) ≡ false
fr-stop zero    v a b c d lt =
  ⊥-elim (≤⇒≯ (≤-reflexive (+-identityʳ v)) lt)
fr-stop (suc k) v a b c d lt = go (blk a b c d v) Eq.refl lt
  where
  go : ∀ (t : Bool) → blk a b c d v ≡ t →
       (if t then fr k (suc v) a b c d else v) < v + suc k →
       blk a b c d (if t then fr k (suc v) a b c d else v) ≡ false
  go true  eq lt′ =
    fr-stop k (suc v) a b c d
      (Eq.subst (fr k (suc v) a b c d <_) (+-suc v k) lt′)
  go false eq lt′ = eq

-- So an unblocked value in the window bounds the answer, which is
-- itself unblocked.
fr-ok : ∀ (k v a b c d w : ℕ) → v ≤ w → w ≤ v + k → blk a b c d w ≡ false →
        (blk a b c d (fr k v a b c d) ≡ false) × (fr k v a b c d ≤ w)
fr-ok k v a b c d w le hi fw = unblocked , r≤w
  where
  r≤w : fr k v a b c d ≤ w
  r≤w = ≮⇒≥ (λ lt → t≢f (Eq.trans (Eq.sym (fr-low k v a b c d w le lt)) fw))

  unblocked : blk a b c d (fr k v a b c d) ≡ false
  unblocked = dec (fr k v a b c d ≟ w)
    where
    dec : Dec (fr k v a b c d ≡ w) → blk a b c d (fr k v a b c d) ≡ false
    dec (yes e) = Eq.subst (λ u → blk a b c d u ≡ false) (Eq.sym e) fw
    dec (no ne) = fr-stop k v a b c d (≤-trans (≤∧≢⇒< r≤w ne) hi)

------------------------------------------------------------------------
-- The two smallest missed naturals

record Small (a b c d : ℕ) : Set where
  field
    e f : ℕ
    e<8 : e < 8
    f<8 : f < 8
    e<f : e < f
    ea  : e ≢ a
    eb  : e ≢ b
    ec  : e ≢ c
    ed  : e ≢ d
    fa  : f ≢ a
    fb  : f ≢ b
    fc  : f ≢ c
    fd  : f ≢ d
    ts  : twoSmallest a b c d ≡ (e , f)

small : ∀ (a b c d : ℕ) → Small a b c d
small a b c d = record
  { e = E ; f = F
  ; e<8 = s≤s (≤-trans (proj₂ okE) (≤-trans A.h₀≤4 4≤7))
  ; f<8 = s≤s (≤-trans (proj₂ okF) (≤-trans A.h₁≤5 5≤7))
  ; e<f = fr-≥ 5 (suc E) a b c d
  ; ea = proj₁ freeE
  ; eb = proj₁ (proj₂ freeE)
  ; ec = proj₁ (proj₂ (proj₂ freeE))
  ; ed = proj₂ (proj₂ (proj₂ freeE))
  ; fa = proj₁ freeF
  ; fb = proj₁ (proj₂ freeF)
  ; fc = proj₁ (proj₂ (proj₂ freeF))
  ; fd = proj₂ (proj₂ (proj₂ freeF))
  ; ts = Eq.refl
  }
  where
  module A = Four (avoid4 (a ∷ b ∷ c ∷ d ∷ []) ≤-refl)

  4≤7 : 4 ≤ 7
  4≤7 = s≤s (s≤s (s≤s (s≤s z≤n)))

  5≤7 : 5 ≤ 7
  5≤7 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

  -- The two survivors miss all four indices.
  h₀-free : blk a b c d A.h₀ ≡ false
  h₀-free = blk-f a b c d A.h₀ (A.h₀∉ here) (A.h₀∉ (there here))
              (A.h₀∉ (there (there here)))
              (A.h₀∉ (there (there (there here))))

  h₁-free : blk a b c d A.h₁ ≡ false
  h₁-free = blk-f a b c d A.h₁ (A.h₁∉ here) (A.h₁∉ (there here))
              (A.h₁∉ (there (there here)))
              (A.h₁∉ (there (there (there here))))

  E F : ℕ
  E = fr 5 0 a b c d
  F = fr 5 (suc E) a b c d

  okE : (blk a b c d E ≡ false) × (E ≤ A.h₀)
  okE = fr-ok 5 0 a b c d A.h₀ z≤n
          (≤-trans A.h₀≤4 (m≤n⇒m≤1+n ≤-refl)) h₀-free

  okF : (blk a b c d F ≡ false) × (F ≤ A.h₁)
  okF = fr-ok 5 (suc E) a b c d A.h₁
          (≤-trans (s≤s (proj₂ okE)) A.h₀<h₁)
          (≤-trans A.h₁≤5 (m≤n+m 5 (suc E))) h₁-free

  freeE : (E ≢ a) × (E ≢ b) × (E ≢ c) × (E ≢ d)
  freeE = blk-≢ a b c d E (proj₁ okE)

  freeF : (F ≢ a) × (F ≢ b) × (F ≢ c) × (F ≢ d)
  freeF = blk-≢ a b c d F (proj₁ okF)
