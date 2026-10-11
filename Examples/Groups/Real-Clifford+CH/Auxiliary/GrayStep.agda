------------------------------------------------------------------------
-- Presentations of groups
--
-- Bit operations for walking along the Gray code (Clément, the proof of
-- Lemma 8.4, Appendix E.2)
--
-- Lemma 8.4 is an induction along the Gray code between two codes that
-- differ in one bit t.  Read in binary (Gray.toBits, least significant
-- bit first) the two indices differ by complementing the bits 0 … t,
-- `compl t` (`gray-compl`: this flips exactly the bit t of the code),
-- the smaller one having 0 at t (`lt-compl`).  Going one index up is
-- `incr` (`toBits-suc`), which complements the bits up to the first 0
-- (`incr-first`); so between two such indices a and b, both a + 1 and
-- b − 1 are again such a pair, the step of the induction
-- (`firstZero-cc`, `compl-comm`, `compl-invol`, `incr-inj`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Bool.Properties using (not-involutive)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (suc-injective ; ≤-trans ; ≤-refl ; +-monoˡ-≤ ; *-monoʳ-≤ ; *-suc ; m≤n+m)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Vec.Properties using (∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (parity ; half ; bit ; toBits ; fromBits ; hd ; gray)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The operations

-- Flip the bit i; complement the bits 0 … i.
flipAt compl : ℕ → Bits n → Bits n
flipAt i       []      = []
flipAt zero    (b ∷ s) = not b ∷ s
flipAt (suc i) (b ∷ s) = b ∷ flipAt i s
compl i       []      = []
compl zero    (b ∷ s) = not b ∷ s
compl (suc i) (b ∷ s) = not b ∷ compl i s

-- One more, in binary.
incr : Bits n → Bits n
incr []          = []
incr (false ∷ s) = true ∷ s
incr (true ∷ s)  = false ∷ incr s

-- The position of the first 0.
firstZero : Bits n → ℕ
firstZero []          = zero
firstZero (false ∷ s) = zero
firstZero (true ∷ s)  = suc (firstZero s)

------------------------------------------------------------------------
-- Complement and the code

private
  not-xor : ∀ b c → not b xor c ≡ not (b xor c)
  not-xor true  c = Eq.sym (not-involutive c)
  not-xor false c = Eq.refl

  xor-nn : ∀ b c → not b xor not c ≡ b xor c
  xor-nn true  c = Eq.refl
  xor-nn false c = not-involutive c

hd-compl : ∀ i c (s : Bits n) → hd (compl i (c ∷ s)) ≡ not c
hd-compl zero    c s = Eq.refl
hd-compl (suc i) c s = Eq.refl

-- Complementing the bits 0 … i flips the bit i of the code.
gray-compl : ∀ i (A : Bits n) → i < n → gray (compl i A) ≡ flipAt i (gray A)
gray-compl i       []          ()
gray-compl zero    (b ∷ s)     _       = Eq.cong (_∷ gray s) (not-xor b (hd s))
gray-compl (suc i) (b ∷ [])    (s≤s ())
gray-compl (suc i) (b ∷ c ∷ s) (s≤s p) =
  Eq.cong₂ _∷_ (Eq.trans (Eq.cong (not b xor_) (hd-compl i c s)) (xor-nn b c))
               (gray-compl i (c ∷ s) p)

compl-invol : ∀ i (s : Bits n) → compl i (compl i s) ≡ s
compl-invol i       []      = Eq.refl
compl-invol zero    (b ∷ s) = Eq.cong (_∷ s) (not-involutive b)
compl-invol (suc i) (b ∷ s) = Eq.cong₂ _∷_ (not-involutive b) (compl-invol i s)

compl-comm : ∀ i j (s : Bits n) → compl i (compl j s) ≡ compl j (compl i s)
compl-comm i       j       []      = Eq.refl
compl-comm zero    zero    (b ∷ s) = Eq.refl
compl-comm zero    (suc j) (b ∷ s) = Eq.refl
compl-comm (suc i) zero    (b ∷ s) = Eq.refl
compl-comm (suc i) (suc j) (b ∷ s) = Eq.cong (not (not b) ∷_) (compl-comm i j s)

flipAt-comm : ∀ i j (s : Bits n) → flipAt i (flipAt j s) ≡ flipAt j (flipAt i s)
flipAt-comm i       j       []      = Eq.refl
flipAt-comm zero    zero    (b ∷ s) = Eq.refl
flipAt-comm zero    (suc j) (b ∷ s) = Eq.refl
flipAt-comm (suc i) zero    (b ∷ s) = Eq.refl
flipAt-comm (suc i) (suc j) (b ∷ s) = Eq.cong (b ∷_) (flipAt-comm i j s)

flipAt-invol : ∀ i (s : Bits n) → flipAt i (flipAt i s) ≡ s
flipAt-invol i       []      = Eq.refl
flipAt-invol zero    (b ∷ s) = Eq.cong (_∷ s) (not-involutive b)
flipAt-invol (suc i) (b ∷ s) = Eq.cong (b ∷_) (flipAt-invol i s)

-- The bits compl i leaves alone, and the one it flips.
lookup-compl-hi : ∀ i j (s : Bits n) → i < j → lookupℕ j (compl i s) ≡ lookupℕ j s
lookup-compl-hi i       j       []      _       = Eq.refl
lookup-compl-hi i       zero    (b ∷ s) ()
lookup-compl-hi zero    (suc j) (b ∷ s) _       = Eq.refl
lookup-compl-hi (suc i) (suc j) (b ∷ s) (s≤s p) = lookup-compl-hi i j s p

lookup-compl-self : ∀ i (s : Bits n) → i < n → lookupℕ i (compl i s) ≡ not (lookupℕ i s)
lookup-compl-self i       []      ()
lookup-compl-self zero    (b ∷ s) _       = Eq.refl
lookup-compl-self (suc i) (b ∷ s) (s≤s p) = lookup-compl-self i s p

------------------------------------------------------------------------
-- The smaller of the two indices has 0 at i

private
  bit≤1 : ∀ b → bit b ≤ 1
  bit≤1 true  = s≤s z≤n
  bit≤1 false = z≤n

  step< : ∀ b {x y} → x < y → bit b + 2 * x < bit (not b) + 2 * y
  step< b {x} {y} x<y =
    ≤-trans (s≤s (+-monoˡ-≤ (2 * x) (bit≤1 b)))
      (≤-trans (Eq.subst (_≤ 2 * y) (*-suc 2 x) (*-monoʳ-≤ 2 x<y))
               (m≤n+m (2 * y) (bit (not b))))

lt-compl : ∀ i (A : Bits n) → lookupℕ i A ≡ false → i < n → fromBits A < fromBits (compl i A)
lt-compl i       []          _  ()
lt-compl zero    (false ∷ s) _  _       = ≤-refl
lt-compl zero    (true ∷ s)  () _
lt-compl (suc i) (b ∷ s)     e  (s≤s p) = step< b (lt-compl i s e p)

------------------------------------------------------------------------
-- One more

private
  half-f : ∀ k → parity k ≡ false → half (suc k) ≡ half k
  half-f zero          _ = Eq.refl
  half-f (suc zero)    ()
  half-f (suc (suc k)) e = Eq.cong suc (half-f k (Eq.trans (Eq.sym (not-involutive (parity k))) e))

  half-t : ∀ k → parity k ≡ true → half (suc k) ≡ suc (half k)
  half-t zero          ()
  half-t (suc zero)    _ = Eq.refl
  half-t (suc (suc k)) e = Eq.cong suc (half-t k (Eq.trans (Eq.sym (not-involutive (parity k))) e))

toBits-suc : ∀ n k → toBits n (suc k) ≡ incr (toBits n k)
toBits-suc zero    k = Eq.refl
toBits-suc (suc n) k = step (parity k) Eq.refl
  where
  step : ∀ b → parity k ≡ b →
         not (parity k) ∷ toBits n (half (suc k)) ≡ incr (parity k ∷ toBits n (half k))
  step false e rewrite e = Eq.cong (true ∷_) (Eq.cong (toBits n) (half-f k e))
  step true  e rewrite e =
    Eq.cong (false ∷_) (Eq.trans (Eq.cong (toBits n) (half-t k e)) (toBits-suc n (half k)))

incr-inj : ∀ {s s′ : Bits n} → incr s ≡ incr s′ → s ≡ s′
incr-inj {s = []}        {[]}         _ = Eq.refl
incr-inj {s = false ∷ s} {false ∷ s′} e = Eq.cong (false ∷_) (∷-injectiveʳ e)
incr-inj {s = false ∷ s} {true ∷ s′}  ()
incr-inj {s = true ∷ s}  {false ∷ s′} ()
incr-inj {s = true ∷ s}  {true ∷ s′}  e = Eq.cong (true ∷_) (incr-inj (∷-injectiveʳ e))

-- Adding one complements the bits up to the first 0.
incr-first : (s : Bits n) → firstZero s < n → incr s ≡ compl (firstZero s) s
incr-first []          ()
incr-first (false ∷ s) _       = Eq.refl
incr-first (true ∷ s)  (s≤s p) = Eq.cong (false ∷_) (incr-first s p)

-- The first 0 comes no later than any 0.
firstZero-≤ : ∀ t (s : Bits n) → lookupℕ t s ≡ false → t < n → firstZero s ≤ t
firstZero-≤ t       []          _  ()
firstZero-≤ t       (false ∷ s) _  _       = z≤n
firstZero-≤ zero    (true ∷ s)  () _
firstZero-≤ (suc t) (true ∷ s)  e  (s≤s p) = s≤s (firstZero-≤ t s e p)

-- After complementing up to the first 0 and then up to a later t, the
-- first 0 is where it was.
firstZero-cc : ∀ z t (s : Bits n) → firstZero s ≡ z → z < t → t < n →
               firstZero (compl t (compl z s)) ≡ z
firstZero-cc z       t       []          _  _       ()
firstZero-cc zero    zero    (b ∷ s)     _  ()      _
firstZero-cc zero    (suc t) (false ∷ s) _  _       _       = Eq.refl
firstZero-cc zero    (suc t) (true ∷ s)  () _       _
firstZero-cc (suc z) t       (false ∷ s) () _       _
firstZero-cc (suc z) zero    (true ∷ s)  _  ()      _
firstZero-cc (suc z) (suc t) (true ∷ s)  e  (s≤s p) (s≤s q) =
  Eq.cong suc (firstZero-cc z t s (suc-injective e) p q)
