------------------------------------------------------------------------
-- Presentations of groups
--
-- Arithmetic for the enumeration-based encoder (`Encoding.agda`).
--
-- That encoder lists its letters by natural-number indices: the bit
-- `bit a t` of an index, the partner `a + 2 ^ t`, and the letters
-- `xword`/`kword`, which test that their indices are in range and in
-- order.  The recursive encoder places a letter one width up through
-- the embeddings of the two partitions, whose index maps are
-- x ↦ 2 x + β (alternating) and x ↦ x, x ↦ 2 ^ m + x (contiguous).
-- This module proves that the bits, the partners and the letters are
-- compatible with those maps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.EncodingSemantics.EnumerationArith where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as F using (Fin ; toℕ ; fromℕ<)
import Data.Fin.Properties as FP
open import Data.Nat.Base
  using (ℕ ; zero ; suc ; _+_ ; _*_ ; _<_ ; _≤_ ; _/_ ; _%_ ; _≡ᵇ_ ; s≤s ; z≤n)
  renaming (_^_ to _^ℕ_)
open import Data.Nat.DivMod
  using (m≡m%n+[m/n]*n ; m%n<n ; [m+kn]%n≡m%n ; m*n%n≡0 ; m*n/n≡m ; +-distrib-/)
import Data.Nat.Properties as NP
import Data.Nat.Solver as ℕSolver
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec)
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (ε)

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; mono ; word)
open import Examples.Groups.CCX+HH.Encoding using (Levels ; bit ; xword ; kword)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (left ; right ; select)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (contiguous ; alternating)
open import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates
  using (contiguous-index ; alternating-index)
  renaming (bit to ⌊_⌋)

private
  module S = ℕSolver.+-*-Solver
  open S using (_:+_ ; _:*_ ; _:=_ ; con)

  variable
    m n a b c d x y : ℕ

------------------------------------------------------------------------
-- Bits

private
  binary : ∀ r → r < 2 → r ≡ ⌊ r ≡ᵇ 1 ⌋
  binary 0 _ = refl
  binary 1 _ = refl
  binary (suc (suc r)) (s≤s (s≤s ()))

  ⌊⌋≤1 : ∀ β → ⌊ β ⌋ ≤ 1
  ⌊⌋≤1 false = z≤n
  ⌊⌋≤1 true = s≤s z≤n

  ⌊⌋%2 : ∀ β → ⌊ β ⌋ % 2 + 0 < 2
  ⌊⌋%2 false = s≤s z≤n
  ⌊⌋%2 true = s≤s (s≤s z≤n)

  ⌊⌋/2 : ∀ β → ⌊ β ⌋ / 2 ≡ 0
  ⌊⌋/2 false = refl
  ⌊⌋/2 true = refl

  ⌊⌋-bit : ∀ β → (⌊ β ⌋ % 2 ≡ᵇ 1) ≡ β
  ⌊⌋-bit false = refl
  ⌊⌋-bit true = refl

  swap : ∀ a β → 2 * a + ⌊ β ⌋ ≡ ⌊ β ⌋ + a * 2
  swap a β = S.solve 2 (λ a b → con 2 :* a :+ b := b :+ a :* con 2) refl a ⌊ β ⌋

-- Every index is twice its half plus its low bit.
split : ∀ a → a ≡ 2 * (a / 2) + ⌊ bit a 0 ⌋
split a = trans (m≡m%n+[m/n]*n a 2)
  (trans (cong (_+ (a / 2) * 2) (binary (a % 2) (m%n<n a 2)))
    (S.solve 2 (λ b q → b :+ q :* con 2 := con 2 :* q :+ b) refl
      ⌊ bit a 0 ⌋ (a / 2)))

bit-low : ∀ a β → bit (2 * a + ⌊ β ⌋) 0 ≡ β
bit-low a β = trans
  (cong (_≡ᵇ 1) (trans (cong (_% 2) (swap a β)) ([m+kn]%n≡m%n ⌊ β ⌋ a 2)))
  (⌊⌋-bit β)

half : ∀ a β → (2 * a + ⌊ β ⌋) / 2 ≡ a
half a β = trans (cong (_/ 2) (swap a β))
  (trans (+-distrib-/ ⌊ β ⌋ (a * 2) lt)
    (cong₂ _+_ (⌊⌋/2 β) (m*n/n≡m a 2)))
  where
  lt : ⌊ β ⌋ % 2 + (a * 2) % 2 < 2
  lt = subst (λ r → ⌊ β ⌋ % 2 + r < 2) (sym (m*n%n≡0 a 2)) (⌊⌋%2 β)

bit-high : ∀ a β t → bit (2 * a + ⌊ β ⌋) (suc t) ≡ bit a t
bit-high a β t = cong (λ x → bit x t) (half a β)

-- A bit below the top is not changed by adding 2 ^ m.
bit-top : ∀ m a t → t < m → bit (2 ^ℕ m + a) t ≡ bit a t
bit-top zero a t ()
bit-top (suc m) a t t<m = trans (cong (λ x → bit x t) eq) (go t t<m)
  where
  q = a / 2
  β = bit a 0

  eq : 2 ^ℕ suc m + a ≡ 2 * (2 ^ℕ m + q) + ⌊ β ⌋
  eq = trans (cong (2 ^ℕ suc m +_) (split a))
    (S.solve 3 (λ p q b → con 2 :* p :+ (con 2 :* q :+ b) := con 2 :* (p :+ q) :+ b)
      refl (2 ^ℕ m) q ⌊ β ⌋)

  go : ∀ t → t < suc m → bit (2 * (2 ^ℕ m + q) + ⌊ β ⌋) t ≡ bit a t
  go zero _ = bit-low (2 ^ℕ m + q) β
  go (suc t) (s≤s t<m) = trans (bit-high (2 ^ℕ m + q) β t) (bit-top m q t t<m)

------------------------------------------------------------------------
-- Bounds

-- 2 y + b < 2 x when y < x and b ≤ 1.
twice< : ∀ y x b → y < x → b ≤ 1 → 2 * y + b < 2 * x
twice< y x b y<x b≤1 = NP.<-≤-trans lt (NP.*-monoʳ-≤ 2 y<x)
  where
  lt : 2 * y + b < 2 * suc y
  lt = subst (2 * y + b <_)
    (S.solve 1 (λ y → con 2 :* y :+ con 2 := con 2 :* (con 1 :+ y)) refl y)
    (NP.+-monoʳ-< (2 * y) (s≤s b≤1))

private
  halve< : ∀ q b x → 2 * q + b < 2 * x → q < x
  halve< q b x lt = NP.*-cancelˡ-< 2 q x (NP.≤-<-trans (NP.m≤m+n (2 * q) b) lt)

-- Adding 2 ^ t to an index whose bit t is clear stays in range.
no-carry : ∀ m a t → a < 2 ^ℕ m → t < m → bit a t ≡ false → a + 2 ^ℕ t < 2 ^ℕ m
no-carry zero a t _ () _
no-carry (suc m) a t a< t<m clear =
  subst (λ z → z + 2 ^ℕ t < 2 ^ℕ suc m) (sym (split a)) (go t t<m clear)
  where
  q = a / 2
  β = bit a 0

  q< : q < 2 ^ℕ m
  q< = halve< q ⌊ β ⌋ (2 ^ℕ m) (subst (_< 2 ^ℕ suc m) (split a) a<)

  go : ∀ t → t < suc m → bit a t ≡ false →
       2 * q + ⌊ β ⌋ + 2 ^ℕ t < 2 ^ℕ suc m
  go zero _ clear = subst (λ z → 2 * q + ⌊ z ⌋ + 1 < 2 ^ℕ suc m) (sym clear)
    (subst (_< 2 ^ℕ suc m) (S.solve 1 (λ q → con 2 :* q :+ con 1 := con 2 :* q :+ con 0 :+ con 1) refl q)
      (twice< q (2 ^ℕ m) 1 q< (s≤s z≤n)))
  go (suc t) (s≤s t<m) clear = subst (_< 2 ^ℕ suc m)
    (S.solve 3 (λ q p b → con 2 :* (q :+ p) :+ b := con 2 :* q :+ b :+ con 2 :* p) refl
      q (2 ^ℕ t) ⌊ β ⌋)
    (twice< (q + 2 ^ℕ t) (2 ^ℕ m) ⌊ β ⌋ (no-carry m q t q< t<m clear) (⌊⌋≤1 β))

------------------------------------------------------------------------
-- Index maps of the two partitions

alt-in : ∀ β → x < 2 ^ℕ m → 2 * x + ⌊ β ⌋ < 2 ^ℕ suc m
alt-in {x} {m} β lt = twice< x (2 ^ℕ m) ⌊ β ⌋ lt (⌊⌋≤1 β)

alt-out : ∀ β → ¬ (x < 2 ^ℕ m) → ¬ (2 * x + ⌊ β ⌋ < 2 ^ℕ suc m)
alt-out {x} {m} β ¬lt lt = ¬lt (halve< x ⌊ β ⌋ (2 ^ℕ m) lt)

alt-mono : ∀ β → x < y → 2 * x + ⌊ β ⌋ < 2 * y + ⌊ β ⌋
alt-mono β lt = NP.+-monoˡ-< ⌊ β ⌋ (NP.*-monoʳ-< 2 lt)

-- The step from one index to its partner commutes with x ↦ 2 x + β.
alt-step : ∀ a β y → 2 * a + ⌊ β ⌋ + 2 * y ≡ 2 * (a + y) + ⌊ β ⌋
alt-step a β y = S.solve 3
  (λ a b y → con 2 :* a :+ b :+ con 2 :* y := con 2 :* (a :+ y) :+ b) refl a ⌊ β ⌋ y

-- The enumeration's even and odd indices, in the form of the map.
even-index : ∀ i → i * 2 ≡ 2 * i + ⌊ false ⌋
even-index i = S.solve 1 (λ i → i :* con 2 := con 2 :* i :+ con 0) refl i

odd-index : ∀ i → suc (i * 2) ≡ 2 * i + ⌊ true ⌋
odd-index i = S.solve 1 (λ i → con 1 :+ i :* con 2 := con 2 :* i :+ con 1) refl i

con-left-in : x < 2 ^ℕ m → x < 2 ^ℕ suc m
con-left-in {m = m} lt = NP.<-≤-trans lt (NP.m≤m+n (2 ^ℕ m) (2 ^ℕ m + 0))

con-right-in : x < 2 ^ℕ m → 2 ^ℕ m + x < 2 ^ℕ suc m
con-right-in {m = m} lt =
  NP.+-monoʳ-< (2 ^ℕ m) (subst (_ <_) (sym (NP.+-identityʳ (2 ^ℕ m))) lt)

con-right-mono : x < y → 2 ^ℕ m + x < 2 ^ℕ m + y
con-right-mono {m = m} = NP.+-monoʳ-< (2 ^ℕ m)

------------------------------------------------------------------------
-- The letters

private
  fin< : (p : a < n) (q : b < n) → a < b → fromℕ< p F.< fromℕ< q
  fin< p q lt = subst₂ _<_ (sym (FP.toℕ-fromℕ< p)) (sym (FP.toℕ-fromℕ< q)) lt

  X-≡ : ∀ {N} {x x′ y y′ : Fin N} → x ≡ x′ → y ≡ y′ →
    .(p : x F.< y) .(p′ : x′ F.< y′) → T.X x y p ≡ T.X x′ y′ p′
  X-≡ refl refl _ _ = refl

  K-≡ : ∀ {N} {x x′ y y′ z z′ w w′ : Fin N} →
    x ≡ x′ → y ≡ y′ → z ≡ z′ → w ≡ w′ →
    .(p : x F.< y) .(q : y F.< z) .(r : z F.< w)
    .(p′ : x′ F.< y′) .(q′ : y′ F.< z′) .(r′ : z′ F.< w′) →
    T.K x y z w p q r ≡ T.K x′ y′ z′ w′ p′ q′ r′
  K-≡ refl refl refl refl _ _ _ _ _ _ = refl

xword-in : ∀ n a b (pa : a < 2 ^ℕ n) (pb : b < 2 ^ℕ n) (ab : a < b) →
  xword n a b ≡ T.X (fromℕ< pa) (fromℕ< pb) (fin< pa pb ab)
xword-in n a b pa pb ab with a NP.<? 2 ^ℕ n | b NP.<? 2 ^ℕ n
... | no ¬p | _ = ⊥-elim (¬p pa)
... | yes _ | no ¬p = ⊥-elim (¬p pb)
... | yes pa′ | yes pb′ with fromℕ< pa′ FP.<? fromℕ< pb′
...   | yes _ = refl
...   | no ¬q = ⊥-elim (¬q (fin< pa′ pb′ ab))

xword-out : ∀ n a b → ¬ (b < 2 ^ℕ n) → xword n a b ≡ ε
xword-out n a b ¬pb with a NP.<? 2 ^ℕ n | b NP.<? 2 ^ℕ n
... | no _ | _ = refl
... | yes _ | no _ = refl
... | yes _ | yes pb = ⊥-elim (¬pb pb)

kword-in : ∀ n a b c d (pa : a < 2 ^ℕ n) (pb : b < 2 ^ℕ n)
  (pc : c < 2 ^ℕ n) (pd : d < 2 ^ℕ n) (ab : a < b) (bc : b < c) (cd : c < d) →
  kword n a b c d ≡ T.K (fromℕ< pa) (fromℕ< pb) (fromℕ< pc) (fromℕ< pd)
    (fin< pa pb ab) (fin< pb pc bc) (fin< pc pd cd)
kword-in n a b c d pa pb pc pd ab bc cd
  with a NP.<? 2 ^ℕ n | b NP.<? 2 ^ℕ n | c NP.<? 2 ^ℕ n | d NP.<? 2 ^ℕ n
... | no ¬p | _ | _ | _ = ⊥-elim (¬p pa)
... | yes _ | no ¬p | _ | _ = ⊥-elim (¬p pb)
... | yes _ | yes _ | no ¬p | _ = ⊥-elim (¬p pc)
... | yes _ | yes _ | yes _ | no ¬p = ⊥-elim (¬p pd)
... | yes pa′ | yes pb′ | yes pc′ | yes pd′
    with fromℕ< pa′ FP.<? fromℕ< pb′ | fromℕ< pb′ FP.<? fromℕ< pc′
       | fromℕ< pc′ FP.<? fromℕ< pd′
...   | yes _ | yes _ | yes _ = refl
...   | no ¬q | _ | _ = ⊥-elim (¬q (fin< pa′ pb′ ab))
...   | yes _ | no ¬q | _ = ⊥-elim (¬q (fin< pb′ pc′ bc))
...   | yes _ | yes _ | no ¬q = ⊥-elim (¬q (fin< pc′ pd′ cd))

kword-out : ∀ n a b c d → ¬ (d < 2 ^ℕ n) → kword n a b c d ≡ ε
kword-out n a b c d ¬pd
  with a NP.<? 2 ^ℕ n | b NP.<? 2 ^ℕ n | c NP.<? 2 ^ℕ n | d NP.<? 2 ^ℕ n
... | no _ | _ | _ | _ = refl
... | yes _ | no _ | _ | _ = refl
... | yes _ | yes _ | no _ | _ = refl
... | yes _ | yes _ | yes _ | no _ = refl
... | yes _ | yes _ | yes _ | yes pd = ⊥-elim (¬pd pd)

------------------------------------------------------------------------
-- A letter one width up, through an embedding with index map f

module Through (m : ℕ) (e : Emb (2 ^ℕ m) (2 ^ℕ suc m)) (f : ℕ → ℕ)
  (ι-f : ∀ i → toℕ (ι e i) ≡ f (toℕ i))
  (f-in : ∀ {x} → x < 2 ^ℕ m → f x < 2 ^ℕ suc m)
  (f-mono : ∀ {x y} → x < y → f x < f y) where

  private
    at : (p : x < 2 ^ℕ m) → fromℕ< (f-in p) ≡ ι e (fromℕ< p)
    at {x} p = FP.toℕ-injective (trans (FP.toℕ-fromℕ< (f-in p))
      (sym (trans (ι-f (fromℕ< p)) (cong f (FP.toℕ-fromℕ< p)))))

  xword-up : a < b → b < 2 ^ℕ m → xword (suc m) (f a) (f b) ≡ word e (xword m a b)
  xword-up {a} {b} ab pb = trans
    (xword-in (suc m) (f a) (f b) (f-in pa) (f-in pb) (f-mono ab))
    (trans (X-≡ (at pa) (at pb) (fin< (f-in pa) (f-in pb) (f-mono ab))
                (mono e (fin< pa pb ab)))
      (cong (word e) (sym (xword-in m a b pa pb ab))))
    where pa = NP.<-trans ab pb

  kword-up : a < b → b < c → c < d → d < 2 ^ℕ m →
    kword (suc m) (f a) (f b) (f c) (f d) ≡ word e (kword m a b c d)
  kword-up {a} {b} {c} {d} ab bc cd pd = trans
    (kword-in (suc m) (f a) (f b) (f c) (f d) (f-in pa) (f-in pb) (f-in pc) (f-in pd)
      (f-mono ab) (f-mono bc) (f-mono cd))
    (trans (K-≡ (at pa) (at pb) (at pc) (at pd)
                (fin< (f-in pa) (f-in pb) (f-mono ab))
                (fin< (f-in pb) (f-in pc) (f-mono bc))
                (fin< (f-in pc) (f-in pd) (f-mono cd))
                (mono e (fin< pa pb ab)) (mono e (fin< pb pc bc)) (mono e (fin< pc pd cd)))
      (cong (word e) (sym (kword-in m a b c d pa pb pc pd ab bc cd))))
    where
    pc = NP.<-trans cd pd
    pb = NP.<-trans bc pc
    pa = NP.<-trans ab pb

------------------------------------------------------------------------
-- The two partitions

module _ (m : ℕ) (β : Bool) where

  private
    module A = Through m (select (alternating (2 ^ℕ m)) β) (λ x → 2 * x + ⌊ β ⌋)
      (alternating-index (2 ^ℕ m) β) (alt-in {m = m} β) (alt-mono β)

  -- Out of range on both sides, or the same letter.
  xword-alt : a < b →
    xword (suc m) (2 * a + ⌊ β ⌋) (2 * b + ⌊ β ⌋) ≡
    word (select (alternating (2 ^ℕ m)) β) (xword m a b)
  xword-alt {a} {b} ab = go (b NP.<? 2 ^ℕ m)
    where
    go : Dec (b < 2 ^ℕ m) →
      xword (suc m) (2 * a + ⌊ β ⌋) (2 * b + ⌊ β ⌋) ≡
      word (select (alternating (2 ^ℕ m)) β) (xword m a b)
    go (yes pb) = A.xword-up ab pb
    go (no ¬pb) = trans (xword-out (suc m) _ _ (alt-out {m = m} β ¬pb))
      (cong (word (select (alternating (2 ^ℕ m)) β)) (sym (xword-out m a b ¬pb)))

  kword-alt : a < b → b < c → c < d →
    kword (suc m) (2 * a + ⌊ β ⌋) (2 * b + ⌊ β ⌋) (2 * c + ⌊ β ⌋) (2 * d + ⌊ β ⌋) ≡
    word (select (alternating (2 ^ℕ m)) β) (kword m a b c d)
  kword-alt {a} {b} {c} {d} ab bc cd = go (d NP.<? 2 ^ℕ m)
    where
    go : Dec (d < 2 ^ℕ m) →
      kword (suc m) (2 * a + ⌊ β ⌋) (2 * b + ⌊ β ⌋) (2 * c + ⌊ β ⌋) (2 * d + ⌊ β ⌋) ≡
      word (select (alternating (2 ^ℕ m)) β) (kword m a b c d)
    go (yes pd) = A.kword-up ab bc cd pd
    go (no ¬pd) = trans (kword-out (suc m) _ _ _ _ (alt-out {m = m} β ¬pd))
      (cong (word (select (alternating (2 ^ℕ m)) β)) (sym (kword-out m a b c d ¬pd)))

module _ (m : ℕ) where

  private
    left-index : ∀ i → toℕ (ι (left (contiguous (2 ^ℕ m))) i) ≡ toℕ i
    left-index i = trans (contiguous-index (2 ^ℕ m) false i)
      (cong (_+ toℕ i) (NP.*-zeroʳ (2 ^ℕ m)))

    right-index : ∀ i → toℕ (ι (right (contiguous (2 ^ℕ m))) i) ≡ 2 ^ℕ m + toℕ i
    right-index i = trans (contiguous-index (2 ^ℕ m) true i)
      (cong (_+ toℕ i) (NP.*-identityʳ (2 ^ℕ m)))

    module L = Through m (left (contiguous (2 ^ℕ m))) (λ x → x)
      left-index (con-left-in {m = m}) (λ lt → lt)
    module R = Through m (right (contiguous (2 ^ℕ m))) (2 ^ℕ m +_)
      right-index (con-right-in {m = m}) (con-right-mono {m = m})

  xword-left : a < b → b < 2 ^ℕ m →
    xword (suc m) a b ≡ word (left (contiguous (2 ^ℕ m))) (xword m a b)
  xword-left = L.xword-up

  xword-right : a < b → b < 2 ^ℕ m →
    xword (suc m) (2 ^ℕ m + a) (2 ^ℕ m + b) ≡
    word (right (contiguous (2 ^ℕ m))) (xword m a b)
  xword-right = R.xword-up

  kword-left : a < b → b < c → c < d → d < 2 ^ℕ m →
    kword (suc m) a b c d ≡ word (left (contiguous (2 ^ℕ m))) (kword m a b c d)
  kword-left = L.kword-up

  kword-right : a < b → b < c → c < d → d < 2 ^ℕ m →
    kword (suc m) (2 ^ℕ m + a) (2 ^ℕ m + b) (2 ^ℕ m + c) (2 ^ℕ m + d) ≡
    word (right (contiguous (2 ^ℕ m))) (kword m a b c d)
  kword-right = R.kword-up

------------------------------------------------------------------------
-- The gate bodies
--
-- `E-X`, `E-CX` and `E-CCX` list, for each index a, the exchange of a
-- with a + 2 ^ t when a condition on the bits of a holds; `E-HH` the
-- four-level block on a, a + 2 ^ p, a + 2 ^ q, a + 2 ^ p + 2 ^ q when
-- the bits p and q of a are clear.

bodyX : (n t : ℕ) → (ℕ → Bool) → ℕ → Levels n
bodyX n t cond a = if cond a then xword n a (a + 2 ^ℕ t) else ε

bodyK : (n p q : ℕ) → ℕ → Levels n
bodyK n p q a = if not (bit a p) ∧ not (bit a q)
  then kword n a (a + 2 ^ℕ p) (a + 2 ^ℕ q) ((a + 2 ^ℕ p) + 2 ^ℕ q) else ε

private
  word-if : ∀ {k l} (e : Emb k l) c w →
    word e (if c then w else ε) ≡ (if c then word e w else ε)
  word-if e true w = refl
  word-if e false w = refl

  if-cong : ∀ N c {w w′ : Levels N} → (c ≡ true → w ≡ w′) →
    (if c then w else ε) ≡ (if c then w′ else ε)
  if-cong N true f = f refl
  if-cong N false f = refl

  if-≡ : ∀ N {c c′} (w : Levels N) → c ≡ c′ →
    (if c then w else ε) ≡ (if c′ then w else ε)
  if-≡ N w refl = refl

  kword-cong : ∀ N {a a′ b b′ c c′ d d′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
    kword N a b c d ≡ kword N a′ b′ c′ d′
  kword-cong N refl refl refl refl = refl

  pow>0 : ∀ t → 0 < 2 ^ℕ t
  pow>0 t = NP.m^n>0 2 t

  partner : ∀ a t → a < a + 2 ^ℕ t
  partner a t = NP.m<m+n a (pow>0 t)

  pow< : ∀ p → 2 ^ℕ p < 2 ^ℕ suc p
  pow< p = NP.m<m+n (2 ^ℕ p) (subst (0 <_) (sym (NP.+-identityʳ (2 ^ℕ p))) (pow>0 p))

  not-true : ∀ {b} → not b ≡ true → b ≡ false
  not-true {false} _ = refl

  ∧-left : ∀ {b c} → b ∧ c ≡ true → b ≡ true
  ∧-left {true} _ = refl

  ∧-right : ∀ {b c} → b ∧ c ≡ true → c ≡ true
  ∧-right {true} p = p

-- One wire up at the bottom: the letters of index 2 a + β are those of
-- index a, embedded on the coordinates with low bit β.
module _ (m t : ℕ) (β : Bool) (cond cond′ : ℕ → Bool)
  (ok : ∀ a → cond′ (2 * a + ⌊ β ⌋) ≡ cond a) where

  bodyX-alt : ∀ a → bodyX (suc m) (suc t) cond′ (2 * a + ⌊ β ⌋) ≡
    word (select (alternating (2 ^ℕ m)) β) (bodyX m t cond a)
  bodyX-alt a = trans (if-≡ (suc m) _ (ok a))
    (trans (cong (λ w → if cond a then w else ε)
      (trans (cong (xword (suc m) (2 * a + ⌊ β ⌋)) (alt-step a β (2 ^ℕ t)))
        (xword-alt m β (partner a t))))
      (sym (word-if (select (alternating (2 ^ℕ m)) β) (cond a) _)))

bodyK-alt : ∀ m p β a →
  bodyK (suc m) (suc p) (suc (suc p)) (2 * a + ⌊ β ⌋) ≡
  word (select (alternating (2 ^ℕ m)) β) (bodyK m p (suc p) a)
bodyK-alt m p β a = trans
  (if-≡ (suc m) _ (cong₂ (λ x y → not x ∧ not y) (bit-high a β p) (bit-high a β (suc p))))
  (trans (cong (λ w → if not (bit a p) ∧ not (bit a (suc p)) then w else ε)
    (trans (kword-cong (suc m) refl (alt-step a β (2 ^ℕ p)) (alt-step a β (2 ^ℕ suc p))
             (trans (cong (_+ 2 ^ℕ suc (suc p)) (alt-step a β (2 ^ℕ p)))
               (alt-step (a + 2 ^ℕ p) β (2 ^ℕ suc p))))
      (kword-alt m β {a} {a + 2 ^ℕ p} {a + 2 ^ℕ suc p} {(a + 2 ^ℕ p) + 2 ^ℕ suc p}
        (partner a p) (NP.+-monoʳ-< a (pow< p))
        (NP.+-monoˡ-< (2 ^ℕ suc p) (partner a p)))))
    (sym (word-if (select (alternating (2 ^ℕ m)) β) (not (bit a p) ∧ not (bit a (suc p)))
      (kword m a (a + 2 ^ℕ p) (a + 2 ^ℕ suc p) ((a + 2 ^ℕ p) + 2 ^ℕ suc p)))))

-- One wire up at the top, for a gate on wire 0: the letters of index a
-- and 2 ^ m + a are those of index a, embedded in the two halves.
module _ (m : ℕ) (m>0 : 0 < m) (cond : ℕ → Bool)
  (clear : ∀ a → cond a ≡ true → bit a 0 ≡ false)
  (top : ∀ a → cond (2 ^ℕ m + a) ≡ cond a) where

  private
    in-range : ∀ a → a < 2 ^ℕ m → cond a ≡ true → a + 1 < 2 ^ℕ m
    in-range a a< ca = no-carry m a 0 a< m>0 (clear a ca)

  bodyX-left : ∀ a → a < 2 ^ℕ m →
    bodyX (suc m) 0 cond a ≡ word (left (contiguous (2 ^ℕ m))) (bodyX m 0 cond a)
  bodyX-left a a< = trans
    (if-cong (suc m) (cond a) (λ ca → xword-left m (partner a 0) (in-range a a< ca)))
    (sym (word-if (left (contiguous (2 ^ℕ m))) (cond a) _))

  bodyX-right : ∀ a → a < 2 ^ℕ m →
    bodyX (suc m) 0 cond (2 ^ℕ m + a) ≡
    word (right (contiguous (2 ^ℕ m))) (bodyX m 0 cond a)
  bodyX-right a a< = trans (if-≡ (suc m) _ (top a))
    (trans (if-cong (suc m) (cond a) (λ ca →
        trans (cong (xword (suc m) (2 ^ℕ m + a)) (NP.+-assoc (2 ^ℕ m) a 1))
          (xword-right m (partner a 0) (in-range a a< ca))))
      (sym (word-if (right (contiguous (2 ^ℕ m))) (cond a) _)))

-- The same for the four-level blocks of a gate on the wires 0 and 1.
module _ (m : ℕ) (m>1 : 1 < m) where

  private
    cond : ℕ → Bool
    cond a = not (bit a 0) ∧ not (bit a 1)

    -- With the bits 0 and 1 of a clear, the block's indices are in range.
    odd-clear : ∀ a → bit a 0 ≡ false → bit (a + 1) 1 ≡ bit a 1
    odd-clear a c0 = trans (cong (λ z → bit z 1) eq) (bit-high (a / 2) true 0)
      where
      eq : a + 1 ≡ 2 * (a / 2) + ⌊ true ⌋
      eq = trans (cong (_+ 1) (trans (split a) (cong (λ z → 2 * (a / 2) + ⌊ z ⌋) c0)))
        (S.solve 1 (λ q → con 2 :* q :+ con 0 :+ con 1 := con 2 :* q :+ con 1) refl (a / 2))

    ranges : ∀ a → a < 2 ^ℕ m → cond a ≡ true → (a + 1) + 2 < 2 ^ℕ m
    ranges a a< ca = no-carry m (a + 1) 1 a1< m>1
      (trans (odd-clear a c0) c1)
      where
      c0 = not-true (∧-left ca)
      c1 = not-true (∧-right {not (bit a 0)} ca)
      a1< = no-carry m a 0 a< (NP.<-trans (s≤s z≤n) m>1) c0

    ab : ∀ a → a < a + 1
    ab a = partner a 0
    bc : ∀ a → a + 1 < a + 2
    bc a = NP.+-monoʳ-< a (s≤s (s≤s z≤n))
    cd : ∀ a → a + 2 < (a + 1) + 2
    cd a = NP.+-monoˡ-< 2 (ab a)

  bodyK-left : ∀ a → a < 2 ^ℕ m →
    bodyK (suc m) 0 1 a ≡ word (left (contiguous (2 ^ℕ m))) (bodyK m 0 1 a)
  bodyK-left a a< = trans
    (if-cong (suc m) (cond a) (λ ca → kword-left m (ab a) (bc a) (cd a) (ranges a a< ca)))
    (sym (word-if (left (contiguous (2 ^ℕ m))) (cond a) _))

  bodyK-right : ∀ a → a < 2 ^ℕ m →
    bodyK (suc m) 0 1 (2 ^ℕ m + a) ≡
    word (right (contiguous (2 ^ℕ m))) (bodyK m 0 1 a)
  bodyK-right a a< = trans
    (if-≡ (suc m) _ (cong₂ (λ x y → not x ∧ not y)
      (bit-top m a 0 (NP.<-trans (s≤s z≤n) m>1)) (bit-top m a 1 m>1)))
    (trans (if-cong (suc m) (cond a) (λ ca → trans
        (kword-cong (suc m) refl (NP.+-assoc (2 ^ℕ m) a 1) (NP.+-assoc (2 ^ℕ m) a 2)
          (trans (cong (_+ 2) (NP.+-assoc (2 ^ℕ m) a 1)) (NP.+-assoc (2 ^ℕ m) (a + 1) 2)))
        (kword-right m (ab a) (bc a) (cd a) (ranges a a< ca))))
      (sym (word-if (right (contiguous (2 ^ℕ m))) (cond a) _)))
