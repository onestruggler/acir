------------------------------------------------------------------------
-- Presentations of groups
--
-- A recursive auxiliary encoder, using the two spectator blocks of
-- each additional wire.  Unlike Encoding's natural-number enumeration,
-- this form exposes the tensor structure for a symbolic-width proof.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.StructuralEncoding where

import Data.Fin.Base as F
open import Data.Nat.Base using (ℕ ; zero ; suc ; s≤s ; z≤n)
  renaming (_^_ to _^ℕ_)
open import Word.Base using (Word ; _•_ ; _ʷ)

open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (word)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary

private variable m n : ℕ

Levels : ℕ → Set
Levels n = Word (T.Gen (2 ^ℕ n))

copy : Partition m n → Word (T.Gen m) → Word (T.Gen n)
copy p w = word (left p) w • word (right p) w

X-block : (n : ℕ) → Levels (suc n)
X-block zero = T.X F.zero (F.suc F.zero) (s≤s z≤n)
X-block (suc n) = copy (contiguous (2 ^ℕ suc n)) (X-block n)

CX-block HH-block : (n : ℕ) → Levels (suc (suc n))
CX-block zero = T.X (F.suc (F.suc F.zero))
  (F.suc (F.suc (F.suc F.zero))) (s≤s (s≤s (s≤s z≤n)))
CX-block (suc n) = copy (contiguous (2 ^ℕ suc (suc n))) (CX-block n)
HH-block zero = T.K F.zero (F.suc F.zero) (F.suc (F.suc F.zero))
  (F.suc (F.suc (F.suc F.zero)))
  (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))
HH-block (suc n) = copy (contiguous (2 ^ℕ suc (suc n))) (HH-block n)

CCX-block : (n : ℕ) → Levels (suc (suc (suc n)))
CCX-block zero = T.X
  (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))
  (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
CCX-block (suc n) = copy (contiguous (2 ^ℕ suc (suc (suc n)))) (CCX-block n)

e : Gen n → Levels n
e (gate₀ ())
e (gate₁ {n} X-gate) = X-block n
e (gate₂ {n} CX-gate) = CX-block n
e (gate₂ {n} HH-gate) = HH-block n
e (gate₃ {n} CCX-gate) = CCX-block n
e (_↥ {n} g) = copy (alternating (2 ^ℕ n)) (e g)

encode : Circuit n → Levels n
encode = e ʷ
