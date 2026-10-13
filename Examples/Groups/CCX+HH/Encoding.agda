------------------------------------------------------------------------
-- Presentations of groups
--
-- Explicit block encoding into Li--Ross--Selinger's dyadic alphabet.
--
-- Natural wire positions are convenient for sharing these constructors
-- with the {X,CX,CCX,H} experiment.  Out-of-range level indices yield
-- the empty word.  The circuit encoder below only requests valid ones.
-- This file defines the translation; semantic correctness at symbolic
-- width and a circuit-level decoding are separate proof obligations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Encoding where

open import Data.Bool.Base using (Bool ; false ; true ; not ; _∧_ ; if_then_else_)
open import Data.Fin.Base using (Fin ; fromℕ<)
import Data.Fin.Properties as FP
open import Data.List.Base using (List ; foldr ; upTo)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _/_ ; _%_ ; _≡ᵇ_)
  renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; _ʷ)

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open import Examples.Groups.CCX+HH.Syntactics

private variable n : ℕ

Levels : ℕ → Set
Levels n = Word (T.Gen (2 ^ℕ n))

-- Bit positions count from the least significant bit.
bit : ℕ → ℕ → Bool
bit a zero = a % 2 ≡ᵇ 1
bit a (suc p) = bit (a / 2) p

∏ : {A B : Set} → List A → (A → Word B) → Word B
∏ xs f = foldr (λ a w → f a • w) ε xs

-- Order the two levels, so this also handles a reversed transposition.
xword : (n a b : ℕ) → Levels n
xword n a b with a NP.<? (2 ^ℕ n) | b NP.<? (2 ^ℕ n)
... | no _ | _ = ε
... | yes _ | no _ = ε
... | yes pa | yes pb with fromℕ< pa FP.<? fromℕ< pb
...   | yes ab = T.X (fromℕ< pa) (fromℕ< pb) ab
...   | no _ with fromℕ< pb FP.<? fromℕ< pa
...     | yes ba = T.X (fromℕ< pb) (fromℕ< pa) ba
...     | no _ = ε

kword : (n a b c d : ℕ) → Levels n
kword n a b c d with a NP.<? (2 ^ℕ n) | b NP.<? (2 ^ℕ n)
                   | c NP.<? (2 ^ℕ n) | d NP.<? (2 ^ℕ n)
... | no _ | _ | _ | _ = ε
... | yes _ | no _ | _ | _ = ε
... | yes _ | yes _ | no _ | _ = ε
... | yes _ | yes _ | yes _ | no _ = ε
... | yes pa | yes pb | yes pc | yes pd
    with fromℕ< pa FP.<? fromℕ< pb | fromℕ< pb FP.<? fromℕ< pc
       | fromℕ< pc FP.<? fromℕ< pd
...   | yes ab | yes bc | yes cd =
        T.K (fromℕ< pa) (fromℕ< pb) (fromℕ< pc) (fromℕ< pd) ab bc cd
...   | _ | _ | _ = ε

-- Products range over the spectator assignments.  The tests choose
-- exactly the least index of each nontrivial block.
E-X : (n target : ℕ) → Levels n
E-X n t = ∏ (upTo (2 ^ℕ n)) λ a →
  if not (bit a t) then xword n a (a + 2 ^ℕ t) else ε

E-CX : (n control target : ℕ) → Levels n
E-CX n c t = ∏ (upTo (2 ^ℕ n)) λ a →
  if bit a c ∧ not (bit a t) then xword n a (a + 2 ^ℕ t) else ε

E-CCX : (n control₁ control₂ target : ℕ) → Levels n
E-CCX n c d t = ∏ (upTo (2 ^ℕ n)) λ a →
  if bit a c ∧ bit a d ∧ not (bit a t)
  then xword n a (a + 2 ^ℕ t) else ε

-- Requires p < q < n for the intended matrix.  The actual circuit
-- encoder always uses q = suc p.  K is symmetric under exchange of
-- its two tensor factors, so either wire is the first H.
E-HH : (n p q : ℕ) → Levels n
E-HH n p q = ∏ (upTo (2 ^ℕ n)) λ a →
  if not (bit a p) ∧ not (bit a q)
  then kword n a (a + 2 ^ℕ p) (a + 2 ^ℕ q)
                  ((a + 2 ^ℕ p) + 2 ^ℕ q)
  else ε

data View : Set where
  at-X   : ℕ → View
  at-CX  : ℕ → View
  at-CCX : ℕ → View
  at-HH  : ℕ → View

up : View → View
up (at-X p) = at-X (suc p)
up (at-CX p) = at-CX (suc p)
up (at-CCX p) = at-CCX (suc p)
up (at-HH p) = at-HH (suc p)

view : Gen n → View
view (gate₀ ())
view X-gen = at-X 0
view CX-gen = at-CX 0
view CCX-gen = at-CCX 0
view HH-gen = at-HH 0
view (g ↥) = up (view g)

encode-view : (n : ℕ) → View → Levels n
encode-view n (at-X p) = E-X n p
encode-view n (at-CX p) = E-CX n (suc p) p
encode-view n (at-CCX p) = E-CCX n (suc p) (suc (suc p)) p
encode-view n (at-HH p) = E-HH n p (suc p)

e : Gen n → Levels n
e {n} g = encode-view n (view g)

encode : Circuit n → Levels n
encode = e ʷ
