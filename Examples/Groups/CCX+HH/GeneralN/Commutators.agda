------------------------------------------------------------------------
-- Presentations of groups
--
-- Explicit commutator witnesses for every primitive gate at every
-- width at least four, using only the wires already present.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.Commutators where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Structural as S
import Examples.Groups.CCX+HH.GeneralN.CommutatorWitnesses as W

record Witness {n : ℕ} (g : Gen n) : Set where
  field
    first second : Circuit n
    first-involutive : (first • first) P.≈ ε
    second-involutive : (second • second) P.≈ ε
    correct : ((first • second) • (first • second)) P.≈ [ g ]ʷ

private
  base : ∀ g → Witness g
  base g = record
    { first = W.first g
    ; second = W.second g
    ; first-involutive = W.first-involutive g
    ; second-involutive = W.second-involutive g
    ; correct = W.commutator g
    }

  top : ∀ {n} {g : Gen n} → Witness g → Witness (g ↧)
  top w = record
    { first = Witness.first w ⇓
    ; second = Witness.second w ⇓
    ; first-involutive = S.cong⇓ (Witness.first-involutive w)
    ; second-involutive = S.cong⇓ (Witness.second-involutive w)
    ; correct = S.cong⇓ (Witness.correct w)
    }

  shift : ∀ {n} {g : Gen n} → Witness g → Witness (g ↥)
  shift w = record
    { first = Witness.first w ↑
    ; second = Witness.second w ↑
    ; first-involutive = S.cong↑ (Witness.first-involutive w)
    ; second-involutive = S.cong↑ (Witness.second-involutive w)
    ; correct = S.cong↑ (Witness.correct w)
    }

witness : ∀ n (g : Gen (4 + n)) → Witness g
witness zero g = base g
witness (suc n) (gate₀ ())
witness (suc n) X-gen = top (witness n X-gen)
witness (suc n) CX-gen = top (witness n CX-gen)
witness (suc n) CCX-gen = top (witness n CCX-gen)
witness (suc n) HH-gen = top (witness n HH-gen)
witness (suc n) (g ↥) = shift (witness n g)
