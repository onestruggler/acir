------------------------------------------------------------------------
-- Presentations of groups
--
-- The optional signs (-1)_[a]^t of the normal syllables: they commute
-- with the generators apart from a (relations (2b), (2d), (2e)), are
-- renamed along X_[a,b] (relation (3c)), and two of them on a cancel
-- (relation (1b)).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.CCX+HH-TwoLevel.Signs {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Fin.Base using (Fin ; _<_)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Column using (Mτ)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (gen-gen ; flip)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  ≢-sym : {a b : Fin n} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (≡.sym e)

------------------------------------------------------------------------
-- Generators apart from an index

Apart : Fin n → Gen n → Set
Apart a (M-gen b)             = a ≢ b
Apart a (X-gen b c _)         = a ≢ b × a ≢ c
Apart a (K-gen b c d e _ _ _) = a ≢ b × a ≢ c × a ≢ d × a ≢ e

-- (-1)_[a] commutes with them.
comm-M : (a : Fin n) (g : Gen n) → Apart a g → M a • [ g ]ʷ ≈ [ g ]ʷ • M a
comm-M a (M-gen b) ab = axiom (r2d ab)
comm-M a (X-gen b c p) (ab , ac) = sym (axiom (r2b p ab ac))
comm-M a (K-gen b c d e p q r) (ab , ac , ad , ae) = axiom (r2e p q r ab ac ad ae)

Mτ-comm : (a : Fin n) (t : Bool) (g : Gen n) → Apart a g → Mτ a t • [ g ]ʷ ≈ [ g ]ʷ • Mτ a t
Mτ-comm a true  g ap = comm-M a g ap
Mτ-comm a false g ap = trans left-unit (sym right-unit)

------------------------------------------------------------------------
-- Cancelling and flipping

Mτ-Mτ : (a : Fin n) (t : Bool) → Mτ a t • Mτ a t ≈ ε
Mτ-Mτ a true  = axiom r1b
Mτ-Mτ a false = left-unit

-- (-1)_[a]^(not t) (-1)_[a] = (-1)_[a]^t.
Mτ-flip : (a : Fin n) (t : Bool) → Mτ a (not t) • M a ≈ Mτ a t
Mτ-flip a true  = left-unit
Mτ-flip a false = axiom r1b

Mτ-flip′ : (a : Fin n) (t : Bool) → M a • Mτ a (not t) ≈ Mτ a t
Mτ-flip′ a true  = right-unit
Mτ-flip′ a false = axiom r1b

------------------------------------------------------------------------
-- Renaming along X_[a,b]

-- X_[a,b] (-1)_[b] = (-1)_[a] X_[a,b], and the other way round.
X-M : {a b : Fin n} .(p : a < b) → X a b p • M b ≈ M a • X a b p
X-M p = axiom (r3c p)

X-M′ : {a b : Fin n} .(p : a < b) → X a b p • M a ≈ M b • X a b p
X-M′ {a} {b} p = sym (flip (X-gen a b p) (sym (X-M p)))

Mτ-X : {a b : Fin n} .(p : a < b) (t : Bool) → X a b p • Mτ b t ≈ Mτ a t • X a b p
Mτ-X p true  = X-M p
Mτ-X p false = trans right-unit (sym left-unit)

Mτ-X′ : {a b : Fin n} .(p : a < b) (t : Bool) → X a b p • Mτ a t ≈ Mτ b t • X a b p
Mτ-X′ p true  = X-M′ p
Mτ-X′ p false = trans right-unit (sym left-unit)
