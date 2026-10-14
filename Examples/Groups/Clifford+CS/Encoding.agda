------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding of n-qubit circuits into words over P′, from four wires
-- on (the analogue of Clément's Definition 8.2)
--
-- A gate is encoded first as a positive product of two-level
-- generators — the gate on the basis vectors of every assignment of
-- the other wires — and then translated into P′ by the coset action
-- from the identity coset (`e`): the product has degree 0 mod 4 (it
-- has 2ⁿ⁻² letters at least), so the action returns to ⟨0⟩ and its
-- output is the P′ word whose spelling the two-level product is, up to
-- the two-level relations (ActionSound).
--
--     iI        ∏ over every basis vector x of i_[x]
--     S on p    ∏ over the vectors with bit p set of i_[x]
--     CS on p   ∏ over the vectors with bits p, p + 1 set of i_[x]
--     K on p    ∏ over the contexts c of the other wires of K on the
--               pair (c with bit p clear , c with bit p set)
--
-- Basis vectors are numbered in Gray order (Numbering), under which
-- the two vectors of a pair need not come in the order of their bit:
-- `Kp a b` is K_[a,b] when a < b and (−1)_[a] K_[b,a] (−1)_[b] when
-- b < a, the same matrix, with a the vector where the wire reads 0.
-- Bitstrings are wire 0 first, as everywhere in this development.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Encoding (m : ℕ) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_<?_)
open import Data.Nat using (suc ; _≤_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ᵗ)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics.Algebra using (Bits)
open import Examples.Groups.Clifford+CS.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏) public
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets using (⟨0⟩)

------------------------------------------------------------------------
-- The width, and the number of basis vectors

n : ℕ
n = ₄₊ m

open import Examples.Groups.Clifford+CS.Numbering n public
  using (N ; N′ ; N≡ ; idx ; cod ; cod-idx ; idx-cod ; idx-inj ; cod-inj)
open import Examples.Groups.Clifford+CS.Numbering n using (16≤2^)

-- Sixteen basis vectors at least.
big : 16 ≤ N
big = Eq.subst (16 ≤_) (Eq.sym N≡) (16≤2^ m)

open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big public using (act)

------------------------------------------------------------------------
-- The position of a gate

data View : Set where
  scalar : Gate 0 → View          -- the scalar
  one    : ℕ → Gate 1 → View      -- a one-wire gate, and its wire
  two    : ℕ → Gate 2 → View      -- a two-wire gate, and its lower wire

view : ∀ {k} → Gen k → View
view (gate₀ h) = scalar h
view (gate₁ h) = one 0 h
view (gate₂ h) = two 0 h
view (g ↥) with view g
... | scalar h = scalar h
... | one p h  = one (suc p) h
... | two p h  = two (suc p) h

------------------------------------------------------------------------
-- Basis vectors

-- The basis vector with bit g on wire p and the context c on the other
-- wires.
str₁ : ℕ → Bits (₃₊ m) → Bool → Bits n
str₁ p c g = insertℕ p g c

-- Bits u on wire p + 1 and t on wire p, the context c on the others.
str₂ : ℕ → Bits (₂₊ m) → Bool → Bool → Bits n
str₂ p c u t = insertℕ (suc p) u (insertℕ p t c)

------------------------------------------------------------------------
-- The two-level products

-- K on the span of the basis vectors a (where the wire reads 0) and b
-- (where it reads 1), whichever is the smaller index.
Kp : Fin N → Fin N → Word (TL.Gen N)
Kp a b with a <? b | b <? a
... | yes p | _     = TL.K a b p
... | no _  | yes q = TL.i a • TL.i a • TL.K b a q • TL.i b • TL.i b
... | no _  | no _  = ε

E-I : Word (TL.Gen N)
E-I = ∏ (allBits n) λ x → TL.i (idx x)

E-S E-K : ℕ → Word (TL.Gen N)
E-S p = ∏ (allBits (₃₊ m)) λ c → TL.i (idx (str₁ p c true))
E-K p = ∏ (allBits (₃₊ m)) λ c → Kp (idx (str₁ p c false)) (idx (str₁ p c true))

E-CS : ℕ → Word (TL.Gen N)
E-CS p = ∏ (allBits (₂₊ m)) λ c → TL.i (idx (str₂ p c true true))

-- The two-level encoding of a generator.
eTL : Gen n → Word (TL.Gen N)
eTL g with view g
... | scalar I-gate = E-I
... | one p S-gate  = E-S p
... | one p K-gate  = E-K p
... | two p CS-gate = E-CS p

------------------------------------------------------------------------
-- The encoding into P′

-- The coset action from ⟨0⟩ translates a two-level word of degree 0
-- into the word over P′ it spells.
e : Gen n → Word (GenP N)
e g = proj₁ ((act ᵗ) ⟨0⟩ (eTL g))
