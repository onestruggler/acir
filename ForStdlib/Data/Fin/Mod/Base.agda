------------------------------------------------------------------------
-- The Agda standard library
--
-- Modular arithmetic on ℤ/nℤ, represented as Fin n
--
-- Residues mod n are Fin n; addition and multiplication are computed
-- on representatives and reduced with _%_.  ℤ* n is the subset of
-- nonzero residues, which for a prime modulus is the group of units
-- (see ForStdlib.Data.Fin.Mod.Prime).
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.Base.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod.Base where

open import Agda.Builtin.FromNat using (Number ; fromNat)
open import Data.Fin.Base using (Fin ; toℕ ; fromℕ< ; inject₁)
open import Data.Fin.Literals using (number)
open import Data.Nat.Base as ℕ using (ℕ ; 2+)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product.Base using (Σ-syntax)
open import Data.Unit.Base using (⊤)
open import Notations using (₀ ; ₁ ; ₁₊ ; ₂₊)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)

import Data.Nat.Literals as ℕₗ

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Numeral literals
--
-- A numeric literal only elaborates through these instances where
-- fromNat is in scope, and imports are not re-exported -- so every
-- module that writes a literal at type ℤ n has to import
-- Agda.Builtin.FromNat itself.  Deliberately not re-exported here:
-- doing so would also route plain ℕ literals in every downstream
-- module through Numℕ.  Both instances are needed: NumFinN covers a
-- general modulus, NumFin pins it to 3 where it cannot be inferred.

instance
  Numℕ : Number ℕ
  Numℕ = ℕₗ.number

instance
  NumFin : Number (Fin 3)
  NumFin = number 3

instance
  NumFinN : Number (Fin n)
  NumFinN {n} = number n


------------------------------------------------------------------------
-- The residues, and the units-to-be

ℤ : ℕ → Set
ℤ n = Fin n

-- The nonzero residues.  For a prime modulus these are exactly the
-- units; at n = 0 there is nothing to exclude, so ℤ* degenerates.
ℤ* : ℕ → Set
ℤ* ₀ = ℤ ₀
ℤ* n@(₁₊ _) = Σ[ a ∈ ℤ n ] (a ≢ ₀)

succ : ℤ n → ℤ n
succ {₁₊ n} ₀ = ₀
succ {2+ n} (₁₊ a) = inject₁ (succ a)

cong-succ : ∀ {a b : ℤ n} → a ≡ b → succ a ≡ succ b
cong-succ {n} {a} {b} eq rewrite eq = refl


------------------------------------------------------------------------
-- Ring operations
--
-- Addition and multiplication are computed on representatives and
-- reduced mod n; _^′_ is the ℕ-indexed power and k ＊ a the k-fold sum.

infixl 8 _^′_
infixl 7 _*_
infixl 6 _+_ _＊_
infixr 8 -_

_+_ : ℤ n → ℤ n → ℤ n
_+_ {₁₊ n} a b = fromℕ< (m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))

_*_ : ℤ n → ℤ n → ℤ n
_*_ {₁₊ n} a b = fromℕ< (m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))

-- The top residue, +1, and 0, at the indices where they are available.
₋₁ : ℤ (₁₊ n)
₋₁ {n} = fromℕ< (n<1+n n)

₊₁ : ℤ (₂₊ n)
₊₁ {n} = ₁

0₂₊ₙ : ℤ (₂₊ n)
0₂₊ₙ {n} = ₀

-_ : ℤ n → ℤ n
-_ {₁₊ n} a = ₋₁ * a

_^′_ : ℤ (₂₊ n) → ℕ → ℤ (₂₊ n)
_^′_ {n} a ₀ = ₁
_^′_ {n} a (₁₊ k) = a * (a ^′ k)

_＊_ : ℕ → ℤ (₁₊ n) → ℤ (₁₊ n)
_＊_ {n} ₀ a = ₀
_＊_ {n} (₁₊ k) a = a + (k ＊ a)
