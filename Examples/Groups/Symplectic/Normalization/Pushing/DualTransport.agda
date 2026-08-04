------------------------------------------------------------------------
-- Presentations of groups
--
-- Transporting srel-wd along duality.
--
-- `dual` swaps the top two wires (Syntactics.Duality-n) and satisfies
-- `dual w ≈ Ex • w • Ex` in the presentation (Lemmas.Duality).  That is
-- an `≈` fact, so it cannot by itself move a statement about the coset
-- action `ract`, which respects `≡` and not `≈` — using it directly
-- would need NF injectivity, which srel-wd is a premise for.
--
-- What *does* transport is the following.  Assume the word-level
-- intertwiner `word-dual`: threading `dual w` from a coset agrees (in ≋)
-- with threading `Ex • w • Ex`.  Then srel-wd for any axiom transports
-- to its dual for free (`srel-wd-dual` below) — in particular c10 ⟹ c11.
--
-- This reduces an open-ended question ("compute every syllable action")
-- to one bounded obligation about a single word, Ex.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.DualTransport
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

-- NOTE: `Syntactics.Duality-n` — the n-ary duality (dual-gen swapping
-- the top two wires at any width) — is currently COMMENTED OUT, in the
-- block at Syntactics.agda:5198-5486.  The only live duality is the
-- 2-qupit `Syntactics.Duality`, whose `dual` has type
-- `Word (Gen 2) → Word (Gen 2)` and which reasons at the `≈` level.
--
-- So this module takes the duality operation as a parameter rather than
-- importing one.  The transport below is independent of *which* word
-- map is used; restoring Duality-n (or any other candidate) instantiates
-- it without changing anything here.

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction p-2 p-prime

------------------------------------------------------------------------
-- ≋ is an equivalence (pointwise ≈ / ≡).

module _ (n : ℕ) where
  open PB (n QRel,_===_)

  ≋-refl : ∀ {x : Circuit n × C (₁₊ n)} → x ≋ x
  ≋-refl = refl , Eq.refl

  ≋-sym : ∀ {x y : Circuit n × C (₁₊ n)} → x ≋ y → y ≋ x
  ≋-sym (r , e) = sym r , Eq.sym e

  ≋-trans : ∀ {x y z : Circuit n × C (₁₊ n)} → x ≋ y → y ≋ z → x ≋ z
  ≋-trans (r₁ , e₁) (r₂ , e₂) = trans r₁ r₂ , Eq.trans e₁ e₂

------------------------------------------------------------------------
-- The Ex-conjugate of an axiom acts alike on both sides.
--
-- This part needs no hypothesis at all: it is pure fusion.  Threading
-- `Ex • u • Ex` and `Ex • t • Ex` from c agrees as soon as u and t agree
-- from the coset Ex leads to.

module _ (n : ℕ) where

  conj-Ex-cong : ∀ {u t : Circuit (₂₊ n)} →
    (∀ (c : C (₂₊ n)) → act (₁₊ n) c u ≋ act (₁₊ n) c t) →
    ∀ (c : C (₂₊ n)) →
      act (₁₊ n) c (Ex • u • Ex) ≋ act (₁₊ n) c (Ex • t • Ex)
  conj-Ex-cong {u} {t} hyp c =
    ≋-cong-•ˡ (₁₊ n) c Ex {u • Ex} {t • Ex}
      (≋-cong-•ʳ (₁₊ n) (step (₁₊ n) c Ex) {u} {t} Ex
        (hyp (step (₁₊ n) c Ex)))

------------------------------------------------------------------------
-- The transport.
--
-- Given the intertwiner for the two words involved, srel-wd for an axiom
-- yields srel-wd for its dual.  Note the hypothesis is only needed at u
-- and t, not at all words.

module _ (n : ℕ) (dual : Circuit (₂₊ n) → Circuit (₂₊ n)) where

  srel-wd-dual : ∀ {u t : Circuit (₂₊ n)} →
    (∀ (c : C (₂₊ n)) → act (₁₊ n) c (dual u) ≋ act (₁₊ n) c (Ex • u • Ex)) →
    (∀ (c : C (₂₊ n)) → act (₁₊ n) c (dual t) ≋ act (₁₊ n) c (Ex • t • Ex)) →
    (∀ (c : C (₂₊ n)) → act (₁₊ n) c u ≋ act (₁₊ n) c t) →
    ∀ (c : C (₂₊ n)) → act (₁₊ n) c (dual u) ≋ act (₁₊ n) c (dual t)
  srel-wd-dual {u} {t} wd-u wd-t hyp c =
    ≋-trans (₁₊ n) (wd-u c)
      (≋-trans (₁₊ n) (conj-Ex-cong n {u} {t} hyp c) (≋-sym (₁₊ n) (wd-t c)))

------------------------------------------------------------------------
-- What remains, precisely.
--
-- `srel-wd-dual` needs the intertwiner only at the two words of the
-- axiom.  For c10 ⟹ c11 that is:
--
--   act c (CZ • H ↓ • CZ)  ≋  act c (Ex • (CZ • H ↑ • CZ) • Ex)
--   act c (c11-RHS)        ≋  act c (Ex • c10-RHS • Ex)
--
-- Both are statements about threading Ex twice, so both reduce (by the
-- fusion law) to knowing σ-Ex and ρ-Ex.  That is the single bounded
-- obligation this development isolates.
