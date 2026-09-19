------------------------------------------------------------------------
-- Presentations of groups
--
-- The equational theory of P (Clément, Definition 4.9 and Figure 8)
--
-- Twenty-seven equations on words over P, at every dimension 2ⁿ with
-- n ≥ 3, whose completeness for the even-parity subgroup is the
-- paper's Theorem 4.10 (Appendix A, by the Reidemeister–Schreier
-- theorem from Theorem 4.4) — a hypothesis of the completeness
-- theorem here.  Indices are basis indices, a + 1 is written as a
-- second index with its value one more, and the side conditions of
-- Figure 8 and its caption are hypotheses of the rules.  A letter
-- with two coinciding indices never occurs under the hypotheses; the
-- letters are written through the deciding wrappers of Encoding so
-- that no proof needs to be carried; the standing convention of the
-- paper that the two indices of an X or H letter differ is a
-- hypothesis wherever they are free.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; suc ; _+_ ; _∸_ ; _<_ ; _≤_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Word.Base using (Word ; WRel ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (code ; parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Encoding

private
  variable
    m : ℕ

-- a′ is a + 1.
Succ : ∀ {N} → Fin N → Fin N → Set
Succ a a′ = toℕ a′ ≡ suc (toℕ a)

-- H_[0,1] H_[3,2], the gate the specific equations are about.
private
  hh₀₁₃₂ : Word (GenP (₃₊ m))
  hh₀₁₃₂ = hhℕ 0 1 3 2

infix 4 _P,_===_
data _P,_===_ (m : ℕ) : WRel (GenP (₃₊ m)) where

  -- (20)–(22): the signs.
  r20 : ∀ a → m P, zz a a === ε
  r21 : ∀ a b → m P, zz a b === zz b a
  r22 : ∀ a b c → m P, zz a b • zz b c === zz a c

  -- (23)–(29): the signed exchanges of consecutive indices.
  r23 : ∀ a a′ → Succ a a′ → m P, zz a a′ === zx a a a′ • zx a a a′
  r24 : ∀ a a′ a″ → Succ a a′ → Succ a′ a″ →
        m P, zx a a a′ • zx a′ a′ a″ • zx a a a′ === zx a′ a′ a″ • zx a a a′ • zx a′ a′ a″
  r25 : ∀ a a′ c → Succ a a′ → toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
        m P, zx a a c === zx a′ a a′ • zx a′ a′ c • zx a a a′
  r26 : ∀ a a′ c → Succ a a′ → toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
        m P, zx c a c === zx a′ a a′ • zx c a′ c • zx a a a′
  r27 : ∀ a c′ c → Succ c′ c → suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
        m P, zx a a c === zx c′ c′ c • zx a a c′ • zx c c′ c
  r28 : ∀ a c′ c → Succ c′ c → suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
        m P, zx c a c === zx c′ c′ c • zx c′ a c′ • zx c c′ c
  r29 : ∀ a a′ → Succ a a′ → m P, zx a a a′ • zx a′ a a′ === ε

  -- (30)–(34): the other exchanges.
  r30 : ∀ c a b → a ≢ b → c ≢ a → c ≢ b → m P, zx c a b === zz c a • zx a a b
  r31 : ∀ a a′ c → Succ a a′ → c ≢ a → c ≢ a′ →
        m P, zz a′ c • zx a a a′ === zx a a a′ • zz a c
  r32 : ∀ a a′ b b′ → Succ a a′ → Succ b b′ → toℕ a′ < toℕ b →
        m P, zx a a a′ • zx b b b′ === zx b b b′ • zx a a a′
  r33 : ∀ b a → m P, zx b a b === zx b b a
  r34 : ∀ a b c d → a ≢ b → c ≢ d → m P, xx a b c d === zx a a b • zx b c d

  -- (35)–(37): the Hadamards, by the pattern of their codes.
  r35 : ∀ a b c d → distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ true →
        hpat (code (₃₊ m) a) (code (₃₊ m) b) (code (₃₊ m) c) (code (₃₊ m) d) ≡ nothing →
        m P, hh a b c d === Σ (toℕ a) (toℕ b) (toℕ c) (toℕ d) • hh₀₁₃₂ • Σ′ (toℕ a) (toℕ b) (toℕ c) (toℕ d)
  r36 : ∀ a b c d pb pc →
        hpat (code (₃₊ m) a) (code (₃₊ m) b) (code (₃₊ m) c) (code (₃₊ m) d) ≡ just (pb , pc) →
        pc < pb → m P, hh a b c d === W₁ (code (₃₊ m) a) pc pb
  r37 : ∀ a b c d pb pc →
        hpat (code (₃₊ m) a) (code (₃₊ m) b) (code (₃₊ m) c) (code (₃₊ m) d) ≡ just (pb , pc) →
        pb < pc → m P, hh a b c d === W₂ (code (₃₊ m) a) pb pc

  -- (38)–(41): H_[0,1] H_[3,2] and the signed exchanges.
  r38 : ∀ a a′ → Succ a a′ → 4 ≤ toℕ a →
        m P, zx a a a′ • hh₀₁₃₂ === hh₀₁₃₂ • zx a a a′
  r39 : m P, zzℕ 0 1 • hh₀₁₃₂ === hh₀₁₃₂ • zzℕ 0 1
  r40 : m P, zzℕ 3 4 • hh₀₁₃₂ === hh₀₁₃₂ • zzℕ 3 4 • zxℕ 2 2 3
  r41 : m P, hh₀₁₃₂ • hh₀₁₃₂ === ε

  -- (42): a Hadamard pair through two fresh indices.
  r42 : ∀ a b c d → a ≢ b → c ≢ d → distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ false →
        let ef = twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d) in
        m P, hhℕ (toℕ a) (toℕ b) (proj₁ ef) (proj₂ ef) • hhℕ (proj₁ ef) (proj₂ ef) (toℕ c) (toℕ d)
             === hh a b c d

  -- (43)–(46): the specific equations on the indices 0 … 7.
  r43 : m P, hhℕ 0 1 3 2 • hhℕ 3 2 4 5 === xxℕ 0 3 1 2 • hhℕ 3 2 4 5 • xxℕ 0 3 1 2
  r44 : m P, xxℕ 0 3 1 2 • hhℕ 0 1 3 2 === hhℕ 0 1 3 2 • xxℕ 0 3 1 2
  r45 : m P, hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6 • zzℕ 0 1 • hhℕ 0 3 1 2
             === hhℕ 0 3 1 2 • zzℕ 0 1 • hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6
  r46 : m P, hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • hhℕ 3 2 4 5 • hhℕ 7 6 4 5 •
             zzℕ 2 3 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2
             === hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • zzℕ 2 3 • hhℕ 7 6 4 5 • hhℕ 3 2 4 5 •
                 hhℕ 3 4 2 5 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6
