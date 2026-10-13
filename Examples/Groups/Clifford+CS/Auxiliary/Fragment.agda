------------------------------------------------------------------------
-- Presentations of groups
--
-- The K-free fragment of the P′ rules
--
-- The rules whose two sides carry no K letter: both sides of each
-- denote a *phased permutation* of the basis — a permutation together
-- with a power of i on each index — which no reading of a K letter is
-- (`PhasedPerm` models the fragment, as `SignedPerm` models Clément's).
--
-- The list is Clément's Figure 8 (20)–(34) transcribed to phases
-- (scratchpad/tF.py, every instance checked on exact matrices): an
-- exchange conjugates a phase without inverting it, so the braid,
-- shrinking, splitting and commutation rules keep their shapes with
-- the sign pair's two instances replaced by a phase pair squared; new
-- is only the algebra of the phase pair itself — pp a a = ε, pp⁴ = ε,
-- commutation, and the telescope pp a b • pp b c = pp a c, which
-- presents the lattice of phase vectors summing to zero.  The exchange
-- pairs being written in increasing order, there is no analogue of
-- Clément's (33), and the parity side conditions of his (25)–(28) are
-- dropped: the four shrinking rules are sound at every gap, and which
-- one a reduction applies is its own choice.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Auxiliary.Fragment where

open import Data.Fin using (Fin ; toℕ ; _<_)
open import Data.Fin.Properties using (<-trans)
open import Data.Nat using (ℕ ; suc ; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx)

private
  variable
    N : ℕ

------------------------------------------------------------------------
-- Consecutive indices

Succ : Fin N → Fin N → Set
Succ a a′ = toℕ a′ ≡ suc (toℕ a)

-- The ordering a letter wants, from consecutiveness.
s< : ∀ {a a′ : Fin N} → Succ a a′ → a < a′
s< {a = a} s = Eq.subst (suc (toℕ a) ≤_) (Eq.sym s) ≤-refl

------------------------------------------------------------------------
-- The letters as words

pw : (a b : Fin N) → Word (GenP N)
pw a b = [ pp a b ]ʷ

xw : (c a b : Fin N) → .(a < b) → Word (GenP N)
xw c a b p = [ px c a b p ]ʷ

dw : (a b c d : Fin N) → .(a < b) → .(c < d) → Word (GenP N)
dw a b c d p q = [ dx a b c d p q ]ʷ

------------------------------------------------------------------------
-- The rules

infix 4 _F,_===_
data _F,_===_ (N : ℕ) : WRel (GenP N) where

  -- The phase pairs: a pair on one index vanishes, a pair has order
  -- four, pairs commute, and pairs telescope.
  pp-id   : ∀ a → N F, pw a a === ε
  pp-ord  : ∀ a b → N F, pw a b ^ 4 === ε
  pp-comm : ∀ a b c d → N F, pw a b • pw c d === pw c d • pw a b
  pp-tele : ∀ a b c → N F, pw a b • pw b c === pw a c

  -- A letter squared is a −1−1 pair, two phase pairs.
  px-sq : ∀ a a′ (s : Succ a a′) →
          N F, pw a a′ • pw a a′ === xw a a a′ (s< s) • xw a a a′ (s< s)

  -- The braid on consecutive triples.
  px-braid : ∀ a a′ a″ (s : Succ a a′) (s′ : Succ a′ a″) →
             N F, xw a a a′ (s< s) • xw a′ a′ a″ (s< s′) • xw a a a′ (s< s)
             === xw a′ a′ a″ (s< s′) • xw a a a′ (s< s) • xw a′ a′ a″ (s< s′)

  -- Shrinking a letter: the lower index moves up …
  px-shrink₁ : ∀ a a′ c (s : Succ a a′) (lt : a′ < c) →
               N F, xw a a c (<-trans (s< s) lt)
               === xw a′ a a′ (s< s) • xw a′ a′ c lt • xw a a a′ (s< s)
  px-shrink₂ : ∀ a a′ c (s : Succ a a′) (lt : a′ < c) →
               N F, xw c a c (<-trans (s< s) lt)
               === xw a′ a a′ (s< s) • xw c a′ c lt • xw a a a′ (s< s)

  -- … or the upper index moves down.
  px-shrink₃ : ∀ a c′ c (s : Succ c′ c) (lt : a < c′) →
               N F, xw a a c (<-trans lt (s< s))
               === xw c′ c′ c (s< s) • xw a a c′ lt • xw c c′ c (s< s)
  px-shrink₄ : ∀ a c′ c (s : Succ c′ c) (lt : a < c′) →
               N F, xw c a c (<-trans lt (s< s))
               === xw c′ c′ c (s< s) • xw c′ a c′ lt • xw c c′ c (s< s)

  -- The two phase choices on a consecutive pair are inverse.
  px-inv : ∀ a a′ (s : Succ a a′) →
           N F, xw a a a′ (s< s) • xw a′ a a′ (s< s) === ε

  -- The sign moves to the lower index at the cost of a −1−1 pair.
  px-sign : ∀ c a b .(ab : a < b) →
            N F, xw c a b ab === pw c a • pw c a • xw a a b ab

  -- A phase pair crosses a letter, its indices transposed.
  px-conj : ∀ a a′ c (s : Succ a a′) → c ≢ a → c ≢ a′ →
            N F, pw a′ c • xw a a a′ (s< s)
            === xw a a a′ (s< s) • pw a c

  -- Letters on disjoint consecutive pairs commute.
  px-comm : ∀ a a′ b b′ (s : Succ a a′) (s′ : Succ b b′) (lt : a′ < b) →
            N F, xw a a a′ (s< s) • xw b b b′ (s< s′)
            === xw b b b′ (s< s′) • xw a a a′ (s< s)

  -- A double exchange is two letters, the signs cancelling.
  dx-split : ∀ a b c d .(ab : a < b) .(cd : c < d) →
             N F, dw a b c d ab cd === xw a a b ab • xw b c d cd
