------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of P′
--
-- The K-free fragment's rules verbatim — the constructors carry the
-- same names, so a derivation reads the same at either relation — plus
-- the K-letter rules, the local algebra scratchpad/tK.py checked on
-- exact matrices (13/13 at N = 8): inverses, the square as a phase
-- word, fresh-pair bridging (sound with no side condition, by
-- cancellation), disjoint commutation, the phases that pass a K pair,
-- relation (15) of the two-level presentation lifted — the −1 moved to
-- a fresh index, where it becomes the sign of the exchange letter —
-- the pair exchange conjugating a K pair to its −1−1 multiple, the
-- double exchange renaming a K pair, and (19) bridged through two
-- fresh pairs.
--
-- What is still missing is the Gray-code layer: the rules relating a
-- K pair to the encoded letters of a width, which come with the
-- encoding and decoding design (scratchpad/four-wire-notes.md).  The
-- fragment results (`NF`, `Unique`) carry into this relation through
-- `free⇒full`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Auxiliary.Rules where

open import Data.Fin using (Fin ; toℕ ; _<_)
open import Data.Fin.Properties using (<-trans)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Data.Nat using (ℕ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; kk)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment
  using (Succ ; s< ; pw ; xw ; dw ; _F,_===_)
open _F,_===_

private
  variable
    N : ℕ

-- The K letter as a word.
kw : (a b c d : Fin N) → .(a < b) → .(c < d) → Word (GenP N)
kw a b c d p q = [ kk a b c d p q ]ʷ

------------------------------------------------------------------------
-- The rules

infix 4 _R,_===_
data _R,_===_ (N : ℕ) : WRel (GenP N) where

  -- The K-free fragment, verbatim.
  pp-id   : ∀ a → N R, pw a a === ε
  pp-ord  : ∀ a b → N R, pw a b ^ 4 === ε
  pp-comm : ∀ a b c d → N R, pw a b • pw c d === pw c d • pw a b
  pp-tele : ∀ a b c → N R, pw a b • pw b c === pw a c
  px-sq : ∀ a a′ (s : Succ a a′) →
          N R, pw a a′ • pw a a′ === xw a a a′ (s< s) • xw a a a′ (s< s)
  px-braid : ∀ a a′ a″ (s : Succ a a′) (s′ : Succ a′ a″) →
             N R, xw a a a′ (s< s) • xw a′ a′ a″ (s< s′) • xw a a a′ (s< s)
             === xw a′ a′ a″ (s< s′) • xw a a a′ (s< s) • xw a′ a′ a″ (s< s′)
  px-shrink₁ : ∀ a a′ c (s : Succ a a′) (lt : a′ < c) →
               N R, xw a a c (<-trans (s< s) lt)
               === xw a′ a a′ (s< s) • xw a′ a′ c lt • xw a a a′ (s< s)
  px-shrink₂ : ∀ a a′ c (s : Succ a a′) (lt : a′ < c) →
               N R, xw c a c (<-trans (s< s) lt)
               === xw a′ a a′ (s< s) • xw c a′ c lt • xw a a a′ (s< s)
  px-shrink₃ : ∀ a c′ c (s : Succ c′ c) (lt : a < c′) →
               N R, xw a a c (<-trans lt (s< s))
               === xw c′ c′ c (s< s) • xw a a c′ lt • xw c c′ c (s< s)
  px-shrink₄ : ∀ a c′ c (s : Succ c′ c) (lt : a < c′) →
               N R, xw c a c (<-trans lt (s< s))
               === xw c′ c′ c (s< s) • xw c′ a c′ lt • xw c c′ c (s< s)
  px-inv : ∀ a a′ (s : Succ a a′) →
           N R, xw a a a′ (s< s) • xw a′ a a′ (s< s) === ε
  px-sign : ∀ c a b .(ab : a < b) →
            N R, xw c a b ab === pw c a • pw c a • xw a a b ab
  px-conj : ∀ a a′ c (s : Succ a a′) → c ≢ a → c ≢ a′ →
            N R, pw a′ c • xw a a a′ (s< s)
            === xw a a a′ (s< s) • pw a c
  px-conj₂ : ∀ a a′ (s : Succ a a′) →
             N R, pw a a′ • xw a a a′ (s< s)
             === xw a a a′ (s< s) • pw a′ a
  px-comm : ∀ a a′ b b′ (s : Succ a a′) (s′ : Succ b b′) (lt : a′ < b) →
            N R, xw a a a′ (s< s) • xw b b b′ (s< s′)
            === xw b b b′ (s< s′) • xw a a a′ (s< s)
  dx-split : ∀ a b c d .(ab : a < b) .(cd : c < d) →
             N R, dw a b c d ab cd === xw a a b ab • xw b c d cd

  -- The K pairs: inverses, the square, and bridging.  Inverses and
  -- bridging cancel whatever the pairs share (relations (17), (18) of
  -- the two-level presentation); the square and everything after it
  -- need the two pairs of the letter disjoint.
  kk-inv : ∀ a b c d .(ab : a < b) .(cd : c < d) →
           N R, kw a b c d ab cd • kw c d a b cd ab === ε
  kk-sq : ∀ a b c d .(ab : a < b) .(cd : c < d) →
          c ≢ a → c ≢ b → d ≢ a → d ≢ b →
          N R, kw a b c d ab cd • kw a b c d ab cd === pw c a • pw d b
  kk-bridge : ∀ a b c d e f .(ab : a < b) .(cd : c < d) .(ef : e < f) →
              N R, kw a b c d ab cd === kw a b e f ab ef • kw e f c d ef cd

  -- Disjoint letters commute.
  kk-pp : ∀ a b c d x y .(ab : a < b) .(cd : c < d) →
          x ≢ a → x ≢ b → x ≢ c → x ≢ d → y ≢ a → y ≢ b → y ≢ c → y ≢ d →
          N R, kw a b c d ab cd • pw x y === pw x y • kw a b c d ab cd
  kk-px : ∀ a b c d s x y .(ab : a < b) .(cd : c < d) .(xy : x < y) →
          s ≢ a → s ≢ b → s ≢ c → s ≢ d →
          x ≢ a → x ≢ b → x ≢ c → x ≢ d → y ≢ a → y ≢ b → y ≢ c → y ≢ d →
          N R, kw a b c d ab cd • xw s x y xy === xw s x y xy • kw a b c d ab cd
  kk-kk : ∀ a b c d e f g h .(ab : a < b) .(cd : c < d) .(ef : e < f) .(gh : g < h) →
          e ≢ a → e ≢ b → e ≢ c → e ≢ d → f ≢ a → f ≢ b → f ≢ c → f ≢ d →
          g ≢ a → g ≢ b → g ≢ c → g ≢ d → h ≢ a → h ≢ b → h ≢ c → h ≢ d →
          N R, kw a b c d ab cd • kw e f g h ef gh
          === kw e f g h ef gh • kw a b c d ab cd

  -- The phases that pass a K pair: the −1−1 on its own indices, and
  -- i_a i_b through a fresh balance.
  kk-mm : ∀ a b c d .(ab : a < b) .(cd : c < d) →
          c ≢ a → c ≢ b → d ≢ a → d ≢ b →
          N R, (pw a b • pw a b) • kw a b c d ab cd
          === kw a b c d ab cd • (pw a b • pw a b)
  kk-ii : ∀ a b c d e .(ab : a < b) .(cd : c < d) →
          c ≢ a → c ≢ b → d ≢ a → d ≢ b →
          e ≢ a → e ≢ b → e ≢ c → e ≢ d →
          N R, (pw a e • pw b e) • kw a b c d ab cd
          === kw a b c d ab cd • (pw a e • pw b e)

  -- Relation (15) of the two-level presentation, lifted: the −1 moves
  -- to a fresh index, where it becomes the sign of the exchange.
  kk-x : ∀ a b c d e .(ab : a < b) .(cd : c < d) →
         c ≢ a → c ≢ b → d ≢ a → d ≢ b →
         e ≢ a → e ≢ b → e ≢ c → e ≢ d →
         N R, kw a b c d ab cd • (pw b e • pw b e)
         === xw e a b ab • kw a b c d ab cd

  -- The pair's own exchange conjugates it to its −1−1 multiple.
  kk-conj : ∀ a b c d .(ab : a < b) .(cd : c < d) →
            c ≢ a → c ≢ b → d ≢ a → d ≢ b →
            N R, xw b a b ab • kw a b c d ab cd • xw a a b ab
            === (pw a b • pw a b) • kw a b c d ab cd

  -- A double exchange renames a K pair.
  kk-ren : ∀ a b c d e f .(ab : a < b) .(cd : c < d)
             .(ae : a < e) .(bf : b < f) .(ef : e < f) →
           c ≢ a → c ≢ b → c ≢ e → c ≢ f → d ≢ a → d ≢ b → d ≢ e → d ≢ f →
           e ≢ a → e ≢ b → f ≢ a → f ≢ b →
           N R, dw a e b f ae bf • kw a b c d ab cd • dw a e b f ae bf
           === kw e f c d ef cd

  -- Relation (19), bridged through two fresh pairs.
  kk-yb : ∀ a b c d e f g h
            .(ab : a < b) .(cd : c < d) .(ac : a < c) .(bd : b < d)
            .(ef : e < f) .(gh : g < h) →
          b ≢ c →
          e ≢ a → e ≢ b → e ≢ c → e ≢ d → f ≢ a → f ≢ b → f ≢ c → f ≢ d →
          g ≢ a → g ≢ b → g ≢ c → g ≢ d → h ≢ a → h ≢ b → h ≢ c → h ≢ d →
          g ≢ e → g ≢ f → h ≢ e → h ≢ f →
          N R, kw a b e f ab ef • kw c d g h cd gh
               • kw a c e f ac ef • kw b d g h bd gh
          === kw a c e f ac ef • kw b d g h bd gh
              • kw a b e f ab ef • kw c d g h cd gh

------------------------------------------------------------------------
-- The fragment embeds

free⇒full : ∀ {u v : Word (GenP N)} → N F, u === v → N R, u === v
free⇒full (pp-id a)                    = pp-id a
free⇒full (pp-ord a b)                 = pp-ord a b
free⇒full (pp-comm a b c d)            = pp-comm a b c d
free⇒full (pp-tele a b c)              = pp-tele a b c
free⇒full (px-sq a a′ s)               = px-sq a a′ s
free⇒full (px-braid a a′ a″ s s′)      = px-braid a a′ a″ s s′
free⇒full (px-shrink₁ a a′ c s lt)     = px-shrink₁ a a′ c s lt
free⇒full (px-shrink₂ a a′ c s lt)     = px-shrink₂ a a′ c s lt
free⇒full (px-shrink₃ a c′ c s lt)     = px-shrink₃ a c′ c s lt
free⇒full (px-shrink₄ a c′ c s lt)     = px-shrink₄ a c′ c s lt
free⇒full (px-inv a a′ s)              = px-inv a a′ s
free⇒full (px-sign c a b ab)           = px-sign c a b ab
free⇒full (px-conj a a′ c s ca ca′)    = px-conj a a′ c s ca ca′
free⇒full (px-conj₂ a a′ s)            = px-conj₂ a a′ s
free⇒full (px-comm a a′ b b′ s s′ lt)  = px-comm a a′ b b′ s s′ lt
free⇒full (dx-split a b c d ab cd)     = dx-split a b c d ab cd

free⇒full-≈ : ∀ {u v : Word (GenP N)} →
              PB._≈_ (N F,_===_) u v → PB._≈_ (N R,_===_) u v
free⇒full-≈ PB.refl         = PB.refl
free⇒full-≈ (PB.sym e)      = PB.sym (free⇒full-≈ e)
free⇒full-≈ (PB.trans e f)  = PB.trans (free⇒full-≈ e) (free⇒full-≈ f)
free⇒full-≈ (PB.cong e f)   = PB.cong (free⇒full-≈ e) (free⇒full-≈ f)
free⇒full-≈ PB.assoc        = PB.assoc
free⇒full-≈ PB.left-unit    = PB.left-unit
free⇒full-≈ PB.right-unit   = PB.right-unit
free⇒full-≈ (PB.axiom a)    = PB.axiom (free⇒full a)
