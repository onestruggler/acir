------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of P′
--
-- The K-free fragment's rules verbatim — the constructors carry the
-- same names, so a derivation reads the same at either relation — plus
-- the rules of the hybrid letter K_[a,b] i_[s]⁻¹, which are the
-- two-level relations of K read through the embedding
--
--     i_[a] ↦ i_[a] i_[s]⁻¹,   X_[a,b] ↦ (−1)_[s] X_[a,b],
--     K_[a,b] ↦ K_[a,b] i_[s]⁻¹
--
-- at a sink s off the relation's indices: the commutations (4)–(9),
-- the swap relations (13), (14) and the relations (15)–(19), each
-- verbatim, so that item (b) of the Reidemeister–Schreier method for a
-- relation with a K is an instance of its rule (order-K follows from
-- (18)).  One rule more moves the sink along a phase pair, which is
-- what lets the coset action and the embedding use different sinks.
-- All were checked on exact matrices at every admissible index
-- assignment (scratchpad/tKI.py, N = 8).
--
-- Relation (16) must be among them: K′ = −K on its block satisfies
-- every two-level relation but (16), and fails item (b) for it
-- (scratchpad/tM16.py) — the first design, with the K pair
-- K_[a,b] K_[c,d]⁻¹ for a letter, had to add it as a rule of its own.
--
-- What is still missing is the Gray-code layer: the rules relating a
-- hybrid letter to the encoded letters of a width, which come with the
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

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment
  using (Succ ; s< ; pw ; xw ; dw ; _F,_===_)
open _F,_===_

private
  variable
    N : ℕ

-- The hybrid letter as a word.
kiw : (a b s : Fin N) → .(a < b) → Word (GenP N)
kiw a b s p = [ ki a b s p ]ʷ

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

  -- The sink moves along a phase pair: K i_s⁻¹ · i_s i_t⁻¹ = K i_t⁻¹.
  ki-sink : ∀ a b s t .(ab : a < b) →
            N R, kiw a b s ab • pw s t === kiw a b t ab

  -- (4)–(9): K commutes with what it does not touch.
  ki-pp : ∀ a b s x .(ab : a < b) → x ≢ a → x ≢ b → s ≢ a → s ≢ b →
          N R, pw x s • kiw a b s ab === kiw a b s ab • pw x s
  ki-px : ∀ a b s x y .(ab : a < b) .(xy : x < y) →
          x ≢ a → x ≢ b → y ≢ a → y ≢ b → s ≢ a → s ≢ b → s ≢ x → s ≢ y →
          N R, xw s x y xy • kiw a b s ab === kiw a b s ab • xw s x y xy
  ki-ki : ∀ a b c d s .(ab : a < b) .(cd : c < d) →
          c ≢ a → c ≢ b → d ≢ a → d ≢ b →
          s ≢ a → s ≢ b → s ≢ c → s ≢ d →
          N R, kiw a b s ab • kiw c d s cd === kiw c d s cd • kiw a b s ab

  -- (13), (14): X_[j,k] swaps the indices j and k of K.
  ki-swap : ∀ j k l s .(p : j < k) .(q : k < l) → s ≢ j → s ≢ k → s ≢ l →
            N R, kiw k l s q • xw s j k p === xw s j k p • kiw j l s (<-trans p q)
  ki-swap′ : ∀ j k l s .(p : j < k) .(q : k < l) → s ≢ j → s ≢ k → s ≢ l →
             N R, kiw j l s (<-trans p q) • xw s k l q === xw s k l q • kiw j k s p

  -- (15)–(18).
  ki-x : ∀ a b s .(ab : a < b) → s ≢ a → s ≢ b →
         N R, kiw a b s ab • (pw b s • pw b s) === xw s a b ab • kiw a b s ab
  ki-16 : ∀ a b s .(ab : a < b) → s ≢ a → s ≢ b →
          N R, kiw a b s ab • (pw b s • (pw b s • pw b s))
          === pw b s • (kiw a b s ab • (pw b s • kiw a b s ab))
  ki-ii : ∀ a b s .(ab : a < b) → s ≢ a → s ≢ b →
          N R, kiw a b s ab • (pw a s • pw b s) === pw a s • (pw b s • kiw a b s ab)
  ki-sq : ∀ a b s .(ab : a < b) → s ≢ a → s ≢ b →
          N R, (kiw a b s ab • kiw a b s ab) • (pw a s • pw b s) === ε

  -- (19).
  ki-yb : ∀ j k l m s .(jk : j < k) .(lm : l < m) .(jl : j < l) .(km : k < m) →
          k ≢ l → s ≢ j → s ≢ k → s ≢ l → s ≢ m →
          N R, kiw j k s jk • (kiw l m s lm • (kiw j l s jl • kiw k m s km))
          === kiw j l s jl • (kiw k m s km • (kiw j k s jk • kiw l m s lm))

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
