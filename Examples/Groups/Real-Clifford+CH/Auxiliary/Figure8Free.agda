------------------------------------------------------------------------
-- Presentations of groups
--
-- The Hadamard-free fragment of Figure 8
--
-- Equations (20)–(34) of Clément's Figure 8 are exactly those whose
-- two sides carry no Hadamard letter, so both sides of each denote a
-- *signed permutation* of the basis.  The congruence they generate is
-- therefore modelled by signed permutations, which the whole theory is
-- not — (41) says a Hadamard pair squared is the identity, and no
-- signed permutation reading of a Hadamard letter can make that true.
--
-- That model is what Lemma A.4's uniqueness needs, and it is the
-- reason this fragment is a relation of its own rather than a
-- selection of Figure 8's: a selection would put a proof beside every
-- `axiom (rNN …)` in the derivations, and there are some hundreds of
-- them.  With the rules restated, the derivations are unchanged; only
-- the relation they are read at moves.
--
-- `free⇒full` and `free⇒full-≈` carry everything proved here back into
-- Figure 8, whose congruence is larger.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (ℕ ; suc ; _∸_ ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Word.Base using (Word ; WRel ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 as F8
open F8 using (Succ) public
open F8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx)

private
  variable
    m : ℕ

------------------------------------------------------------------------
-- The rules
--
-- Equations (20)–(34), verbatim from `Figure8`; the constructors carry
-- the same names, so a derivation reads the same at either relation.

infix 4 _PF,_===_
data _PF,_===_ (m : ℕ) : WRel (GenP (₃₊ m)) where

  -- (20)–(22): the signs.
  r20 : ∀ a → m PF, zz a a === ε
  r21 : ∀ a b → m PF, zz a b === zz b a
  r22 : ∀ a b c → m PF, zz a b • zz b c === zz a c

  -- (23)–(29): the signed exchanges of consecutive indices.
  r23 : ∀ a a′ → Succ a a′ → m PF, zz a a′ === zx a a a′ • zx a a a′
  r24 : ∀ a a′ a″ → Succ a a′ → Succ a′ a″ →
        m PF, zx a a a′ • zx a′ a′ a″ • zx a a a′ === zx a′ a′ a″ • zx a a a′ • zx a′ a′ a″
  r25 : ∀ a a′ c → Succ a a′ → toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
        m PF, zx a a c === zx a′ a a′ • zx a′ a′ c • zx a a a′
  r26 : ∀ a a′ c → Succ a a′ → toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
        m PF, zx c a c === zx a′ a a′ • zx c a′ c • zx a a a′
  r27 : ∀ a c′ c → Succ c′ c → suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
        m PF, zx a a c === zx c′ c′ c • zx a a c′ • zx c c′ c
  r28 : ∀ a c′ c → Succ c′ c → suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
        m PF, zx c a c === zx c′ c′ c • zx c′ a c′ • zx c c′ c
  r29 : ∀ a a′ → Succ a a′ → m PF, zx a a a′ • zx a′ a a′ === ε

  -- (30)–(34): the other exchanges.
  r30 : ∀ c a b → a ≢ b → c ≢ a → c ≢ b → m PF, zx c a b === zz c a • zx a a b
  r31 : ∀ a a′ c → Succ a a′ → c ≢ a → c ≢ a′ →
        m PF, zz a′ c • zx a a a′ === zx a a a′ • zz a c
  r32 : ∀ a a′ b b′ → Succ a a′ → Succ b b′ → toℕ a′ < toℕ b →
        m PF, zx a a a′ • zx b b b′ === zx b b b′ • zx a a a′
  r33 : ∀ b a → m PF, zx b a b === zx b b a
  r34 : ∀ a b c d → a ≢ b → c ≢ d → m PF, xx a b c d === zx a a b • zx b c d

------------------------------------------------------------------------
-- Back into Figure 8

free⇒full : ∀ {u v : Word (GenP (₃₊ m))} → m PF, u === v → m P, u === v
free⇒full (r20 a)                 = F8.r20 a
free⇒full (r21 a b)               = F8.r21 a b
free⇒full (r22 a b c)             = F8.r22 a b c
free⇒full (r23 a a′ s)            = F8.r23 a a′ s
free⇒full (r24 a a′ a″ s s′)      = F8.r24 a a′ a″ s s′
free⇒full (r25 a a′ c s lt p)     = F8.r25 a a′ c s lt p
free⇒full (r26 a a′ c s lt p)     = F8.r26 a a′ c s lt p
free⇒full (r27 a c′ c s lt p)     = F8.r27 a c′ c s lt p
free⇒full (r28 a c′ c s lt p)     = F8.r28 a c′ c s lt p
free⇒full (r29 a a′ s)            = F8.r29 a a′ s
free⇒full (r30 c a b ab ca cb)    = F8.r30 c a b ab ca cb
free⇒full (r31 a a′ c s ca ca′)   = F8.r31 a a′ c s ca ca′
free⇒full (r32 a a′ b b′ s s′ lt) = F8.r32 a a′ b b′ s s′ lt
free⇒full (r33 b a)               = F8.r33 b a
free⇒full (r34 a b c d ab cd)     = F8.r34 a b c d ab cd

-- And the congruence with it: the larger theory proves whatever the
-- fragment proves.
free⇒full-≈ : ∀ {u v : Word (GenP (₃₊ m))} →
              PB._≈_ (m PF,_===_) u v → PB._≈_ (m P,_===_) u v
free⇒full-≈ PB.refl         = PB.refl
free⇒full-≈ (PB.sym e)      = PB.sym (free⇒full-≈ e)
free⇒full-≈ (PB.trans e e′) = PB.trans (free⇒full-≈ e) (free⇒full-≈ e′)
free⇒full-≈ (PB.cong e e′)  = PB.cong (free⇒full-≈ e) (free⇒full-≈ e′)
free⇒full-≈ PB.assoc        = PB.assoc
free⇒full-≈ PB.left-unit    = PB.left-unit
free⇒full-≈ PB.right-unit   = PB.right-unit
free⇒full-≈ (PB.axiom a)    = PB.axiom (free⇒full a)
