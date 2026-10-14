------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of P′ are sound for the two-level presentation
--
-- `sound-ax` reads each rule of `Rules` through asG and sends it to
-- its derivation in `SoundLemmas`; `sound` extends that to the
-- congruence.  So two words over P′ that the rules identify denote
-- words over the two-level generators that Bian and Selinger's
-- relations identify — the soundness half of comparing the P′ theory
-- with Clifford+CS-TwoLevel's presentation of U_N(ℤ[½,i]).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.Sound (N : ℕ) where

open import Data.Fin.Properties using (<-trans ; <⇒≢)
open import Word.Base using (Word ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (s<)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
open _R,_===_
open import Examples.Groups.Clifford+CS.Auxiliary.SoundBase N
  using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open import Examples.Groups.Clifford+CS.Auxiliary.SoundLemmas N

------------------------------------------------------------------------
-- Each rule

sound-ax : ∀ {u v : Word (GenP N)} → N R, u === v → (asG ʷ) u ≈ (asG ʷ) v
sound-ax (pp-id a)                 = sd-pp-id a
sound-ax (pp-ord a b)              = sd-pp-ord a b
sound-ax (pp-comm a b c d)         = sd-pp-comm a b c d
sound-ax (pp-tele a b c)           = sd-pp-tele a b c
sound-ax (px-sq a a′ s)            = sd-px-sq a a′ (s< s)
sound-ax (px-braid a a′ a″ s s′)   = sd-px-braid a a′ a″ (s< s) (s< s′)
sound-ax (px-shrink₁ a a′ c s lt)  = sd-px-shrink₁ a a′ c (s< s) lt
sound-ax (px-shrink₂ a a′ c s lt)  = sd-px-shrink₂ a a′ c (s< s) lt
sound-ax (px-shrink₃ a c′ c s lt)  = sd-px-shrink₃ a c′ c lt (s< s)
sound-ax (px-shrink₄ a c′ c s lt)  = sd-px-shrink₄ a c′ c lt (s< s)
sound-ax (px-inv a a′ s)           = sd-px-inv a a′ (s< s)
-- The rule's right side is bracketed to the right.
sound-ax (px-sign c a b ab)        = trans (sd-px-sign c a b ab) assoc
sound-ax (px-conj a a′ c s ca ca′) = sd-px-conj a a′ c (s< s) ca ca′
sound-ax (px-conj₂ a a′ s)         = sd-px-conj₂ a a′ (s< s)
-- a < a′ < b < b′: the four indices are distinct.
sound-ax (px-comm a a′ b b′ s s′ lt) =
  sd-px-comm a a′ b b′ (s< s) (s< s′)
    (<⇒≢ (<-trans (s< s) lt)) (<⇒≢ (<-trans (<-trans (s< s) lt) (s< s′)))
    (<⇒≢ lt) (<⇒≢ (<-trans lt (s< s′)))
sound-ax (dx-split a b c d ab cd)  = sd-dx-split a b c d ab cd
sound-ax (ki-sink a b s t ab)       = sd-ki-sink a b s t ab
sound-ax (ki-pp a b s x ab xa xb sa sb) = sd-ki-pp a b s x ab xa xb sa sb
sound-ax (ki-px a b s x y ab xy xa xb ya yb sa sb sx sy) =
  sd-ki-px a b s x y ab xy xa xb ya yb sa sb sx sy
sound-ax (ki-ki a b c d s ab cd ca cb da db sa sb sc sd) =
  sd-ki-ki a b c d s ab cd ca cb da db sa sb sc sd
sound-ax (ki-swap j k l s p q sj sk sl)  = sd-ki-swap j k l s p q sj sk sl
sound-ax (ki-swap′ j k l s p q sj sk sl) = sd-ki-swap′ j k l s p q sj sk sl
sound-ax (ki-x a b s ab sa sb)       = sd-ki-x a b s ab sa sb
sound-ax (ki-16 a b s ab sa sb)      = sd-ki-16 a b s ab sa sb
sound-ax (ki-ii a b s ab sa sb)      = sd-ki-ii a b s ab sa sb
sound-ax (ki-sq a b s ab sa sb)      = sd-ki-sq a b s ab sa sb
sound-ax (ki-yb j k l m s jk lm jl km kl sj sk sl sm) =
  sd-ki-yb j k l m s jk lm jl km kl sj sk sl sm

------------------------------------------------------------------------
-- The congruence

sound : ∀ {u v : Word (GenP N)} →
        PB._≈_ (N R,_===_) u v → (asG ʷ) u ≈ (asG ʷ) v
sound PB.refl          = refl
sound (PB.sym e)       = sym (sound e)
sound (PB.trans e f)   = trans (sound e) (sound f)
sound (PB.cong e f)    = cong (sound e) (sound f)
sound PB.assoc         = assoc
sound PB.left-unit     = left-unit
sound PB.right-unit    = right-unit
sound (PB.axiom a)     = sound-ax a
