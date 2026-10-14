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
sound-ax (kk-inv a b c d ab cd)    = sd-kk-inv a b c d ab cd
sound-ax (kk-sq a b c d ab cd ca cb da db) =
  sd-kk-sq a b c d ab cd ca cb da db
sound-ax (kk-bridge a b c d e f ab cd ef) =
  sd-kk-bridge a b c d e f ab cd ef
sound-ax (kk-pp a b c d x y ab cd xa xb xc xd ya yb yc yd) =
  sd-kk-pp a b c d x y ab cd xa xb xc xd ya yb yc yd
sound-ax (kk-px a b c d s x y ab cd xy sa sb sc sd
                xa xb xc xd ya yb yc yd) =
  sd-kk-px a b c d s x y ab cd xy sa sb sc sd xa xb xc xd ya yb yc yd
sound-ax (kk-kk a b c d e f g h ab cd ef gh
                ea eb ec ed fa fb fc fd ga gb gc gd ha hb hc hd) =
  sd-kk-kk a b c d e f g h ab cd ef gh
           ea eb ec ed fa fb fc fd ga gb gc gd ha hb hc hd
sound-ax (kk-mm a b c d ab cd ca cb da db) =
  sd-kk-mm a b c d ab cd ca cb da db
sound-ax (kk-ii a b c d e ab cd ca cb da db ea eb ec ed) =
  sd-kk-ii a b c d e ab cd ca cb da db ea eb ec ed
sound-ax (kk-x a b c d e ab cd ca cb da db ea eb ec ed) =
  sd-kk-x a b c d e ab cd ca cb da db ea eb ec ed
sound-ax (kk-conj a b c d ab cd ca cb da db) =
  sd-kk-conj a b c d ab cd ca cb da db
sound-ax (kk-ren a b c d e f ab cd ae bf ef
                 ca cb ce cf da db de df ea eb fa fb) =
  sd-kk-ren a b c d e f ab cd ae bf ef
            ca cb ce cf da db de df ea eb fa fb
sound-ax (kk-yb a b c d e f g h ab cd ac bd ef gh bc
                ea eb ec ed fa fb fc fd ga gb gc gd ha hb hc hd
                ge gf he hf) =
  sd-kk-yb a b c d e f g h ab cd ac bd ef gh bc
           ea eb ec ed fa fb fc fd ga gb gc gd ha hb hc hd ge gf he hf

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
