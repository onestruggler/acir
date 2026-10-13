------------------------------------------------------------------------
-- Presentations of groups
--
-- The physical mixed atom M_a X_bc K_abcd at every width at least four.
-- Five fresh levels provide a disjoint K block and a spare sign.  The
-- circuit is the square of a paired K followed by a sign pair.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.GeneralN.MixedPhysical (n : ℕ) where

open import Data.Fin.Base using (Fin ; suc ; _<_)
open import Data.Fin.Properties using (<⇒≢)
open import Data.Nat.Base using (_≤_ ; s≤s ; z≤n)
import Data.Nat.Properties as NP
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; _•_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; mono ; emb ; _∷ᵢ_ ; [_]ᵢ)
import Examples.Groups.CCX+HH.GeneralN.KPairBase as Base
import Examples.Groups.CCX+H.GeneralN.KPairRouting as Route
import Examples.Groups.CCX+H.GeneralN.SignPair as Sign
import Examples.Groups.CCX+H.GeneralN.MixedAtom as Mixed
open import Examples.Groups.CCX+HH.GeneralN.FiveFreshLevels using (five ; module Five)
open import Examples.Groups.CCX+HH.GeneralN.PhysicalEquality using (product)

width = 4 + n
Level = Fin (2 ^ width)

private
  bound : 9 ≤ 2 ^ width
  bound = NP.≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
    (NP.^-monoʳ-≤ 2 {4} {4 + n} (NP.m≤m+n 4 n))

module Block (a b c d : Level) (ab : a < b) (bc : b < c) (cd : c < d) where

  private
    module F = Five (five (a ∷ b ∷ c ∷ d ∷ []) bound)
    e = ι F.levels ₀
    f = ι F.levels ₁
    g = ι F.levels ₂
    h = ι F.levels ₃
    i = ι F.levels ₄
    fg : f < g
    fg = mono F.levels {a = ₁} {b = ₂} (s≤s (s≤s z≤n))
    gh : g < h
    gh = mono F.levels {a = ₂} {b = ₃} (s≤s (s≤s (s≤s z≤n)))
    hi : h < i
    hi = mono F.levels {a = ₃} {b = ₄} (s≤s (s≤s (s≤s (s≤s z≤n))))

    module B = Base n
    source : Emb 8 (2 ^ width)
    source = record { ι = B.level ; mono = B.increasing }

    target : Route.DisjointBlocks n
    target = record
      { first = emb (a ∷ b ∷ c ∷ d ∷ []) (ab ∷ᵢ bc ∷ᵢ cd ∷ᵢ [ d ]ᵢ)
      ; second = record { ι = λ j → ι F.levels (suc j) ; mono = λ p → mono F.levels (s≤s p) }
      ; apart = λ j k eq → F.outside (suc k) j (sym eq)
      }
    module Pair = Route.Compile n source B.circuit B.correct target
    module S = Sign n

    module M = Mixed.Block a b c d e f g h i ab bc cd fg gh hi
      (λ eq → F.outside ₁ ₀ (sym eq)) (λ eq → F.outside ₂ ₀ (sym eq))
      (λ eq → F.outside ₃ ₀ (sym eq)) (λ eq → F.outside ₄ ₀ (sym eq))
      (λ eq → F.outside ₁ ₁ (sym eq)) (λ eq → F.outside ₂ ₁ (sym eq))
      (λ eq → F.outside ₃ ₁ (sym eq)) (λ eq → F.outside ₄ ₁ (sym eq))
      (λ eq → F.outside ₁ ₂ (sym eq)) (λ eq → F.outside ₂ ₂ (sym eq))
      (λ eq → F.outside ₃ ₂ (sym eq)) (λ eq → F.outside ₄ ₂ (sym eq))
      (λ eq → F.outside ₁ ₃ (sym eq)) (λ eq → F.outside ₂ ₃ (sym eq))
      (λ eq → F.outside ₃ ₃ (sym eq)) (λ eq → F.outside ₄ ₃ (sym eq))
      (F.outside ₀ ₀) (F.outside ₀ ₁) (F.outside ₀ ₂) (F.outside ₀ ₃)
      (<⇒≢ (mono F.levels {a = ₀} {b = ₁} (s≤s z≤n)))
      (<⇒≢ (mono F.levels {a = ₀} {b = ₂} (s≤s z≤n)))
      (<⇒≢ (mono F.levels {a = ₀} {b = ₃} (s≤s z≤n)))
      (<⇒≢ (mono F.levels {a = ₀} {b = ₄} (s≤s z≤n)))

    one : H.Circuit width
    one = Pair.circuit • S.circuit a e

    one-correct : Q.interpret one ≡ A.⟦ M.Q • M.S ⟧ᵐ
    one-correct = product Pair.circuit (S.circuit a e) M.Q M.S Pair.correct (S.correct a e)

  circuit : H.Circuit width
  circuit = one • one

  auxiliary : Word (T.Gen (2 ^ width))
  auxiliary = (T.M a • T.X b c bc) • T.K a b c d ab bc cd

  correct : Q.interpret circuit ≡ A.⟦ auxiliary ⟧ᵐ
  correct = trans (product one one (M.Q • M.S) (M.Q • M.S) one-correct one-correct)
    (Red.sound-act M.mixed A.𝕀)
