{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.HadamardRelations.r7d₁_i2345 where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding using (decode)
open import Examples.Groups.CCX+HH-3qubit.Repaired.EvenCompleteness using (even ; from-even)
import Examples.Groups.CCX+HH-3qubit.Normalization as N
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingMatrices as DM
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS

left right : Word (L.Genᴸ 8)
left = (L.H) • (L.Xᴸ (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (s≤s (s≤s (s≤s (s≤s z≤n))))) • (L.H)
right = (L.Xᴸ (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (s≤s (s≤s (s≤s (s≤s z≤n))))) • (L.Kᴸ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

-- Share the computed dyadic bodies. Their abstraction prevents the
-- matrix proof from normalizing a large circuit in its goal type.
abstract
  left-body right-body : Word N.DGen
  left-body = N.Normal.body (N.normalize ((decode ʷ) left))
  right-body = N.Normal.body (N.normalize ((decode ʷ) right))

  left-even : (decode ʷ) left ≈ N.dyadic left-body
  left-even = even (N.normalize ((decode ʷ) left)) Eq.refl
  right-even : (decode ʷ) right ≈ N.dyadic right-body
  right-even = even (N.normalize ((decode ʷ) right)) Eq.refl

proved : (decode ʷ) left ≈ (decode ʷ) right
proved = from-even left-body right-body left-even right-even
  (Eq.trans (Eq.sym (DM.decode-matrix left))
    (Eq.trans (SS.sound-axiom 4 (L.r7d₁ {w = (suc (suc (zero)))} {x = (suc (suc (suc (zero))))} {y = (suc (suc (suc (suc (zero)))))} {z = (suc (suc (suc (suc (suc (zero))))))} (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) Eq.refl Eq.refl Eq.refl Eq.refl)) (DM.decode-matrix right)))
