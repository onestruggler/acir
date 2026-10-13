------------------------------------------------------------------------
-- Presentations of groups
--
-- Contiguous spectator blocks are ordinary vector concatenation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH.EncodingSemantics.Append
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Fin.Base using (_↑ˡ_)
open import Data.Nat.Base using (ℕ) renaming (_*_ to _*ℕ_)
open import Data.Vec.Base using (Vec ; [] ; _++_)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks

open Action isCR adjI h using (_!_ ; vec-ext)
open EmbedAction isCR adjI h using (restrict ; restrict-!)
open Blocks isCR adjI h using (parallel ; parallel-left ; parallel-right ; restrict-ext)

private variable m : ℕ

-- The final empty vector matches 2*m = m+(m+0) definitionally.
join : Vec A m → Vec A m → Vec A (2 *ℕ m)
join u v = u ++ (v ++ [])

left-join : (u v : Vec A m) → restrict (left (contiguous m)) (join u v) ≡ u
left-join {m} u v = vec-ext λ i →
  trans (restrict-! (left (contiguous m)) (join u v) i) (VP.lookup-++ˡ u (v ++ []) i)

right-join : (u v : Vec A m) → restrict (right (contiguous m)) (join u v) ≡ v
right-join {m} u v = vec-ext λ i →
  trans (restrict-! (right (contiguous m)) (join u v) i)
    (trans (VP.lookup-++ʳ u (v ++ []) (i ↑ˡ 0)) (VP.lookup-++ˡ v [] i))

join-restrict : (v : Vec A (2 *ℕ m)) →
  join (restrict (left (contiguous m)) v) (restrict (right (contiguous m)) v) ≡ v
join-restrict {m} v = restrict-ext (contiguous m)
  (left-join (restrict (left (contiguous m)) v) (restrict (right (contiguous m)) v))
  (right-join (restrict (left (contiguous m)) v) (restrict (right (contiguous m)) v))

parallel-join : (f g : Vec A m → Vec A m) (u v : Vec A m) →
  parallel (contiguous m) f g (join u v) ≡ join (f u) (g v)
parallel-join {m} f g u v = restrict-ext (contiguous m)
  (trans (parallel-left (contiguous m) f g (join u v))
    (trans (cong f (left-join u v)) (sym (left-join (f u) (g v)))))
  (trans (parallel-right (contiguous m) f g (join u v))
    (trans (cong g (right-join u v)) (sym (right-join (f u) (g v)))))

parallel-split : (f g : Vec A m → Vec A m) (v : Vec A (2 *ℕ m)) →
  parallel (contiguous m) f g v ≡
  join (f (restrict (left (contiguous m)) v)) (g (restrict (right (contiguous m)) v))
parallel-split {m} f g v = restrict-ext (contiguous m)
  (trans (parallel-left (contiguous m) f g v)
    (sym (left-join (f (restrict (left (contiguous m)) v))
      (g (restrict (right (contiguous m)) v)))))
  (trans (parallel-right (contiguous m) f g v)
    (sym (right-join (f (restrict (left (contiguous m)) v))
      (g (restrict (right (contiguous m)) v)))))
