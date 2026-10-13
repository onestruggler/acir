------------------------------------------------------------------------
-- Presentations of groups
--
-- Parallel copies of an auxiliary operator on two disjoint blocks.
-- The block action is defined on vectors, independently of words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH.EncodingSemantics.Blocks
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Vec.Base using (Vec ; tabulate)
open import Relation.Binary.PropositionalEquality

open import Word.Base using (Word ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition public
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction

open Action isCR adjI h
open EmbedAction isCR adjI h

private variable m n : ℕ

module _ (p : Partition m n) where

  private
    l = left p
    r = right p

  -- A direct sum of two vector operators, with either ordering of the
  -- coordinates.  Tensoring with an idle qubit is the case f = g.
  parallel : (Vec A m → Vec A m) → (Vec A m → Vec A m) →
             Vec A n → Vec A n
  parallel f g v = tabulate λ x →
    [ (λ y → f (restrict l v) ! y)
    , (λ y → g (restrict r v) ! y) ]′ (locate p x)

  parallel-left : ∀ f g v → restrict l (parallel f g v) ≡ f (restrict l v)
  parallel-left f g v = vec-ext λ x →
    trans (restrict-! l (parallel f g v) x)
      (trans (!-tabulate _ (ι l x))
        (cong [ (λ y → f (restrict l v) ! y)
              , (λ y → g (restrict r v) ! y) ]′ (locate-left p x)))

  parallel-right : ∀ f g v → restrict r (parallel f g v) ≡ g (restrict r v)
  parallel-right f g v = vec-ext λ x →
    trans (restrict-! r (parallel f g v) x)
      (trans (!-tabulate _ (ι r x))
        (cong [ (λ y → f (restrict l v) ! y)
              , (λ y → g (restrict r v) ! y) ]′ (locate-right p x)))

  restrict-ext : ∀ {u v : Vec A n} →
    restrict l u ≡ restrict l v → restrict r u ≡ restrict r v → u ≡ v
  restrict-ext {u} {v} le re = vec-ext λ x →
    trans (cong (u !_) (sym (cover p x)))
      (trans (at (locate p x)) (cong (v !_) (cover p x)))
    where
    at : ∀ side → u ! [ ι l , ι r ]′ side ≡ v ! [ ι l , ι r ]′ side
    at (inj₁ y) = trans (sym (restrict-! l u y))
      (trans (cong (_! y) le) (restrict-! l v y))
    at (inj₂ y) = trans (sym (restrict-! r u y))
      (trans (cong (_! y) re) (restrict-! r v y))

  private
    other-left : ∀ w v → restrict l (actVʷ (word r w) v) ≡ restrict l v
    other-left w v = vec-ext λ x →
      trans (restrict-! l (actVʷ (word r w) v) x)
        (trans (emb-actVʷ-out r w v (ι l x) (disjoint p x))
          (sym (restrict-! l v x)))

    other-right : ∀ w v → restrict r (actVʷ (word l w) v) ≡ restrict r v
    other-right w v = vec-ext λ x →
      trans (restrict-! r (actVʷ (word l w) v) x)
        (trans (emb-actVʷ-out l w v (ι r x) (λ y eq → disjoint p y x (sym eq)))
          (sym (restrict-! r v x)))

  encode-parallel : Word (Gen m) → Word (Gen m) → Word (Gen n)
  encode-parallel u v = word l u • word r v

  encode-parallel-correct : ∀ u w v →
    actVʷ (encode-parallel u w) v ≡ parallel (actVʷ u) (actVʷ w) v
  encode-parallel-correct u w v = restrict-ext
    (trans (emb-actVʷ-restrict l u (actVʷ (word r w) v))
      (trans (cong (actVʷ u) (other-left w v))
        (sym (parallel-left (actVʷ u) (actVʷ w) v))))
    (trans (other-right u (actVʷ (word r w) v))
      (trans (emb-actVʷ-restrict r w v)
        (sym (parallel-right (actVʷ u) (actVʷ w) v))))

  parallel-cong : ∀ {f f′ g g′ : Vec A m → Vec A m} →
    (∀ v → f v ≡ f′ v) → (∀ v → g v ≡ g′ v) →
    ∀ v → parallel f g v ≡ parallel f′ g′ v
  parallel-cong {f} {f′} {g} {g′} ff gg v = restrict-ext
    (trans (parallel-left f g v)
      (trans (ff (restrict l v)) (sym (parallel-left f′ g′ v))))
    (trans (parallel-right f g v)
      (trans (gg (restrict r v)) (sym (parallel-right f′ g′ v))))

  parallel-id : ∀ v → parallel (λ x → x) (λ x → x) v ≡ v
  parallel-id v = restrict-ext
    (parallel-left (λ x → x) (λ x → x) v)
    (parallel-right (λ x → x) (λ x → x) v)

  parallel-compose : ∀ f g f′ g′ v →
    parallel f g (parallel f′ g′ v) ≡
    parallel (λ x → f (f′ x)) (λ x → g (g′ x)) v
  parallel-compose f g f′ g′ v = restrict-ext
    (trans (parallel-left f g (parallel f′ g′ v))
      (trans (cong f (parallel-left f′ g′ v))
        (sym (parallel-left (λ x → f (f′ x)) (λ x → g (g′ x)) v))))
    (trans (parallel-right f g (parallel f′ g′ v))
      (trans (cong g (parallel-right f′ g′ v))
        (sym (parallel-right (λ x → f (f′ x)) (λ x → g (g′ x)) v))))
