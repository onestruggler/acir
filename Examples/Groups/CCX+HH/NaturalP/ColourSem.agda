------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled circuits of the two colours, as vector operators.
--
-- X on wire 0 exchanges the even and the odd coordinates (`x-block`,
-- through the interchange of the top and bottom partitions), so it
-- conjugates an operator on the two blocks to the one with the blocks
-- exchanged (`x-conj`).  Hence ctrl⁻ C = X • ctrl C • X acts as C where
-- wire 0 is 0 (`ctrl⁻-sem`), a circuit controlled by wire 0 and one
-- controlled by its negation commute (`opposite-sem`), and a circuit one
-- wire up is the product of its two controlled versions (`split-sem`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.ColourSem where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_ ; _*_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (_•_)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ)
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
open EmbedAction isCommutativeRing-D adj-D ½ᴰ using (restrict)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (Partition ; select ; parallel ; restrict-ext ; parallel-compose)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange
import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates as Coordinates
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; τ-↑ ; interpret)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl ; ctrl⁻)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSem using (ctrl-sem)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (Op ; pick ; parallel-select ; ctrlA)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; quantum-shift)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics using (action⇒matrix)

private
  module I = Interchange isCommutativeRing-D adj-D ½ᴰ

  variable
    n : ℕ

------------------------------------------------------------------------
-- X on wire 0

-- X on wire 0 exchanges the two blocks of the bottom partition.
x-block : ∀ n b (u : Q.State (suc n)) →
  restrict (select (alternating (2 ^ n)) b) (Q.x n u) ≡
  restrict (select (alternating (2 ^ n)) (not b)) u
x-block zero false (a ∷ c ∷ []) = refl
x-block zero true  (a ∷ c ∷ []) = refl
x-block (suc n) b u = restrict-ext r (at false) (at true)
  where
  M = 2 ^ n
  p = alternating M
  r = contiguous M
  q = contiguous (2 * M)
  s = alternating (2 * M)
  open I.Square p r q s (Coordinates.commute M) using (restrict-commute)

  pick-same : ∀ a (w : Q.State (suc n)) → pick (Q.x n) (Q.x n) a w ≡ Q.x n w
  pick-same false w = refl
  pick-same true  w = refl

  at : ∀ a → restrict (select r a) (restrict (select s b) (Q.x (suc n) u)) ≡
             restrict (select r a) (restrict (select s (not b)) u)
  at a = trans (sym (restrict-commute a b (Q.x (suc n) u)))
    (trans (cong (restrict (select p b)) (parallel-select q (Q.x n) (Q.x n) a u))
    (trans (cong (restrict (select p b)) (pick-same a (restrict (select q a) u)))
    (trans (x-block n b (restrict (select q a) u))
      (restrict-commute a (not b) u))))

-- … so it conjugates an operator on the two blocks to the exchanged one.
x-conj : ∀ n (f g : Op (2 ^ n)) (v : Q.State (suc n)) →
  Q.x n (parallel (alternating (2 ^ n)) f g (Q.x n v)) ≡
  parallel (alternating (2 ^ n)) g f v
x-conj n f g v = restrict-ext p (at false) (at true)
  where
  p = alternating (2 ^ n)

  flip : ∀ b (w : Vec D (2 ^ n)) → pick f g (not b) w ≡ pick g f b w
  flip false w = refl
  flip true  w = refl

  back : ∀ b → restrict (select p (not b)) (Q.x n v) ≡ restrict (select p b) v
  back false = x-block n true v
  back true  = x-block n false v

  at : ∀ b → restrict (select p b) (Q.x n (parallel p f g (Q.x n v))) ≡
             restrict (select p b) (parallel p g f v)
  at b = trans (x-block n b (parallel p f g (Q.x n v)))
    (trans (parallel-select p f g (not b) (Q.x n v))
    (trans (cong (pick f g (not b)) (back b))
    (trans (flip b (restrict (select p b) v))
      (sym (parallel-select p g f b v)))))

------------------------------------------------------------------------
-- The two colours

ctrl⁻-sem : (C : P.Circuit (₄₊ n)) → ∀ v →
  quantum (τ (ctrl⁻ C)) v ≡
  parallel (alternating (2 ^ ₄₊ n)) (quantum (τ C)) (λ x → x) v
ctrl⁻-sem {n} C v =
  trans (cong (Q.x (₄₊ n)) (ctrl-sem C (Q.x (₄₊ n) v)))
    (x-conj (₄₊ n) (λ x → x) (quantum (τ C)) v)

-- A circuit controlled by wire 0 and one controlled by its negation
-- commute.
opposite-sem : (A B : P.Circuit (₄₊ n)) →
  interpret (ctrl A • ctrl⁻ B) ≡ interpret (ctrl⁻ B • ctrl A)
opposite-sem {n} A B =
  action⇒matrix {u = τ (ctrl A • ctrl⁻ B)} {v = τ (ctrl⁻ B • ctrl A)} λ v →
  trans (cong (quantum (τ (ctrl A))) (ctrl⁻-sem B v))
  (trans (ctrl-sem A (parallel p qB (λ x → x) v))
  (trans (parallel-compose p (λ x → x) qA qB (λ x → x) v)
  (sym (trans (cong (quantum (τ (ctrl⁻ B))) (ctrl-sem A v))
       (trans (ctrl⁻-sem B (ctrlA (2 ^ ₄₊ n) qA v))
         (parallel-compose p qB (λ x → x) (λ x → x) qA v))))))
  where
  p = alternating (2 ^ ₄₊ n)
  qA = quantum (τ A)
  qB = quantum (τ B)

-- A circuit one wire up is its two controlled versions.
split-sem : (w : P.Circuit (₄₊ n)) →
  interpret (w P.↑) ≡ interpret (ctrl w • ctrl⁻ w)
split-sem {n} w =
  action⇒matrix {u = τ (w P.↑)} {v = τ (ctrl w • ctrl⁻ w)} λ v →
  trans (cong (λ c → quantum c v) (τ-↑ w))
  (trans (quantum-shift (τ w) v)
  (sym (trans (cong (quantum (τ (ctrl w))) (ctrl⁻-sem w v))
       (trans (ctrl-sem w (parallel p qw (λ x → x) v))
         (parallel-compose p (λ x → x) qw qw (λ x → x) v)))))
  where
  p = alternating (2 ^ ₄₊ n)
  qw = quantum (τ w)
