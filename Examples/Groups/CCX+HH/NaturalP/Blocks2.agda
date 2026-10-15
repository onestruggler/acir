------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-by-two blocks of vector operators, and a control on wire 0.
--
-- Interchange.Square swaps two nested partitions when the same operator
-- runs on every block.  A controlled operator runs different ones on
-- different blocks, so here the four blocks carry four operators
-- (`interchange₂`).  `ctrlA f` is f controlled by wire 0 (identity on
-- the even coordinates, f on the odd ones: wire 0 is the least
-- significant bit), and `top-ctrl` says that an idle wire on top commutes
-- with the control.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Blocks2 where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ) renaming (_*_ to _*ℕ_)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
open EmbedAction isCommutativeRing-D adj-D ½ᴰ using (restrict)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (Partition ; select ; parallel ; parallel-left ; parallel-right ; restrict-ext
        ; parallel-id ; parallel-cong ; parallel-compose)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange
import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates as Coordinates
private module I = Interchange isCommutativeRing-D adj-D ½ᴰ

private
  variable
    m n k : ℕ

Op : ℕ → Set
Op m = Vec D m → Vec D m

-- The operator on side b of a partition.
pick : Op m → Op m → Bool → Op m
pick f g false = f
pick f g true  = g

parallel-select : (p : Partition m n) (f g : Op m) (b : Bool) (v : Vec D n) →
  restrict (select p b) (parallel p f g v) ≡ pick f g b (restrict (select p b) v)
parallel-select p f g false v = parallel-left p f g v
parallel-select p f g true  v = parallel-right p f g v

module Square₂ (p r : Partition m n) (q s : Partition n k)
  (commute : ∀ a b i →
    ι (select q a) (ι (select p b) i) ≡ ι (select s b) (ι (select r a) i)) where

  open I.Square p r q s commute using (restrict-commute)

  -- f a b runs on the block that is side a of q and side b of p, that
  -- is, side b of s and side a of r.
  interchange₂ : (f : Bool → Bool → Op m) (v : Vec D k) →
    parallel q (parallel p (f false false) (f false true))
               (parallel p (f true false) (f true true)) v ≡
    parallel s (parallel r (f false false) (f true false))
               (parallel r (f false true) (f true true)) v
  interchange₂ f v = restrict-ext q
    (restrict-ext p (at false false) (at false true))
    (restrict-ext p (at true false) (at true true))
    where
    L = parallel q (parallel p (f false false) (f false true))
                   (parallel p (f true false) (f true true)) v
    R = parallel s (parallel r (f false false) (f true false))
                   (parallel r (f false true) (f true true)) v
    lhs-at : ∀ a b → restrict (select p b) (restrict (select q a) L) ≡
                     f a b (restrict (select p b) (restrict (select q a) v))
    lhs-at a b = trans (cong (restrict (select p b)) (parallel-select q
        (parallel p (f false false) (f false true)) (parallel p (f true false) (f true true)) a v))
      (trans (cong (restrict (select p b)) (pick-out a))
        (trans (parallel-select p (f a false) (f a true) b (restrict (select q a) v))
          (pick-in a b (restrict (select p b) (restrict (select q a) v)))))
      where
      pick-out : ∀ a → pick (parallel p (f false false) (f false true))
                            (parallel p (f true false) (f true true)) a (restrict (select q a) v)
                     ≡ parallel p (f a false) (f a true) (restrict (select q a) v)
      pick-out false = refl
      pick-out true = refl
      pick-in : ∀ a b x → pick (f a false) (f a true) b x ≡ f a b x
      pick-in a false x = refl
      pick-in a true x = refl
    rhs-at : ∀ a b → restrict (select r a) (restrict (select s b) R) ≡
                     f a b (restrict (select r a) (restrict (select s b) v))
    rhs-at a b = trans (cong (restrict (select r a)) (parallel-select s
        (parallel r (f false false) (f true false)) (parallel r (f false true) (f true true)) b v))
      (trans (cong (restrict (select r a)) (pick-out b))
        (trans (parallel-select r (f false b) (f true b) a (restrict (select s b) v))
          (pick-in a b (restrict (select r a) (restrict (select s b) v)))))
      where
      pick-out : ∀ b → pick (parallel r (f false false) (f true false))
                            (parallel r (f false true) (f true true)) b (restrict (select s b) v)
                     ≡ parallel r (f false b) (f true b) (restrict (select s b) v)
      pick-out false = refl
      pick-out true = refl
      pick-in : ∀ a b x → pick (f false b) (f true b) a x ≡ f a b x
      pick-in false b x = refl
      pick-in true b x = refl
    at : ∀ a b → restrict (select p b) (restrict (select q a) L) ≡
                 restrict (select p b) (restrict (select q a) R)
    at a b = trans (lhs-at a b)
      (trans (cong (f a b) (restrict-commute a b v))
        (trans (sym (rhs-at a b)) (sym (restrict-commute a b R))))

------------------------------------------------------------------------
-- A control on wire 0

-- f on the odd coordinates (wire 0 set), the identity on the even ones.
ctrlA : (M : ℕ) → Op M → Op (2 *ℕ M)
ctrlA M f = parallel (alternating M) (λ x → x) f

-- The idle wire on top of a vector operator.
topA : (M : ℕ) → Op M → Op (2 *ℕ M)
topA M f = parallel (contiguous M) f f

-- An idle wire on top commutes with the control on wire 0.
top-ctrl : ∀ M (f : Op M) v →
  topA (2 *ℕ M) (ctrlA M f) v ≡ ctrlA (2 *ℕ M) (topA M f) v
top-ctrl M f v = trans
  (Square₂.interchange₂ (alternating M) (contiguous M)
    (contiguous (2 *ℕ M)) (alternating (2 *ℕ M)) (Coordinates.commute M)
    (λ a b → pick (λ x → x) f b) v)
  (parallel-cong (alternating (2 *ℕ M))
    {f = parallel (contiguous M) (λ x → x) (λ x → x)} {f′ = λ x → x}
    {g = topA M f} {g′ = topA M f} (parallel-id (contiguous M)) (λ _ → refl) v)
