------------------------------------------------------------------------
-- Presentations of groups
--
-- Independent spectator wires can be added in either order.  The
-- general lemma reduces this vector identity to commuting coordinate
-- embeddings; Binary supplies the concrete arithmetic instance.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH.EncodingSemantics.Interchange
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Nat.Base using (ℕ) renaming (_*_ to _*ℕ_)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates as Coordinates
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks

open Action isCR adjI h using (_!_ ; vec-ext)
open EmbedAction isCR adjI h using (restrict ; restrict-!)
open Blocks isCR adjI h using (parallel ; parallel-left ; parallel-right ; restrict-ext)

private variable m n k : ℕ

duplicate : Partition m n → (Vec A m → Vec A m) → Vec A n → Vec A n
duplicate p f = parallel p f f

duplicate-restrict : ∀ (p : Partition m n) f b v →
  restrict (select p b) (duplicate p f v) ≡ f (restrict (select p b) v)
duplicate-restrict p f false = parallel-left p f f
duplicate-restrict p f true = parallel-right p f f

module Square (p r : Partition m n) (q s : Partition n k)
  (commute : ∀ a b i →
    ι (select q a) (ι (select p b) i) ≡
    ι (select s b) (ι (select r a) i)) where

  restrict-commute : ∀ a b v →
    restrict (select p b) (restrict (select q a) v) ≡
    restrict (select r a) (restrict (select s b) v)
  restrict-commute a b v = vec-ext λ i →
    trans (restrict-! (select p b) (restrict (select q a) v) i)
      (trans (restrict-! (select q a) v (ι (select p b) i))
        (trans (cong (v !_) (commute a b i))
          (trans (sym (restrict-! (select s b) v (ι (select r a) i)))
            (sym (restrict-! (select r a) (restrict (select s b) v) i)))))

  interchange : ∀ f v →
    duplicate q (duplicate p f) v ≡ duplicate s (duplicate r f) v
  interchange f v = restrict-ext q
    (restrict-ext p (at false false) (at false true))
    (restrict-ext p (at true false) (at true true))
    where
    at : ∀ a b →
      restrict (select p b) (restrict (select q a) (duplicate q (duplicate p f) v)) ≡
      restrict (select p b) (restrict (select q a) (duplicate s (duplicate r f) v))
    at a b = begin
      restrict (select p b) (restrict (select q a) (duplicate q (duplicate p f) v))
        ≡⟨ cong (restrict (select p b)) (duplicate-restrict q (duplicate p f) a v) ⟩
      restrict (select p b) (duplicate p f (restrict (select q a) v))
        ≡⟨ duplicate-restrict p f b (restrict (select q a) v) ⟩
      f (restrict (select p b) (restrict (select q a) v))
        ≡⟨ cong f (restrict-commute a b v) ⟩
      f (restrict (select r a) (restrict (select s b) v))
        ≡⟨ sym (duplicate-restrict r f a (restrict (select s b) v)) ⟩
      restrict (select r a) (duplicate r f (restrict (select s b) v))
        ≡⟨ cong (restrict (select r a)) (sym (duplicate-restrict s (duplicate r f) b v)) ⟩
      restrict (select r a) (restrict (select s b) (duplicate s (duplicate r f) v))
        ≡⟨ sym (restrict-commute a b (duplicate s (duplicate r f) v)) ⟩
      restrict (select p b) (restrict (select q a) (duplicate s (duplicate r f) v)) ∎
      where open ≡-Reasoning

top-bottom : ∀ m (f : Vec A m → Vec A m) v →
  duplicate (contiguous (2 *ℕ m)) (duplicate (alternating m) f) v ≡
  duplicate (alternating (2 *ℕ m)) (duplicate (contiguous m) f) v
top-bottom m = Square.interchange (alternating m) (contiguous m)
  (contiguous (2 *ℕ m)) (alternating (2 *ℕ m)) (Coordinates.commute m)
