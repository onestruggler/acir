------------------------------------------------------------------------
-- Presentations of groups
--
-- All scaled Schreier edges reduce to the three dyadic primitives
-- plus IH.  The four additional edge plans are H and MM(0,1) H.
-- Every plan equality is derived from Tables 1 and 2.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _*_)

module Examples.Groups.CCX+H.GeneralN.ScaledEdgePlans (k : ℕ) where

open import Data.Fin.Base using (zero ; suc)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH.Subgroup.Presentation as Dyadic
import Examples.Groups.CCX+H.GeneralN.Presentation as Scaled
import Examples.Groups.CCX+H.GeneralN.EdgePlans as Plans
import Examples.Groups.CCX+H.GeneralN.SignedEdges as Signed
import Examples.Groups.CCX+H.GeneralN.HadamardSchreier as Hadamard
open import Examples.Groups.CCX+H.GeneralN.Action
  using (Coset ; c00 ; c10 ; c11 ; c01)
open import Presentation.Base (T._===ᴸ_ {6 + k * 2}) hiding (_===_)

module Auxiliary = Scaled (2 + k)
module D = Plans (k * 2)
private
  module Y = Dyadic (4 + k * 2)
  module S = Signed (4 + k * 2)
  module H = Hadamard (2 + k)

data Primitive : Set where
  dyadic : D.Primitive → Primitive
  hadamard : Primitive

e : Primitive → Word (T.Genᴸ (6 + k * 2))
e (dyadic p) = T.⌊ D.e p ⌋ʷ
e hadamard = T.H

read : Word Primitive → Word (T.Genᴸ (6 + k * 2))
read = e ʷ

private
  lift : Word D.Primitive → Word Primitive
  lift = wmap dyadic

  lift-read : ∀ w → read (lift w) ≡ T.⌊ D.read w ⌋ʷ
  lift-read [ p ]ʷ = Eq.refl
  lift-read ε = Eq.refl
  lift-read (u • v) = Eq.cong₂ _•_ (lift-read u) (lift-read v)

  lift-edge : ∀ q g → Auxiliary.e (q , T.⌊ g ⌋) ≡ T.⌊ Y.e (q , g) ⌋ʷ
  lift-edge c00 (U.M-gen a) = Eq.refl
  lift-edge c10 (U.M-gen a) = Eq.refl
  lift-edge c11 (U.M-gen a) = Eq.refl
  lift-edge c01 (U.M-gen a) = Eq.refl
  lift-edge c00 (U.X-gen a b ab) = Eq.refl
  lift-edge c10 (U.X-gen a b ab) = Eq.refl
  lift-edge c11 (U.X-gen a b ab) = Eq.refl
  lift-edge c01 (U.X-gen a b ab) = Eq.refl
  lift-edge c00 (U.K-gen a b c d ab bc cd) = Eq.refl
  lift-edge c10 (U.K-gen a b c d ab bc cd) = Eq.refl
  lift-edge c11 (U.K-gen a b c d ab bc cd) = Eq.refl
  lift-edge c01 (U.K-gen a b c d ab bc cd) = Eq.refl

  pair : Word Primitive
  pair = [ dyadic (D.signed (S.MM zero (suc zero))) ]ʷ

plan : Auxiliary.Edge → Word Primitive
plan (q , T.⌊ g ⌋) = lift (D.plan (q , g))
plan (c00 , T.IH) = [ hadamard ]ʷ
plan (c10 , T.IH) = pair • [ hadamard ]ʷ
plan (c11 , T.IH) = pair • [ hadamard ]ʷ
plan (c01 , T.IH) = pair • [ hadamard ]ʷ

correct : ∀ y → Auxiliary.e y ≈ read (plan y)
correct (q , T.⌊ g ⌋) = trans (refl' (lift-edge q g))
  (trans (T.⌊⌋-cong (D.correct (q , g)))
    (refl' (Eq.sym (lift-read (D.plan (q , g))))))
correct (c00 , T.IH) = trans assoc H.edge00
correct (c10 , T.IH) = trans assoc H.edge10
correct (c11 , T.IH) = trans assoc H.edge11
correct (c01 , T.IH) = trans assoc H.edge01
