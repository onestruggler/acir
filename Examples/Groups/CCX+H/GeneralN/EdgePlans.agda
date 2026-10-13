------------------------------------------------------------------------
-- Presentations of groups
--
-- An unconditional finite plan for every dyadic Schreier edge at
-- dimensions >= 6.  The plans use only sign pairs, double exchanges,
-- and mixed M_a X_bc K_abcd atoms.  Their correctness is a derivation
-- from Table 1.  Physical realization of these three primitives is
-- the remaining circuit-specific part of the decoder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.EdgePlans (N : ℕ) where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
import Examples.Groups.CCX+HH.Subgroup.Presentation as Sub
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00 ; c10 ; c11 ; c01)
import Examples.Groups.CCX+H.GeneralN.DyadicSchreier as Factor
import Examples.Groups.CCX+H.GeneralN.SignedEdges as Signed
open import Examples.Groups.CCX+H.GeneralN.SpareLevels using (two-spares ; module TwoSpares)
open import Presentation.Base (U._===_ {6 + N}) hiding (_===_)

private
  module P = Sub (4 + N)
  module S = Signed (4 + N)
  open D using (_⁻¹ ; ⁻¹-cong)

data Primitive : Set where
  signed : S.Atom → Primitive
  mixed : (a b c d : Fin (6 + N)) → .(a < b) → .(b < c) → .(c < d) → Primitive

e : Primitive → Word (U.Gen (6 + N))
e (signed a) = S.e a
e (mixed a b c d ab bc cd) =
  (U.M a • U.X b c bc) • U.K a b c d ab bc cd

read : Word Primitive → Word (U.Gen (6 + N))
read = e ʷ

private
  lift : Word S.Atom → Word Primitive
  lift = wmap signed

  signed-read : ∀ w → read (lift w) ≡ S.decode w
  signed-read [ a ]ʷ = Eq.refl
  signed-read ε = Eq.refl
  signed-read (u • v) = Eq.cong₂ _•_ (signed-read u) (signed-read v)

  inv : S.Atom → S.Atom
  inv (S.MM a b) = S.MM b a
  inv (S.XX a b c d ab cd) = S.XX c d a b cd ab

  reverse : Word S.Atom → Word S.Atom
  reverse [ a ]ʷ = [ inv a ]ʷ
  reverse ε = ε
  reverse (u • v) = reverse v • reverse u

  inverse-read : ∀ w → S.decode (reverse w) ≡ S.decode w ⁻¹
  inverse-read [ S.MM a b ]ʷ = Eq.refl
  inverse-read [ S.XX a b c d ab cd ]ʷ = Eq.refl
  inverse-read ε = Eq.refl
  inverse-read (u • v) = Eq.cong₂ _•_ (inverse-read v) (inverse-read u)

  norm : ∀ {w} (d : S.Decoded w) → w ≈ read (lift (S.Decoded.atoms d))
  norm d = trans (S.Decoded.correct d)
    (refl' (Eq.sym (signed-read (S.Decoded.atoms d))))

  norm-inverse : ∀ {w} (d : S.Decoded w) →
    w ⁻¹ ≈ read (lift (reverse (S.Decoded.atoms d)))
  norm-inverse d = trans (⁻¹-cong (S.Decoded.correct d))
    (refl' (Eq.sym (Eq.trans (signed-read (reverse (S.Decoded.atoms d)))
      (inverse-read (S.Decoded.atoms d)))))

module KPlan
  (a b c d : Fin (6 + N))
  .(ab : a < b) .(bc : b < c) .(cd : c < d) where

  private
    module Spare = TwoSpares (two-spares (a ∷ b ∷ c ∷ d ∷ []))
    e′ = Spare.first
    f′ = Spare.second
    ef = Spare.ordered
    module B = Factor.Block (4 + N) a b c d e′ f′ ab bc cd ef
      (Spare.first-outside zero) (Spare.first-outside (suc zero))
      (Spare.first-outside (suc (suc zero)))
      (Spare.first-outside (suc (suc (suc zero))))
      (Spare.second-outside zero) (Spare.second-outside (suc zero))
      (Spare.second-outside (suc (suc zero)))
      (Spare.second-outside (suc (suc (suc zero))))
    module F = S.KFactors a b c d e′ f′ ab bc cd ef
    t s : Coset → Word S.Atom
    t q = S.Decoded.atoms (F.normalize-T q)
    s q = S.Decoded.atoms (F.normalize-S q)

    same-S : ∀ q → B.S q ≡ F.S q
    same-S c00 = Eq.refl
    same-S c10 = Eq.refl
    same-S c11 = Eq.refl
    same-S c01 = Eq.refl

  plan : Coset → Word Primitive
  plan q = (lift (t q) • lift (reverse (s q))) •
    ([ mixed a b c d ab bc cd ]ʷ • lift (s q))

  correct : ∀ q → P.e (q , U.K-gen a b c d ab bc cd) ≈ read (plan q)
  correct q = trans (B.edge-factor q)
    (cong (cong (norm (F.normalize-T q))
        (trans (⁻¹-cong (refl' (same-S q))) (norm-inverse (F.normalize-S q))))
      (cong refl (trans (refl' (same-S q)) (norm (F.normalize-S q)))))

plan : P.Edge → Word Primitive
plan (q , U.M-gen a) = lift (S.Decoded.atoms (S.sign-edge q a))
plan (q , U.X-gen a b ab) = lift (S.Decoded.atoms (S.exchange-edge q a b ab))
plan (q , U.K-gen a b c d ab bc cd) = KPlan.plan a b c d ab bc cd q

correct : ∀ y → P.e y ≈ read (plan y)
correct (q , U.M-gen a) = norm (S.sign-edge q a)
correct (q , U.X-gen a b ab) = norm (S.exchange-edge q a b ab)
correct (q , U.K-gen a b c d ab bc cd) = KPlan.correct a b c d ab bc cd q
