------------------------------------------------------------------------
-- Presentations of groups
--
-- The dyadic edge plans at an arbitrary dimension N >= 6.  Exposing N
-- directly lets the physical decoder instantiate N = 2^(4+n) without
-- casting circuits, matrix dimensions, or auxiliary source words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.DecodingPlans where

open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; _+_ ; _≤_ ; s≤s ; z≤n)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin ; _<_ ; fromℕ< ; toℕ)
import Data.Fin.Properties as FP
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH.Subgroup.PresentationAt as Sub
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset)
import Examples.Groups.CCX+H.GeneralN.EdgePlans as Plans
import Examples.Groups.CCX+H.GeneralN.SignedEdges as Signed

data Atom (N : ℕ) : Set where
  MM : Fin N → Fin N → Atom N
  XX : (a b c d : Fin N) → .(a < b) → .(c < d) → Atom N
  J : (a b c d : Fin N) → .(a < b) → .(b < c) → .(c < d) → Atom N

e : ∀ {N} → Atom N → Word (U.Gen N)
e (MM a b) = U.M a • U.M b
e (XX a b c d ab cd) = U.X a b ab • U.X c d cd
e (J a b c d ab bc cd) = (U.M a • U.X b c bc) • U.K a b c d ab bc cd

read : ∀ {N} → Word (Atom N) → Word (U.Gen N)
read = e ʷ

module At (N : ℕ) (enough : 6 ≤ N) where
  private
    p₀ : 0 Nat.< N
    p₀ = NP.≤-trans (s≤s z≤n) enough
    p₁ : 1 Nat.< N
    p₁ = NP.≤-trans (s≤s (s≤s z≤n)) enough
    a b : Fin N
    a = fromℕ< p₀
    b = fromℕ< p₁
    a<b : a < b
    a<b = Eq.subst₂ Nat._<_ (Eq.sym (FP.toℕ-fromℕ< p₀))
      (Eq.sym (FP.toℕ-fromℕ< p₁)) (s≤s z≤n)

  module Auxiliary = Sub N a b a<b
  open Auxiliary public using (Edge) renaming (e to source)

private
  module Six (k : ℕ) where
    module P = Plans k
    module S = Signed (4 + k)
    module A = PB (U._===_ {6 + k})

    atom : P.Primitive → Atom (6 + k)
    atom (P.signed (S.MM a b)) = MM a b
    atom (P.signed (S.XX a b c d ab cd)) = XX a b c d ab cd
    atom (P.mixed a b c d ab bc cd) = J a b c d ab bc cd

    word-correct : ∀ w → read (wmap atom w) ≡ P.read w
    word-correct [ P.signed (S.MM a b) ]ʷ = Eq.refl
    word-correct [ P.signed (S.XX a b c d ab cd) ]ʷ = Eq.refl
    word-correct [ P.mixed a b c d ab bc cd ]ʷ = Eq.refl
    word-correct ε = Eq.refl
    word-correct (u • v) = Eq.cong₂ _•_ (word-correct u) (word-correct v)

    plan : Coset × U.Gen (6 + k) → Word (Atom (6 + k))
    plan y = wmap atom (P.plan y)

    correct : ∀ enough y → PB._≈_ (U._===_ {6 + k})
      (At.source (6 + k) enough y) (read (plan y))
    correct enough y = A.trans (P.correct y)
      (A.refl' (Eq.sym (word-correct (P.plan y))))

plan : (N : ℕ) → (enough : 6 ≤ N) → Coset × U.Gen N → Word (Atom N)
plan 0 ()
plan 1 (s≤s ())
plan 2 (s≤s (s≤s ()))
plan 3 (s≤s (s≤s (s≤s ())))
plan 4 (s≤s (s≤s (s≤s (s≤s ()))))
plan 5 (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
plan (suc (suc (suc (suc (suc (suc k)))))) enough = Six.plan k

correct : ∀ N enough y → PB._≈_ (U._===_ {N})
  (At.source N enough y) (read (plan N enough y))
correct 0 ()
correct 1 (s≤s ())
correct 2 (s≤s (s≤s ()))
correct 3 (s≤s (s≤s (s≤s ())))
correct 4 (s≤s (s≤s (s≤s (s≤s ()))))
correct 5 (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
correct (suc (suc (suc (suc (suc (suc k)))))) enough = Six.correct k enough
