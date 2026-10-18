------------------------------------------------------------------------
-- Presentations of groups
--
-- The indices of the atoms of an edge plan.
--
-- Every atom in the plan of an auxiliary edge (c , y)
-- (GeneralN/DecodingPlans) has its indices among the indices of the
-- generator y and the indices below 16: the coset representatives use
-- the indices 0 and 1, the K-plans two spares below 6
-- (GeneralN/SpareLevels), and a swap of indices returns one of them.
-- So any property of indices that holds of y's indices and of every
-- small index holds of every atom (`plan-args`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.PlanArgs where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_ ; z≤n ; s≤s)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_×_ ; _,_ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
open U using (M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00 ; c10 ; c11 ; c01)
open import Examples.Groups.CCX+HH.GeneralN.DecodingPlans using (Atom ; MM ; XX ; J ; plan ; module Six)
import Examples.Groups.CCX+H.GeneralN.EdgePlans as Plans
import Examples.Groups.CCX+H.GeneralN.SignedEdges as Signed
open import Examples.Groups.CCX+H.GeneralN.SignedNormalization using (swap)
open import Examples.Groups.CCX+H.GeneralN.SpareLevels
  using (two-spares ; module TwoSpares ; two-spares-first ; two-spares-second)

------------------------------------------------------------------------
-- Properties of indices

AllW : ∀ {A : Set} → (A → Set) → Word A → Set
AllW Q [ x ]ʷ  = Q x
AllW Q ε       = ⊤
AllW Q (u • v) = AllW Q u × AllW Q v

GenQ : ∀ {N} → (Fin N → Set) → U.Gen N → Set
GenQ Q (M-gen a)             = Q a
GenQ Q (X-gen a b _)         = Q a × Q b
GenQ Q (K-gen a b c d _ _ _) = Q a × Q b × Q c × Q d

AtomQ : ∀ {N} → (Fin N → Set) → Atom N → Set
AtomQ Q (MM a b)          = Q a × Q b
AtomQ Q (XX a b c d _ _)  = Q a × Q b × Q c × Q d
AtomQ Q (J a b c d _ _ _) = Q a × Q b × Q c × Q d

Small : ∀ {N} → (Fin N → Set) → Set
Small Q = ∀ z → toℕ z < 16 → Q z

swap-Q : ∀ {n} (Q : Fin n → Set) {a b c : Fin n} → Q a → Q b → Q c → Q (swap a b c)
swap-Q Q {a} {b} {c} qa qb qc with c ≟ a
... | yes _ = qb
... | no _ with c ≟ b
...   | yes _ = qa
...   | no _  = qc

------------------------------------------------------------------------
-- The plans at 6 + k

module _ (k : ℕ) where

  private
    module P = Plans k
    module S = Signed (4 + k)

  PrimQ : (Fin (6 + k) → Set) → P.Primitive → Set
  PrimQ Q (P.signed (S.MM a b))          = Q a × Q b
  PrimQ Q (P.signed (S.XX a b c d _ _))  = Q a × Q b × Q c × Q d
  PrimQ Q (P.mixed a b c d _ _ _)        = Q a × Q b × Q c × Q d

  atoms-args : (Q : Fin (6 + k) → Set) (w : Word P.Primitive) →
    AllW (PrimQ Q) w → AllW (AtomQ Q) (wmap (Six.atom k) w)
  atoms-args Q [ P.signed (S.MM a b) ]ʷ          q = q
  atoms-args Q [ P.signed (S.XX a b c d _ _) ]ʷ  q = q
  atoms-args Q [ P.mixed a b c d _ _ _ ]ʷ        q = q
  atoms-args Q ε                                 q = tt
  atoms-args Q (u • v)                   (qu , qv) = atoms-args Q u qu , atoms-args Q v qv

  prim-args : (Q : Fin (6 + k) → Set) → Small Q → (q : Coset) (y : U.Gen (6 + k)) →
    GenQ Q y → AllW (PrimQ Q) (P.plan (q , y))
  prim-args Q sm q (M-gen a) qa = sign q
    where
    qi = sm zero (s≤s z≤n)
    qj = sm (suc zero) (s≤s (s≤s z≤n))
    σQ : ∀ {z} → Q z → Q (swap zero (suc zero) z)
    σQ = swap-Q Q qi qj
    sign : ∀ q → AllW (PrimQ Q) (P.plan (q , M-gen a))
    sign c00 = qa , qi
    sign c10 = qi , qa
    sign c11 = (σQ qa , σQ (σQ qi)) , (qi , qj , qi , qj)
    sign c01 = (qi , σQ qa) , (qi , qj , qi , qj)
  prim-args Q sm q (X-gen a b ab) (qa , qb) = exch q
    where
    qi = sm zero (s≤s z≤n)
    qj = sm (suc zero) (s≤s (s≤s z≤n))
    σQ : ∀ {z} → Q z → Q (swap zero (suc zero) z)
    σQ = swap-Q Q qi qj
    abQ : ∀ {z} → Q z → Q (swap a b z)
    abQ = swap-Q Q qa qb
    exch : ∀ q → AllW (PrimQ Q) (P.plan (q , X-gen a b ab))
    exch c00 = qa , qb , qi , qj
    exch c10 = (qi , abQ (σQ qi)) , (qa , qb , qi , qj)
    exch c11 = qi , qj , qa , qb
    exch c01 = (qi , σQ (abQ qi)) , (qi , qj , qa , qb)
  prim-args Q sm q (K-gen a b c d ab bc cd) (qa , qb , qc , qd) = kplan q
    where
    qi = sm zero (s≤s z≤n)
    qj = sm (suc zero) (s≤s (s≤s z≤n))
    sp = two-spares (a ∷ b ∷ c ∷ d ∷ [])
    qe = sm (TwoSpares.first sp)
      (s≤s (NP.≤-trans (two-spares-first (a ∷ b ∷ c ∷ d ∷ [])) (NP.m≤m+n 4 11)))
    qf = sm (TwoSpares.second sp)
      (s≤s (NP.≤-trans (two-spares-second (a ∷ b ∷ c ∷ d ∷ [])) (NP.m≤m+n 5 10)))
    σQ : ∀ {z} → Q z → Q (swap zero (suc zero) z)
    σQ = swap-Q Q qi qj
    τQ : ∀ {z} → Q z → Q (swap b c z)
    τQ = swap-Q Q qb qc
    ρQ : ∀ {z} → Q z → Q (swap (TwoSpares.first sp) (TwoSpares.second sp) z)
    ρQ = swap-Q Q qe qf
    kplan : ∀ q → AllW (PrimQ Q) (P.plan (q , K-gen a b c d ab bc cd))
    kplan c00 = (((τQ qa , τQ (σQ qi)) , (qb , qc , qi , qj)) , ((qi , qj , qe , qf) , (ρQ (σQ qi) , qe)))
              , ((qa , qb , qc , qd) , ((qe , ρQ (σQ qi)) , (qe , qf , qi , qj)))
    kplan c10 = (((qi , τQ qa) , (qb , qc , qi , qj)) , (qi , qj , qe , qf))
              , ((qa , qb , qc , qd) , (qe , qf , qi , qj))
    kplan c11 = (((σQ (τQ qa) , σQ (τQ qi)) , (qi , qj , qb , qc)) , (qi , qe))
              , ((qa , qb , qc , qd) , (qe , qi))
    kplan c01 = (((qi , σQ (τQ qa)) , (qi , qj , qb , qc)) , tt)
              , ((qa , qb , qc , qd) , tt)

------------------------------------------------------------------------
-- At any dimension

plan-args : ∀ N enough (Q : Fin N → Set) → Small Q → (g : Coset × U.Gen N) →
  GenQ Q (proj₂ g) → AllW (AtomQ Q) (plan N enough g)
plan-args 0 ()
plan-args 1 (s≤s ())
plan-args 2 (s≤s (s≤s ()))
plan-args 3 (s≤s (s≤s (s≤s ())))
plan-args 4 (s≤s (s≤s (s≤s (s≤s ()))))
plan-args 5 (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
plan-args (suc (suc (suc (suc (suc (suc k)))))) enough Q sm (q , y) gq =
  atoms-args k Q (Plans.plan k (q , y)) (prim-args k Q sm q y gq)
