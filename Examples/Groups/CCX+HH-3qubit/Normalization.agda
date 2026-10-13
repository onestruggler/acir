------------------------------------------------------------------------
-- Lemmas 6.1 and 6.2: move H₂ to the right; keep at most one copy.
-- The dyadic part uses only the four primitive Toffoli-K generators,
-- CCZ, and the negatively controlled K gate. Derived gates are first
-- eliminated by the defining equations of Figure 4.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Normalization where

open import Data.Bool.Base using (Bool ; true ; false)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Core
open import Presentation.Base _===_ hiding (_===_ ; _≈_)
open import Presentation.Properties _===_ using (by-assoc)

data DGen : Set where
  dX0 dCX01 dCCX12 dK12 dCCZ dNK : DGen

inc : DGen → Gen
inc dX0 = X0-gen
inc dCX01 = CX01-gen
inc dCCX12 = CCX12-gen
inc dK12 = K12-gen
inc dCCZ = CCZ-gen
inc dNK = NK-gen

dyadic : Word DGen → Word Gen
dyadic = wmap inc

forget : CGen → DGen
forget cX0 = dX0
forget cCX01 = dCX01
forget cCCX12 = dCCX12
forget cK12 = dK12
forget cCCZ = dCCZ
forget cNK = dNK
forget cH2 = dX0

private
  dk01 = wmap forget wK01
  dccx01 = wmap forget wCCX01

conjugate : DGen → Word DGen
conjugate dX0 = [ dX0 ]ʷ
conjugate dCX01 = [ dCX01 ]ʷ
conjugate dCCX12 = dk01 • [ dK12 ]ʷ • [ dCCZ ]ʷ • [ dK12 ]ʷ • dk01
conjugate dK12 = [ dK12 ]ʷ
conjugate dCCZ = dccx01
conjugate dNK = [ dNK ]ʷ

past-gen : (g : DGen) → H2 • [ inc g ]ʷ ≈ dyadic (conjugate g) • H2
past-gen dX0 = axiom r102
past-gen dCX01 = axiom r103
past-gen dCCX12 = trans (axiom r104)
  (trans expanded (by-assoc Eq.refl))
  where
  expanded : K01 • K12 • CCZ • K12 • K01 • H2 ≈
             dyadic dk01 • K12 • CCZ • K12 • dyadic dk01 • H2
  expanded = cong eK01
    (cong refl (cong refl (cong refl (cong eK01 refl))))
past-gen dK12 = axiom r106
past-gen dCCZ = trans (axiom r105) (cong eCCX01 refl)
past-gen dNK = axiom r107

-- Lemma 6.1, with the resulting word computed explicitly.
past-word : (w : Word DGen) →
            H2 • dyadic w ≈ dyadic ((conjugate ʷ) w) • H2
past-word [ g ]ʷ = past-gen g
past-word ε = by-assoc Eq.refl
past-word (w • v) = trans (sym assoc)
  (trans (cong (past-word w) refl)
    (trans assoc (trans (cong refl (past-word v)) (sym assoc))))

tail : Bool → Word Gen
tail false = ε
tail true = H2

record Normal (w : Word Gen) : Set where
  constructor normal
  field
    body : Word DGen
    odd : Bool
    derivation : w ≈ dyadic body • tail odd

combine : ∀ {w v} → Normal w → Normal v → Normal (w • v)
combine (normal a false ea) (normal b q eb) =
  normal (a • b) q
    (trans (cong ea eb) (trans (cong right-unit refl) (sym assoc)))
combine (normal a true ea) (normal b false eb) =
  normal (a • (conjugate ʷ) b) true
    (trans (cong ea eb) (trans (cong refl right-unit)
      (trans assoc (trans (cong refl (past-word b)) (sym assoc)))))
combine (normal a true ea) (normal b true eb) =
  normal (a • (conjugate ʷ) b) false
    (trans (cong ea eb) (trans (sym assoc)
      (trans (cong assoc refl)
        (trans (cong (cong refl (past-word b)) refl)
          (trans (cong (sym assoc) refl)
            (trans assoc (cong refl (axiom r108))))))))

private
  core-normal : (w : Word CGen) → Normal ⌞ w ⌟
  core-normal [ cX0 ]ʷ = normal [ dX0 ]ʷ false (sym right-unit)
  core-normal [ cCX01 ]ʷ = normal [ dCX01 ]ʷ false (sym right-unit)
  core-normal [ cCCX12 ]ʷ = normal [ dCCX12 ]ʷ false (sym right-unit)
  core-normal [ cK12 ]ʷ = normal [ dK12 ]ʷ false (sym right-unit)
  core-normal [ cCCZ ]ʷ = normal [ dCCZ ]ʷ false (sym right-unit)
  core-normal [ cNK ]ʷ = normal [ dNK ]ʷ false (sym right-unit)
  core-normal [ cH2 ]ʷ = normal ε true (sym left-unit)
  core-normal ε = normal ε false (sym left-unit)
  core-normal (w • v) = combine (core-normal w) (core-normal v)

-- Lemma 6.2 for the entire alphabet Σ₂, not just the primitive gates.
normalize : (w : Word Gen) → Normal w
normalize w = lift (core-normal (expand w))
  where
  lift : Normal ⌞ expand w ⌟ → Normal w
  lift (normal b q e) = normal b q (trans (word-expand w) e)
