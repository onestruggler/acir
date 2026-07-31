------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Push3 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open NFBase using (NormalFormInjective ; NormalForm)
import Normalization.CosetNF as CosetNF


--open import Examples.Groups.Symplectic.NewCosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Data.Sum


private variable
  n : ℕ

open import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime as TD
import Examples.Groups.Symplectic.BR.Two.D-Bot p-2 p-prime as TDB
import Examples.Groups.Symplectic.BR.Two.B-Top p-2 p-prime as TBT
import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
import Examples.Groups.Symplectic.BR.Two.L-CZ p-2 p-prime as LCZ
import Examples.Groups.Symplectic.BR.Two.L2-CZ p-2 p-prime as LCZ2
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as TDw
open import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (push-LM1 ; A-dir-S-power)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMScz p-2 p-prime
  using (push-E-S^)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBvcz p-2 p-prime
  using (bvec↑-cz ; Wof)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMW p-2 p-prime
  using (push-MW)
open import Examples.Groups.Symplectic.Normalization.Pushing.SectionLMBridge p-2 p-prime
  using (mbox-eq ; vbbox-eq)
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM

open import Data.Vec
open import Data.Nat using (s≤s ; z≤n)


------------------------------------------------------------------------
-- Right coset action

-- The right action of a generator on a coset: ract c b returns the
-- residual circuit b' and the coset c' reached from c by b, so that
-- [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ (see ract-sound below).
ract : ∀ {n} (vb : Vec B n) (m : M (₂₊ n)) -> Circuit (₁₊ n) × M (₂₊ n)
-- Push CZ through the lifted B-vector (leaving it unchanged, PushBvcz.
-- bvec↑-cz), then push the resulting residual Wof vb through the M box
-- (PushMW.push-MW).  The M box carries the whole update; the residual
-- escapes one wire up.
ract {n} vb m = proj₁ (push-MW m vb) , proj₁ (proj₂ (push-MW m vb))

------------------------------------------------------------------------
-- Soundness of the coset action

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c b we have [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract-sound : ∀ {n} vb m →
  let
    open PB ((₂₊ n) QRel,_===_)
    (dir , m') = ract {n} vb m
  in

    ([ m ]ᵐ • [ vb ]ᵛᵇ ↑) • CZ ≈ dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑)

-- Bridge Section's coset boxes to LM-Sym's (SectionLMBridge), run the
-- B-vector cascade (bvec↑-cz) then the M-box push (push-MW), bridge back.
ract-sound {n} vb m = proof
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  pr   = push-MW m vb
  dir  = proj₁ pr
  m'   = proj₁ (proj₂ pr)
  mweq = proj₂ (proj₂ pr)   -- LM.[ m ]ᵐ • Wof vb ≈ dir ↑ • LM.[ m' ]ᵐ

  proof : ([ m ]ᵐ • [ vb ]ᵛᵇ ↑) • CZ ≈ dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑)
  proof = begin
    ([ m ]ᵐ • [ vb ]ᵛᵇ ↑) • CZ
      ≈⟨ cleft (cong (refl' (mbox-eq m)) (refl' (Eq.cong (_↑) (vbbox-eq vb)))) ⟩
    (LM.[ m ]ᵐ • LM.[ vb ]ᵛᵇ ↑) • CZ                ≈⟨ assoc ⟩
    LM.[ m ]ᵐ • (LM.[ vb ]ᵛᵇ ↑ • CZ)                ≈⟨ cright (bvec↑-cz vb) ⟩
    LM.[ m ]ᵐ • (Wof vb • LM.[ vb ]ᵛᵇ ↑)            ≈⟨ sym assoc ⟩
    (LM.[ m ]ᵐ • Wof vb) • LM.[ vb ]ᵛᵇ ↑            ≈⟨ cleft mweq ⟩
    (dir ↑ • LM.[ m' ]ᵐ) • LM.[ vb ]ᵛᵇ ↑            ≈⟨ assoc ⟩
    dir ↑ • (LM.[ m' ]ᵐ • LM.[ vb ]ᵛᵇ ↑)
      ≈⟨ cright (cong (refl' (Eq.sym (mbox-eq m'))) (refl' (Eq.sym (Eq.cong (_↑) (vbbox-eq vb))))) ⟩
    dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑)                  ∎
