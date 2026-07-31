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

module Examples.Groups.Symplectic.Normalization.Pushing.Push6 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Data.Sum


private variable
  n : ℕ


open import Data.Vec
open import Data.Nat using (s≤s ; z≤n)

import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
import Examples.Groups.Symplectic.BR.Two.L2-CZ p-2 p-prime as LCZ2
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMBword p-2 p-prime
  using (push-MBvec-word)
open import Examples.Groups.Symplectic.Normalization.Pushing.SectionLMBridge p-2 p-prime
  using (mbox-eq ; vbbox-eq)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (cong↓ᵏ ; ↑↓ᵏ-comm)
import Examples.Groups.Symplectic.Normalization.Pushing.Push2 p-2 p-prime as Push2

------------------------------------------------------------------------
-- Right coset action  (CZ on a bottom D box above a lifted ML' box)
--
-- The box  [ d ]ᵈ • [ ml' ]ᵐˡ' ↑  is a bottom D box (wires 0,1) with the
-- ML' box lifted onto wires ≥ 1.  Merging d into the M column gives
-- [ (d ∷ dvec , e) ]ᵐ • [ l' ]ˡ' ↑ ; because the L' box is lifted, its A
-- box is the *rightmost* box (nearest CZ) — so CZ meets the lifted A box
-- first (LCZ2's inj₂/L'1 case, whose residual is top-H-free), and the
-- whole enlarged M column + B-vector is then handled by push-MBvec-word,
-- exactly as in Push2.  The residual A box may collapse the L' into the
-- sum (Push2.coset-n).

ract : ∀ {n} -> ML' (₂₊ n) -> D → SympGate 2 → Circuit (₂₊ n) × ML (₃₊ n)
ract {n} ((dvec , e) , (bv , a)) d CZ-gate =
  proj₁ r , Push2.coset-n l'' (proj₁ (proj₂ r)) bv
  where
  M+  = (d ∷ dvec , e)
  lc  = inj₂ ([] , a)
  l'' = LCZ2.l'-of lc
  r   = push-MBvec-word (LCZ2.dir-of lc) (Push2.dir-of₂-No-Top lc) M+ bv

------------------------------------------------------------------------
-- Widening and soundness

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  -- The lifted A box meeting CZ, widened to width (₃₊ n): the analogue of
  -- Push2.core-widen for the L2-CZ inj₂ (lone lifted A box) case.
  core-widen-A : (a : A) →
    [ a ]ᵃ ↑ • CZ ≈
      (LCZ2.dir-of (inj₂ ([] , a)) ↓ᵏ (₁₊ n)) •
      (LCZ2.intp (LCZ2.l'-of (inj₂ ([] , a))) ↓ᵏ (₁₊ n))
  core-widen-A a = begin
    [ a ]ᵃ ↑ • CZ                                            ≈⟨ cleft (sym left-unit) ⟩
    (ε • [ a ]ᵃ ↑) • CZ                                      ≈⟨ cleft (refl' aeq) ⟩
    (LCZ2.intp (inj₂ ([] , a)) ↓ᵏ (₁₊ n)) • CZ
      ≈⟨ cong↓ᵏ (₁₊ n) _ _ (LCZ2.lemma-dir-and-l' (inj₂ ([] , a))) ⟩
    (LCZ2.dir-of (inj₂ ([] , a)) ↓ᵏ (₁₊ n)) •
      (LCZ2.intp (LCZ2.l'-of (inj₂ ([] , a))) ↓ᵏ (₁₊ n))    ∎
    where
    -- ε • [ a ]ᵃ ↑  is definitionally  intp (inj₂ ([] , a))  widened by ↓ᵏ.
    aeq : ε • [ a ]ᵃ ↑ ≡ LCZ2.intp (inj₂ ([] , a)) ↓ᵏ (₁₊ n)
    aeq = Eq.sym (Eq.trans (↑↓ᵏ-comm (ε • LM.[_]ᵃ {n = 0} a) (₁₊ n))
                           (Eq.cong _↑ (Eq.cong (ε •_) (Push2.abox-↓ᵏ-LM0 a))))

ract-sound : ∀ {n} ml' d g →
  let
    open PB ((₃₊ n) QRel,_===_)
    (dir , c') = ract {n} ml' d g
  in
    ([ d ]ᵈ • [ ml' ]ᵐˡ' ↑) • [ gate₂ g ]ʷ ≈ dir ↑ • [ c' ]ᵐˡ

ract-sound {n} ((dvec , e) , (bv , a)) d CZ-gate = begin
  ([ d ]ᵈ • ([ (dvec , e) ]ᵐ ↑ • ([ bv ]ᵛᵇ ↑ • [ a ]ᵃ ↑))) • CZ
    ≈⟨ cleft (sym assoc) ⟩
  ([ M+ ]ᵐ • ([ bv ]ᵛᵇ ↑ • [ a ]ᵃ ↑)) • CZ                 ≈⟨ assoc ⟩
  [ M+ ]ᵐ • (([ bv ]ᵛᵇ ↑ • [ a ]ᵃ ↑) • CZ)                 ≈⟨ cright assoc ⟩
  [ M+ ]ᵐ • ([ bv ]ᵛᵇ ↑ • ([ a ]ᵃ ↑ • CZ))                 ≈⟨ cright (cright (core-widen-A a)) ⟩
  [ M+ ]ᵐ • ([ bv ]ᵛᵇ ↑ • ((LCZ2.dir-of lc ↓ᵏ (₁₊ n)) • core'))
    ≈⟨ cright (sym assoc) ⟩
  [ M+ ]ᵐ • (([ bv ]ᵛᵇ ↑ • (LCZ2.dir-of lc ↓ᵏ (₁₊ n))) • core')
    ≈⟨ sym assoc ⟩
  ([ M+ ]ᵐ • ([ bv ]ᵛᵇ ↑ • (LCZ2.dir-of lc ↓ᵏ (₁₊ n)))) • core'
    ≈⟨ cleft (cong (refl' (mbox-eq M+)) (cong (refl' (Eq.cong (_↑) (vbbox-eq bv))) refl)) ⟩
  (LM.[ M+ ]ᵐ • (LM.[ bv ]ᵛᵇ ↑ • (LCZ2.dir-of lc ↓ᵏ (₁₊ n)))) • core'
    ≈⟨ cleft eq-r ⟩
  (dir ↑ • (LM.[ M+' ]ᵐ • LM.[ bv ]ᵛᵇ ↑)) • core'
    ≈⟨ cleft (cright (cong (refl' (Eq.sym (mbox-eq M+'))) (refl' (Eq.cong (_↑) (Eq.sym (vbbox-eq bv)))))) ⟩
  (dir ↑ • ([ M+' ]ᵐ • [ bv ]ᵛᵇ ↑)) • core'                ≈⟨ assoc ⟩
  dir ↑ • (([ M+' ]ᵐ • [ bv ]ᵛᵇ ↑) • core')                ≈⟨ cright assoc ⟩
  dir ↑ • ([ M+' ]ᵐ • ([ bv ]ᵛᵇ ↑ • core'))                ≈⟨ cright (Push2.coset-eq-n l'' M+' bv) ⟩
  dir ↑ • [ Push2.coset-n l'' M+' bv ]ᵐˡ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  M+    = (d ∷ dvec , e)
  lc    = inj₂ ([] , a)
  l''   = LCZ2.l'-of lc
  r     = push-MBvec-word (LCZ2.dir-of lc) (Push2.dir-of₂-No-Top lc) M+ bv
  dir   = proj₁ r
  M+'   = proj₁ (proj₂ r)
  eq-r  = proj₂ (proj₂ r)
  core' = LCZ2.intp l'' ↓ᵏ (₁₊ n)
