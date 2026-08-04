------------------------------------------------------------------------
-- Presentations of groups
--
-- Well-definedness of the coset action on the group-specific axioms
-- (the srel case of ⁻¹[⇑]-wd'' in Normalization.agda), one axiom at a
-- time.  For an axiom u === t we must show the threaded action agrees:
-- (ract ᵗ) c u ≋ (ract ᵗ) c t.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Sum using (inj₁ ; inj₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)
import Relation.Binary.Reasoning.Setoid as SR
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_%_ ; m%n<n ; %-distribˡ-+ ; m*n%n≡0 ; m<n⇒m%n≡m ; m%n%n≡m%n)
open import Data.Product using (∃)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<)
import Data.Nat.Properties as NP
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (A-dir-S-power)
import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDW1 p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD2 p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD3 p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDGo p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2 p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10 p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10e p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10g p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10i p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10j p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10k p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10m p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10o p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11 p-2 p-prime

------------------------------------------------------------------------
-- The axioms, one at a time.

srel-wd : ∀ {n} (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
  Base._SRel,_===_ (₁₊ n) u t → (ract {n} ᵗ) c u ≋ (ract {n} ᵗ) c t
srel-wd {zero} (([] , e) , ([] , ((₀ , ₀) , nz)))     Base.order-S = ⊥-elim (nz auto)
srel-wd {zero} (([] , e) , ([] , ((₀ , ₁₊ b') , nz))) Base.order-S =
  sing0 ,
  Eq.trans (ract1-S^-a0 p e b' nz)
           (c1-eq (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- (kS-a0 b' nz))))
                            (+-identityʳ e))
                  Eq.refl)
srel-wd {zero} (([] , e) , ([] , ((₁₊ a' , b) , nz))) Base.order-S =
  sing0 ,
  Eq.trans (ract1-S^-a+ p e a' b nz)
           (c1-eq Eq.refl
                  (Eq.cong (λ z → ₁₊ a' , z)
                           (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- (₁₊ a'))))
                                     (+-identityʳ b))))
srel-wd {suc m} (inj₁ ml') Base.order-S = {!!}
srel-wd {suc m} (inj₂ ((₀ , b) , lm)) Base.order-S = orderS-go-0 b lm
srel-wd {suc m} (inj₂ ((₁₊ a , b) , lm)) Base.order-S = orderS-go-+ a b lm
-- order-H at width 1: the A box 4-cycles under H ((0,b) ↦ (b,0) ↦
-- (0,-b) ↦ (-b,0) ↦ (0,b), and (a,b) ↦ (b,-a) ↦ (-a,-b) ↦ (-b,a) ↦
-- (a,b)); the escape powers vanish except on fully nonzero boxes, where
-- they telescope as (ab)⁻¹ - (ab)⁻¹ + (ab)⁻¹ - (ab)⁻¹ ≡ ₀.  Negated
-- components are stuck, so the orbit is rewritten into constructor form
-- (x≢0⇒suc) before each blocked step.
srel-wd {zero} (([] , e) , ([] , ((₀ , ₀) , nz))) Base.order-H = ⊥-elim (nz auto)
srel-wd {zero} (([] , e) , ([] , ((₀ , ₁₊ b₀) , nz))) Base.order-H =
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ y eq-y →
  order-H-0b e b₀ nz y eq-y
srel-wd {zero} (([] , e) , ([] , ((₁₊ a₀ , ₀) , nz))) Base.order-H =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ y)) (neg≢0 (₁₊ y) λ ()) λ y2 eq-y2 →
  order-H-a0 e a₀ nz y y2 eq-y eq-y2
srel-wd {zero} (([] , e) , ([] , ((₁₊ a₀ , ₁₊ b₀) , nz))) Base.order-H =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  order-H-nn e a₀ b₀ nz y z eq-y eq-z
srel-wd {suc m} (inj₁ ml')     Base.order-H = {!!}
-- order-H on inj₂: the D box 4-cycles under (a,b) ↦ (b,-a); the Hdir
-- escapes collapse to H ^ 4 (fully nonzero pattern still open).
srel-wd {suc m} (inj₂ ((₀ , ₀) , lm)) Base.order-H = orderH-go-00 lm
srel-wd {suc m} (inj₂ ((₀ , ₁₊ b') , lm)) Base.order-H = orderH-go-0b b' lm
srel-wd {suc m} (inj₂ ((₁₊ a' , ₀) , lm)) Base.order-H = orderH-go-a0 a' lm
srel-wd {suc m} (inj₂ ((₁₊ a' , ₁₊ b') , lm)) Base.order-H = orderH-go-nn a' b' lm
srel-wd {zero} (([] , e) , ([] , ((₀ , ₀) , nz))) Base.order-SH = ⊥-elim (nz auto)
srel-wd {zero} (([] , e) , ([] , ((₀ , ₁₊ b₀) , nz))) Base.order-SH =
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  order-SH-0b e b₀ nz z eq-z
srel-wd {zero} (([] , e) , ([] , ((₁₊ a₀ , ₀) , nz))) Base.order-SH =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  order-SH-a0 e a₀ nz y eq-y
srel-wd {zero} (([] , e) , ([] , ((₁₊ a₀ , ₁₊ b₀) , nz))) Base.order-SH =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-fin (₁₊ b₀ + - (₁₊ a₀))
    (λ Xeq → order-SH-nn0 e a₀ b₀ nz y eq-y Xeq)
    (λ w Xeq → elim-suc (- (₁₊ w)) (neg≢0 (₁₊ w) λ ()) λ t eq-t →
       order-SH-nnw e a₀ b₀ nz y z w t eq-y eq-z Xeq eq-t)
srel-wd {suc m} (inj₁ ml')      Base.order-SH = {!!}
-- order-SH on the (₀,₀) inj₂ coset: every letter's escape is the
-- letter itself (the box cycles through (₀,±0)), so the residual tree
-- is literally (S • H) ^ 3 after normalising -0 components.
srel-wd {suc m} (inj₂ ((₀ , ₀) , lm)) Base.order-SH = orderSH-go-00 lm
srel-wd {suc m} (inj₂ ((₀ , ₁₊ b') , lm)) Base.order-SH = orderSH-go-0b b' lm
srel-wd {suc m} (inj₂ ((₁₊ a' , ₀) , lm)) Base.order-SH = orderSH-go-a0 a' lm
srel-wd {suc m} (inj₂ ((₁₊ a' , ₁₊ b') , lm)) Base.order-SH = orderSH-go-nn a' b' lm
srel-wd {zero} (([] , e) , ([] , ((₀ , ₀) , nz))) Base.comm-HHS = ⊥-elim (nz auto)
srel-wd {zero} (([] , e) , ([] , ((₀ , ₁₊ b₀) , nz))) Base.comm-HHS =
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ y eq-y →
  comm-HHS-0b e b₀ nz y eq-y
srel-wd {zero} (([] , e) , ([] , ((₁₊ a₀ , ₀) , nz))) Base.comm-HHS =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  comm-HHS-a0 e a₀ nz y eq-y
srel-wd {zero} (([] , e) , ([] , ((₁₊ a₀ , ₁₊ b₀) , nz))) Base.comm-HHS =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-fin (₁₊ b₀ + - (₁₊ a₀))
    (λ Xeq → comm-HHS-nn0 e a₀ b₀ nz y z eq-y eq-z Xeq)
    (λ w Xeq → comm-HHS-nnw e a₀ b₀ nz y z w eq-y eq-z Xeq)
srel-wd {suc m} (inj₁ ml')      Base.comm-HHS = {!!}
-- comm-HHS on (₀,·) inj₂ cosets: the residuals normalise to the two
-- sides of the axiom itself (fully nonzero D boxes still open).
srel-wd {suc m} (inj₂ ((₀ , ₀) , lm)) Base.comm-HHS = commHHS-go-00 lm
srel-wd {suc m} (inj₂ ((₀ , ₁₊ b') , lm)) Base.comm-HHS = commHHS-go-0b b' lm
srel-wd {suc m} (inj₂ ((₁₊ a' , ₀) , lm)) Base.comm-HHS = commHHS-go-a0 a' lm
srel-wd {suc m} (inj₂ ((₁₊ a' , ₁₊ b') , lm)) Base.comm-HHS = commHHS-go-nn a' b' lm
-- M-mul at width 1: two M threadings against one, by ractM!.
srel-wd {zero} (([] , e) , ([] , (ab , nz))) (Base.M-mul x y) =
  PB.trans sing0 (PB.sym sing0) ,
  Eq.trans (Eq.cong (λ z → (ract {0} ᵗ) z (ZM y) .proj₂)
             (ractM! x e ab nz (Mact-nz x ab nz)))
  (Eq.trans (ractM! y e
              (x .proj₁ * ab .proj₁ , (x ⁻¹) .proj₁ * ab .proj₂)
              (Mact-nz x ab nz)
              (Mact-nz y _ (Mact-nz x ab nz)))
  (Eq.trans (c1-eq Eq.refl (Eq.cong₂ _,_
      (Eq.trans (Eq.sym (*-assoc (y .proj₁) (x .proj₁) (ab .proj₁)))
                (Eq.cong (_* ab .proj₁) (*-comm (y .proj₁) (x .proj₁))))
      (Eq.trans (Eq.sym (*-assoc ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) (ab .proj₂)))
                (Eq.cong (_* ab .proj₂)
                  (Eq.trans (*-comm ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁))
                            (Eq.sym (inv-distrib x y)))))))
            (Eq.sym (ractM! (x *' y) e ab nz (Mact-nz (x *' y) ab nz)))))
srel-wd {suc m} (inj₁ ml')      (Base.M-mul x y) = {!!}
-- M-mul on inj₂: thread the two M-words through the D box via the MD
-- engine; the escapes multiply by the M-mul axiom one width down.
srel-wd {suc m} (inj₂ ((₀ , b) , lm)) (Base.M-mul x y) =
  Mmul-wd-0 x y b ((x ⁻¹) .proj₁ * b) lm Eq.refl
srel-wd {suc m} (inj₂ ((₁₊ a' , b) , lm)) (Base.M-mul x y) =
  Mmul-wd-+ x y a'
    (x≢0⇒suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂) .proj₁)
    b ((x ⁻¹) .proj₁ * b) lm
    (x≢0⇒suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂) .proj₂)
    Eq.refl
srel-wd {zero} (([] , e) , ([] , ((₀ , ₀) , nz))) (Base.semi-MS x) =
  ⊥-elim (nz auto)
srel-wd {zero} (([] , e) , ([] , ((₀ , ₁₊ β') , nz))) (Base.semi-MS x) =
  elim-suc ((x ⁻¹) .proj₁ * ₁₊ β') (((x ⁻¹) *' (₁₊ β' , λ ())) .proj₂)
    λ m eq-m →
  PB.trans sing0 (PB.sym sing0) , semi-MS-0b x e β' nz m eq-m
srel-wd {zero} (([] , e) , ([] , ((₁₊ α' , β) , nz))) (Base.semi-MS x) =
  elim-suc (x .proj₁ * ₁₊ α') ((x *' (₁₊ α' , λ ())) .proj₂)
    λ s eq-s →
  PB.trans sing0 (PB.sym sing0) , semi-MS-nn x e α' β nz s eq-s
srel-wd {suc m} (inj₁ ml')      (Base.semi-MS x) = {!!}
-- semi-MS on inj₂: on a = 0 boxes both sides escape through the axiom;
-- on a ≠ 0 boxes the S/S^ letters are absorbed and both sides collapse
-- to the M escape alone.
srel-wd {suc m} (inj₂ ((₀ , b) , lm)) (Base.semi-MS x) =
  semiMS-wd-0 x b ((x ⁻¹) .proj₁ * b) lm Eq.refl
srel-wd {suc m} (inj₂ ((₁₊ a' , b) , lm)) (Base.semi-MS x) =
  semiMS-wd-+ x a'
    (x≢0⇒suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂) .proj₁)
    b ((x ⁻¹) .proj₁ * b) (b + nsum (toℕ (x ^2)) (- ₁₊ a')) lm
    (x≢0⇒suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂) .proj₂)
    Eq.refl Eq.refl
-- semi-M↑CZ: the lifted M word threads the second D box (ract-↑-≡),
-- and the axiom applies directly since its words are already ↑-shaped.
srel-wd {suc n'} (inj₁ ml') (Base.semi-M↑CZ x) = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) (Base.semi-M↑CZ x) = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) (Base.semi-M↑CZ x) = {!!}
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₀ , g2) , lm2))) (Base.semi-M↑CZ x) =
  semiMuCZ-go-00 x b1 g2 ((x ⁻¹) .proj₁ * g2) lm2 Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₁₊ c2 , g2) , lm2))) (Base.semi-M↑CZ x) =
  semiMuCZ-go-0c x (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₁) c2
    (x≢0⇒suc (x .proj₁ * ₁₊ c2) ((x *' (₁₊ c2 , λ ())) .proj₂) .proj₁)
    b1 g2 ((x ⁻¹) .proj₁ * g2) (b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2)) lm2
    (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₂)
    (x≢0⇒suc (x .proj₁ * ₁₊ c2) ((x *' (₁₊ c2 , λ ())) .proj₂) .proj₂)
    Eq.refl Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1 , b1) , inj₂ ((₀ , g2) , lm2))) (Base.semi-M↑CZ x) =
  semiMuCZ-go-a0 x (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₁) a1
    b1 g2 ((x ⁻¹) .proj₁ * g2) (g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1)) lm2
    (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₂)
    Eq.refl Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1 , b1) , inj₂ ((₁₊ c2 , g2) , lm2))) (Base.semi-M↑CZ x) =
  semiMuCZ-go-cc x (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₁) a1 c2
    (x≢0⇒suc (x .proj₁ * ₁₊ c2) ((x *' (₁₊ c2 , λ ())) .proj₂) .proj₁)
    b1 g2 ((x ⁻¹) .proj₁ * g2) (b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2))
    (g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1)) lm2
    (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₂)
    (x≢0⇒suc (x .proj₁ * ₁₊ c2) ((x *' (₁₊ c2 , λ ())) .proj₂) .proj₂)
    Eq.refl Eq.refl Eq.refl
-- semi-M↓CZ: on doubly-inj₂ cosets M↓≡ turns the down-widened M word
-- into the plain M word and the MD/CZ^ engines drive both sides to the
-- axiom one width down (SrelWDMCZ).
srel-wd {suc n'} (inj₁ ml') (Base.semi-M↓CZ x) = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) (Base.semi-M↓CZ x) = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) (Base.semi-M↓CZ x) = {!!}
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₀ , g2) , lm2))) (Base.semi-M↓CZ x) =
  semiMCZ-go-00 x b1 g2 ((x ⁻¹) .proj₁ * b1) lm2 Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₁₊ c2 , g2) , lm2))) (Base.semi-M↓CZ x) =
  semiMCZ-go-0c x (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₁) c2 b1 g2
    ((x ⁻¹) .proj₁ * b1) (b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2)) lm2
    (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₂) Eq.refl Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1 , b1) , inj₂ ((₀ , g2) , lm2))) (Base.semi-M↓CZ x) =
  semiMCZ-go-a0 x (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₁) a1
    (x≢0⇒suc (x .proj₁ * ₁₊ a1) ((x *' (₁₊ a1 , λ ())) .proj₂) .proj₁)
    b1 g2 ((x ⁻¹) .proj₁ * b1) (g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1)) lm2
    (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₂)
    (x≢0⇒suc (x .proj₁ * ₁₊ a1) ((x *' (₁₊ a1 , λ ())) .proj₂) .proj₂)
    Eq.refl Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1 , b1) , inj₂ ((₁₊ c2 , g2) , lm2))) (Base.semi-M↓CZ x) =
  semiMCZ-go-cc x (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₁) a1
    (x≢0⇒suc (x .proj₁ * ₁₊ a1) ((x *' (₁₊ a1 , λ ())) .proj₂) .proj₁) c2
    b1 g2 ((x ⁻¹) .proj₁ * b1) (b1 + nsum (toℕ (x .proj₁)) (- ₁₊ c2))
    (g2 + nsum (toℕ (x .proj₁)) (- ₁₊ a1)) lm2
    (x≢0⇒suc (x .proj₁) (x .proj₂) .proj₂)
    (x≢0⇒suc (x .proj₁ * ₁₊ a1) ((x *' (₁₊ a1 , λ ())) .proj₂) .proj₂)
    Eq.refl Eq.refl Eq.refl
-- order-CZ on a doubly-inj₂ coset: the b-shifts cycle with period p
-- (nsum-p≡0) and the residual is the p-th power of the DD-CZ escape,
-- which vanishes as a conjugate of CZ ^ p (fully nonzero pattern open).
srel-wd {suc n'} (inj₁ ml') Base.order-CZ = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) Base.order-CZ = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) Base.order-CZ = {!!}
srel-wd {suc (suc m)} (inj₂ (d1 , inj₂ (d2 , lm2))) Base.order-CZ =
  orderCZ-go d1 d2 lm2
-- comm-CZ-S↓ on a doubly-inj₂ coset: both gates act on the two bottom
-- D boxes; the coset updates are commuting b-shifts, and the CZ escape
-- (b-irrelevant, a-components preserved) commutes with the S escape.
srel-wd {suc n'} (inj₁ ml') Base.comm-CZ-S↓ = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) Base.comm-CZ-S↓ = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) Base.comm-CZ-S↓ = {!!}
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ (d2 , lm2))) Base.comm-CZ-S↓ =
  comm-W-S b1 d2 , Eq.refl
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1 , b1) , inj₂ (d2 , lm2))) Base.comm-CZ-S↓ =
  commCZS↓-go-+ a1 b1 d2 lm2
-- comm-CZ-S↑ on a doubly-inj₂ coset: S↑ recurses onto the second D box.
srel-wd {suc n'} (inj₁ ml') Base.comm-CZ-S↑ = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) Base.comm-CZ-S↑ = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) Base.comm-CZ-S↑ = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₂ ((₀ , b2) , lm2))) Base.comm-CZ-S↑ =
  comm-W-S↑ d b2 , Eq.refl
srel-wd {suc (suc m)} (inj₂ (d , inj₂ ((₁₊ a2 , b2) , lm2))) Base.comm-CZ-S↑ =
  commCZS↑-go-+ d a2 b2 lm2
-- selinger-c10: the S⁻¹ = S^(p-1) chunks thread through the box pair
-- with the S^-engines; on the all-zero pattern every escape is its
-- letter and the residual is the axiom (other patterns open).
srel-wd {suc n'} (inj₁ ml') Base.selinger-c10 = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) Base.selinger-c10 = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) Base.selinger-c10 = {!!}
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₀ , ₀) , lm2))) Base.selinger-c10 =
  c10-go-000 b1 lm2
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₀ , ₁₊ b2') , lm2))) Base.selinger-c10 =
  c10-go-0b2 b1 b2' lm2
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₀) , lm2))) Base.selinger-c10 =
  c10-go-0a0 b1 a2' lm2
srel-wd {suc (suc m)} (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₁₊ b2'') , lm2))) Base.selinger-c10 =
  elim-fin (₁₊ b2'' + ₁₊ a2')
    (λ eqs → elim-suc (- ₁₊ a2') (neg≢0 (₁₊ a2') λ ()) λ y eq-y →
       c10-go-0aaA b1 a2' b2'' y lm2 eqs eq-y)
    (λ w eqw → c10-go-0aaB b1 a2' b2'' w lm2 eqw)
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₀) , lm2))) Base.selinger-c10 =
  elim-suc (- ₁₊ a1') (neg≢0 (₁₊ a1') λ ()) λ y eq-y →
  c10-go-a00 b1 a1' y lm2 eq-y
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₁₊ b2') , lm2))) Base.selinger-c10 =
  elim-fin (₁₊ b2' + - ₁₊ a1')
    (λ eqX → c10-go-a0bα b1 a1' b2' lm2 eqX)
    (λ x eqX → c10-go-a0bβ b1 a1' b2' x lm2 eqX)
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2))) Base.selinger-c10 =
  elim-fin (b2 + - ₁₊ a1')
    (λ eqY → elim-fin (b2 + ₁₊ a2')
      (λ eqZ → c10-go-aaαα b1 b2 a1' a2' lm2 eqY eqZ)
      (λ z eqZ → c10-go-aaαβ b1 b2 a1' a2' z lm2 eqY eqZ))
    (λ y eqY → elim-fin (b2 + ₁₊ a2')
      (λ eqZ → c10-go-aaβα b1 b2 a1' a2' y lm2 eqY eqZ)
      (λ z eqZ → c10-go-aaββ b1 b2 a1' a2' y z lm2 eqY eqZ))
srel-wd {suc n'} (inj₁ ml') Base.selinger-c11 = {!!}
srel-wd {suc zero} (inj₂ (d , ml1)) Base.selinger-c11 = {!!}
srel-wd {suc (suc m)} (inj₂ (d , inj₁ ml')) Base.selinger-c11 = {!!}
srel-wd {suc (suc m)} (inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2))) Base.selinger-c11 =
  c11-go-000 b2 lm2
srel-wd {suc (suc m)} (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₀ , b2) , lm2))) Base.selinger-c11 =
  c11-go-0b1 b1' b2 lm2
srel-wd {suc (suc m)} (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₁₊ a2' , b2) , lm2))) Base.selinger-c11 = {!!}
srel-wd {suc (suc m)} (inj₂ ((₀ , ₀) , inj₂ ((₁₊ a2' , b2) , lm2))) Base.selinger-c11 =
  elim-suc (- (₁₊ a2')) (neg≢0 (₁₊ a2') λ ()) λ y eq-y →
  c11-go-0a2 b2 a2' y lm2 eq-y
srel-wd {suc (suc m)} (inj₂ ((₁₊ a1' , b1) , inj₂ (d2 , lm2))) Base.selinger-c11 = {!!}
-- selinger-c12 on triply-inj₂ cosets with a clean middle wire: the two
-- CZ escapes commute letterwise (axiom at the cores).  Nonzero-middle
-- patterns still open.
srel-wd {suc (suc n)} (inj₁ ml') Base.selinger-c12 = {!!}
srel-wd {suc (suc n)} (inj₂ (d1 , inj₁ ml')) Base.selinger-c12 = {!!}
srel-wd {suc (suc zero)} (inj₂ (d1 , inj₂ (d2 , ml1))) Base.selinger-c12 = {!!}
srel-wd {suc (suc (suc m))} (inj₂ (d1 , inj₂ (d2 , inj₁ ml'))) Base.selinger-c12 = {!!}
srel-wd {suc (suc (suc m))} (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3)))) Base.selinger-c12 =
  c12-go-000 b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3)))) Base.selinger-c12 =
  c12-go-a00 a1' b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3)))) Base.selinger-c12 =
  c12-go-00c a3' b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3)))) Base.selinger-c12 =
  c12-go-a0c a1' a3' b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , b2) , inj₂ ((₀ , b3) , lm3)))) Base.selinger-c12 =
  c12-go-0c0 a2' b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , inj₂ ((₀ , b3) , lm3)))) Base.selinger-c12 =
  c12-go-aa0 a1' a2' b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , b2) , inj₂ ((₁₊ a3' , b3) , lm3)))) Base.selinger-c12 =
  c12-go-0aa a2' a3' b1 b2 b3 lm3
srel-wd {suc (suc (suc m))} (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , inj₂ ((₁₊ a3' , b3) , lm3)))) Base.selinger-c12 =
  c12-go-aaa a1' a2' a3' b1 b2 b3 lm3
srel-wd c Base.selinger-c13   = {!!}
srel-wd c Base.selinger-c14   = {!!}
srel-wd c Base.selinger-c15   = {!!}
