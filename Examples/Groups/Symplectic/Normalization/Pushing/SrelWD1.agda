------------------------------------------------------------------------
-- Presentations of groups
--
-- Width-1 well-definedness of the coset action, COMPLETE: the {zero}
-- clauses of SrelWD.srel-wd extracted into a hole-free --safe module,
-- so the 0→1 tower level can be instantiated (SrelWD itself still has
-- open higher-width holes and cannot be imported).  At width 1 only
-- the six unary axiom families apply (the CZ families need width ≥ 2
-- and are excluded by their indices).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD1
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDW1
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  p-2 p-prime

------------------------------------------------------------------------
-- The width-1 axioms, one at a time (verbatim from SrelWD's {zero}
-- clauses).

srel-wd1 : ∀ (c : C 1) {u t : Circuit 1} →
  Base._SRel,_===_ 1 u t →
  (ract {0} ᵗ) c u ≋ (ract {0} ᵗ) c t
srel-wd1 (([] , e) , ([] , ((₀ , ₀) , nz)))     Base.order-S = ⊥-elim (nz auto)
srel-wd1 (([] , e) , ([] , ((₀ , ₁₊ b') , nz))) Base.order-S =
  sing0 ,
  Eq.trans (ract1-S^-a0 p e b' nz)
           (c1-eq (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- (kS-a0 b' nz))))
                            (+-identityʳ e))
                  Eq.refl)
srel-wd1 (([] , e) , ([] , ((₁₊ a' , b) , nz))) Base.order-S =
  sing0 ,
  Eq.trans (ract1-S^-a+ p e a' b nz)
           (c1-eq Eq.refl
                  (Eq.cong (λ z → ₁₊ a' , z)
                           (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- (₁₊ a'))))
                                     (+-identityʳ b))))
srel-wd1 (([] , e) , ([] , ((₀ , ₀) , nz))) Base.order-H = ⊥-elim (nz auto)
srel-wd1 (([] , e) , ([] , ((₀ , ₁₊ b₀) , nz))) Base.order-H =
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ y eq-y →
  order-H-0b e b₀ nz y eq-y
srel-wd1 (([] , e) , ([] , ((₁₊ a₀ , ₀) , nz))) Base.order-H =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ y)) (neg≢0 (₁₊ y) λ ()) λ y2 eq-y2 →
  order-H-a0 e a₀ nz y y2 eq-y eq-y2
srel-wd1 (([] , e) , ([] , ((₁₊ a₀ , ₁₊ b₀) , nz))) Base.order-H =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  order-H-nn e a₀ b₀ nz y z eq-y eq-z
srel-wd1 (([] , e) , ([] , ((₀ , ₀) , nz))) Base.order-SH = ⊥-elim (nz auto)
srel-wd1 (([] , e) , ([] , ((₀ , ₁₊ b₀) , nz))) Base.order-SH =
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  order-SH-0b e b₀ nz z eq-z
srel-wd1 (([] , e) , ([] , ((₁₊ a₀ , ₀) , nz))) Base.order-SH =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  order-SH-a0 e a₀ nz y eq-y
srel-wd1 (([] , e) , ([] , ((₁₊ a₀ , ₁₊ b₀) , nz))) Base.order-SH =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-fin (₁₊ b₀ + - (₁₊ a₀))
    (λ Xeq → order-SH-nn0 e a₀ b₀ nz y eq-y Xeq)
    (λ w Xeq → elim-suc (- (₁₊ w)) (neg≢0 (₁₊ w) λ ()) λ t eq-t →
       order-SH-nnw e a₀ b₀ nz y z w t eq-y eq-z Xeq eq-t)
srel-wd1 (([] , e) , ([] , ((₀ , ₀) , nz))) Base.comm-HHS = ⊥-elim (nz auto)
srel-wd1 (([] , e) , ([] , ((₀ , ₁₊ b₀) , nz))) Base.comm-HHS =
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ y eq-y →
  comm-HHS-0b e b₀ nz y eq-y
srel-wd1 (([] , e) , ([] , ((₁₊ a₀ , ₀) , nz))) Base.comm-HHS =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  comm-HHS-a0 e a₀ nz y eq-y
srel-wd1 (([] , e) , ([] , ((₁₊ a₀ , ₁₊ b₀) , nz))) Base.comm-HHS =
  elim-suc (- (₁₊ a₀)) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- (₁₊ b₀)) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-fin (₁₊ b₀ + - (₁₊ a₀))
    (λ Xeq → comm-HHS-nn0 e a₀ b₀ nz y z eq-y eq-z Xeq)
    (λ w Xeq → comm-HHS-nnw e a₀ b₀ nz y z w eq-y eq-z Xeq)
srel-wd1 (([] , e) , ([] , (ab , nz))) (Base.M-mul x y) =
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
srel-wd1 (([] , e) , ([] , ((₀ , ₀) , nz))) (Base.semi-MS x) =
  ⊥-elim (nz auto)
srel-wd1 (([] , e) , ([] , ((₀ , ₁₊ β') , nz))) (Base.semi-MS x) =
  elim-suc ((x ⁻¹) .proj₁ * ₁₊ β') (((x ⁻¹) *' (₁₊ β' , λ ())) .proj₂)
    λ m eq-m →
  PB.trans sing0 (PB.sym sing0) , semi-MS-0b x e β' nz m eq-m
srel-wd1 (([] , e) , ([] , ((₁₊ α' , β) , nz))) (Base.semi-MS x) =
  elim-suc (x .proj₁ * ₁₊ α') ((x *' (₁₊ α' , λ ())) .proj₂)
    λ s eq-s →
  PB.trans sing0 (PB.sym sing0) , semi-MS-nn x e α' β nz s eq-s

------------------------------------------------------------------------
-- The FULL level-1 well-definedness: the lifted relation at width 1 is
-- srel (the six families above) + cong↑ (a lifted width-0 word — Gen 0
-- is empty, so both sides fix the coset and the residuals collapse) +
-- comm₁ (vacuous: its lifted gate lives in the empty Gen 0); comm₂ is
-- excluded by its width index.

ract-base-↑ : (c : C 1) (w : Circuit 0) → (ract {0} ᵗ) c (w ↑) .proj₂ ≡ c
ract-base-↑ c ε       = Eq.refl
ract-base-↑ c [ () ]ʷ
ract-base-↑ c (u • v) rewrite ract-base-↑ c u = ract-base-↑ c v

wd1 : ∀ (c : C 1) {u t : Circuit 1} →
  Symplectic._QRel,_===_ 1 u t →
  (ract {0} ᵗ) c u ≋ (ract {0} ᵗ) c t
wd1 c (srel x) = srel-wd1 c x
wd1 c (cong↑ {w = w} {v} eq) =
    PB.trans sing0 (PB.sym sing0)
  , Eq.trans (ract-base-↑ c w) (Eq.sym (ract-base-↑ c v))
wd1 c (comm₁ h ())
