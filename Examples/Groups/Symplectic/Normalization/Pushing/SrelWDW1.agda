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

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDW1
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
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
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)
import Relation.Binary.Reasoning.Setoid as SR
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Fin using (Fin)
import Data.Nat.Properties as NP
open import Data.Unit using (tt)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (A-dir-S-power)
import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime

-- The three width-1 H⁴ orbits, one helper per zero-pattern of the A
-- box.  The traversal fully computes (the width-1 action never inspects
-- the A value), so each case is a pair of value equalities: the E box
-- accumulates the four escape powers, the A box comes back to itself.
-- Stuck (negated) intermediate values are handled by rewriting through
-- the a'H-cong / kH-cong congruences using the successor forms
-- (y ≡ -a, …) supplied by elim-suc.
order-H-0b : ∀ (e : E) (b₀ : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y : Fin (₁₊ p-2)) →
  - (₁₊ b₀) ≡ ₁₊ y →
  ((ract {0} ᵗ) (mk e (₀ , ₁₊ b₀) nz) (H ^ 4)) ≋
    (ε , mk e (₀ , ₁₊ b₀) nz)
order-H-0b e b₀ nz y eq-y = sing0 , c1-eq e-fix v4eq
  where
  A0 A2 A3 : A
  A0 = (₀ , ₁₊ b₀) , nz
  A2 = OA.dir-and-A'-of 0 (OA.dir-and-A'-of 0 A0 gH tt .proj₂) gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gH tt .proj₂

  v2eq : A2 .proj₁ ≡ (₀ , ₁₊ y)
  v2eq = Eq.cong (₀ ,_) eq-y
  v3eq : A3 .proj₁ ≡ (₁₊ y , ₀)
  v3eq = a'H-cong {A2} {(₀ , ₁₊ y) , (λ ())} v2eq
  v4eq : a'H A3 ≡ (₀ , ₁₊ b₀)
  v4eq = Eq.trans (a'H-cong {A3} {(₁₊ y , ₀) , (λ ())} v3eq)
           (Eq.cong (₀ ,_)
             (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ b₀))))

  e-fix : (((e + - ₀) + - ₀) + - kH A2) + - kH A3 ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong (((e + - ₀) + - ₀) +_)
        (Eq.cong -_ (kH-cong {A2} {(₀ , ₁₊ y) , (λ ())} v2eq)))
      (Eq.cong -_ (kH-cong {A3} {(₁₊ y , ₀) , (λ ())} v3eq)))
    (Eq.trans (e+-0 _) (Eq.trans (e+-0 _) (Eq.trans (e+-0 _) (e+-0 e))))

order-H-a0 : ∀ (e : E) (a₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀)) (y y2 : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y → - (₁₊ y) ≡ ₁₊ y2 →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₀) nz) (H ^ 4)) ≋
    (ε , mk e (₁₊ a₀ , ₀) nz)
order-H-a0 e a₀ nz y y2 eq-y eq-y2 = sing0 , c1-eq e-fix v4eq
  where
  A1 A2 A3 : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₀) , nz) gH tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gH tt .proj₂

  v1eq : A1 .proj₁ ≡ (₀ , ₁₊ y)
  v1eq = Eq.cong (₀ ,_) eq-y
  v2eq : A2 .proj₁ ≡ (₁₊ y , ₀)
  v2eq = a'H-cong {A1} {(₀ , ₁₊ y) , (λ ())} v1eq
  v3eq : A3 .proj₁ ≡ (₀ , ₁₊ y2)
  v3eq = Eq.trans (a'H-cong {A2} {(₁₊ y , ₀) , (λ ())} v2eq)
                  (Eq.cong (₀ ,_) eq-y2)
  v4eq : a'H A3 ≡ (₁₊ a₀ , ₀)
  v4eq = Eq.trans (a'H-cong {A3} {(₀ , ₁₊ y2) , (λ ())} v3eq)
           (Eq.cong (_, ₀)
             (Eq.trans (Eq.sym eq-y2)
               (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀)))))

  e-fix : (((e + - ₀) + - kH A1) + - kH A2) + - kH A3 ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_
        (Eq.cong ((e + - ₀) +_)
          (Eq.cong -_ (kH-cong {A1} {(₀ , ₁₊ y) , (λ ())} v1eq)))
        (Eq.cong -_ (kH-cong {A2} {(₁₊ y , ₀) , (λ ())} v2eq)))
      (Eq.cong -_ (kH-cong {A3} {(₀ , ₁₊ y2) , (λ ())} v3eq)))
    (Eq.trans (e+-0 _) (Eq.trans (e+-0 _) (Eq.trans (e+-0 _) (e+-0 e))))

order-H-nn : ∀ (e : E) (a₀ b₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y z : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y → - (₁₊ b₀) ≡ ₁₊ z →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) (H ^ 4)) ≋
    (ε , mk e (₁₊ a₀ , ₁₊ b₀) nz)
order-H-nn e a₀ b₀ nz y z eq-y eq-z = sing0 , c1-eq e-fix v4eq
  where
  eq3 : - (₁₊ y) ≡ ₁₊ a₀
  eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))
  eq4 : - (₁₊ z) ≡ ₁₊ b₀
  eq4 = Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b₀))

  A0 A1 A2 A3 : A
  A0 = (₁₊ a₀ , ₁₊ b₀) , nz
  A1 = OA.dir-and-A'-of 0 A0 gH tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gH tt .proj₂

  v1eq : A1 .proj₁ ≡ (₁₊ b₀ , ₁₊ y)
  v1eq = Eq.cong (₁₊ b₀ ,_) eq-y
  v2eq : A2 .proj₁ ≡ (₁₊ y , ₁₊ z)
  v2eq = Eq.trans (a'H-cong {A1} {(₁₊ b₀ , ₁₊ y) , (λ ())} v1eq)
                  (Eq.cong (₁₊ y ,_) eq-z)
  v3eq : A3 .proj₁ ≡ (₁₊ z , ₁₊ a₀)
  v3eq = Eq.trans (a'H-cong {A2} {(₁₊ y , ₁₊ z) , (λ ())} v2eq)
                  (Eq.cong (₁₊ z ,_) eq3)
  v4eq : a'H A3 ≡ (₁₊ a₀ , ₁₊ b₀)
  v4eq = Eq.trans (a'H-cong {A3} {(₁₊ z , ₁₊ a₀) , (λ ())} v3eq)
                  (Eq.cong (₁₊ a₀ ,_) eq4)

  u : ℤ* ₚ
  u = (₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())

  K1 K2 K3 K4 : ℤ ₚ
  K1 = A-dir-S-power ((₁₊ a₀ , ₁₊ b₀) , nz) gH tt .proj₁
  K2 = A-dir-S-power ((₁₊ b₀ , ₁₊ y) , (λ ())) gH tt .proj₁
  K3 = A-dir-S-power ((₁₊ y , ₁₊ z) , (λ ())) gH tt .proj₁
  K4 = A-dir-S-power ((₁₊ z , ₁₊ a₀) , (λ ())) gH tt .proj₁

  K2≡ : K2 ≡ - K1
  K2≡ = Eq.trans
    (inv-cong ((₁₊ b₀ , λ ()) *' (₁₊ y , λ ())) (-' u)
      (Eq.trans (Eq.cong (₁₊ b₀ *_) (Eq.sym eq-y))
        (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ b₀) (₁₊ a₀)))
                  (Eq.cong -_ (*-comm (₁₊ b₀) (₁₊ a₀))))))
    (inv-neg-comm u)

  K3≡ : K3 ≡ K1
  K3≡ = inv-cong ((₁₊ y , λ ()) *' (₁₊ z , λ ())) u
    (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-y) (Eq.sym eq-z))
      (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a₀) (- (₁₊ b₀))))
        (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* (₁₊ a₀) (₁₊ b₀))))
                  (-‿involutive (₁₊ a₀ * ₁₊ b₀)))))

  K4≡ : K4 ≡ - K1
  K4≡ = Eq.trans
    (inv-cong ((₁₊ z , λ ()) *' (₁₊ a₀ , λ ())) (-' u)
      (Eq.trans (Eq.cong (_* ₁₊ a₀) (Eq.sym eq-z))
        (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b₀) (₁₊ a₀)))
                  (Eq.cong -_ (*-comm (₁₊ b₀) (₁₊ a₀))))))
    (inv-neg-comm u)

  k1fix : kH A1 ≡ - K1
  k1fix = Eq.trans (kH-cong {A1} {(₁₊ b₀ , ₁₊ y) , (λ ())} v1eq) K2≡
  k2fix : kH A2 ≡ K1
  k2fix = Eq.trans (kH-cong {A2} {(₁₊ y , ₁₊ z) , (λ ())} v2eq) K3≡
  k3fix : kH A3 ≡ - K1
  k3fix = Eq.trans (kH-cong {A3} {(₁₊ z , ₁₊ a₀) , (λ ())} v3eq) K4≡

  s1 : ∀ x → (x + - K1) + - (- K1) ≡ x
  s1 x = Eq.trans (+-assoc x (- K1) (- (- K1)))
         (Eq.trans (Eq.cong (x +_) (+-inverseʳ (- K1))) (+-identityʳ x))

  e-fix : (((e + - K1) + - kH A1) + - kH A2) + - kH A3 ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_ (Eq.cong ((e + - K1) +_) (Eq.cong -_ k1fix))
                    (Eq.cong -_ k2fix))
      (Eq.cong -_ k3fix))
    (Eq.trans (s1 ((e + - K1) + - (- K1))) (s1 e))

-- comm-HHS at width 1, one helper per zero-pattern of the A box.  Both
-- sides are computed to their (e , a) updates; the escape powers agree
-- because H's power on a fully nonzero box only changes by a sign under
-- negating a factor (Kab-neg), and S's power is invariant under
-- negating the b component (negneg-*).
comm-HHS-0b : ∀ (e : E) (b₀ : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y : Fin (₁₊ p-2)) →
  - (₁₊ b₀) ≡ ₁₊ y →
  ((ract {0} ᵗ) (mk e (₀ , ₁₊ b₀) nz) (H • H • S)) ≋
    ((ract {0} ᵗ) (mk e (₀ , ₁₊ b₀) nz) (S • H • H))
comm-HHS-0b e b₀ nz y eq-y =
  PB.trans sing0 (PB.sym sing0) , c1-eq e-eq ab-eq
  where
  A2 A3 : A
  A2 = OA.dir-and-A'-of 0
         (OA.dir-and-A'-of 0 ((₀ , ₁₊ b₀) , nz) gH tt .proj₂) gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂

  v2eq : A2 .proj₁ ≡ (₀ , ₁₊ y)
  v2eq = Eq.cong (₀ ,_) eq-y

  ab-eq : A3 .proj₁ ≡ (₀ , - (₁₊ b₀))
  ab-eq = Eq.trans (a'S-cong {A2} {(₀ , ₁₊ y) , (λ ())} v2eq)
                   (Eq.cong (₀ ,_) (Eq.sym eq-y))

  Bi : ℤ ₚ
  Bi = ((₁₊ b₀ , λ ()) ⁻¹) .proj₁

  i : ((₁₊ y , λ ()) ⁻¹) .proj₁ ≡ - Bi
  i = Eq.trans (inv-cong (₁₊ y , λ ()) (-' (₁₊ b₀ , λ ())) (Eq.sym eq-y))
               (inv-neg-comm (₁₊ b₀ , λ ()))

  kSfix : kS A2 ≡ kS-a0 b₀ nz
  kSfix = Eq.trans (kS-cong {A2} {(₀ , ₁₊ y) , (λ ())} v2eq)
                   (Eq.trans (Eq.cong₂ _*_ i i) (negneg-* Bi Bi))

  e-eq : ((e + - ₀) + - ₀) + - kS A2 ≡ ((e + - kS-a0 b₀ nz) + - ₀) + - ₀
  e-eq = Eq.trans (Eq.cong (_+ (- kS A2)) (Eq.trans (e+-0 (e + - ₀)) (e+-0 e)))
         (Eq.trans (Eq.cong (λ v → e + - v) kSfix)
           (Eq.sym (Eq.trans (e+-0 ((e + - kS-a0 b₀ nz) + - ₀))
                             (e+-0 (e + - kS-a0 b₀ nz)))))

comm-HHS-a0 : ∀ (e : E) (a₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀)) (y : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₀) nz) (H • H • S)) ≋
    ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₀) nz) (S • H • H))
comm-HHS-a0 e a₀ nz y eq-y =
  PB.trans sing0 (PB.sym sing0) , c1-eq e-eq ab-eq
  where
  A1 A2 A3 A1ʳ A2ʳ A3ʳ : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₀) , nz) gH tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A1ʳ = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₀) , nz) gS tt .proj₂
  A2ʳ = OA.dir-and-A'-of 0 A1ʳ gH tt .proj₂
  A3ʳ = OA.dir-and-A'-of 0 A2ʳ gH tt .proj₂

  v1eq : A1 .proj₁ ≡ (₀ , ₁₊ y)
  v1eq = Eq.cong (₀ ,_) eq-y
  v2eq : A2 .proj₁ ≡ (₁₊ y , ₀)
  v2eq = a'H-cong {A1} {(₀ , ₁₊ y) , (λ ())} v1eq
  v3eq : A3 .proj₁ ≡ (₁₊ y , - (₁₊ y))
  v3eq = Eq.trans (a'S-cong {A2} {(₁₊ y , ₀) , (λ ())} v2eq)
                  (Eq.cong (₁₊ y ,_) (+-0ˡ (- (₁₊ y))))

  v1ʳeq : A1ʳ .proj₁ ≡ (₁₊ a₀ , ₁₊ y)
  v1ʳeq = Eq.cong (₁₊ a₀ ,_) (Eq.trans (+-0ˡ (- (₁₊ a₀))) eq-y)
  v2ʳeq : A2ʳ .proj₁ ≡ (₁₊ y , ₁₊ y)
  v2ʳeq = Eq.trans (a'H-cong {A1ʳ} {(₁₊ a₀ , ₁₊ y) , (λ ())} v1ʳeq)
                   (Eq.cong (₁₊ y ,_) eq-y)
  v3ʳeq : A3ʳ .proj₁ ≡ (₁₊ y , - (₁₊ y))
  v3ʳeq = a'H-cong {A2ʳ} {(₁₊ y , ₁₊ y) , (λ ())} v2ʳeq

  ab-eq : A3 .proj₁ ≡ A3ʳ .proj₁
  ab-eq = Eq.trans v3eq (Eq.sym v3ʳeq)

  kHfix : kH A1 ≡ ₀
  kHfix = kH-cong {A1} {(₀ , ₁₊ y) , (λ ())} v1eq
  kSfix : kS A2 ≡ ₀
  kSfix = kS-cong {A2} {(₁₊ y , ₀) , (λ ())} v2eq

  e-L : ((e + - ₀) + - kH A1) + - kS A2 ≡ e
  e-L = Eq.trans
    (Eq.cong₂ _+_ (Eq.cong ((e + - ₀) +_) (Eq.cong -_ kHfix))
                  (Eq.cong -_ kSfix))
    (Eq.trans (e+-0 ((e + - ₀) + - ₀)) (Eq.trans (e+-0 (e + - ₀)) (e+-0 e)))

  KabYY : Kab y y ≡ Kab a₀ a₀
  KabYY = inv-cong ((₁₊ y , λ ()) *' (₁₊ y , λ ()))
                   ((₁₊ a₀ , λ ()) *' (₁₊ a₀ , λ ()))
            (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-y) (Eq.sym eq-y))
                      (negneg-* (₁₊ a₀) (₁₊ a₀)))

  e-R : ((e + - ₀) + - kH A1ʳ) + - kH A2ʳ ≡ e
  e-R = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong ((e + - ₀) +_)
        (Eq.cong -_ (Eq.trans (kH-cong {A1ʳ} {(₁₊ a₀ , ₁₊ y) , (λ ())} v1ʳeq)
                              (Kab-neg a₀ a₀ y (Eq.sym eq-y)))))
      (Eq.cong -_ (Eq.trans (kH-cong {A2ʳ} {(₁₊ y , ₁₊ y) , (λ ())} v2ʳeq)
                            KabYY)))
    (Eq.trans (cancel-+' (e + - ₀) (Kab a₀ a₀)) (e+-0 e))

  e-eq : ((e + - ₀) + - kH A1) + - kS A2 ≡ ((e + - ₀) + - kH A1ʳ) + - kH A2ʳ
  e-eq = Eq.trans e-L (Eq.sym e-R)

comm-HHS-nn0 : ∀ (e : E) (a₀ b₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y z : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y → - (₁₊ b₀) ≡ ₁₊ z → ₁₊ b₀ + - (₁₊ a₀) ≡ ₀ →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) (H • H • S)) ≋
    ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) (S • H • H))
comm-HHS-nn0 e a₀ b₀ nz y z eq-y eq-z Xeq =
  PB.trans sing0 (PB.sym sing0) , c1-eq e-eq ab-eq
  where
  A1 A2 A3 A1ʳ A2ʳ A3ʳ : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₁₊ b₀) , nz) gH tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A1ʳ = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₁₊ b₀) , nz) gS tt .proj₂
  A2ʳ = OA.dir-and-A'-of 0 A1ʳ gH tt .proj₂
  A3ʳ = OA.dir-and-A'-of 0 A2ʳ gH tt .proj₂

  eq3 : - (₁₊ y) ≡ ₁₊ a₀
  eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

  v1eq : A1 .proj₁ ≡ (₁₊ b₀ , ₁₊ y)
  v1eq = Eq.cong (₁₊ b₀ ,_) eq-y
  v2eq : A2 .proj₁ ≡ (₁₊ y , ₁₊ z)
  v2eq = Eq.trans (a'H-cong {A1} {(₁₊ b₀ , ₁₊ y) , (λ ())} v1eq)
                  (Eq.cong (₁₊ y ,_) eq-z)
  v3eq : A3 .proj₁ ≡ (₁₊ y , ₁₊ z + - (₁₊ y))
  v3eq = a'S-cong {A2} {(₁₊ y , ₁₊ z) , (λ ())} v2eq

  v1ʳeq : A1ʳ .proj₁ ≡ (₁₊ a₀ , ₀)
  v1ʳeq = Eq.cong (₁₊ a₀ ,_) Xeq
  v2ʳeq : A2ʳ .proj₁ ≡ (₀ , ₁₊ y)
  v2ʳeq = Eq.trans (a'H-cong {A1ʳ} {(₁₊ a₀ , ₀) , (λ ())} v1ʳeq)
                   (Eq.cong (₀ ,_) eq-y)
  v3ʳeq : A3ʳ .proj₁ ≡ (₁₊ y , ₀)
  v3ʳeq = a'H-cong {A2ʳ} {(₀ , ₁₊ y) , (λ ())} v2ʳeq

  beq : ₁₊ b₀ ≡ ₁₊ a₀
  beq = +-‿cancel (₁₊ b₀) (₁₊ a₀) Xeq

  zy-0 : ₁₊ z + - (₁₊ y) ≡ ₀
  zy-0 = Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-z) eq3)
         (Eq.trans (Eq.cong (- (₁₊ b₀) +_) (Eq.sym beq)) (+-inverseˡ (₁₊ b₀)))

  ab-eq : A3 .proj₁ ≡ A3ʳ .proj₁
  ab-eq = Eq.trans v3eq
            (Eq.trans (Eq.cong (₁₊ y ,_) zy-0) (Eq.sym v3ʳeq))

  k1fix : kH A1 ≡ - Kab a₀ b₀
  k1fix = Eq.trans (kH-cong {A1} {(₁₊ b₀ , ₁₊ y) , (λ ())} v1eq)
                   (Kab-neg a₀ b₀ y (Eq.sym eq-y))
  k2fix : kS A2 ≡ ₀
  k2fix = kS-cong {A2} {(₁₊ y , ₁₊ z) , (λ ())} v2eq

  e-L : ((e + - Kab a₀ b₀) + - kH A1) + - kS A2 ≡ e
  e-L = Eq.trans
    (Eq.cong₂ _+_ (Eq.cong ((e + - Kab a₀ b₀) +_) (Eq.cong -_ k1fix))
                  (Eq.cong -_ k2fix))
    (Eq.trans (e+-0 ((e + - Kab a₀ b₀) + - (- Kab a₀ b₀)))
              (cancel-+ e (Kab a₀ b₀)))

  e-R : ((e + - ₀) + - kH A1ʳ) + - kH A2ʳ ≡ e
  e-R = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong ((e + - ₀) +_)
        (Eq.cong -_ (kH-cong {A1ʳ} {(₁₊ a₀ , ₀) , (λ ())} v1ʳeq)))
      (Eq.cong -_ (kH-cong {A2ʳ} {(₀ , ₁₊ y) , (λ ())} v2ʳeq)))
    (Eq.trans (e+-0 ((e + - ₀) + - ₀)) (Eq.trans (e+-0 (e + - ₀)) (e+-0 e)))

  e-eq : ((e + - Kab a₀ b₀) + - kH A1) + - kS A2 ≡
         ((e + - ₀) + - kH A1ʳ) + - kH A2ʳ
  e-eq = Eq.trans e-L (Eq.sym e-R)

comm-HHS-nnw : ∀ (e : E) (a₀ b₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y z w : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y → - (₁₊ b₀) ≡ ₁₊ z → ₁₊ b₀ + - (₁₊ a₀) ≡ ₁₊ w →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) (H • H • S)) ≋
    ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) (S • H • H))
comm-HHS-nnw e a₀ b₀ nz y z w eq-y eq-z Xeq =
  PB.trans sing0 (PB.sym sing0) , c1-eq e-eq ab-eq
  where
  A1 A2 A3 A1ʳ A2ʳ A3ʳ : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₁₊ b₀) , nz) gH tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A1ʳ = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₁₊ b₀) , nz) gS tt .proj₂
  A2ʳ = OA.dir-and-A'-of 0 A1ʳ gH tt .proj₂
  A3ʳ = OA.dir-and-A'-of 0 A2ʳ gH tt .proj₂

  eq3 : - (₁₊ y) ≡ ₁₊ a₀
  eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

  v1eq : A1 .proj₁ ≡ (₁₊ b₀ , ₁₊ y)
  v1eq = Eq.cong (₁₊ b₀ ,_) eq-y
  v2eq : A2 .proj₁ ≡ (₁₊ y , ₁₊ z)
  v2eq = Eq.trans (a'H-cong {A1} {(₁₊ b₀ , ₁₊ y) , (λ ())} v1eq)
                  (Eq.cong (₁₊ y ,_) eq-z)
  v3eq : A3 .proj₁ ≡ (₁₊ y , ₁₊ z + - (₁₊ y))
  v3eq = a'S-cong {A2} {(₁₊ y , ₁₊ z) , (λ ())} v2eq

  v1ʳeq : A1ʳ .proj₁ ≡ (₁₊ a₀ , ₁₊ w)
  v1ʳeq = Eq.cong (₁₊ a₀ ,_) Xeq
  v2ʳeq : A2ʳ .proj₁ ≡ (₁₊ w , ₁₊ y)
  v2ʳeq = Eq.trans (a'H-cong {A1ʳ} {(₁₊ a₀ , ₁₊ w) , (λ ())} v1ʳeq)
                   (Eq.cong (₁₊ w ,_) eq-y)
  v3ʳeq : A3ʳ .proj₁ ≡ (₁₊ y , - (₁₊ w))
  v3ʳeq = a'H-cong {A2ʳ} {(₁₊ w , ₁₊ y) , (λ ())} v2ʳeq

  Q : - (₁₊ w) ≡ - (₁₊ b₀) + ₁₊ a₀
  Q = Eq.trans (Eq.cong -_ (Eq.sym Xeq))
      (Eq.trans (Eq.sym (-‿+-comm (₁₊ b₀) (- (₁₊ a₀))))
                (Eq.cong (- (₁₊ b₀) +_) (-‿involutive (₁₊ a₀))))

  ab-eq : A3 .proj₁ ≡ A3ʳ .proj₁
  ab-eq = Eq.trans v3eq
            (Eq.trans
              (Eq.cong (₁₊ y ,_)
                (Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-z) eq3) (Eq.sym Q)))
              (Eq.sym v3ʳeq))

  k1fix : kH A1 ≡ - Kab a₀ b₀
  k1fix = Eq.trans (kH-cong {A1} {(₁₊ b₀ , ₁₊ y) , (λ ())} v1eq)
                   (Kab-neg a₀ b₀ y (Eq.sym eq-y))
  k2fix : kS A2 ≡ ₀
  k2fix = kS-cong {A2} {(₁₊ y , ₁₊ z) , (λ ())} v2eq

  e-L : ((e + - Kab a₀ b₀) + - kH A1) + - kS A2 ≡ e
  e-L = Eq.trans
    (Eq.cong₂ _+_ (Eq.cong ((e + - Kab a₀ b₀) +_) (Eq.cong -_ k1fix))
                  (Eq.cong -_ k2fix))
    (Eq.trans (e+-0 ((e + - Kab a₀ b₀) + - (- Kab a₀ b₀)))
              (cancel-+ e (Kab a₀ b₀)))

  kA1ʳfix : kH A1ʳ ≡ Kab a₀ w
  kA1ʳfix = kH-cong {A1ʳ} {(₁₊ a₀ , ₁₊ w) , (λ ())} v1ʳeq
  kA2ʳfix : kH A2ʳ ≡ - Kab a₀ w
  kA2ʳfix = Eq.trans (kH-cong {A2ʳ} {(₁₊ w , ₁₊ y) , (λ ())} v2ʳeq)
                     (Kab-neg a₀ w y (Eq.sym eq-y))

  e-R : ((e + - ₀) + - kH A1ʳ) + - kH A2ʳ ≡ e
  e-R = Eq.trans
    (Eq.cong₂ _+_ (Eq.cong ((e + - ₀) +_) (Eq.cong -_ kA1ʳfix))
                  (Eq.cong -_ kA2ʳfix))
    (Eq.trans (cancel-+ (e + - ₀) (Kab a₀ w)) (e+-0 e))

  e-eq : ((e + - Kab a₀ b₀) + - kH A1) + - kS A2 ≡
         ((e + - ₀) + - kH A1ʳ) + - kH A2ʳ
  e-eq = Eq.trans e-L (Eq.sym e-R)

------------------------------------------------------------------------
-- Value-level machinery for the M-word cases (M-mul, semi-MS).
--
-- The S-power and H updates of the A box agree, on values, with the
-- total affine maps valS / valH (up to -0/+0 normalisation at the zero
-- patterns).  The M word S^x•H•S^x⁻¹•H•S^x•H then acts on values as
-- diag(x, x⁻¹) — proven once, by ring algebra, in valM-orbit.


-- (S•H)³ at width 1, one helper per zero-pattern.  Six alternating
-- steps; the A box follows the SL₂ orbit of H·S (order 3), and the
-- escape powers cancel: squares of inverses against Kab's (inv-distrib)
-- and, on the fully nonzero orbit, the partial fraction pf-inv.
order-SH-0b : ∀ (e : E) (b₀ : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) (z : Fin (₁₊ p-2)) →
  - (₁₊ b₀) ≡ ₁₊ z →
  ((ract {0} ᵗ) (mk e (₀ , ₁₊ b₀) nz) ((S • H) ^ 3)) ≋
    (ε , mk e (₀ , ₁₊ b₀) nz)
order-SH-0b e b₀ nz z eq-z = sing0 , c1-eq e-fix ab-eq
  where
  A1 A2 A3 A4 A5 : A
  A1 = OA.dir-and-A'-of 0 ((₀ , ₁₊ b₀) , nz) gS tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A4 = OA.dir-and-A'-of 0 A3 gH tt .proj₂
  A5 = OA.dir-and-A'-of 0 A4 gS tt .proj₂

  eqz4 : - (₁₊ z) ≡ ₁₊ b₀
  eqz4 = Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b₀))

  v3eq : A3 .proj₁ ≡ (₁₊ b₀ , ₁₊ z)
  v3eq = Eq.cong (₁₊ b₀ ,_) (Eq.trans (+-0ˡ (- (₁₊ b₀))) eq-z)
  v4eq : A4 .proj₁ ≡ (₁₊ z , ₁₊ z)
  v4eq = Eq.trans (a'H-cong {A3} {(₁₊ b₀ , ₁₊ z) , (λ ())} v3eq)
                  (Eq.cong (₁₊ z ,_) eq-z)
  v5eq : A5 .proj₁ ≡ (₁₊ z , ₀)
  v5eq = Eq.trans (a'S-cong {A4} {(₁₊ z , ₁₊ z) , (λ ())} v4eq)
                  (Eq.cong (₁₊ z ,_) (+-inverseʳ (₁₊ z)))

  ab-eq : a'H A5 ≡ (₀ , ₁₊ b₀)
  ab-eq = Eq.trans (a'H-cong {A5} {(₁₊ z , ₀) , (λ ())} v5eq)
                   (Eq.cong (₀ ,_) eqz4)

  k3fix : kH A3 ≡ - Kab b₀ b₀
  k3fix = Eq.trans (kH-cong {A3} {(₁₊ b₀ , ₁₊ z) , (λ ())} v3eq)
                   (Kab-neg b₀ b₀ z (Eq.sym eq-z))
  k4fix : kS A4 ≡ ₀
  k4fix = kS-cong {A4} {(₁₊ z , ₁₊ z) , (λ ())} v4eq
  k5fix : kH A5 ≡ ₀
  k5fix = kH-cong {A5} {(₁₊ z , ₀) , (λ ())} v5eq

  K0fix : kS-a0 b₀ nz ≡ Kab b₀ b₀
  K0fix = Eq.sym (inv-distrib (₁₊ b₀ , λ ()) (₁₊ b₀ , λ ()))

  e-fix : (((((e + - kS-a0 b₀ nz) + - ₀) + - ₀) + - kH A3) + - kS A4) + - kH A5
          ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_
        (Eq.cong ((((e + - kS-a0 b₀ nz) + - ₀) + - ₀) +_) (Eq.cong -_ k3fix))
        (Eq.cong -_ k4fix))
      (Eq.cong -_ k5fix))
    (Eq.trans (e+-0 _)
    (Eq.trans (e+-0 _)
    (Eq.trans (Eq.cong (_+ - (- Kab b₀ b₀))
                (Eq.trans (e+-0 ((e + - kS-a0 b₀ nz) + - ₀))
                          (e+-0 (e + - kS-a0 b₀ nz))))
    (Eq.trans (Eq.cong (λ v → (e + - v) + - (- Kab b₀ b₀)) K0fix)
              (cancel-+ e (Kab b₀ b₀))))))

order-SH-a0 : ∀ (e : E) (a₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀)) (y : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₀) nz) ((S • H) ^ 3)) ≋
    (ε , mk e (₁₊ a₀ , ₀) nz)
order-SH-a0 e a₀ nz y eq-y = sing0 , c1-eq e-fix ab-eq
  where
  A1 A2 A3 A4 A5 : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₀) , nz) gS tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A4 = OA.dir-and-A'-of 0 A3 gH tt .proj₂
  A5 = OA.dir-and-A'-of 0 A4 gS tt .proj₂

  eq3 : - (₁₊ y) ≡ ₁₊ a₀
  eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

  v1eq : A1 .proj₁ ≡ (₁₊ a₀ , ₁₊ y)
  v1eq = Eq.cong (₁₊ a₀ ,_) (Eq.trans (+-0ˡ (- (₁₊ a₀))) eq-y)
  v2eq : A2 .proj₁ ≡ (₁₊ y , ₁₊ y)
  v2eq = Eq.trans (a'H-cong {A1} {(₁₊ a₀ , ₁₊ y) , (λ ())} v1eq)
                  (Eq.cong (₁₊ y ,_) eq-y)
  v3eq : A3 .proj₁ ≡ (₁₊ y , ₀)
  v3eq = Eq.trans (a'S-cong {A2} {(₁₊ y , ₁₊ y) , (λ ())} v2eq)
                  (Eq.cong (₁₊ y ,_) (+-inverseʳ (₁₊ y)))
  v4eq : A4 .proj₁ ≡ (₀ , ₁₊ a₀)
  v4eq = Eq.trans (a'H-cong {A3} {(₁₊ y , ₀) , (λ ())} v3eq)
                  (Eq.cong (₀ ,_) eq3)
  v5eq : A5 .proj₁ ≡ (₀ , ₁₊ a₀)
  v5eq = a'S-cong {A4} {(₀ , ₁₊ a₀) , (λ ())} v4eq

  ab-eq : a'H A5 ≡ (₁₊ a₀ , ₀)
  ab-eq = a'H-cong {A5} {(₀ , ₁₊ a₀) , (λ ())} v5eq

  k1fix : kH A1 ≡ - Kab a₀ a₀
  k1fix = Eq.trans (kH-cong {A1} {(₁₊ a₀ , ₁₊ y) , (λ ())} v1eq)
                   (Kab-neg a₀ a₀ y (Eq.sym eq-y))
  k2fix : kS A2 ≡ ₀
  k2fix = kS-cong {A2} {(₁₊ y , ₁₊ y) , (λ ())} v2eq
  k3fix : kH A3 ≡ ₀
  k3fix = kH-cong {A3} {(₁₊ y , ₀) , (λ ())} v3eq
  k4fix : kS A4 ≡ Kab a₀ a₀
  k4fix = Eq.trans (kS-cong {A4} {(₀ , ₁₊ a₀) , (λ ())} v4eq)
                   (Eq.sym (inv-distrib (₁₊ a₀ , λ ()) (₁₊ a₀ , λ ())))
  k5fix : kH A5 ≡ ₀
  k5fix = kH-cong {A5} {(₀ , ₁₊ a₀) , (λ ())} v5eq

  e-fix : (((((e + - ₀) + - kH A1) + - kS A2) + - kH A3) + - kS A4) + - kH A5
          ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_
        (Eq.cong₂ _+_
          (Eq.cong₂ _+_
            (Eq.cong ((e + - ₀) +_) (Eq.cong -_ k1fix))
            (Eq.cong -_ k2fix))
          (Eq.cong -_ k3fix))
        (Eq.cong -_ k4fix))
      (Eq.cong -_ k5fix))
    (Eq.trans (e+-0 _)
    (Eq.trans (Eq.cong (_+ - Kab a₀ a₀)
                (Eq.trans (e+-0 _) (e+-0 ((e + - ₀) + - (- Kab a₀ a₀)))))
    (Eq.trans (cancel-+' (e + - ₀) (Kab a₀ a₀)) (e+-0 e))))

order-SH-nn0 : ∀ (e : E) (a₀ b₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y → ₁₊ b₀ + - (₁₊ a₀) ≡ ₀ →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) ((S • H) ^ 3)) ≋
    (ε , mk e (₁₊ a₀ , ₁₊ b₀) nz)
order-SH-nn0 e a₀ b₀ nz y eq-y Xeq = sing0 , c1-eq e-fix ab-eq
  where
  A1 A2 A3 A4 A5 : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₁₊ b₀) , nz) gS tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A4 = OA.dir-and-A'-of 0 A3 gH tt .proj₂
  A5 = OA.dir-and-A'-of 0 A4 gS tt .proj₂

  eq3 : - (₁₊ y) ≡ ₁₊ a₀
  eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))
  beq : ₁₊ b₀ ≡ ₁₊ a₀
  beq = +-‿cancel (₁₊ b₀) (₁₊ a₀) Xeq

  v1eq : A1 .proj₁ ≡ (₁₊ a₀ , ₀)
  v1eq = Eq.cong (₁₊ a₀ ,_) Xeq
  v2eq : A2 .proj₁ ≡ (₀ , ₁₊ y)
  v2eq = Eq.trans (a'H-cong {A1} {(₁₊ a₀ , ₀) , (λ ())} v1eq)
                  (Eq.cong (₀ ,_) eq-y)
  v3eq : A3 .proj₁ ≡ (₀ , ₁₊ y)
  v3eq = a'S-cong {A2} {(₀ , ₁₊ y) , (λ ())} v2eq
  v4eq : A4 .proj₁ ≡ (₁₊ y , ₀)
  v4eq = a'H-cong {A3} {(₀ , ₁₊ y) , (λ ())} v3eq
  v5eq : A5 .proj₁ ≡ (₁₊ y , ₁₊ a₀)
  v5eq = Eq.trans (a'S-cong {A4} {(₁₊ y , ₀) , (λ ())} v4eq)
                  (Eq.cong (₁₊ y ,_) (Eq.trans (+-0ˡ (- (₁₊ y))) eq3))

  ab-eq : a'H A5 ≡ (₁₊ a₀ , ₁₊ b₀)
  ab-eq = Eq.trans (a'H-cong {A5} {(₁₊ y , ₁₊ a₀) , (λ ())} v5eq)
                   (Eq.cong (₁₊ a₀ ,_) (Eq.trans eq3 (Eq.sym beq)))

  k1fix : kH A1 ≡ ₀
  k1fix = kH-cong {A1} {(₁₊ a₀ , ₀) , (λ ())} v1eq
  k2fix : kS A2 ≡ Kab a₀ a₀
  k2fix = Eq.trans (kS-cong {A2} {(₀ , ₁₊ y) , (λ ())} v2eq)
          (Eq.trans (Eq.sym (inv-distrib (₁₊ y , λ ()) (₁₊ y , λ ())))
                    (Kab-yy a₀ y (Eq.sym eq-y)))
  k3fix : kH A3 ≡ ₀
  k3fix = kH-cong {A3} {(₀ , ₁₊ y) , (λ ())} v3eq
  k4fix : kS A4 ≡ ₀
  k4fix = kS-cong {A4} {(₁₊ y , ₀) , (λ ())} v4eq
  k5fix : kH A5 ≡ - Kab a₀ a₀
  k5fix = Eq.trans (kH-cong {A5} {(₁₊ y , ₁₊ a₀) , (λ ())} v5eq)
          (Eq.trans (Kab-comm y a₀) (Kab-neg a₀ a₀ y (Eq.sym eq-y)))

  e-fix : (((((e + - ₀) + - kH A1) + - kS A2) + - kH A3) + - kS A4) + - kH A5
          ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_
        (Eq.cong₂ _+_
          (Eq.cong₂ _+_
            (Eq.cong ((e + - ₀) +_) (Eq.cong -_ k1fix))
            (Eq.cong -_ k2fix))
          (Eq.cong -_ k3fix))
        (Eq.cong -_ k4fix))
      (Eq.cong -_ k5fix))
    (Eq.trans
      (Eq.cong (λ v → ((((v + - Kab a₀ a₀) + - ₀) + - ₀) + - (- Kab a₀ a₀)))
               (Eq.trans (e+-0 (e + - ₀)) (e+-0 e)))
    (Eq.trans
      (Eq.cong (_+ - (- Kab a₀ a₀))
               (Eq.trans (e+-0 _) (e+-0 (e + - Kab a₀ a₀))))
      (cancel-+ e (Kab a₀ a₀))))

order-SH-nnw : ∀ (e : E) (a₀ b₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀)) (y z w t : Fin (₁₊ p-2)) →
  - (₁₊ a₀) ≡ ₁₊ y → - (₁₊ b₀) ≡ ₁₊ z → ₁₊ b₀ + - (₁₊ a₀) ≡ ₁₊ w →
  - (₁₊ w) ≡ ₁₊ t →
  ((ract {0} ᵗ) (mk e (₁₊ a₀ , ₁₊ b₀) nz) ((S • H) ^ 3)) ≋
    (ε , mk e (₁₊ a₀ , ₁₊ b₀) nz)
order-SH-nnw e a₀ b₀ nz y z w t eq-y eq-z Xeq eq-t =
  sing0 , c1-eq e-fix ab-eq
  where
  A1 A2 A3 A4 A5 : A
  A1 = OA.dir-and-A'-of 0 ((₁₊ a₀ , ₁₊ b₀) , nz) gS tt .proj₂
  A2 = OA.dir-and-A'-of 0 A1 gH tt .proj₂
  A3 = OA.dir-and-A'-of 0 A2 gS tt .proj₂
  A4 = OA.dir-and-A'-of 0 A3 gH tt .proj₂
  A5 = OA.dir-and-A'-of 0 A4 gS tt .proj₂

  eqz4 : - (₁₊ z) ≡ ₁₊ b₀
  eqz4 = Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b₀))

  awb : ₁₊ a₀ + ₁₊ w ≡ ₁₊ b₀
  awb = Eq.trans (Eq.cong (₁₊ a₀ +_) (Eq.sym Xeq))
        (Eq.trans (+-comm (₁₊ a₀) (₁₊ b₀ + - (₁₊ a₀)))
        (Eq.trans (+-assoc (₁₊ b₀) (- (₁₊ a₀)) (₁₊ a₀))
        (Eq.trans (Eq.cong (₁₊ b₀ +_) (+-inverseˡ (₁₊ a₀)))
                  (+-identityʳ (₁₊ b₀)))))

  v1eq : A1 .proj₁ ≡ (₁₊ a₀ , ₁₊ w)
  v1eq = Eq.cong (₁₊ a₀ ,_) Xeq
  v2eq : A2 .proj₁ ≡ (₁₊ w , ₁₊ y)
  v2eq = Eq.trans (a'H-cong {A1} {(₁₊ a₀ , ₁₊ w) , (λ ())} v1eq)
                  (Eq.cong (₁₊ w ,_) eq-y)
  v3eq : A3 .proj₁ ≡ (₁₊ w , ₁₊ z)
  v3eq = Eq.trans (a'S-cong {A2} {(₁₊ w , ₁₊ y) , (λ ())} v2eq)
           (Eq.cong (₁₊ w ,_)
             (Eq.trans (Eq.cong (_+ - (₁₊ w)) (Eq.sym eq-y))
               (Eq.trans (-‿+-comm (₁₊ a₀) (₁₊ w))
                 (Eq.trans (Eq.cong -_ awb) eq-z))))
  v4eq : A4 .proj₁ ≡ (₁₊ z , ₁₊ t)
  v4eq = Eq.trans (a'H-cong {A3} {(₁₊ w , ₁₊ z) , (λ ())} v3eq)
                  (Eq.cong (₁₊ z ,_) eq-t)
  v5eq : A5 .proj₁ ≡ (₁₊ z , ₁₊ a₀)
  v5eq = Eq.trans (a'S-cong {A4} {(₁₊ z , ₁₊ t) , (λ ())} v4eq)
           (Eq.cong (₁₊ z ,_)
             (Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-t) eqz4) wb-a))
    where
    wb-a : - (₁₊ w) + ₁₊ b₀ ≡ ₁₊ a₀
    wb-a = Eq.trans (Eq.cong (- (₁₊ w) +_) (Eq.sym awb))
           (Eq.trans (Eq.cong (- (₁₊ w) +_) (+-comm (₁₊ a₀) (₁₊ w)))
           (Eq.trans (Eq.sym (+-assoc (- (₁₊ w)) (₁₊ w) (₁₊ a₀)))
           (Eq.trans (Eq.cong (_+ ₁₊ a₀) (+-inverseˡ (₁₊ w)))
                     (+-0ˡ (₁₊ a₀)))))

  ab-eq : a'H A5 ≡ (₁₊ a₀ , ₁₊ b₀)
  ab-eq = Eq.trans (a'H-cong {A5} {(₁₊ z , ₁₊ a₀) , (λ ())} v5eq)
                   (Eq.cong (₁₊ a₀ ,_) eqz4)

  k1fix : kH A1 ≡ Kab a₀ w
  k1fix = kH-cong {A1} {(₁₊ a₀ , ₁₊ w) , (λ ())} v1eq
  k2fix : kS A2 ≡ ₀
  k2fix = kS-cong {A2} {(₁₊ w , ₁₊ y) , (λ ())} v2eq
  k3fix : kH A3 ≡ - Kab b₀ w
  k3fix = Eq.trans (kH-cong {A3} {(₁₊ w , ₁₊ z) , (λ ())} v3eq)
                   (Kab-neg b₀ w z (Eq.sym eq-z))
  k4fix : kS A4 ≡ ₀
  k4fix = kS-cong {A4} {(₁₊ z , ₁₊ t) , (λ ())} v4eq
  k5fix : kH A5 ≡ - Kab b₀ a₀
  k5fix = Eq.trans (kH-cong {A5} {(₁₊ z , ₁₊ a₀) , (λ ())} v5eq)
          (Eq.trans (Kab-comm z a₀) (Kab-neg b₀ a₀ z (Eq.sym eq-z)))

  P Q R : ℤ ₚ
  P = Kab a₀ w
  Q = Kab b₀ w
  R = Kab b₀ a₀

  e-fix : (((((e + - ₀) + - kH A1) + - kS A2) + - kH A3) + - kS A4) + - kH A5
          ≡ e
  e-fix = Eq.trans
    (Eq.cong₂ _+_
      (Eq.cong₂ _+_
        (Eq.cong₂ _+_
          (Eq.cong₂ _+_
            (Eq.cong ((e + - ₀) +_) (Eq.cong -_ k1fix))
            (Eq.cong -_ k2fix))
          (Eq.cong -_ k3fix))
        (Eq.cong -_ k4fix))
      (Eq.cong -_ k5fix))
    (Eq.trans
      (Eq.cong (λ v → ((((v + - P) + - ₀) + - (- Q)) + - ₀) + - (- R))
               (e+-0 e))
    (Eq.trans
      (Eq.cong (λ v → ((v + - (- Q)) + - ₀) + - (- R)) (e+-0 (e + - P)))
    (Eq.trans
      (Eq.cong (_+ - (- R)) (e+-0 ((e + - P) + - (- Q))))
    (Eq.trans
      (Eq.cong₂ _+_ (Eq.cong ((e + - P) +_) (-‿involutive Q)) (-‿involutive R))
    (Eq.trans (Eq.cong (_+ R) (+-assoc e (- P) Q))
    (Eq.trans (+-assoc e (- P + Q) R)
    (Eq.trans
      (Eq.cong (e +_)
        (Eq.trans (+-assoc (- P) Q R)
          (Eq.trans (Eq.cong (- P +_) (pf-inv a₀ w b₀ awb))
                    (+-inverseˡ P))))
      (+-identityʳ e))))))))
