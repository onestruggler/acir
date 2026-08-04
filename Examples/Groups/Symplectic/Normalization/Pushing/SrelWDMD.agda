------------------------------------------------------------------------
-- Presentations of groups
--
-- Threading the M-word through an inj₂ (D-box) coset: closed forms for
-- the residual and coset of (ract ᵗ) (inj₂ (d , lm)) (M x), one zero
-- pattern of d at a time.  On a = 0 boxes M x escapes as M x itself; on
-- a ≠ 0 boxes it escapes as M (x ⁻¹); in both cases the box updates as
-- (a , b) ↦ (x·a , x⁻¹·b).  Supports the M-mul and semi-MS inj₂ cases
-- of srel-wd.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Empty using (⊥-elim)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM p-2 p-prime
  using (nsum-* ; nsum-neg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime

------------------------------------------------------------------------
-- Any S-power is a ZM-unit with quotient 1.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open Lemmas0 j

  Sk≈unit : ∀ (k : ℤ ₚ) → S^ k ≈ ZM (₁ , λ ()) • S^ k
  Sk≈unit k = trans (sym left-unit) (cong lemma-M1 refl)

------------------------------------------------------------------------
-- The M-orbit engine, pattern (₀ , ₀): every letter escapes as itself.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)

  private
    ract' = ract {₁₊ m}
    one' : ℤ* ₚ
    one' = (₁ , λ ())
    m1' : ℤ* ₚ
    m1' = -' (₁ , λ ())

  MD-resid-00 : ∀ (x : ℤ* ₚ) (lm : C (₁₊ m)) →
    ((ract' ᵗ) (inj₂ ((₀ , ₀) , lm)) (ZM x)) .proj₁ ≈ ZM x
  MD-resid-00 x lm = refl'ᵣ (
    Eq.trans (Eq.cong₂ _•_ (ract-S^-resid-a0 ₀ lm (toℕ xv))
      (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixz • H • S^ xz • H)) .proj₁)
        (Eq.trans (ract-S^-coset (₀ , ₀) lm (toℕ xv))
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) ₀)))))
    (Eq.cong (λ t → (S ^ toℕ xv) • (H • t))
      (Eq.trans (Eq.cong₂ _•_ (ract-S^-resid-a0 (- ₀) lm (toℕ ixv))
        (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xz • H)) .proj₁)
          (Eq.trans (ract-S^-coset (₀ , - ₀) lm (toℕ ixv))
            (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ ixv) (- ₀))))))
      (Eq.cong (λ t → (S ^ toℕ ixv) • t)
        (Eq.trans (Eq.cong₂ _•_
            (Eq.cong (λ v → Hdir v ↓ᵏ m) (Eq.cong (₀ ,_) -0#≈0#))
            (Eq.cong (λ c → ((ract' ᵗ) c (S^ xz • H)) .proj₁)
              (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) -0#≈0# -0#≈0#)))
        (Eq.cong (λ t → H • t)
          (Eq.cong₂ _•_ (ract-S^-resid-a0 ₀ lm (toℕ xv))
            (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₁)
              (Eq.trans (ract-S^-coset (₀ , ₀) lm (toℕ xv))
                (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) ₀)))))))))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    xz = xv
    ixz = ixv

  MD-coset-00 : ∀ (x : ℤ* ₚ) (lm : C (₁₊ m)) →
    ((ract' ᵗ) (inj₂ ((₀ , ₀) , lm)) (ZM x)) .proj₂ ≡ inj₂ ((₀ , ₀) , lm)
  MD-coset-00 x lm =
    Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixz • H • S^ xz • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₀ , ₀) lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) ₀))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xz • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₀ , - ₀) lm (toℕ ixv))
        (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ ixv) (- ₀)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (S^ xz • H)) .proj₂)
      (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) -0#≈0# -0#≈0#))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₂)
      (Eq.trans (ract-S^-coset (₀ , ₀) lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) ₀))))
      (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) -0#≈0#))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    xz = xv
    ixz = ixv

------------------------------------------------------------------------
-- Pattern (₀ , ₁₊ b'): M x escapes as an S-power, a ZM unit and HH,
-- merging back to ZM x; the box becomes (₀ , x⁻¹·b).

  MD-resid-0b : ∀ (x : ℤ* ₚ) (b' t' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    - ((x ⁻¹) .proj₁ * ₁₊ b') ≡ ₁₊ t' →
    ((ract' ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) (ZM x)) .proj₁ ≈ ZM x
  MD-resid-0b x b' t' lm eq-t =
    trans (refl'ᵣ (
      Eq.trans (Eq.cong₂ _•_ (ract-S^-resid-a0 (₁₊ b') lm (toℕ xv))
        (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₁)
          (Eq.trans (ract-S^-coset (₀ , ₁₊ b') lm (toℕ xv))
            (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) (₁₊ b'))))))
      (Eq.cong (λ t → (S ^ toℕ xv) • (ε • t))
        (Eq.cong₂ _•_ Eq.refl
          (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₁)
              (Eq.trans (ract-S^-coset (₁₊ b' , - ₀) lm (toℕ ixv))
                (Eq.cong (λ d → inj₂ (d , lm))
                  (Eq.trans (it-dDS-nz (toℕ ixv) (₁₊ b') (- ₀) (λ ()))
                    (Eq.cong (₁₊ b' ,_) vT)))))
            (Eq.cong₂ _•_ (hpad b' t')
              (Eq.cong₂ _•_ Eq.refl
                (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₁)
                  (Eq.trans (ract-S^-coset (₁₊ t' , - ₁₊ b') lm (toℕ xv))
                    (Eq.cong (λ d → inj₂ (d , lm))
                      (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ t') (- ₁₊ b') (λ ()))
                        (Eq.cong (₁₊ t' ,_) vZ))))))))))))
    (trans (cong refl (trans left-unit
      (trans (cong (ract-S^-resid-a+ (₁₊ b' , - ₀) lm (toℕ ixv) (λ ()))
                   (cong refl (cong (ract-S^-resid-a+ (₁₊ t' , - ₁₊ b') lm (toℕ xv) (λ ())) refl)))
      (trans left-unit (cong refl left-unit)))))
    (trans (cong (Sk≈unit (x .proj₁)) (cong refl HH≈unit))
    (trans (cong refl (unit-merge qU m1' rU ₀))
    (trans (unit-merge one' (qU *' m1') (x .proj₁) RU)
           (unit-≈M (one' *' (qU *' m1')) x RRex Qval R0)))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    B* T* : ℤ* ₚ
    B* = (₁₊ b' , λ ())
    T* = (₁₊ t' , λ ())
    iB = (B* ⁻¹) .proj₁
    iT = (T* ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    inst-b = nztoℕ {y = ₁₊ b'} {neq0 = λ ()}

    xt≡ : xv * ₁₊ t' ≡ - ₁₊ b'
    xt≡ = Eq.trans (Eq.cong (xv *_) (Eq.sym eq-t))
          (Eq.trans (Eq.sym (-‿distribʳ-* xv (ixv * ₁₊ b')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc xv ixv (₁₊ b')))
              (Eq.trans (Eq.cong (_* ₁₊ b') (lemma-⁻¹ʳ xv {{inst-x}}))
                        (*-identityˡ (₁₊ b'))))))

    vT : - ₀ + nsum (toℕ ixv) (- ₁₊ b') ≡ ₁₊ t'
    vT = Eq.trans (Eq.cong₂ _+_ -0#≈0# (nsum-neg ixv (₁₊ b')))
         (Eq.trans (+-0ˡ (- (ixv * ₁₊ b'))) eq-t)

    vZ : - ₁₊ b' + nsum (toℕ xv) (- ₁₊ t') ≡ ₀
    vZ = Eq.trans (Eq.cong (- ₁₊ b' +_) (nsum-neg xv (₁₊ t')))
         (Eq.trans (Eq.cong (λ v → - ₁₊ b' + - v) xt≡)
         (Eq.trans (Eq.cong (- ₁₊ b' +_) (-‿involutive (₁₊ b')))
                   (+-inverseˡ (₁₊ b'))))

    qU = B* *' (T* ⁻¹)
    rU = ₁₊ t' * iB
    RU = rU * (((m1' ⁻¹) .proj₁) * ((m1' ⁻¹) .proj₁)) + ₀
    RRex = (x .proj₁) *
             ((((qU *' m1') ⁻¹) .proj₁) * (((qU *' m1') ⁻¹) .proj₁)) + RU

    iT≡ : iT ≡ - (xv * iB)
    iT≡ = Eq.trans (ineg ((x ⁻¹) *' B*) T* (Eq.sym eq-t))
          (Eq.cong -_ (Eq.trans (inv-distrib (x ⁻¹) B*)
                                (Eq.cong (_* iB) (inv-involutive x))))

    bxiB : ₁₊ b' * (xv * iB) ≡ xv
    bxiB = Eq.trans (Eq.sym (*-assoc (₁₊ b') xv iB))
           (Eq.trans (Eq.cong (_* iB) (*-comm (₁₊ b') xv))
           (Eq.trans (*-assoc xv (₁₊ b') iB)
           (Eq.trans (Eq.cong (xv *_) (lemma-⁻¹ʳ (₁₊ b') {{inst-b}}))
                     (*-identityʳ xv))))

    qUv : qU .proj₁ ≡ - xv
    qUv = Eq.trans (Eq.cong (₁₊ b' *_) iT≡)
          (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ b') (xv * iB)))
                    (Eq.cong -_ bxiB))

    qm1v : (qU *' m1') .proj₁ ≡ xv
    qm1v = Eq.trans (Eq.cong (_* (- ₁)) qUv)
           (Eq.trans (negneg-* xv ₁) (*-identityʳ xv))

    Qval : (one' *' (qU *' m1')) .proj₁ ≡ x .proj₁
    Qval = Eq.trans (*-identityˡ ((qU *' m1') .proj₁)) qm1v

    iQ2≡ : ((qU *' m1') ⁻¹) .proj₁ ≡ ixv
    iQ2≡ = inv-cong (qU *' m1') x qm1v

    i-neg≡ : ((m1' ⁻¹) .proj₁) ≡ - ₁
    i-neg≡ = Eq.trans (inv-neg-comm (₁ , λ ())) (Eq.cong -_ inv-₁)

    rU≡ : rU ≡ - ixv
    rU≡ = Eq.trans (Eq.cong (_* iB) (Eq.sym eq-t))
          (Eq.trans (Eq.sym (-‿distribˡ-* (ixv * ₁₊ b') iB))
            (Eq.cong -_
              (Eq.trans (*-assoc ixv (₁₊ b') iB)
              (Eq.trans (Eq.cong (ixv *_) (lemma-⁻¹ʳ (₁₊ b') {{inst-b}}))
                        (*-identityʳ ixv)))))

    RU≡ : RU ≡ - ixv
    RU≡ = Eq.trans (+-identityʳ (rU * (((m1' ⁻¹) .proj₁) * ((m1' ⁻¹) .proj₁))))
          (Eq.trans (Eq.cong (rU *_)
              (Eq.trans (Eq.cong₂ _*_ i-neg≡ i-neg≡)
                (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))))
          (Eq.trans (*-identityʳ rU) rU≡))

    R0 : RRex ≡ ₀
    R0 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong (xv *_) (Eq.cong₂ _*_ iQ2≡ iQ2≡))
          (Eq.trans (Eq.sym (*-assoc xv ixv ixv))
          (Eq.trans (Eq.cong (_* ixv) (lemma-⁻¹ʳ xv {{inst-x}}))
                    (*-identityˡ ixv))))
        RU≡)
      (+-inverseʳ ixv)

  MD-coset-0b : ∀ (x : ℤ* ₚ) (b' t' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    - ((x ⁻¹) .proj₁ * ₁₊ b') ≡ ₁₊ t' →
    ((ract' ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) (ZM x)) .proj₂ ≡
    inj₂ ((₀ , (x ⁻¹) .proj₁ * ₁₊ b') , lm)
  MD-coset-0b x b' t' lm eq-t =
    Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₀ , ₁₊ b') lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) (₁₊ b')))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ b' , - ₀) lm (toℕ ixv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ ixv) (₁₊ b') (- ₀) (λ ()))
            (Eq.cong (₁₊ b' ,_) vT)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ t' , - ₁₊ b') lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ t') (- ₁₊ b') (λ ()))
            (Eq.cong (₁₊ t' ,_) vZ)))))
      (Eq.cong (λ v → inj₂ ((₀ , v) , lm))
        (Eq.trans (Eq.cong -_ (Eq.sym eq-t))
                  (-‿involutive ((x ⁻¹) .proj₁ * ₁₊ b'))))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}

    xt≡ : xv * ₁₊ t' ≡ - ₁₊ b'
    xt≡ = Eq.trans (Eq.cong (xv *_) (Eq.sym eq-t))
          (Eq.trans (Eq.sym (-‿distribʳ-* xv (ixv * ₁₊ b')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc xv ixv (₁₊ b')))
              (Eq.trans (Eq.cong (_* ₁₊ b') (lemma-⁻¹ʳ xv {{inst-x}}))
                        (*-identityˡ (₁₊ b'))))))

    vT : - ₀ + nsum (toℕ ixv) (- ₁₊ b') ≡ ₁₊ t'
    vT = Eq.trans (Eq.cong₂ _+_ -0#≈0# (nsum-neg ixv (₁₊ b')))
         (Eq.trans (+-0ˡ (- (ixv * ₁₊ b'))) eq-t)

    vZ : - ₁₊ b' + nsum (toℕ xv) (- ₁₊ t') ≡ ₀
    vZ = Eq.trans (Eq.cong (- ₁₊ b' +_) (nsum-neg xv (₁₊ t')))
         (Eq.trans (Eq.cong (λ v → - ₁₊ b' + - v) xt≡)
         (Eq.trans (Eq.cong (- ₁₊ b' +_) (-‿involutive (₁₊ b')))
                   (+-inverseˡ (₁₊ b'))))

------------------------------------------------------------------------
-- Pattern (₁₊ a' , ₀): M x escapes as a ZM unit, HH and an S-power,
-- merging to ZM (x ⁻¹); the box becomes (x·a , ₀).

  MD-resid-a0 : ∀ (x : ℤ* ₚ) (a' s' u' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    - (x .proj₁ * ₁₊ a') ≡ ₁₊ s' → - ₁₊ s' ≡ ₁₊ u' →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) (ZM x)) .proj₁ ≈ ZM (x ⁻¹)
  MD-resid-a0 x a' s' u' lm eq-s eq-u =
    trans (refl'ᵣ (
      Eq.cong₂ _•_ Eq.refl
        (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₁)
            (Eq.trans (ract-S^-coset (₁₊ a' , ₀) lm (toℕ xv))
              (Eq.cong (λ d → inj₂ (d , lm))
                (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ a') ₀ (λ ()))
                  (Eq.cong (₁₊ a' ,_) vS)))))
          (Eq.cong₂ _•_ (hpad a' s')
            (Eq.cong₂ _•_ Eq.refl
              (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₁)
                  (Eq.trans (ract-S^-coset (₁₊ s' , - ₁₊ a') lm (toℕ ixv))
                    (Eq.cong (λ d → inj₂ (d , lm))
                      (Eq.trans (it-dDS-nz (toℕ ixv) (₁₊ s') (- ₁₊ a') (λ ()))
                        (Eq.cong (₁₊ s' ,_) vC)))))
                (Eq.cong (λ t → HH • t)
                  (Eq.cong₂ _•_ (ract-S^-resid-a0 (- ₁₊ s') lm (toℕ xv))
                    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₁)
                        (Eq.trans (ract-S^-coset (₀ , - ₁₊ s') lm (toℕ xv))
                          (Eq.cong (λ d → inj₂ (d , lm))
                            (it-dDS-a0 (toℕ xv) (- ₁₊ s')))))
                      (Eq.cong (λ v → Hdir v ↓ᵏ m)
                        (Eq.cong (₀ ,_) eq-u)))))))))))
    (trans (cong (ract-S^-resid-a+ (₁₊ a' , ₀) lm (toℕ xv) (λ ()))
                 (cong refl (cong (ract-S^-resid-a+ (₁₊ s' , - ₁₊ a') lm (toℕ ixv) (λ ()))
                                  (cong refl right-unit))))
    (trans left-unit
    (trans (cong refl left-unit)
    (trans (cong refl (cong HH≈unit (Sk≈unit (x .proj₁))))
    (trans (cong refl (unit-merge m1' one' ₀ (x .proj₁)))
    (trans (unit-merge qU (m1' *' one') rU R23)
           (unit-≈M (qU *' (m1' *' one')) (x ⁻¹) RRex Qval R0)))))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    A* S* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    S* = (₁₊ s' , λ ())
    iA = (A* ⁻¹) .proj₁
    iS = (S* ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    vS : ₀ + nsum (toℕ xv) (- ₁₊ a') ≡ ₁₊ s'
    vS = Eq.trans (Eq.cong (₀ +_) (nsum-neg xv (₁₊ a')))
         (Eq.trans (+-0ˡ (- (xv * ₁₊ a'))) eq-s)

    ixs≡ : ixv * ₁₊ s' ≡ - ₁₊ a'
    ixs≡ = Eq.trans (Eq.cong (ixv *_) (Eq.sym eq-s))
           (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ a')))
             (Eq.cong -_
               (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a')))
               (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ˡ xv {{inst-x}}))
                         (*-identityˡ (₁₊ a'))))))

    vC : - ₁₊ a' + nsum (toℕ ixv) (- ₁₊ s') ≡ ₀
    vC = Eq.trans (Eq.cong (- ₁₊ a' +_) (nsum-neg ixv (₁₊ s')))
         (Eq.trans (Eq.cong (λ v → - ₁₊ a' + - v) ixs≡)
         (Eq.trans (Eq.cong (- ₁₊ a' +_) (-‿involutive (₁₊ a')))
                   (+-inverseˡ (₁₊ a'))))

    qU = A* *' (S* ⁻¹)
    rU = ₁₊ s' * iA
    R23 = ₀ * (((one' ⁻¹) .proj₁) * ((one' ⁻¹) .proj₁)) + x .proj₁
    RRex = rU *
             ((((m1' *' one') ⁻¹) .proj₁) * (((m1' *' one') ⁻¹) .proj₁)) + R23

    iS≡ : iS ≡ - (ixv * iA)
    iS≡ = Eq.trans (ineg (x *' A*) S* (Eq.sym eq-s))
          (Eq.cong -_ (inv-distrib x A*))

    axiA : ₁₊ a' * (ixv * iA) ≡ ixv
    axiA = Eq.trans (Eq.sym (*-assoc (₁₊ a') ixv iA))
           (Eq.trans (Eq.cong (_* iA) (*-comm (₁₊ a') ixv))
           (Eq.trans (*-assoc ixv (₁₊ a') iA)
           (Eq.trans (Eq.cong (ixv *_) (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))
                     (*-identityʳ ixv))))

    qUv : qU .proj₁ ≡ - ixv
    qUv = Eq.trans (Eq.cong (₁₊ a' *_) iS≡)
          (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ a') (ixv * iA)))
                    (Eq.cong -_ axiA))

    mv : (m1' *' one') .proj₁ ≡ - ₁
    mv = *-identityʳ (- ₁)

    Qval : (qU *' (m1' *' one')) .proj₁ ≡ (x ⁻¹) .proj₁
    Qval = Eq.trans (Eq.cong₂ _*_ qUv mv)
           (Eq.trans (negneg-* ixv ₁) (*-identityʳ ixv))

    i-neg≡ : ((m1' ⁻¹) .proj₁) ≡ - ₁
    i-neg≡ = Eq.trans (inv-neg-comm (₁ , λ ())) (Eq.cong -_ inv-₁)

    iq2≡ : ((m1' *' one') ⁻¹) .proj₁ ≡ - ₁
    iq2≡ = Eq.trans (inv-cong (m1' *' one') m1' mv) i-neg≡

    rU≡ : rU ≡ - xv
    rU≡ = Eq.trans (Eq.cong (_* iA) (Eq.sym eq-s))
          (Eq.trans (Eq.sym (-‿distribˡ-* (xv * ₁₊ a') iA))
            (Eq.cong -_
              (Eq.trans (*-assoc xv (₁₊ a') iA)
              (Eq.trans (Eq.cong (xv *_) (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))
                        (*-identityʳ xv)))))

    R0 : RRex ≡ ₀
    R0 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong (rU *_)
            (Eq.trans (Eq.cong₂ _*_ iq2≡ iq2≡)
              (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))))
          (Eq.trans (*-identityʳ rU) rU≡))
        (+-0ˡ (x .proj₁)))
      (+-inverseˡ xv)

  MD-coset-a0 : ∀ (x : ℤ* ₚ) (a' s' u' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    - (x .proj₁ * ₁₊ a') ≡ ₁₊ s' → - ₁₊ s' ≡ ₁₊ u' →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) (ZM x)) .proj₂ ≡
    inj₂ ((x .proj₁ * ₁₊ a' , ₀) , lm)
  MD-coset-a0 x a' s' u' lm eq-s eq-u =
    Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ a' , ₀) lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ a') ₀ (λ ()))
            (Eq.cong (₁₊ a' ,_) vS)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ s' , - ₁₊ a') lm (toℕ ixv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ ixv) (₁₊ s') (- ₁₊ a') (λ ()))
            (Eq.cong (₁₊ s' ,_) vC)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₂)
      (Eq.trans (ract-S^-coset (₀ , - ₁₊ s') lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 (toℕ xv) (- ₁₊ s')))))
      (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm))
        (Eq.trans (Eq.cong -_ (Eq.sym eq-s))
                  (-‿involutive (x .proj₁ * ₁₊ a')))
        -0#≈0#)))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}

    vS : ₀ + nsum (toℕ xv) (- ₁₊ a') ≡ ₁₊ s'
    vS = Eq.trans (Eq.cong (₀ +_) (nsum-neg xv (₁₊ a')))
         (Eq.trans (+-0ˡ (- (xv * ₁₊ a'))) eq-s)

    ixs≡ : ixv * ₁₊ s' ≡ - ₁₊ a'
    ixs≡ = Eq.trans (Eq.cong (ixv *_) (Eq.sym eq-s))
           (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ a')))
             (Eq.cong -_
               (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a')))
               (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ˡ xv {{inst-x}}))
                         (*-identityˡ (₁₊ a'))))))

    vC : - ₁₊ a' + nsum (toℕ ixv) (- ₁₊ s') ≡ ₀
    vC = Eq.trans (Eq.cong (- ₁₊ a' +_) (nsum-neg ixv (₁₊ s')))
         (Eq.trans (Eq.cong (λ v → - ₁₊ a' + - v) ixs≡)
         (Eq.trans (Eq.cong (- ₁₊ a' +_) (-‿involutive (₁₊ a')))
                   (+-inverseˡ (₁₊ a'))))

------------------------------------------------------------------------
-- Pattern (₁₊ a' , ₁₊ b') with b = x·a (the S-pass kills the b slot):
-- escapes HH, an S-power and a ZM unit, merging to ZM (x ⁻¹).

  MD-resid-nn0 : ∀ (x : ℤ* ₚ) (a' b' y : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    - ₁₊ a' ≡ ₁₊ y → ₁₊ b' + - (x .proj₁ * ₁₊ a') ≡ ₀ →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (ZM x)) .proj₁ ≈ ZM (x ⁻¹)
  MD-resid-nn0 x a' b' y lm eq-y Weq =
    trans (refl'ᵣ (
      Eq.cong₂ _•_ Eq.refl
        (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₁)
            (Eq.trans (ract-S^-coset (₁₊ a' , ₁₊ b') lm (toℕ xv))
              (Eq.cong (λ d → inj₂ (d , lm))
                (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ a') (₁₊ b') (λ ()))
                  (Eq.cong (₁₊ a' ,_) vW)))))
          (Eq.cong (λ t → HH • t)
            (Eq.cong₂ _•_ (ract-S^-resid-a0 (- ₁₊ a') lm (toℕ ixv))
              (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₁)
                  (Eq.trans (ract-S^-coset (₀ , - ₁₊ a') lm (toℕ ixv))
                    (Eq.cong (λ d → inj₂ (d , lm))
                      (Eq.trans (it-dDS-a0 (toℕ ixv) (- ₁₊ a'))
                        (Eq.cong (₀ ,_) eq-y)))))
                (Eq.cong (λ t → ε • t)
                  (Eq.cong₂ _•_ Eq.refl
                    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₁)
                        (Eq.trans (ract-S^-coset (₁₊ y , - ₀) lm (toℕ xv))
                          (Eq.cong (λ d → inj₂ (d , lm))
                            (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ y) (- ₀) (λ ()))
                              (Eq.cong (₁₊ y ,_) vB)))))
                      (hpad y b'))))))))))
    (trans (cong refl (cong refl (cong refl (cong refl
      (cong (ract-S^-resid-a+ (₁₊ y , - ₀) lm (toℕ xv) (λ ())) refl)))))
    (trans (cong (ract-S^-resid-a+ (₁₊ a' , ₁₊ b') lm (toℕ xv) (λ ())) refl)
    (trans left-unit
    (trans (cong refl (cong refl (trans left-unit left-unit)))
    (trans (cong HH≈unit (cong (Sk≈unit ((x ⁻¹) .proj₁)) refl))
    (trans (cong refl (unit-merge one' qU ((x ⁻¹) .proj₁) rU))
    (trans (unit-merge m1' (one' *' qU) ₀ R23)
           (unit-≈M (m1' *' (one' *' qU)) (x ⁻¹) RRex Qval R0))))))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    A* B* Y* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    B* = (₁₊ b' , λ ())
    Y* = (₁₊ y , λ ())
    iA = (A* ⁻¹) .proj₁
    iB = (B* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    beq : ₁₊ b' ≡ xv * ₁₊ a'
    beq = +-‿cancel (₁₊ b') (xv * ₁₊ a') Weq

    vW : ₁₊ b' + nsum (toℕ xv) (- ₁₊ a') ≡ ₀
    vW = Eq.trans (Eq.cong (₁₊ b' +_) (nsum-neg xv (₁₊ a'))) Weq

    xy≡ : xv * ₁₊ y ≡ - ₁₊ b'
    xy≡ = Eq.trans (Eq.cong (xv *_) (Eq.sym eq-y))
          (Eq.trans (Eq.sym (-‿distribʳ-* xv (₁₊ a')))
            (Eq.cong -_ (Eq.sym beq)))

    vB : - ₀ + nsum (toℕ xv) (- ₁₊ y) ≡ ₁₊ b'
    vB = Eq.trans (Eq.cong₂ _+_ -0#≈0# (nsum-neg xv (₁₊ y)))
         (Eq.trans (+-0ˡ (- (xv * ₁₊ y)))
         (Eq.trans (Eq.cong -_ xy≡) (-‿involutive (₁₊ b'))))

    qU = Y* *' (B* ⁻¹)
    rU = ₁₊ b' * iY
    R23 = ((x ⁻¹) .proj₁) * (((qU ⁻¹) .proj₁) * ((qU ⁻¹) .proj₁)) + rU
    RRex = ₀ * ((((one' *' qU) ⁻¹) .proj₁) * (((one' *' qU) ⁻¹) .proj₁)) + R23

    iB≡ : iB ≡ ixv * iA
    iB≡ = Eq.trans (inv-cong B* (x *' A*) beq) (inv-distrib x A*)

    aixiA : ₁₊ a' * (ixv * iA) ≡ ixv
    aixiA = Eq.trans (Eq.sym (*-assoc (₁₊ a') ixv iA))
            (Eq.trans (Eq.cong (_* iA) (*-comm (₁₊ a') ixv))
            (Eq.trans (*-assoc ixv (₁₊ a') iA)
            (Eq.trans (Eq.cong (ixv *_) (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))
                      (*-identityʳ ixv))))

    qUv : qU .proj₁ ≡ - ixv
    qUv = Eq.trans (Eq.cong (_* iB) (Eq.sym eq-y))
          (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a') iB))
            (Eq.cong -_
              (Eq.trans (Eq.cong (₁₊ a' *_) iB≡) aixiA)))

    m1qv : (one' *' qU) .proj₁ ≡ - ixv
    m1qv = Eq.trans (*-identityˡ (qU .proj₁)) qUv

    Qval : (m1' *' (one' *' qU)) .proj₁ ≡ (x ⁻¹) .proj₁
    Qval = Eq.trans (Eq.cong ((- ₁) *_) m1qv)
           (Eq.trans (negneg-* ₁ ixv) (*-identityˡ ixv))

    iqU≡ : ((qU) ⁻¹) .proj₁ ≡ - xv
    iqU≡ = Eq.trans (inv-cong qU (-' (x ⁻¹)) qUv)
           (Eq.trans (inv-neg-comm (x ⁻¹)) (Eq.cong -_ (inv-involutive x)))

    rU≡ : rU ≡ - xv
    rU≡ = Eq.trans (Eq.cong (₁₊ b' *_) (ineg A* Y* (Eq.sym eq-y)))
          (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ b') iA))
            (Eq.cong -_
              (Eq.trans (Eq.cong (_* iA) beq)
              (Eq.trans (*-assoc xv (₁₊ a') iA)
              (Eq.trans (Eq.cong (xv *_) (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))
                        (*-identityʳ xv))))))

    R23≡ : R23 ≡ ₀
    R23≡ = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong (ixv *_)
            (Eq.trans (Eq.cong₂ _*_ iqU≡ iqU≡) (negneg-* xv xv)))
          (Eq.trans (Eq.sym (*-assoc ixv xv xv))
          (Eq.trans (Eq.cong (_* xv) (lemma-⁻¹ˡ xv {{inst-x}}))
                    (*-identityˡ xv))))
        rU≡)
      (+-inverseʳ xv)

    R0 : RRex ≡ ₀
    R0 = Eq.trans (+-0ˡ R23) R23≡

  MD-coset-nn0 : ∀ (x : ℤ* ₚ) (a' b' y : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    - ₁₊ a' ≡ ₁₊ y → ₁₊ b' + - (x .proj₁ * ₁₊ a') ≡ ₀ →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (ZM x)) .proj₂ ≡
    inj₂ ((x .proj₁ * ₁₊ a' , (x ⁻¹) .proj₁ * ₁₊ b') , lm)
  MD-coset-nn0 x a' b' y lm eq-y Weq =
    Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ a' , ₁₊ b') lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ a') (₁₊ b') (λ ()))
            (Eq.cong (₁₊ a' ,_) vW)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₀ , - ₁₊ a') lm (toℕ ixv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-a0 (toℕ ixv) (- ₁₊ a'))
            (Eq.cong (₀ ,_) eq-y)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ y , - ₀) lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ y) (- ₀) (λ ()))
            (Eq.cong (₁₊ y ,_) vB)))))
      (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) beq
        (Eq.trans
          (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a')))
          (Eq.sym ixb≡a)))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}

    beq : ₁₊ b' ≡ xv * ₁₊ a'
    beq = +-‿cancel (₁₊ b') (xv * ₁₊ a') Weq

    vW : ₁₊ b' + nsum (toℕ xv) (- ₁₊ a') ≡ ₀
    vW = Eq.trans (Eq.cong (₁₊ b' +_) (nsum-neg xv (₁₊ a'))) Weq

    xy≡ : xv * ₁₊ y ≡ - ₁₊ b'
    xy≡ = Eq.trans (Eq.cong (xv *_) (Eq.sym eq-y))
          (Eq.trans (Eq.sym (-‿distribʳ-* xv (₁₊ a')))
            (Eq.cong -_ (Eq.sym beq)))

    vB : - ₀ + nsum (toℕ xv) (- ₁₊ y) ≡ ₁₊ b'
    vB = Eq.trans (Eq.cong₂ _+_ -0#≈0# (nsum-neg xv (₁₊ y)))
         (Eq.trans (+-0ˡ (- (xv * ₁₊ y)))
         (Eq.trans (Eq.cong -_ xy≡) (-‿involutive (₁₊ b'))))

    ixb≡a : ixv * ₁₊ b' ≡ ₁₊ a'
    ixb≡a = Eq.trans (Eq.cong (ixv *_) beq)
            (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a')))
            (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ˡ xv {{inst-x}}))
                      (*-identityˡ (₁₊ a'))))

------------------------------------------------------------------------
-- Pattern (₁₊ a' , ₁₊ b') with b ≠ x·a: three ZM units telescoping to
-- ZM (x ⁻¹); the box becomes (x·a , x⁻¹·b).

  MD-resid-nnw : ∀ (x : ℤ* ₚ) (a' b' w' t' v' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    ₁₊ b' + - (x .proj₁ * ₁₊ a') ≡ ₁₊ w' →
    - ((x ⁻¹) .proj₁ * ₁₊ b') ≡ ₁₊ t' →
    x .proj₁ * ₁₊ a' ≡ ₁₊ v' →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (ZM x)) .proj₁ ≈ ZM (x ⁻¹)
  MD-resid-nnw x a' b' w' t' v' lm Weq eq-t eq-v =
    trans (refl'ᵣ (
      Eq.cong₂ _•_ Eq.refl
        (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₁)
            (Eq.trans (ract-S^-coset (₁₊ a' , ₁₊ b') lm (toℕ xv))
              (Eq.cong (λ d → inj₂ (d , lm))
                (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ a') (₁₊ b') (λ ()))
                  (Eq.cong (₁₊ a' ,_) vW)))))
          (Eq.cong₂ _•_ (hpad a' w')
            (Eq.cong₂ _•_ Eq.refl
              (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₁)
                  (Eq.trans (ract-S^-coset (₁₊ w' , - ₁₊ a') lm (toℕ ixv))
                    (Eq.cong (λ d → inj₂ (d , lm))
                      (Eq.trans (it-dDS-nz (toℕ ixv) (₁₊ w') (- ₁₊ a') (λ ()))
                        (Eq.cong (₁₊ w' ,_) vT)))))
                (Eq.cong₂ _•_ (hpad w' t')
                  (Eq.cong₂ _•_ Eq.refl
                    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₁)
                        (Eq.trans (ract-S^-coset (₁₊ t' , - ₁₊ w') lm (toℕ xv))
                          (Eq.cong (λ d → inj₂ (d , lm))
                            (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ t') (- ₁₊ w') (λ ()))
                              (Eq.cong (₁₊ t' ,_) vV)))))
                      (hpad t' v'))))))))))
    (trans (cong (ract-S^-resid-a+ (₁₊ a' , ₁₊ b') lm (toℕ xv) (λ ()))
                 (cong refl (cong (ract-S^-resid-a+ (₁₊ w' , - ₁₊ a') lm (toℕ ixv) (λ ()))
                   (cong refl (cong (ract-S^-resid-a+ (₁₊ t' , - ₁₊ w') lm (toℕ xv) (λ ())) refl)))))
    (trans left-unit
    (trans (cong refl (trans left-unit (cong refl left-unit)))
    (trans (cong refl (unit-merge q₂ q₃ r₂ r₃))
    (trans (unit-merge q₁ (q₂ *' q₃) r₁ R₂₃)
           (unit-≈M (q₁ *' (q₂ *' q₃)) (x ⁻¹) RRex Qval R0))))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    A* B* W* T* V* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    B* = (₁₊ b' , λ ())
    W* = (₁₊ w' , λ ())
    T* = (₁₊ t' , λ ())
    V* = (₁₊ v' , λ ())
    iA = (A* ⁻¹) .proj₁
    iB = (B* ⁻¹) .proj₁
    iW = (W* ⁻¹) .proj₁
    iT = (T* ⁻¹) .proj₁
    iV = (V* ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}
    inst-b = nztoℕ {y = ₁₊ b'} {neq0 = λ ()}
    inst-w = nztoℕ {y = ₁₊ w'} {neq0 = λ ()}
    inst-t = nztoℕ {y = ₁₊ t'} {neq0 = λ ()}

    vW : ₁₊ b' + nsum (toℕ xv) (- ₁₊ a') ≡ ₁₊ w'
    vW = Eq.trans (Eq.cong (₁₊ b' +_) (nsum-neg xv (₁₊ a'))) Weq

    ixw≡ : ixv * ₁₊ w' ≡ ixv * ₁₊ b' + - ₁₊ a'
    ixw≡ = Eq.trans (Eq.cong (ixv *_) (Eq.sym Weq))
      (Eq.trans (*-distribˡ-+ ixv (₁₊ b') (- (xv * ₁₊ a')))
        (Eq.cong ((ixv * ₁₊ b') +_)
          (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ a')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a')))
              (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ (₁₊ a'))))))))

    vT : - ₁₊ a' + nsum (toℕ ixv) (- ₁₊ w') ≡ ₁₊ t'
    vT = Eq.trans (Eq.cong (- ₁₊ a' +_) (nsum-neg ixv (₁₊ w')))
      (Eq.trans (Eq.cong (λ v → - ₁₊ a' + - v) ixw≡)
      (Eq.trans (Eq.cong (- ₁₊ a' +_)
          (Eq.trans (Eq.sym (-‿+-comm (ixv * ₁₊ b') (- ₁₊ a')))
            (Eq.cong (- (ixv * ₁₊ b') +_) (-‿involutive (₁₊ a')))))
      (Eq.trans (Eq.cong (- ₁₊ a' +_) (+-comm (- (ixv * ₁₊ b')) (₁₊ a')))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ a') (₁₊ a') (- (ixv * ₁₊ b'))))
      (Eq.trans (Eq.cong (_+ - (ixv * ₁₊ b')) (+-inverseˡ (₁₊ a')))
      (Eq.trans (+-0ˡ (- (ixv * ₁₊ b'))) eq-t))))))

    xt≡ : xv * ₁₊ t' ≡ - ₁₊ b'
    xt≡ = Eq.trans (Eq.cong (xv *_) (Eq.sym eq-t))
          (Eq.trans (Eq.sym (-‿distribʳ-* xv (ixv * ₁₊ b')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc xv ixv (₁₊ b')))
              (Eq.trans (Eq.cong (_* ₁₊ b') (lemma-⁻¹ʳ xv {{inst-x}}))
                        (*-identityˡ (₁₊ b'))))))

    negw≡ : - ₁₊ w' ≡ - ₁₊ b' + ₁₊ v'
    negw≡ = Eq.trans (Eq.cong -_ (Eq.sym Weq))
      (Eq.trans (Eq.sym (-‿+-comm (₁₊ b') (- (xv * ₁₊ a'))))
      (Eq.cong (- ₁₊ b' +_)
        (Eq.trans (-‿involutive (xv * ₁₊ a')) eq-v)))

    vV : - ₁₊ w' + nsum (toℕ xv) (- ₁₊ t') ≡ ₁₊ v'
    vV = Eq.trans (Eq.cong₂ _+_ negw≡ (nsum-neg xv (₁₊ t')))
      (Eq.trans (Eq.cong (λ v → (- ₁₊ b' + ₁₊ v') + - v) xt≡)
      (Eq.trans (Eq.cong ((- ₁₊ b' + ₁₊ v') +_) (-‿involutive (₁₊ b')))
      (Eq.trans (Eq.cong (_+ ₁₊ b') (+-comm (- ₁₊ b') (₁₊ v')))
      (Eq.trans (+-assoc (₁₊ v') (- ₁₊ b') (₁₊ b'))
      (Eq.trans (Eq.cong (₁₊ v' +_) (+-inverseˡ (₁₊ b')))
                (+-identityʳ (₁₊ v')))))))

    q₁ = A* *' (W* ⁻¹)
    q₂ = W* *' (T* ⁻¹)
    q₃ = T* *' (V* ⁻¹)
    r₁ = ₁₊ w' * iA
    r₂ = ₁₊ t' * iW
    r₃ = ₁₊ v' * iT
    R₂₃ = r₂ * (((q₃ ⁻¹) .proj₁) * ((q₃ ⁻¹) .proj₁)) + r₃
    RRex = r₁ * ((((q₂ *' q₃) ⁻¹) .proj₁) * (((q₂ *' q₃) ⁻¹) .proj₁)) + R₂₃

    iV≡ : iV ≡ ixv * iA
    iV≡ = Eq.trans (inv-cong V* (x *' A*) (Eq.sym eq-v)) (inv-distrib x A*)

    Qval : (q₁ *' (q₂ *' q₃)) .proj₁ ≡ (x ⁻¹) .proj₁
    Qval = Eq.trans (Eq.cong (q₁ .proj₁ *_) (quotient-mul W* T* V*))
      (Eq.trans (quotient-mul A* W* V*)
      (Eq.trans (Eq.cong (₁₊ a' *_) iV≡)
      (Eq.trans (Eq.sym (*-assoc (₁₊ a') ixv iA))
      (Eq.trans (Eq.cong (_* iA) (*-comm (₁₊ a') ixv))
      (Eq.trans (*-assoc ixv (₁₊ a') iA)
      (Eq.trans (Eq.cong (ixv *_) (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))
                (*-identityʳ ixv)))))))

    iQ₂₃≡ : ((q₂ *' q₃) ⁻¹) .proj₁ ≡ iW * ₁₊ v'
    iQ₂₃≡ = Eq.trans (inv-cong (q₂ *' q₃) (W* *' (V* ⁻¹)) (quotient-mul W* T* V*))
                     (iexp W* V*)

    iq₃≡ : (q₃ ⁻¹) .proj₁ ≡ iT * ₁₊ v'
    iq₃≡ = iexp T* V*

    iAV≡xv : iA * ₁₊ v' ≡ xv
    iAV≡xv = Eq.trans (Eq.cong (iA *_) (Eq.sym eq-v))
      (Eq.trans (Eq.sym (*-assoc iA xv (₁₊ a')))
      (Eq.trans (Eq.cong (_* ₁₊ a') (*-comm iA xv))
      (Eq.trans (*-assoc xv iA (₁₊ a'))
      (Eq.trans (Eq.cong (xv *_) (lemma-⁻¹ˡ (₁₊ a') {{inst-a}}))
                (*-identityʳ xv)))))

    outer≡ : r₁ * ((iW * ₁₊ v') * (iW * ₁₊ v')) ≡ xv * (iW * ₁₊ v')
    outer≡ = Eq.trans (Eq.cong (_* ((iW * ₁₊ v') * (iW * ₁₊ v'))) (*-comm (₁₊ w') iA))
      (Eq.trans (*-assoc iA (₁₊ w') ((iW * ₁₊ v') * (iW * ₁₊ v')))
      (Eq.trans (Eq.cong (iA *_) (Eq.sym (*-assoc (₁₊ w') (iW * ₁₊ v') (iW * ₁₊ v'))))
      (Eq.trans (Eq.cong (λ t → iA * (t * (iW * ₁₊ v')))
          (Eq.trans (Eq.sym (*-assoc (₁₊ w') iW (₁₊ v')))
          (Eq.trans (Eq.cong (_* ₁₊ v') (lemma-⁻¹ʳ (₁₊ w') {{inst-w}}))
                    (*-identityˡ (₁₊ v')))))
      (Eq.trans (Eq.sym (*-assoc iA (₁₊ v') (iW * ₁₊ v')))
                (Eq.cong (_* (iW * ₁₊ v')) iAV≡xv)))))

    step1 : r₂ * ((iT * ₁₊ v') * (iT * ₁₊ v')) ≡ (iW * ₁₊ v') * (iT * ₁₊ v')
    step1 = Eq.trans (Eq.cong (_* ((iT * ₁₊ v') * (iT * ₁₊ v'))) (*-comm (₁₊ t') iW))
      (Eq.trans (*-assoc iW (₁₊ t') ((iT * ₁₊ v') * (iT * ₁₊ v')))
      (Eq.trans (Eq.cong (iW *_) (Eq.sym (*-assoc (₁₊ t') (iT * ₁₊ v') (iT * ₁₊ v'))))
      (Eq.trans (Eq.cong (λ t → iW * (t * (iT * ₁₊ v')))
          (Eq.trans (Eq.sym (*-assoc (₁₊ t') iT (₁₊ v')))
          (Eq.trans (Eq.cong (_* ₁₊ v') (lemma-⁻¹ʳ (₁₊ t') {{inst-t}}))
                    (*-identityˡ (₁₊ v')))))
      (Eq.sym (*-assoc iW (₁₊ v') (iT * ₁₊ v'))))))

    VW-b : ₁₊ v' + ₁₊ w' ≡ ₁₊ b'
    VW-b = Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-v) (Eq.sym Weq))
      (Eq.trans (Eq.cong ((xv * ₁₊ a') +_) (+-comm (₁₊ b') (- (xv * ₁₊ a'))))
      (Eq.trans (Eq.sym (+-assoc (xv * ₁₊ a') (- (xv * ₁₊ a')) (₁₊ b')))
      (Eq.trans (Eq.cong (_+ ₁₊ b') (+-inverseʳ (xv * ₁₊ a')))
                (+-0ˡ (₁₊ b')))))

    iT≡ : iT ≡ - (xv * iB)
    iT≡ = Eq.trans (ineg ((x ⁻¹) *' B*) T* (Eq.sym eq-t))
          (Eq.cong -_ (Eq.trans (inv-distrib (x ⁻¹) B*)
                                (Eq.cong (_* iB) (inv-involutive x))))

    ibvw : (iB * ₁₊ v') * (iW * ₁₊ b') ≡ ₁₊ v' * iW
    ibvw = Eq.trans (Eq.cong (_* (iW * ₁₊ b')) (*-comm iB (₁₊ v')))
      (Eq.trans (*-assoc (₁₊ v') iB (iW * ₁₊ b'))
        (Eq.cong (₁₊ v' *_)
          (Eq.trans (Eq.sym (*-assoc iB iW (₁₊ b')))
          (Eq.trans (Eq.cong (_* ₁₊ b') (*-comm iB iW))
          (Eq.trans (*-assoc iW iB (₁₊ b'))
          (Eq.trans (Eq.cong (iW *_) (lemma-⁻¹ˡ (₁₊ b') {{inst-b}}))
                    (*-identityʳ iW)))))))

    inner≡ : (iW * ₁₊ v') * (iT * ₁₊ v') + r₃ ≡ - (xv * (iW * ₁₊ v'))
    inner≡ = Eq.trans
      (Eq.cong₂ _+_ (*-comm (iW * ₁₊ v') (iT * ₁₊ v'))
        (Eq.trans (*-comm (₁₊ v') iT)
                  (Eq.sym (*-identityʳ (iT * ₁₊ v')))))
      (Eq.trans (Eq.sym (*-distribˡ-+ (iT * ₁₊ v') (iW * ₁₊ v') ₁))
      (Eq.trans (Eq.cong ((iT * ₁₊ v') *_)
          (Eq.trans (Eq.cong ((iW * ₁₊ v') +_)
              (Eq.sym (lemma-⁻¹ˡ (₁₊ w') {{inst-w}})))
          (Eq.trans (Eq.sym (*-distribˡ-+ iW (₁₊ v') (₁₊ w')))
                    (Eq.cong (iW *_) VW-b))))
      (Eq.trans (Eq.cong (_* (iW * ₁₊ b'))
          (Eq.trans (Eq.cong (_* ₁₊ v') iT≡)
                    (Eq.sym (-‿distribˡ-* (xv * iB) (₁₊ v')))))
      (Eq.trans (Eq.sym (-‿distribˡ-* ((xv * iB) * ₁₊ v') (iW * ₁₊ b')))
        (Eq.cong -_
          (Eq.trans (Eq.cong (_* (iW * ₁₊ b')) (*-assoc xv iB (₁₊ v')))
          (Eq.trans (*-assoc xv (iB * ₁₊ v') (iW * ₁₊ b'))
            (Eq.trans (Eq.cong (xv *_) ibvw)
                      (Eq.cong (xv *_) (*-comm (₁₊ v') iW))))))))))

    R0 : RRex ≡ ₀
    R0 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong (r₁ *_) (Eq.cong₂ _*_ iQ₂₃≡ iQ₂₃≡)) outer≡)
        (Eq.trans (Eq.cong₂ _+_
            (Eq.trans (Eq.cong (r₂ *_) (Eq.cong₂ _*_ iq₃≡ iq₃≡)) step1)
            Eq.refl)
          inner≡))
      (+-inverseʳ (xv * (iW * ₁₊ v')))

  MD-coset-nnw : ∀ (x : ℤ* ₚ) (a' b' w' t' v' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
    ₁₊ b' + - (x .proj₁ * ₁₊ a') ≡ ₁₊ w' →
    - ((x ⁻¹) .proj₁ * ₁₊ b') ≡ ₁₊ t' →
    x .proj₁ * ₁₊ a' ≡ ₁₊ v' →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (ZM x)) .proj₂ ≡
    inj₂ ((x .proj₁ * ₁₊ a' , (x ⁻¹) .proj₁ * ₁₊ b') , lm)
  MD-coset-nnw x a' b' w' t' v' lm Weq eq-t eq-v =
    Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ ixv • H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ a' , ₁₊ b') lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ a') (₁₊ b') (λ ()))
            (Eq.cong (₁₊ a' ,_) vW)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c (H • S^ xv • H)) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ w' , - ₁₊ a') lm (toℕ ixv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ ixv) (₁₊ w') (- ₁₊ a') (λ ()))
            (Eq.cong (₁₊ w' ,_) vT)))))
    (Eq.trans (Eq.cong (λ c → ((ract' ᵗ) c H) .proj₂)
      (Eq.trans (ract-S^-coset (₁₊ t' , - ₁₊ w') lm (toℕ xv))
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz (toℕ xv) (₁₊ t') (- ₁₊ w') (λ ()))
            (Eq.cong (₁₊ t' ,_) vV)))))
      (Eq.cong₂ (λ u v → inj₂ ((u , v) , lm)) (Eq.sym eq-v)
        (Eq.trans (Eq.cong -_ (Eq.sym eq-t))
                  (-‿involutive ((x ⁻¹) .proj₁ * ₁₊ b'))))))
    where
    xv = x .proj₁
    ixv = (x ⁻¹) .proj₁
    inst-x = nztoℕ {y = xv} {neq0 = x .proj₂}

    vW : ₁₊ b' + nsum (toℕ xv) (- ₁₊ a') ≡ ₁₊ w'
    vW = Eq.trans (Eq.cong (₁₊ b' +_) (nsum-neg xv (₁₊ a'))) Weq

    ixw≡ : ixv * ₁₊ w' ≡ ixv * ₁₊ b' + - ₁₊ a'
    ixw≡ = Eq.trans (Eq.cong (ixv *_) (Eq.sym Weq))
      (Eq.trans (*-distribˡ-+ ixv (₁₊ b') (- (xv * ₁₊ a')))
        (Eq.cong ((ixv * ₁₊ b') +_)
          (Eq.trans (Eq.sym (-‿distribʳ-* ixv (xv * ₁₊ a')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc ixv xv (₁₊ a')))
              (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ˡ xv {{inst-x}}))
                        (*-identityˡ (₁₊ a'))))))))

    vT : - ₁₊ a' + nsum (toℕ ixv) (- ₁₊ w') ≡ ₁₊ t'
    vT = Eq.trans (Eq.cong (- ₁₊ a' +_) (nsum-neg ixv (₁₊ w')))
      (Eq.trans (Eq.cong (λ v → - ₁₊ a' + - v) ixw≡)
      (Eq.trans (Eq.cong (- ₁₊ a' +_)
          (Eq.trans (Eq.sym (-‿+-comm (ixv * ₁₊ b') (- ₁₊ a')))
            (Eq.cong (- (ixv * ₁₊ b') +_) (-‿involutive (₁₊ a')))))
      (Eq.trans (Eq.cong (- ₁₊ a' +_) (+-comm (- (ixv * ₁₊ b')) (₁₊ a')))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ a') (₁₊ a') (- (ixv * ₁₊ b'))))
      (Eq.trans (Eq.cong (_+ - (ixv * ₁₊ b')) (+-inverseˡ (₁₊ a')))
      (Eq.trans (+-0ˡ (- (ixv * ₁₊ b'))) eq-t))))))

    xt≡ : xv * ₁₊ t' ≡ - ₁₊ b'
    xt≡ = Eq.trans (Eq.cong (xv *_) (Eq.sym eq-t))
          (Eq.trans (Eq.sym (-‿distribʳ-* xv (ixv * ₁₊ b')))
            (Eq.cong -_
              (Eq.trans (Eq.sym (*-assoc xv ixv (₁₊ b')))
              (Eq.trans (Eq.cong (_* ₁₊ b') (lemma-⁻¹ʳ xv {{inst-x}}))
                        (*-identityˡ (₁₊ b'))))))

    negw≡ : - ₁₊ w' ≡ - ₁₊ b' + ₁₊ v'
    negw≡ = Eq.trans (Eq.cong -_ (Eq.sym Weq))
      (Eq.trans (Eq.sym (-‿+-comm (₁₊ b') (- (xv * ₁₊ a'))))
      (Eq.cong (- ₁₊ b' +_)
        (Eq.trans (-‿involutive (xv * ₁₊ a')) eq-v)))

    vV : - ₁₊ w' + nsum (toℕ xv) (- ₁₊ t') ≡ ₁₊ v'
    vV = Eq.trans (Eq.cong₂ _+_ negw≡ (nsum-neg xv (₁₊ t')))
      (Eq.trans (Eq.cong (λ v → (- ₁₊ b' + ₁₊ v') + - v) xt≡)
      (Eq.trans (Eq.cong ((- ₁₊ b' + ₁₊ v') +_) (-‿involutive (₁₊ b')))
      (Eq.trans (Eq.cong (_+ ₁₊ b') (+-comm (- ₁₊ b') (₁₊ v')))
      (Eq.trans (+-assoc (₁₊ v') (- ₁₊ b') (₁₊ b'))
      (Eq.trans (Eq.cong (₁₊ v' +_) (+-inverseˡ (₁₊ b')))
                (+-identityʳ (₁₊ v')))))))

------------------------------------------------------------------------
-- Total closed forms: witnesses are marshalled internally, so callers
-- see only the zero pattern of the a-slot.

  MD-resid!0 : ∀ (x : ℤ* ₚ) (b : ℤ ₚ) (lm : C (₁₊ m)) →
    ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x)) .proj₁ ≈ ZM x
  MD-resid!0 x ₀ lm = MD-resid-00 x lm
  MD-resid!0 x (₁₊ b') lm =
    elim-suc (- ((x ⁻¹) .proj₁ * ₁₊ b'))
      (neg≢0 ((x ⁻¹) .proj₁ * ₁₊ b') (((x ⁻¹) *' (₁₊ b' , λ ())) .proj₂))
      λ t' eq-t → MD-resid-0b x b' t' lm eq-t

  MD-coset!0 : ∀ (x : ℤ* ₚ) (b : ℤ ₚ) (lm : C (₁₊ m)) →
    ((ract' ᵗ) (inj₂ ((₀ , b) , lm)) (ZM x)) .proj₂ ≡
    inj₂ ((₀ , (x ⁻¹) .proj₁ * b) , lm)
  MD-coset!0 x ₀ lm =
    Eq.trans (MD-coset-00 x lm)
      (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) (Eq.sym (*-zeroʳ ((x ⁻¹) .proj₁))))
  MD-coset!0 x (₁₊ b') lm =
    elim-suc (- ((x ⁻¹) .proj₁ * ₁₊ b'))
      (neg≢0 ((x ⁻¹) .proj₁ * ₁₊ b') (((x ⁻¹) *' (₁₊ b' , λ ())) .proj₂))
      λ t' eq-t → MD-coset-0b x b' t' lm eq-t

  MD-resid!+ : ∀ (x : ℤ* ₚ) (a' : Fin (₁₊ p-2)) (b : ℤ ₚ) (lm : C (₁₊ m)) →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x)) .proj₁ ≈ ZM (x ⁻¹)
  MD-resid!+ x a' ₀ lm =
    elim-suc (- (x .proj₁ * ₁₊ a'))
      (neg≢0 (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂))
      λ s' eq-s → elim-suc (- ₁₊ s') (neg≢0 (₁₊ s') λ ())
      λ u' eq-u → MD-resid-a0 x a' s' u' lm eq-s eq-u
  MD-resid!+ x a' (₁₊ b') lm =
    elim-fin (₁₊ b' + - (x .proj₁ * ₁₊ a'))
      (λ Weq → elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ())
        λ y eq-y → MD-resid-nn0 x a' b' y lm eq-y Weq)
      (λ w' Weq →
        elim-suc (- ((x ⁻¹) .proj₁ * ₁₊ b'))
          (neg≢0 ((x ⁻¹) .proj₁ * ₁₊ b') (((x ⁻¹) *' (₁₊ b' , λ ())) .proj₂))
        λ t' eq-t →
        elim-suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂)
        λ v' eq-v → MD-resid-nnw x a' b' w' t' v' lm Weq eq-t eq-v)

  MD-coset!+ : ∀ (x : ℤ* ₚ) (a' : Fin (₁₊ p-2)) (b : ℤ ₚ) (lm : C (₁₊ m)) →
    ((ract' ᵗ) (inj₂ ((₁₊ a' , b) , lm)) (ZM x)) .proj₂ ≡
    inj₂ ((x .proj₁ * ₁₊ a' , (x ⁻¹) .proj₁ * b) , lm)
  MD-coset!+ x a' ₀ lm =
    elim-suc (- (x .proj₁ * ₁₊ a'))
      (neg≢0 (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂))
      λ s' eq-s → elim-suc (- ₁₊ s') (neg≢0 (₁₊ s') λ ())
      λ u' eq-u →
        Eq.trans (MD-coset-a0 x a' s' u' lm eq-s eq-u)
          (Eq.cong (λ v → inj₂ ((x .proj₁ * ₁₊ a' , v) , lm))
            (Eq.sym (*-zeroʳ ((x ⁻¹) .proj₁))))
  MD-coset!+ x a' (₁₊ b') lm =
    elim-fin (₁₊ b' + - (x .proj₁ * ₁₊ a'))
      (λ Weq → elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ())
        λ y eq-y → MD-coset-nn0 x a' b' y lm eq-y Weq)
      (λ w' Weq →
        elim-suc (- ((x ⁻¹) .proj₁ * ₁₊ b'))
          (neg≢0 ((x ⁻¹) .proj₁ * ₁₊ b') (((x ⁻¹) *' (₁₊ b' , λ ())) .proj₂))
        λ t' eq-t →
        elim-suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂)
        λ v' eq-v → MD-coset-nnw x a' b' w' t' v' lm Weq eq-t eq-v)

------------------------------------------------------------------------
-- ZM value congruence (the nz slots are proof-irrelevant).

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open Lemmas0 j

  ZM-val≈ : ∀ (q q' : ℤ* ₚ) → q .proj₁ ≡ q' .proj₁ → ZM q ≈ ZM q'
  ZM-val≈ q q' eq = aux-MM (q .proj₂) (q' .proj₂) eq
