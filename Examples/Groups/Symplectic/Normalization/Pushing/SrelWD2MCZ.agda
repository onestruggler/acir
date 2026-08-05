------------------------------------------------------------------------
-- Presentations of groups
--
-- Toward the semi-M↑CZ/M↓CZ width-2 inj₂ coset halves at a (₀,b) A box
-- (the shape-stable branch; a≠0 hits the L'1→L'2 shape-crossing and
-- stays parked).  This file provides the k-fold CZ orbit at an
-- abstract (₀,b) box — OrdCZ-0b's step/orbit generalized from the
-- fixed p-power to any k (its versions are module-private) — the
-- engine both axioms' CZ^ legs run on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD2MCZ
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Fin using (Fin ; toℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₂)
open import Data.Vec using ([])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿distribʳ-* ; -0#≈0#)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C ; ract ; nsum ; _≋_ ; c1-eq ; elim-suc)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using (E1 ; GCZd ; inj₂-w1-de-eq)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (eCZ ; nsum-*)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  p-2 p-prime using (ractM! ; Mact-nz)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMD
  p-2 p-prime using (MD-coset!0 ; MD-coset!+)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (M↓≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWD
  p-2 p-prime using (inv-val-cong)
import Examples.Groups.Symplectic.Normalization.Pushing.StrategyB2
  p-2 p-prime as SB2

------------------------------------------------------------------------
-- The k-fold CZ orbit at a (₀,b) A box: the L' shape is stable, the D
-- box drifts by nsum t' (−1) in its second slot per step, and the E box
-- absorbs nsum t' (eCZ da) per step (t' = toℕ b⁻¹).

module CZOrbit-0b (b : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b) ≢ (₀ , ₀)) where

  tCZ : ℕ
  tCZ = toℕ (((₁₊ b , λ ()) ⁻¹) .proj₁)

  cst : D → E → C 2
  cst dd ee = inj₂ (dd , (([] , ee) , ([] , ((₀ , ₁₊ b) , nz))))

  stepCZ : ∀ (da db e : ℤ ₚ) →
    proj₂ (ract {1} (cst (da , db) e) (gate₂ CZ-gate))
    ≡ cst (da , db + nsum tCZ (- ₁)) (e + - nsum tCZ (eCZ da))
  stepCZ da db e =
    inj₂-w1-de-eq (GCZd tCZ da db) (Eq.cong (λ z → e + - z) (E1 tCZ da db))

  orbitCZ : ∀ (k : ℕ) (da db e : ℤ ₚ) →
    ((ract {1} ᵗ) (cst (da , db) e) (CZ ^ k)) .proj₂
    ≡ cst (da , db + nsum k (nsum tCZ (- ₁)))
          (e + nsum k (- nsum tCZ (eCZ da)))
  orbitCZ zero da db e =
    inj₂-w1-de-eq
      (Eq.cong (da ,_) (Eq.sym (+-identityʳ db)))
      (Eq.sym (+-identityʳ e))
  orbitCZ (suc zero) da db e =
    Eq.trans (stepCZ da db e)
      (inj₂-w1-de-eq
        (Eq.cong (da ,_)
          (Eq.cong (db +_) (Eq.sym (+-identityʳ (nsum tCZ (- ₁))))))
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- nsum tCZ (eCZ da))))))
  orbitCZ (suc (suc k)) da db e =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ da db e))
    (Eq.trans (orbitCZ (suc k) da (db + nsum tCZ (- ₁))
        (e + - nsum tCZ (eCZ da)))
      (inj₂-w1-de-eq
        (Eq.cong (da ,_)
          (+-assoc db (nsum tCZ (- ₁)) (nsum (suc k) (nsum tCZ (- ₁)))))
        (+-assoc e (- nsum tCZ (eCZ da))
          (nsum (suc k) (- nsum tCZ (eCZ da))))))

------------------------------------------------------------------------
-- semi-M↑CZ at inj₂ (d , (₀,b)-box): the M x ↑ leg threads through the
-- D box into a width-1 ractM! run (box (₀,b) ↦ (₀ , x⁻¹·b), e and d
-- fixed); the CZ legs run the orbit above — a single step at the
-- updated box on the left, toℕ x steps at the original box on the
-- right.  The two agree because the orbit rate at the updated box is
-- (x⁻¹·b)⁻¹ = x·b⁻¹ (nsum-* / inv-distrib / inv-involutive).

module SemiMuCZ-0b (x : ℤ* ₚ) (b : Fin (₁₊ p-2))
  (nz : (₀ , ₁₊ b) ≢ (₀ , ₀))
  (m' : Fin (₁₊ p-2)) (eq-m : (x ⁻¹) .proj₁ * ₁₊ b ≡ ₁₊ m')
  where

  nzM' : (₀ , ₁₊ m') ≢ (₀ , ₀)
  nzM' = λ ()

  open CZOrbit-0b b nz using ()
    renaming (tCZ to tB ; cst to cstB ; orbitCZ to orbitB)
  open CZOrbit-0b m' nzM' using ()
    renaming (tCZ to tM ; cst to cstM ; stepCZ to stepM)

  private
    X : ℤ ₚ
    X = x .proj₁

    B* M* : ℤ* ₚ
    B* = (₁₊ b , λ ())
    M* = (₁₊ m' , λ ())

    -- The width-1 M run with the box fixed into constructor form.
    mfix : ∀ (e : E) →
      ((ract {0} ᵗ) (([] , e) , ([] , ((₀ , ₁₊ b) , nz))) (ZM x)) .proj₂
      ≡ (([] , e) , ([] , ((₀ , ₁₊ m') , nzM')))
    mfix e = Eq.trans (ractM! x e (₀ , ₁₊ b) nz (Mact-nz x (₀ , ₁₊ b) nz))
                      (c1-eq {nz' = nzM'} Eq.refl
                        (Eq.cong₂ _,_ (*-zeroʳ (x .proj₁)) eq-m))

    -- The lifted M word threads the D box untouched.
    mthread : ∀ (dd : D) (e : E) →
      ((ract {1} ᵗ)
         (inj₂ (dd , (([] , e) , ([] , ((₀ , ₁₊ b) , nz))))) (ZM x ↑)) .proj₂
      ≡ inj₂ (dd , (([] , e) , ([] , ((₀ , ₁₊ m') , nzM'))))
    mthread dd e =
      Eq.trans
        (Eq.cong proj₂
          (ract-↑-≡ dd (([] , e) , ([] , ((₀ , ₁₊ b) , nz))) (ZM x)))
        (Eq.cong (λ z → inj₂ (dd , z)) (mfix e))

    -- The orbit rate at the updated box is x times the original rate.
    tMval : (M* ⁻¹) .proj₁ ≡ X * (B* ⁻¹) .proj₁
    tMval = Eq.trans (inv-val-cong M* ((x ⁻¹) *' B*) (Eq.sym eq-m))
            (Eq.trans (inv-distrib (x ⁻¹) B*)
                      (Eq.cong (_* (B* ⁻¹) .proj₁) (inv-involutive x)))

    nsumtM : ∀ (v : ℤ ₚ) → nsum tM v ≡ X * ((B* ⁻¹) .proj₁ * v)
    nsumtM v = Eq.trans (nsum-* ((M* ⁻¹) .proj₁) v)
               (Eq.trans (Eq.cong (_* v) tMval)
                         (*-assoc X ((B* ⁻¹) .proj₁) v))

    dNT : ∀ (v : ℤ ₚ) → nsum tM v ≡ nsum (toℕ X) (nsum tB v)
    dNT v = Eq.trans (nsumtM v)
            (Eq.sym (Eq.trans (nsum-* X (nsum tB v))
                              (Eq.cong (X *_) (nsum-* ((B* ⁻¹) .proj₁) v))))

    eNT : ∀ (w : ℤ ₚ) → - nsum tM w ≡ nsum (toℕ X) (- nsum tB w)
    eNT w = Eq.trans (Eq.cong -_ (nsumtM w))
            (Eq.trans (-‿distribʳ-* X ((B* ⁻¹) .proj₁ * w))
            (Eq.sym (Eq.trans (nsum-* X (- nsum tB w))
              (Eq.cong (X *_)
                (Eq.cong -_ (nsum-* ((B* ⁻¹) .proj₁) w))))))

  -- The coset half.
  semiMuCZ-wd2-0b-coset : ∀ (da db e : ℤ ₚ) →
    ((ract {1} ᵗ) (cstB (da , db) e) (ZM x ↑ • CZ)) .proj₂
    ≡ ((ract {1} ᵗ) (cstB (da , db) e) (CZ^ (x ^1) • ZM x ↑)) .proj₂
  semiMuCZ-wd2-0b-coset da db e =
    Eq.trans
      (Eq.trans
        (Eq.cong (λ z → ((ract {1} ᵗ) z CZ) .proj₂) (mthread (da , db) e))
        (stepM da db e))
    (Eq.trans
      (inj₂-w1-de-eq
        (Eq.cong (da ,_) (Eq.cong (db +_) (dNT (- ₁))))
        (Eq.cong (e +_) (eNT (eCZ da))))
      (Eq.sym
        (Eq.trans
          (Eq.cong (λ z → ((ract {1} ᵗ) z (ZM x ↑)) .proj₂)
                   (orbitB (toℕ X) da db e))
          (mthread (da , db + nsum (toℕ X) (nsum tB (- ₁)))
                   (e + nsum (toℕ X) (- nsum tB (eCZ da)))))))

------------------------------------------------------------------------
-- The full ≋ pair: elim-suc glue + Strategy B.

semi-M↑CZ-wd2-inj₂-0b : ∀ (x : ℤ* ₚ) (da db e : ℤ ₚ)
  (b : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b) ≢ (₀ , ₀)) →
  let c = inj₂ ((da , db) , (([] , e) , ([] , ((₀ , ₁₊ b) , nz)))) in
  (ract {1} ᵗ) c (ZM x ↑ • CZ) ≋ (ract {1} ᵗ) c (CZ^ (x ^1) • ZM x ↑)
semi-M↑CZ-wd2-inj₂-0b x da db e b nz =
  elim-suc ((x ⁻¹) .proj₁ * ₁₊ b) (((x ⁻¹) *' (₁₊ b , λ ())) .proj₂)
    λ m' eq-m →
  SB2.wd-from-coset
    (inj₂ ((da , db) , (([] , e) , ([] , ((₀ , ₁₊ b) , nz)))))
    (srel (Base.semi-M↑CZ x))
    (SemiMuCZ-0b.semiMuCZ-wd2-0b-coset x b nz m' eq-m da db e)

------------------------------------------------------------------------
-- semi-M↓CZ at inj₂ (d , (₀,bA)-box): the down-widened M word equals
-- the plain width-2 M word (M↓≡), which drives the D BOX (MD-coset!0/+
-- from the M-mul engine: (₀,b) ↦ (₀ , x⁻¹·b), (₁₊a',b) ↦ (x·a' ,
-- x⁻¹·b), the width-1 part untouched); the CZ legs run the same
-- CZOrbit-0b since the A box is fixed on both sides.

module SemiMdCZ-0A (x : ℤ* ₚ) (bA : Fin (₁₊ p-2))
  (nzA : (₀ , ₁₊ bA) ≢ (₀ , ₀))
  where

  open CZOrbit-0b bA nzA using ()
    renaming (tCZ to tA ; cst to cstA ; stepCZ to stepA ; orbitCZ to orbitA)

  private
    X : ℤ ₚ
    X = x .proj₁

    x⁻¹v : ℤ ₚ
    x⁻¹v = (x ⁻¹) .proj₁

    BA* : ℤ* ₚ
    BA* = (₁₊ bA , λ ())

    ml1e : E → C 1
    ml1e e = ([] , e) , ([] , ((₀ , ₁₊ bA) , nzA))

    ΔA : ℤ ₚ
    ΔA = nsum tA (- ₁)

    -- x⁻¹ · (k-fold drift) = one-step drift.
    chain2 : x⁻¹v * nsum (toℕ X) ΔA ≡ ΔA
    chain2 = Eq.trans (Eq.cong (x⁻¹v *_) (nsum-* X ΔA))
             (Eq.trans (Eq.sym (*-assoc x⁻¹v X ΔA))
             (Eq.trans (Eq.cong (_* ΔA)
                 (lemma-⁻¹ˡ X {{nztoℕ {y = X} {neq0 = x .proj₂}}}))
               (*-identityˡ ΔA)))

    dsnd : ∀ (ddb : ℤ ₚ) →
      x⁻¹v * ddb + ΔA ≡ x⁻¹v * (ddb + nsum (toℕ X) ΔA)
    dsnd ddb = Eq.sym
      (Eq.trans (*-distribˡ-+ x⁻¹v ddb (nsum (toℕ X) ΔA))
                (Eq.cong ((x⁻¹v * ddb) +_) chain2))

    -- nsum tA ₀ vanishes (rate times zero).
    z0 : nsum tA ₀ ≡ ₀
    z0 = Eq.trans (nsum-* ((BA* ⁻¹) .proj₁) ₀) (*-zeroʳ ((BA* ⁻¹) .proj₁))

    -z0 : - nsum tA ₀ ≡ ₀
    -z0 = Eq.trans (Eq.cong -_ z0) -0#≈0#

    e00 : ∀ (e : E) → e + - nsum tA ₀ ≡ e
    e00 e = Eq.trans (Eq.cong (e +_) -z0) (+-identityʳ e)

    e00' : ∀ (e : E) → e + nsum (toℕ X) (- nsum tA ₀) ≡ e
    e00' e = Eq.trans
      (Eq.cong (e +_)
        (Eq.trans (Eq.cong (nsum (toℕ X)) -z0)
        (Eq.trans (nsum-* X ₀) (*-zeroʳ X))))
      (+-identityʳ e)

  -- D box (₀ , ddb): the drive scales the second slot; no e-emission
  -- (eCZ ₀ = ₀).
  semiMdCZ-00-coset : ∀ (ddb e : ℤ ₚ) →
    ((ract {1} ᵗ) (cstA (₀ , ddb) e) (ZM x ↓ • CZ)) .proj₂
    ≡ ((ract {1} ᵗ) (cstA (₀ , ddb) e) (CZ^ (x ^1) • ZM x ↓)) .proj₂
  semiMdCZ-00-coset ddb e =
    Eq.trans
      (Eq.trans
        (Eq.cong (λ w → ((ract {1} ᵗ) (cstA (₀ , ddb) e) (w • CZ)) .proj₂)
                 (M↓≡ x))
      (Eq.trans
        (Eq.cong (λ z → ((ract {1} ᵗ) z CZ) .proj₂)
                 (MD-coset!0 x ddb (ml1e e)))
        (stepA ₀ (x⁻¹v * ddb) e)))
    (Eq.trans
      (inj₂-w1-de-eq
        (Eq.cong (₀ ,_) (dsnd ddb))
        (Eq.trans (e00 e) (Eq.sym (e00' e))))
      (Eq.sym
        (Eq.trans
          (Eq.cong (λ z → ((ract {1} ᵗ) z (ZM x ↓)) .proj₂)
                   (orbitA (toℕ X) ₀ ddb e))
        (Eq.trans
          (Eq.cong (λ w → ((ract {1} ᵗ)
              (cstA (₀ , ddb + nsum (toℕ X) ΔA)
                    (e + nsum (toℕ X) (- nsum tA ₀))) w) .proj₂)
            (M↓≡ x))
          (MD-coset!0 x (ddb + nsum (toℕ X) ΔA)
            (ml1e (e + nsum (toℕ X) (- nsum tA ₀))))))))

  -- D box (₁₊ a' , ddb): the drive scales both slots; the e-emission
  -- rates match because bA⁻¹·(x·a') = x·(bA⁻¹·a').
  semiMdCZ-+-coset : ∀ (a' v' : Fin (₁₊ p-2))
    (eq-v : X * ₁₊ a' ≡ ₁₊ v') (ddb e : ℤ ₚ) →
    ((ract {1} ᵗ) (cstA (₁₊ a' , ddb) e) (ZM x ↓ • CZ)) .proj₂
    ≡ ((ract {1} ᵗ) (cstA (₁₊ a' , ddb) e) (CZ^ (x ^1) • ZM x ↓)) .proj₂
  semiMdCZ-+-coset a' v' eq-v ddb e =
    Eq.trans
      (Eq.trans
        (Eq.cong (λ w → ((ract {1} ᵗ) (cstA (₁₊ a' , ddb) e) (w • CZ)) .proj₂)
                 (M↓≡ x))
      (Eq.trans
        (Eq.cong (λ z → ((ract {1} ᵗ) z CZ) .proj₂)
          (Eq.trans (MD-coset!+ x a' ddb (ml1e e))
            (Eq.cong (λ u → inj₂ ((u , x⁻¹v * ddb) , ml1e e)) eq-v)))
        (stepA (₁₊ v') (x⁻¹v * ddb) e)))
    (Eq.trans
      (inj₂-w1-de-eq
        (Eq.cong₂ _,_ (Eq.sym eq-v) (dsnd ddb))
        (Eq.cong (e +_) e+))
      (Eq.sym
        (Eq.trans
          (Eq.cong (λ z → ((ract {1} ᵗ) z (ZM x ↓)) .proj₂)
                   (orbitA (toℕ X) (₁₊ a') ddb e))
        (Eq.trans
          (Eq.cong (λ w → ((ract {1} ᵗ)
              (cstA (₁₊ a' , ddb + nsum (toℕ X) ΔA)
                    (e + nsum (toℕ X) (- nsum tA (eCZ (₁₊ a'))))) w) .proj₂)
            (M↓≡ x))
          (MD-coset!+ x a' (ddb + nsum (toℕ X) ΔA)
            (ml1e (e + nsum (toℕ X) (- nsum tA (eCZ (₁₊ a'))))))))))
    where
    bAi : ℤ ₚ
    bAi = (BA* ⁻¹) .proj₁

    swap3 : bAi * (X * ₁₊ a') ≡ X * (bAi * ₁₊ a')
    swap3 = Eq.trans (Eq.sym (*-assoc bAi X (₁₊ a')))
            (Eq.trans (Eq.cong (_* ₁₊ a') (*-comm bAi X))
                      (*-assoc X bAi (₁₊ a')))

    e+ : - nsum tA (₁₊ v') ≡ nsum (toℕ X) (- nsum tA (₁₊ a'))
    e+ = Eq.trans (Eq.cong -_
           (Eq.trans (nsum-* bAi (₁₊ v'))
           (Eq.trans (Eq.cong (bAi *_) (Eq.sym eq-v)) swap3)))
         (Eq.trans (-‿distribʳ-* X (bAi * ₁₊ a'))
         (Eq.sym (Eq.trans (nsum-* X (- nsum tA (₁₊ a')))
           (Eq.cong (X *_) (Eq.cong -_ (nsum-* bAi (₁₊ a')))))))

------------------------------------------------------------------------
-- The full ≋ pair for the ↓ variant, dispatched over the D box.

semi-M↓CZ-wd2-inj₂-0A : ∀ (x : ℤ* ₚ) (dd : D) (e : ℤ ₚ)
  (bA : Fin (₁₊ p-2)) (nzA : (₀ , ₁₊ bA) ≢ (₀ , ₀)) →
  let c = inj₂ (dd , (([] , e) , ([] , ((₀ , ₁₊ bA) , nzA)))) in
  (ract {1} ᵗ) c (ZM x ↓ • CZ) ≋ (ract {1} ᵗ) c (CZ^ (x ^1) • ZM x ↓)
semi-M↓CZ-wd2-inj₂-0A x (₀ , ddb) e bA nzA =
  SB2.wd-from-coset
    (inj₂ ((₀ , ddb) , (([] , e) , ([] , ((₀ , ₁₊ bA) , nzA)))))
    (srel (Base.semi-M↓CZ x))
    (SemiMdCZ-0A.semiMdCZ-00-coset x bA nzA ddb e)
semi-M↓CZ-wd2-inj₂-0A x (₁₊ a' , ddb) e bA nzA =
  elim-suc (x .proj₁ * ₁₊ a') ((x *' (₁₊ a' , λ ())) .proj₂)
    λ v' eq-v →
  SB2.wd-from-coset
    (inj₂ ((₁₊ a' , ddb) , (([] , e) , ([] , ((₀ , ₁₊ bA) , nzA)))))
    (srel (Base.semi-M↓CZ x))
    (SemiMdCZ-0A.semiMdCZ-+-coset x bA nzA a' v' eq-v ddb e)
