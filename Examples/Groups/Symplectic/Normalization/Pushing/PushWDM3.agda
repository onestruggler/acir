------------------------------------------------------------------------
-- Presentations of groups
--
-- order-CZ width-2 COSET halves on inj₁ cosets, the drift branches.
-- With an a-nonzero A box the LCZ2 collapse takes the no-test clause
-- every step: for a (₀ , dd) B box the CZ direction is ε and only the
-- B box's d-component drifts (by − a per step); the p-orbit closes by
-- nsum-p≡0.  Leaf file over the cached interfaces so the edit-check
-- loop stays fast.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.PushWDM3
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as TDw
  using (push-D-w)
open import Examples.Groups.Symplectic.Normalization.Pushing.Push2
  p-2 p-prime using (coset)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using (E1 ; GCZd ; ES ; GS ; EH ; EH3)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿involutive ; -‿+-comm ; -‿distribʳ-*)
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (eCZ ; nsum-*)

------------------------------------------------------------------------
-- The (a ≠ 0 , c = 0) branch: direction ε, pure d-drift.

module OrdCZ-inj₁-c0 (a' : Fin (₁₊ p-2)) where

  -- A-box equality with the pinned absurd proof.
  A-fix : ∀ {b₁ b₂ : ℤ ₚ} → b₁ ≡ b₂ →
    _≡_ {A = A} ((₁₊ a' , b₁) , λ ()) ((₁₊ a' , b₂) , λ ())
  A-fix Eq.refl = Eq.refl

  cst : ℤ ₚ → ℤ ₚ → E → D → C 2
  cst dd b e d₀ =
    inj₁ ((d₀ ∷ [] , e) , (((₀ , dd) ∷ []) , ((₁₊ a' , b) , λ ())))

  cst-cong : ∀ {dd₁ dd₂ b₁ b₂ e₁ e₂ : ℤ ₚ} {d₀ : D} →
    dd₁ ≡ dd₂ → b₁ ≡ b₂ → e₁ ≡ e₂ →
    cst dd₁ b₁ e₁ d₀ ≡ cst dd₂ b₂ e₂ d₀
  cst-cong {d₀ = d₀} pdd pb pe =
    Eq.cong₂ (λ u v → inj₁ ((d₀ ∷ [] , u) , v)) pe
      (Eq.cong₂ (λ u v → ((₀ , u) ∷ []) , v) pdd (A-fix pb))

  -- One CZ step: the collapse direction is ε (a ≠ 0 with a zero-a B
  -- box), the D box and E pick up only removable ₀-junk, and the B
  -- box's d-component drops by a.  The dd-split lets the LCZ2 case
  -- tree (which examines the B box's d-component first) reduce.
  stepCZ : ∀ (d₀ : D) (e dd b : ℤ ₚ) →
    proj₂ (ract {1} (cst dd b e d₀) (gate₂ CZ-gate))
    ≡ cst (dd + - ₁₊ a') (b + - ₀) (e + - ₀) d₀
  stepCZ d₀ e ₀ b = Eq.refl
  stepCZ d₀ e (₁₊ dd') b = Eq.refl

  orbit : ∀ (k : ℕ) (d₀ : D) (e dd b : ℤ ₚ) →
    ((ract {1} ᵗ) (cst dd b e d₀) (CZ ^ k)) .proj₂
    ≡ cst (dd + nsum k (- ₁₊ a')) (b + nsum k (- ₀)) (e + nsum k (- ₀)) d₀
  orbit zero d₀ e dd b =
    cst-cong (Eq.sym (+-identityʳ dd)) (Eq.sym (+-identityʳ b))
             (Eq.sym (+-identityʳ e))
  orbit (suc zero) d₀ e dd b =
    Eq.trans (stepCZ d₀ e dd b)
      (cst-cong
        (Eq.cong (dd +_) (Eq.sym (+-identityʳ (- ₁₊ a'))))
        (Eq.cong (b +_) (Eq.sym (+-identityʳ (- ₀))))
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- ₀)))))
  orbit (suc (suc k)) d₀ e dd b =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ d₀ e dd b))
    (Eq.trans (orbit (suc k) d₀ (e + - ₀) (dd + - ₁₊ a') (b + - ₀))
      (cst-cong
        (+-assoc dd (- ₁₊ a') (nsum (suc k) (- ₁₊ a')))
        (+-assoc b (- ₀) (nsum (suc k) (- ₀)))
        (+-assoc e (- ₀) (nsum (suc k) (- ₀)))))

  ordCZ-inj₁-c0-coset : ∀ (d₀ : D) (e dd b : ℤ ₚ) →
    ((ract {1} ᵗ) (cst dd b e d₀) (CZ ^ p)) .proj₂
    ≡ ((ract {1} ᵗ) (cst dd b e d₀) ε) .proj₂
  ordCZ-inj₁-c0-coset d₀ e dd b =
    Eq.trans (orbit p d₀ e dd b)
      (cst-cong
        (Eq.trans (Eq.cong (dd +_) (nsum-p≡0 (- ₁₊ a'))) (+-identityʳ dd))
        (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- ₀))) (+-identityʳ b))
        (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- ₀))) (+-identityʳ e)))

------------------------------------------------------------------------
-- The (a = 0 , c = 0 , dd = 0) branch: the direction is CZ^ b⁻¹ with
-- the canonical ntH-CZ^ witness, so PushWDM's E1/GCZd closed forms
-- apply on the nose: the D box gains nsum t (− 1) on its b-component
-- and E drops by nsum t (eCZ da) per step, with t = toℕ b⁻¹ fixed.

module OrdCZ-inj₁-00 (b' : Fin (₁₊ p-2)) where

  private
    t : ℕ
    t = toℕ (((₁₊ b' , λ ()) ⁻¹) .proj₁)

  cst : E → D → C 2
  cst e d₀ =
    inj₁ ((d₀ ∷ [] , e) , (((₀ , ₀) ∷ []) , ((₀ , ₁₊ b') , λ ())))

  -- Proof-agnostic collapse onto the canonical coset: the l'-of
  -- no-branch produces a where-lifted nonzero proof, which unifies
  -- away once the value components are rewritten.
  fix : ∀ {d₁ d₂ : D} {e₁ e₂ dd₁ b₁ : ℤ ₚ}
    {pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₀ , b₁) (₀ , ₀) → ⊥} →
    d₁ ≡ d₂ → e₁ ≡ e₂ → dd₁ ≡ ₀ → b₁ ≡ ₁₊ b' →
    _≡_ {A = C 2}
      (inj₁ ((d₁ ∷ [] , e₁) , (((₀ , dd₁) ∷ []) , ((₀ , b₁) , pr))))
      (cst e₂ d₂)
  fix Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  z00 : ∀ (x : ℤ ₚ) → x + - ₀ ≡ x
  z00 x = Eq.trans (Eq.cong (x +_) -₀≡₀') (+-identityʳ x)
    where
    -₀≡₀' : - ₀ ≡ ₀
    -₀≡₀' = Eq.trans (Eq.sym (+-identityʳ (- z)))
                     (+-inverseˡ z)
      where
      z : ℤ ₚ
      z = ₀

  stepCZ : ∀ (e da db : ℤ ₚ) →
    proj₂ (ract {1} (cst e (da , db)) (gate₂ CZ-gate))
    ≡ cst (e + - nsum t (eCZ da)) (da , db + nsum t (- ₁))
  stepCZ e da db = fix
    (GCZd t da db)
    (Eq.cong (λ z → e + - z) (E1 t da db))
    (z00 ₀)
    (z00 (₁₊ b'))

  cstC : ∀ {e₁ e₂ : ℤ ₚ} {da db₁ db₂ : ℤ ₚ} →
    e₁ ≡ e₂ → db₁ ≡ db₂ → cst e₁ (da , db₁) ≡ cst e₂ (da , db₂)
  cstC {da = da} pe pdb =
    Eq.cong₂ (λ u v → cst u (da , v)) pe pdb

  orbit : ∀ (k : ℕ) (e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst e (da , db)) (CZ ^ k)) .proj₂
    ≡ cst (e + nsum k (- nsum t (eCZ da)))
          (da , db + nsum k (nsum t (- ₁)))
  orbit zero e da db =
    cstC (Eq.sym (+-identityʳ e)) (Eq.sym (+-identityʳ db))
  orbit (suc zero) e da db =
    Eq.trans (stepCZ e da db)
      (cstC
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- nsum t (eCZ da)))))
        (Eq.cong (db +_) (Eq.sym (+-identityʳ (nsum t (- ₁))))))
  orbit (suc (suc k)) e da db =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ e da db))
    (Eq.trans (orbit (suc k) (e + - nsum t (eCZ da)) da
        (db + nsum t (- ₁)))
      (cstC
        (+-assoc e (- nsum t (eCZ da)) (nsum (suc k) (- nsum t (eCZ da))))
        (+-assoc db (nsum t (- ₁)) (nsum (suc k) (nsum t (- ₁))))))

  ordCZ-inj₁-00-coset : ∀ (e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst e (da , db)) (CZ ^ p)) .proj₂
    ≡ ((ract {1} ᵗ) (cst e (da , db)) ε) .proj₂
  ordCZ-inj₁-00-coset e da db =
    Eq.trans (orbit p e da db)
      (cstC
        (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- nsum t (eCZ da))))
                  (+-identityʳ e))
        (Eq.trans (Eq.cong (db +_) (nsum-p≡0 (nsum t (- ₁))))
                  (+-identityʳ db)))

------------------------------------------------------------------------
-- The (a = 0 , c = 0 , dd ≠ 0) branch: the direction gains an S-power
-- prefix (S^ (− b⁻¹dd + − b⁻¹dd) • CZ^ b⁻¹) whose push through the D
-- box emits nothing (ES) and shifts the box b-component by
-- nsum tS (− da) (GS); the CZ part then behaves as in the previous
-- branch.  Both exponents are fixed along the orbit.

module OrdCZ-inj₁-0d (b' dd' : Fin (₁₊ p-2)) where

  private
    bI : ℤ ₚ
    bI = ((₁₊ b' , λ ()) ⁻¹) .proj₁
    t : ℕ
    t = toℕ bI
    kSd : ℤ ₚ
    kSd = - (bI * ₁₊ dd') + - (bI * ₁₊ dd')
    tS : ℕ
    tS = toℕ kSd

  cst : E → D → C 2
  cst e d₀ =
    inj₁ ((d₀ ∷ [] , e) , (((₀ , ₁₊ dd') ∷ []) , ((₀ , ₁₊ b') , λ ())))

  fix : ∀ {d₁ d₂ : D} {e₁ e₂ dd₁ b₁ : ℤ ₚ}
    {pr : _≡_ {A = ℤ ₚ × ℤ ₚ} (₀ , b₁) (₀ , ₀) → ⊥} →
    d₁ ≡ d₂ → e₁ ≡ e₂ → dd₁ ≡ ₁₊ dd' → b₁ ≡ ₁₊ b' →
    _≡_ {A = C 2}
      (inj₁ ((d₁ ∷ [] , e₁) , (((₀ , dd₁) ∷ []) , ((₀ , b₁) , pr))))
      (cst e₂ d₂)
  fix Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  z00' : ∀ (x : ℤ ₚ) → x + - ₀ ≡ x
  z00' x = Eq.trans (Eq.cong (x +_) neg0) (+-identityʳ x)
    where
    neg0 : - ₀ ≡ ₀
    neg0 = Eq.trans (Eq.sym (+-identityʳ (- z))) (+-inverseˡ z)
      where
      z : ℤ ₚ
      z = ₀

  stepCZ : ∀ (e da db : ℤ ₚ) →
    proj₂ (ract {1} (cst e (da , db)) (gate₂ CZ-gate))
    ≡ cst (e + - nsum t (eCZ da))
          (da , db + (nsum tS (- da) + nsum t (- ₁)))
  stepCZ e da db = fix
    (Eq.trans
      (Eq.cong (λ dm →
          TDw.push-D-w dm (CZ ^ t) (TDw.ntH-^ TDw.ntH-CZ t)
            .proj₂ .proj₂)
        (GS tS da db))
    (Eq.trans (GCZd t da (db + nsum tS (- da)))
      (Eq.cong (da ,_)
        (+-assoc db (nsum tS (- da)) (nsum t (- ₁))))))
    (Eq.cong (λ z → e + - z)
      (Eq.trans (Eq.cong₂ _+_ (ES tS da db)
          (Eq.trans
            (Eq.cong (λ dm →
                TDw.push-D-w dm (CZ ^ t) (TDw.ntH-^ TDw.ntH-CZ t)
                  .proj₁)
              (GS tS da db))
            (E1 t da (db + nsum tS (- da)))))
        (+-identityˡ (nsum t (eCZ da)))))
    (z00' (₁₊ dd'))
    (z00' (₁₊ b'))

  cstC : ∀ {e₁ e₂ : ℤ ₚ} {da db₁ db₂ : ℤ ₚ} →
    e₁ ≡ e₂ → db₁ ≡ db₂ → cst e₁ (da , db₁) ≡ cst e₂ (da , db₂)
  cstC {da = da} pe pdb =
    Eq.cong₂ (λ u v → cst u (da , v)) pe pdb

  orbit : ∀ (k : ℕ) (e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst e (da , db)) (CZ ^ k)) .proj₂
    ≡ cst (e + nsum k (- nsum t (eCZ da)))
          (da , db + nsum k (nsum tS (- da) + nsum t (- ₁)))
  orbit zero e da db =
    cstC (Eq.sym (+-identityʳ e)) (Eq.sym (+-identityʳ db))
  orbit (suc zero) e da db =
    Eq.trans (stepCZ e da db)
      (cstC
        (Eq.cong (e +_) (Eq.sym (+-identityʳ (- nsum t (eCZ da)))))
        (Eq.cong (db +_)
          (Eq.sym (+-identityʳ (nsum tS (- da) + nsum t (- ₁))))))
  orbit (suc (suc k)) e da db =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ e da db))
    (Eq.trans (orbit (suc k) (e + - nsum t (eCZ da)) da
        (db + (nsum tS (- da) + nsum t (- ₁))))
      (cstC
        (+-assoc e (- nsum t (eCZ da)) (nsum (suc k) (- nsum t (eCZ da))))
        (+-assoc db (nsum tS (- da) + nsum t (- ₁))
          (nsum (suc k) (nsum tS (- da) + nsum t (- ₁))))))

  ordCZ-inj₁-0d-coset : ∀ (e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst e (da , db)) (CZ ^ p)) .proj₂
    ≡ ((ract {1} ᵗ) (cst e (da , db)) ε) .proj₂
  ordCZ-inj₁-0d-coset e da db =
    Eq.trans (orbit p e da db)
      (cstC
        (Eq.trans (Eq.cong (e +_) (nsum-p≡0 (- nsum t (eCZ da))))
                  (+-identityʳ e))
        (Eq.trans (Eq.cong (db +_)
                    (nsum-p≡0 (nsum tS (- da) + nsum t (- ₁))))
                  (+-identityʳ db)))

------------------------------------------------------------------------
-- The (a ≠ 0 , c ≠ 0) branch: the direction is the constant sandwich
-- H ^ 3 • S^ (− a·c⁻¹) • H.  Through the D box: the H-pushes emit
-- nothing and quarter-turn the box (GH is definitional), the S-power
-- emits nothing (ES) and shifts by nsum tk (− (− db)); composed, the
-- box map is (da , db) ↦ (da + nsum tk db , db) with everything else
-- emitting ₀.  All four coset accumulators drift by constants.

module OrdCZ-inj₁-cc (a₀ c₁' : Fin (₁₊ p-2)) where

  private
    cI : ℤ ₚ
    cI = ((₁₊ c₁' , λ ()) ⁻¹) .proj₁
    kHs : ℤ ₚ
    kHs = - (₁₊ a₀ * cI)
    tk : ℕ
    tk = toℕ kHs

  cst : ℤ ₚ → ℤ ₚ → E → ℤ ₚ → ℤ ₚ → C 2
  cst dd b e da db =
    inj₁ (((da , db) ∷ [] , e) ,
          (((₁₊ c₁' , dd) ∷ []) , ((₁₊ a₀ , b) , λ ())))

  z00c : ∀ (x : ℤ ₚ) → x + - ₀ ≡ x
  z00c x = Eq.trans (Eq.cong (x +_) neg0) (+-identityʳ x)
    where
    neg0 : - ₀ ≡ ₀
    neg0 = Eq.trans (Eq.sym (+-identityʳ (- z))) (+-inverseˡ z)
      where
      z : ℤ ₚ
      z = ₀

  cstC : ∀ {dd₁ dd₂ b₁ b₂ e₁ e₂ da₁ da₂ db : ℤ ₚ} →
    dd₁ ≡ dd₂ → b₁ ≡ b₂ → e₁ ≡ e₂ → da₁ ≡ da₂ →
    cst dd₁ b₁ e₁ da₁ db ≡ cst dd₂ b₂ e₂ da₂ db
  cstC {dd₂ = dd₂} {b₁ = b₁} {b₂ = b₂} {e₁ = e₁} {e₂ = e₂}
       {da₁ = da₁} {db = db} pdd pb pe pda =
    Eq.trans (Eq.cong (λ u → cst u b₁ e₁ da₁ db) pdd)
    (Eq.trans (Eq.cong (λ u → cst dd₂ u e₁ da₁ db) pb)
    (Eq.trans (Eq.cong (λ u → cst dd₂ b₂ u da₁ db) pe)
              (Eq.cong (λ u → cst dd₂ b₂ e₂ u db) pda)))

  private
    sbox : ℤ ₚ → ℤ ₚ → ℤ ₚ × ℤ ₚ
    sbox da db =
      TDw.push-D-w (- db , - - da) (S ^ tk) (TDw.ntH-^ TDw.ntH-S tk)
        .proj₂ .proj₂

  stepCZ : ∀ (dd b e da db : ℤ ₚ) →
    proj₂ (ract {1} (cst dd b e da db) (gate₂ CZ-gate))
    ≡ cst (dd + - ₁₊ a₀) (b + - ₁₊ c₁') e (da + nsum tk db) db
  stepCZ dd b e da db = Eq.cong₂ (λ dp ee → inj₁ ((dp ∷ [] , ee) ,
      (((₁₊ c₁' , dd + - ₁₊ a₀) ∷ []) , ((₁₊ a₀ , b + - ₁₊ c₁') , λ ()))))
    d-eq e-eq
    where
    d-eq : TDw.push-D-w (sbox da db) H TDw.ntH-H .proj₂ .proj₂
           ≡ (da + nsum tk db , db)
    d-eq = Eq.trans
      (Eq.cong (λ bx → TDw.push-D-w bx H TDw.ntH-H .proj₂ .proj₂)
        (GS tk (- db) (- - da)))
      (Eq.cong₂ _,_
        (Eq.cong₂ _+_ (-‿involutive da)
          (Eq.cong (nsum tk) (-‿involutive db)))
        (-‿involutive db))
    e-eq : e + - (TDw.push-D-w (da , db) (H ^ 3)
                    (TDw.ntH-^ TDw.ntH-H 3) .proj₁
                  + (TDw.push-D-w (- db , - - da) (S ^ tk)
                       (TDw.ntH-^ TDw.ntH-S tk) .proj₁
                     + TDw.push-D-w (sbox da db) H TDw.ntH-H .proj₁))
           ≡ e
    e-eq = Eq.trans
      (Eq.cong (λ z → e + - z)
        (Eq.trans (Eq.cong₂ _+_ (EH3 da db)
            (Eq.trans (Eq.cong₂ _+_ (ES tk (- db) (- - da))
                (EH (sbox da db .proj₁) (sbox da db .proj₂)))
              (+-identityʳ ₀)))
          (+-identityˡ ₀)))
      (z00c e)

  orbit : ∀ (k : ℕ) (dd b e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst dd b e da db) (CZ ^ k)) .proj₂
    ≡ cst (dd + nsum k (- ₁₊ a₀)) (b + nsum k (- ₁₊ c₁')) e
          (da + nsum k (nsum tk db)) db
  orbit zero dd b e da db =
    cstC (Eq.sym (+-identityʳ dd)) (Eq.sym (+-identityʳ b)) Eq.refl
         (Eq.sym (+-identityʳ da))
  orbit (suc zero) dd b e da db =
    Eq.trans (stepCZ dd b e da db)
      (cstC
        (Eq.cong (dd +_) (Eq.sym (+-identityʳ (- ₁₊ a₀))))
        (Eq.cong (b +_) (Eq.sym (+-identityʳ (- ₁₊ c₁'))))
        Eq.refl
        (Eq.cong (da +_) (Eq.sym (+-identityʳ (nsum tk db)))))
  orbit (suc (suc k)) dd b e da db =
    Eq.trans (Eq.cong (λ c → ((ract {1} ᵗ) c (CZ ^ suc k)) .proj₂)
        (stepCZ dd b e da db))
    (Eq.trans (orbit (suc k) (dd + - ₁₊ a₀) (b + - ₁₊ c₁') e
        (da + nsum tk db) db)
      (cstC
        (+-assoc dd (- ₁₊ a₀) (nsum (suc k) (- ₁₊ a₀)))
        (+-assoc b (- ₁₊ c₁') (nsum (suc k) (- ₁₊ c₁')))
        Eq.refl
        (+-assoc da (nsum tk db) (nsum (suc k) (nsum tk db)))))

  ordCZ-inj₁-cc-coset : ∀ (dd b e da db : ℤ ₚ) →
    ((ract {1} ᵗ) (cst dd b e da db) (CZ ^ p)) .proj₂
    ≡ ((ract {1} ᵗ) (cst dd b e da db) ε) .proj₂
  ordCZ-inj₁-cc-coset dd b e da db =
    Eq.trans (orbit p dd b e da db)
      (cstC
        (Eq.trans (Eq.cong (dd +_) (nsum-p≡0 (- ₁₊ a₀))) (+-identityʳ dd))
        (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- ₁₊ c₁'))) (+-identityʳ b))
        Eq.refl
        (Eq.trans (Eq.cong (da +_) (nsum-p≡0 (nsum tk db)))
                  (+-identityʳ da)))

------------------------------------------------------------------------
-- The ZM word through a D box acts as the symplectic scaling
-- diag(x , x⁻¹): the S-power stages are GS shifts, the H stages
-- definitional quarter-turns, and the composite telescopes.  This is
-- the cornerstone for the shape-crossing order-CZ branches, whose
-- drift directions contain ZM factors.

module _ (x* : ℤ* ₚ) where
  private
    xv  = x* .proj₁
    xIv = (x* ⁻¹) .proj₁
    tx  = toℕ xv
    txI = toℕ xIv
    inst = nztoℕ {y = xv} {neq0 = x* .proj₂}
    B₁n = λ (α β : ℤ ₚ) → β + nsum tx (- α)
    A₂n = λ (α β : ℤ ₚ) → - α + nsum txI (- B₁n α β)

  GZM : ∀ (α β : ℤ ₚ) →
    TDw.push-D-w (α , β) (ZM x*) (TDw.ntH-ZM x*) .proj₂ .proj₂
    ≡ (xv * α , xIv * β)
  GZM α β =
    Eq.trans (Eq.cong (λ bx → TDw.push-D-w bx
        (H • (S^ xIv • (H • (S^ xv • H))))
        (TDw.ntH-H TDw.•ⁿ (TDw.ntH-S^ xIv TDw.•ⁿ
          (TDw.ntH-H TDw.•ⁿ (TDw.ntH-S^ xv TDw.•ⁿ TDw.ntH-H))))
        .proj₂ .proj₂)
      (GS tx α β))
    (Eq.trans (Eq.cong (λ bx → TDw.push-D-w bx
        (H • (S^ xv • H))
        (TDw.ntH-H TDw.•ⁿ (TDw.ntH-S^ xv TDw.•ⁿ TDw.ntH-H))
        .proj₂ .proj₂)
      (GS txI (B₁n α β) (- α)))
    (Eq.trans (Eq.cong (λ bx → TDw.push-D-w bx H TDw.ntH-H .proj₂ .proj₂)
      (GS tx (A₂n α β) (- B₁n α β)))
      (Eq.cong₂ _,_ (fst-full α β) (snd-full α β))))
    where
    open Eq.≡-Reasoning
    r1 : ∀ (α : ℤ ₚ) → nsum tx (- α) ≡ xv * - α
    r1 α = nsum-* xv (- α)
    inner1 : ∀ (α β : ℤ ₚ) → - (β + xv * - α) ≡ - β + xv * α
    inner1 α β = Eq.trans
      (Eq.cong (λ z → - (β + z)) (Eq.sym (-‿distribʳ-* xv α)))
      (Eq.trans (Eq.sym (-‿+-comm β (- (xv * α))))
        (Eq.cong (- β +_) (-‿involutive (xv * α))))
    A₂-alg : ∀ (α β : ℤ ₚ) → - α + xIv * - (β + xv * - α) ≡ - (xIv * β)
    A₂-alg α β = begin
      - α + xIv * - (β + xv * - α)
        ≡⟨ Eq.cong (λ z → - α + xIv * z) (inner1 α β) ⟩
      - α + xIv * (- β + xv * α)
        ≡⟨ Eq.cong (- α +_) (*-distribˡ-+ xIv (- β) (xv * α)) ⟩
      - α + (xIv * - β + xIv * (xv * α))
        ≡⟨ Eq.cong (- α +_) (Eq.cong₂ _+_
             (Eq.sym (-‿distribʳ-* xIv β))
             (Eq.trans (Eq.sym (*-assoc xIv xv α))
               (Eq.trans (Eq.cong (_* α) (lemma-⁻¹ˡ xv {{inst}}))
                         (*-identityˡ α)))) ⟩
      - α + (- (xIv * β) + α)
        ≡⟨ Eq.cong (- α +_) (+-comm (- (xIv * β)) α) ⟩
      - α + (α + - (xIv * β))
        ≡⟨ Eq.sym (+-assoc (- α) α (- (xIv * β))) ⟩
      (- α + α) + - (xIv * β)
        ≡⟨ Eq.cong (_+ - (xIv * β)) (+-inverseˡ α) ⟩
      ₀ + - (xIv * β)
        ≡⟨ +-identityˡ (- (xIv * β)) ⟩
      - (xIv * β) ∎
    A₂-chain : ∀ (α β : ℤ ₚ) → A₂n α β ≡ - (xIv * β)
    A₂-chain α β = Eq.trans
      (Eq.cong (λ z → - α + nsum txI (- (β + z))) (r1 α))
      (Eq.trans (Eq.cong (- α +_) (nsum-* xIv (- (β + xv * - α))))
        (A₂-alg α β))
    snd-full : ∀ (α β : ℤ ₚ) → - A₂n α β ≡ xIv * β
    snd-full α β = Eq.trans (Eq.cong -_ (A₂-chain α β))
      (-‿involutive (xIv * β))
    fst-full : ∀ (α β : ℤ ₚ) →
      - B₁n α β + nsum tx (- A₂n α β) ≡ xv * α
    fst-full α β = begin
      - B₁n α β + nsum tx (- A₂n α β)
        ≡⟨ Eq.cong₂ (λ u v → - (β + u) + nsum tx v)
             (r1 α) (snd-full α β) ⟩
      - (β + xv * - α) + nsum tx (xIv * β)
        ≡⟨ Eq.cong₂ _+_ (inner1 α β) (nsum-* xv (xIv * β)) ⟩
      (- β + xv * α) + xv * (xIv * β)
        ≡⟨ Eq.cong ((- β + xv * α) +_)
             (Eq.trans (Eq.sym (*-assoc xv xIv β))
               (Eq.trans (Eq.cong (_* β) (lemma-⁻¹ʳ xv {{inst}}))
                         (*-identityˡ β))) ⟩
      (- β + xv * α) + β
        ≡⟨ Eq.cong (_+ β) (+-comm (- β) (xv * α)) ⟩
      (xv * α + - β) + β
        ≡⟨ +-assoc (xv * α) (- β) β ⟩
      xv * α + (- β + β)
        ≡⟨ Eq.cong (xv * α +_) (+-inverseˡ β) ⟩
      xv * α + ₀
        ≡⟨ +-identityʳ (xv * α) ⟩
      xv * α ∎

  -- The ZM word emits nothing: every stage's emission is ₀ (ES/EH at
  -- the η-projections of the intermediate boxes).
  EZM : ∀ (α β : ℤ ₚ) →
    TDw.push-D-w (α , β) (ZM x*) (TDw.ntH-ZM x*) .proj₁ ≡ ₀
  EZM α β =
    Eq.trans (Eq.cong₂ _+_ (ES tx α β)
      (Eq.cong₂ _+_ (EH (P₁ .proj₁) (P₁ .proj₂))
        (Eq.cong₂ _+_ (ES txI (P₁ .proj₂) (- P₁ .proj₁))
          (Eq.cong₂ _+_ (EH (P₂ .proj₁) (P₂ .proj₂))
            (Eq.cong₂ _+_ (ES tx (P₂ .proj₂) (- P₂ .proj₁))
              (EH (P₃ .proj₁) (P₃ .proj₂)))))))
    (Eq.trans (+-identityˡ (₀ + (₀ + (₀ + (₀ + ₀)))))
    (Eq.trans (+-identityˡ (₀ + (₀ + (₀ + ₀))))
    (Eq.trans (+-identityˡ (₀ + (₀ + ₀)))
    (Eq.trans (+-identityˡ (₀ + ₀)) (+-identityˡ ₀)))))
    where
    P₁ = TDw.push-D-w (α , β) (S ^ tx)
           (TDw.ntH-^ TDw.ntH-S tx) .proj₂ .proj₂
    P₂ = TDw.push-D-w (P₁ .proj₂ , - P₁ .proj₁) (S ^ txI)
           (TDw.ntH-^ TDw.ntH-S txI) .proj₂ .proj₂
    P₃ = TDw.push-D-w (P₂ .proj₂ , - P₂ .proj₁) (S ^ tx)
           (TDw.ntH-^ TDw.ntH-S tx) .proj₂ .proj₂
