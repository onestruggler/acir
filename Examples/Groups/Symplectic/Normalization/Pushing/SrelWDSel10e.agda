------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on doubly-inj₂ boxes (₀,b1)/(₁₊a2',₁₊b2''), branch B:
-- the S⁻¹↑-shifted slot Sv = b₂ + a₂ is nonzero (witness w), so all
-- three H↑ escapes are hpad units and the residual identity is the
-- Borel-normalized identityB from SrelWDSel10d.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10e
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Fin using (Fin ; toℕ)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10d
  p-2 p-prime using (module BValues ; identityB)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    WB : Word (Gen (₂₊ m))
    WB = H ↑ • (CZ • (H ↑) ^ 3)

  c10-go-0aaB : ∀ (b1 : ℤ ₚ) (a2' b2'' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w →
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₁₊ b2'') , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₁₊ b2'') , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-0aaB b1 a2' b2'' w lm2 eq-w = resid≈ , coset≡
    where
    open BValues a2' b2'' w eq-w

    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , ₁₊ b2'') , lm2)

    nfixa : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    bfixr1B : ₁₊ b2'' + nsum p-1 (- ₁₊ a2') ≡ ₁₊ w
    bfixr1B = Eq.trans (Eq.cong (₁₊ b2'' +_) nfixa) eq-w

    bfixr3B : - ₁₊ a2' + nsum p-1 (- ₁₊ w) ≡ ₁₊ b2''
    bfixr3B = Eq.trans (Eq.cong (- ₁₊ a2' +_)
        (Eq.trans (nsum-p-1 (- ₁₊ w)) (-‿involutive (₁₊ w))))
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (Eq.sym eq-w))
      (Eq.trans (+-comm (- ₁₊ a2') (₁₊ b2'' + ₁₊ a2'))
      (Eq.trans (+-assoc (₁₊ b2'') (₁₊ a2') (- ₁₊ a2'))
      (Eq.trans (Eq.cong (₁₊ b2'' +_) (+-inverseʳ (₁₊ a2')))
        (+-identityʳ (₁₊ b2''))))))

    bfixr6B : - ₁₊ w + nsum p-1 (- ₁₊ b2'') ≡ - ₁₊ a2'
    bfixr6B = Eq.trans (Eq.cong (- ₁₊ w +_)
        (Eq.trans (nsum-p-1 (- ₁₊ b2'')) (-‿involutive (₁₊ b2''))))
      (Eq.trans (Eq.cong (λ t → - t + ₁₊ b2'') (Eq.sym eq-w))
      (Eq.trans (Eq.cong (_+ ₁₊ b2'')
          (Eq.sym (-‿+-comm (₁₊ b2'') (₁₊ a2'))))
      (Eq.trans (Eq.cong (_+ ₁₊ b2'')
          (+-comm (- ₁₊ b2'') (- ₁₊ a2')))
      (Eq.trans (+-assoc (- ₁₊ a2') (- ₁₊ b2'') (₁₊ b2''))
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (+-inverseˡ (₁₊ b2'')))
        (+-identityʳ (- ₁₊ a2')))))))

    d1fixB : (b1 + - ₁₊ a2') + - ₁₊ b2'' ≡ b1 + - ₁₊ w
    d1fixB = Eq.trans (+-assoc b1 (- ₁₊ a2') (- ₁₊ b2''))
      (Eq.cong (b1 +_)
        (Eq.trans (+-comm (- ₁₊ a2') (- ₁₊ b2''))
        (Eq.trans (-‿+-comm (₁₊ b2'') (₁₊ a2'))
          (Eq.cong -_ eq-w))))

    cFB : C (₃₊ m)
    cFB = inj₂ ((₀ , b1 + - ₁₊ w) , inj₂ ((₁₊ b2'' , - ₁₊ a2') , lm2))

    -- LHS: the middle escape is the (a₂,b₂) hpad unit.
    L-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≡
            WB • ((ZM q* • S^ rv) ↑ • WB)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.trans
        (Eq.cong (λ v → (Hdir (₁₊ a2' , v) ↓ᵏ m) ↑) (e0 (₁₊ b2'')))
        (Eq.cong _↑ (hpad a2' b2'')))
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ ((₀ , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2)))
          (e0 (₁₊ b2'')))))

    L-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡ cFB
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₀ , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2)))
          (e0 (₁₊ b2''))))
      (Eq.cong₂ (λ v u → inj₂ ((₀ , v) , inj₂ ((₁₊ b2'' , u) , lm2)))
        d1fixB
        (e0 (- ₁₊ a2')))

    -- RHS letters.
    E₁raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , ₁₊ b2'') , lm2)) S⁻¹) .proj₁
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ w , - ₁₊ a2') , lm2)) S⁻¹) .proj₁
    E₆raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ b2'' , - ₁₊ w) , lm2)) S⁻¹) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1fixB : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (S⁻¹ ↑)) ≡
             (E₁raw ↑ , inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₁₊ w) , lm2)))
    r1fixB = Eq.trans (ract-↑-≡ (₀ , b1) lm S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , ₁₊ b2'') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') (₁₊ b2'') (λ ()))
                (Eq.cong (₁₊ a2' ,_) bfixr1B))))))

    r3fixB : ((ract2 ᵗ) (inj₂ ((₀ , b1) ,
               inj₂ ((₁₊ w , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
             (E₃raw ↑ , inj₂ ((₀ , b1) , inj₂ ((₁₊ w , ₁₊ b2'') , lm2)))
    r3fixB = Eq.trans
      (ract-↑-≡ (₀ , b1) (inj₂ ((₁₊ w , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ w , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ w) (- ₁₊ a2') (λ ()))
                (Eq.cong (₁₊ w ,_) bfixr3B))))))

    r5fixB : ((ract2 ᵗ) (inj₂ ((₀ , b1 + - ₁₊ w) ,
               inj₂ ((₁₊ w , ₁₊ b2'' + - ₀) , lm2))) (H ↑)) ≡
             ((ZM q₂* • S^ r₂v) ↑ ,
              inj₂ ((₀ , b1 + - ₁₊ w) ,
                inj₂ ((₁₊ b2'' , - ₁₊ w) , lm2)))
    r5fixB = Eq.trans
      (Eq.cong (λ v → ((Hdir (₁₊ w , v) ↓ᵏ m) ↑ ,
          inj₂ ((₀ , b1 + - ₁₊ w) , inj₂ (Hd' (₁₊ w , v) , lm2))))
        (e0 (₁₊ b2'')))
      (Eq.cong₂ _,_ (Eq.cong _↑ (hpad w b2'')) Eq.refl)

    r6fixB : ((ract2 ᵗ) (inj₂ ((₀ , b1 + - ₁₊ w) ,
               inj₂ ((₁₊ b2'' , - ₁₊ w) , lm2))) (S⁻¹ ↑)) ≡
             (E₆raw ↑ , cFB)
    r6fixB = Eq.trans
      (ract-↑-≡ (₀ , b1 + - ₁₊ w) (inj₂ ((₁₊ b2'' , - ₁₊ w) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1 + - ₁₊ w) , c))
          (Eq.trans (ract-S^-coset (₁₊ b2'' , - ₁₊ w) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ b2'') (- ₁₊ w) (λ ()))
                (Eq.cong (₁₊ b2'' ,_) bfixr6B))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            E₁raw ↑ • ((ZM q₁* • S^ r₁v) ↑ •
              (E₃raw ↑ • (WB • ((ZM q₂* • S^ r₂v) ↑ •
                (E₆raw ↑ • S ^ p-1)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1fixB)
      (Eq.cong (λ t → E₁raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_
          (Eq.trans (Eq.cong _↑ (hpad a2' w)) Eq.refl)
          Eq.refl)
      (Eq.cong (λ t → (ZM q₁* • S^ r₁v) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3fixB)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.cong (λ t → WB • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5fixB)
      (Eq.cong (λ t → (ZM q₂* • S^ r₂v) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6fixB)
      (Eq.cong (λ t → E₆raw ↑ • t)
        (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) cFB u) .proj₁) (↓-pow-S p-1))
          (ract-S^-resid-a0 (b1 + - ₁₊ w)
            (inj₂ ((₁₊ b2'' , - ₁₊ a2') , lm2)) p-1))))))))))))

    Rclean : E₁raw ↑ • ((ZM q₁* • S^ r₁v) ↑ •
               (E₃raw ↑ • (WB • ((ZM q₂* • S^ r₂v) ↑ •
                 (E₆raw ↑ • S ^ p-1))))) ≈
             (ZM q₁* ↑ • S^ r₁v ↑) •
               (WB • ((ZM q₂* ↑ • S^ r₂v ↑) • S⁻¹))
    Rclean =
      trans (trans (cleft (lemma-cong↑ E₁raw ε
          (ract-S^-resid-a+ (₁₊ a2' , ₁₊ b2'') lm2 p-1 (λ ())))) left-unit)
      (cright (trans (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ w , - ₁₊ a2') lm2 p-1 (λ ())))) left-unit)
        (cright (cright (trans (cleft (lemma-cong↑ E₆raw ε
          (ract-S^-resid-a+ (₁₊ b2'' , - ₁₊ w) lm2 p-1 (λ ()))))
          left-unit)))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (identityB a2' b2'' w eq-w)
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cFB
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1fixB)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3fixB)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5fixB)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6fixB)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) cFB u) .proj₂) (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₀ , b1 + - ₁₊ w)
          (inj₂ ((₁₊ b2'' , - ₁₊ a2') , lm2)) p-1)
        (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ b2'' , - ₁₊ a2') , lm2)))
          (it-dDS-a0 p-1 (b1 + - ₁₊ w))))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
