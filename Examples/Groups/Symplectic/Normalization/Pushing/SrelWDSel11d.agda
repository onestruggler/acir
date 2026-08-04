------------------------------------------------------------------------
-- Presentations of groups
--
-- The branch-β orbit for selinger-c11 on doubly-inj₂ boxes
-- (₀,₁₊b1')/(₁₊a2',b2).  With b₁ = a₂ + x the two clause-4 pads and
-- the Borel H-escape all become functions of Q = b₁/x, which is
-- exactly the shape idc11c consumes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11d
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11c
  p-2 p-prime using (idc11c)

------------------------------------------------------------------------
-- Ring facts.  Every value cast in this orbit is one instance of
-- split: dividing a sum by one of its summands peels off a ₁.

module _ where

  split : ∀ (c d i : ℤ ₚ) → d * i ≡ ₁ → - ((c + d) * i) ≡ - ₁ + - (c * i)
  split c d i di1 =
    Eq.trans (Eq.cong -_ (*-distribʳ-+ i c d))
    (Eq.trans (Eq.cong (λ t → - (c * i + t)) di1)
    (Eq.trans (Eq.sym (-‿+-comm (c * i) ₁))
      (+-comm (- (c * i)) (- ₁))))

------------------------------------------------------------------------
-- The orbit.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract3 = ract {₂₊ m}

    W3d : Word (Gen (₂₊ m))
    W3d = H ↑ • (CZ • (H ↑) ^ 3)

    padof : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    padof u w =
      H • (H ↑ • (CZ • (S^ u • (H ^ 3 • (S^ w ↑ • (H ↑) ^ 3)))))

  c11-go-0b2β : ∀ (b2 : ℤ ₚ) (b1' a2' x : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ₁₊ b1' + - ₁₊ a2' ≡ ₁₊ x →
    ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-0b2β b2 b1' a2' x lm2 eq-X = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    instB = nztoℕ {y = ₁₊ b1'} {neq0 = λ ()}
    instA = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}
    instX = nztoℕ {y = ₁₊ x} {neq0 = λ ()}

    iB = ((₁₊ b1' , λ ()) ⁻¹) .proj₁
    iA = ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    iX = ((₁₊ x , λ ()) ⁻¹) .proj₁

    Q : ℤ* ₚ
    Q = (₁₊ b1' , λ ()) *' ((₁₊ x , λ ()) ⁻¹)

    BiB : ₁₊ b1' * iB ≡ ₁
    BiB = lemma-⁻¹ʳ (₁₊ b1') {{instB}}

    AiA : ₁₊ a2' * iA ≡ ₁
    AiA = lemma-⁻¹ʳ (₁₊ a2') {{instA}}

    XiX : ₁₊ x * iX ≡ ₁
    XiX = lemma-⁻¹ʳ (₁₊ x) {{instX}}

    -- b₁ = a₂ + x, in the three arrangements the casts need.
    Beq : ₁₊ a2' + ₁₊ x ≡ ₁₊ b1'
    Beq = Eq.trans (Eq.cong (₁₊ a2' +_) (Eq.sym eq-X))
      (Eq.trans (Eq.sym (+-assoc (₁₊ a2') (₁₊ b1') (- ₁₊ a2')))
      (Eq.trans (Eq.cong (_+ - ₁₊ a2') (+-comm (₁₊ a2') (₁₊ b1')))
      (Eq.trans (+-assoc (₁₊ b1') (₁₊ a2') (- ₁₊ a2'))
      (Eq.trans (Eq.cong (₁₊ b1' +_) (+-inverseʳ (₁₊ a2')))
        (+-identityʳ (₁₊ b1'))))))

    BeqX : ₁₊ x + ₁₊ a2' ≡ ₁₊ b1'
    BeqX = Eq.trans (+-comm (₁₊ x) (₁₊ a2')) Beq

    AeqNX : - ₁₊ x + ₁₊ b1' ≡ ₁₊ a2'
    AeqNX = Eq.trans (Eq.cong (- ₁₊ x +_) (Eq.sym BeqX))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ x) (₁₊ x) (₁₊ a2')))
      (Eq.trans (Eq.cong (_+ ₁₊ a2') (+-inverseˡ (₁₊ x)))
        (+-identityˡ (₁₊ a2'))))

    -- Q⁻¹ = x/b₁.
    vQinv : ₁₊ x * iB ≡ (Q ⁻¹) .proj₁
    vQinv = Eq.sym (Eq.trans (inv-distrib (₁₊ b1' , λ ()) ((₁₊ x , λ ()) ⁻¹))
      (Eq.trans (Eq.cong (iB *_) (inv-involutive (₁₊ x , λ ())))
        (*-comm iB (₁₊ x))))

    -- The four pad slots.
    vU : - ₁₊ a2' * iX ≡ ₁ + - (Q .proj₁)
    vU = Eq.sym
      (Eq.trans (Eq.cong (λ t → ₁ + - (t * iX)) (Eq.sym Beq))
      (Eq.trans (Eq.cong (₁ +_) (split (₁₊ a2') (₁₊ x) iX XiX))
      (Eq.trans (Eq.sym (+-assoc ₁ (- ₁) (- (₁₊ a2' * iX))))
      (Eq.trans (Eq.cong (_+ - (₁₊ a2' * iX)) (+-inverseʳ ₁))
      (Eq.trans (+-identityˡ (- (₁₊ a2' * iX)))
        (-‿distribˡ-* (₁₊ a2') iX))))))

    vS : - ₁₊ b1' * iA ≡ - ₁ + (- ₁₊ x * iA)
    vS = Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b1') iA))
      (Eq.trans (Eq.cong (λ t → - (t * iA)) (Eq.sym BeqX))
      (Eq.trans (split (₁₊ x) (₁₊ a2') iA AiA)
        (Eq.cong (- ₁ +_) (-‿distribˡ-* (₁₊ x) iA))))

    vR : - ₁₊ a2' * iB ≡ - ₁ + (Q ⁻¹) .proj₁
    vR = Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a2') iB))
      (Eq.trans (Eq.cong (λ t → - (t * iB)) (Eq.sym AeqNX))
      (Eq.trans (split (- ₁₊ x) (₁₊ b1') iB BiB)
        (Eq.cong (- ₁ +_)
          (Eq.trans
            (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribˡ-* (₁₊ x) iB)))
              (-‿involutive (₁₊ x * iB)))
            vQinv))))

    -- Coset arithmetic.
    nfixx : nsum p-1 (- ₁₊ x) ≡ ₁₊ x
    nfixx = Eq.trans (nsum-p-1 (- ₁₊ x)) (-‿involutive (₁₊ x))

    nfixa : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    bfix3 : - ₀ + nsum p-1 (- ₁₊ b1') ≡ ₁₊ b1'
    bfix3 = Eq.trans (Eq.cong₂ _+_ -0#≈0#
        (Eq.trans (nsum-p-1 (- ₁₊ b1')) (-‿involutive (₁₊ b1'))))
      (+-identityˡ (₁₊ b1'))

    nBA : - ₁₊ b1' + ₁₊ a2' ≡ - ₁₊ x
    nBA = Eq.trans (Eq.cong (λ t → - t + ₁₊ a2') (Eq.sym Beq))
      (Eq.trans (Eq.cong (_+ ₁₊ a2')
          (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ x))))
      (Eq.trans (+-assoc (- ₁₊ a2') (- ₁₊ x) (₁₊ a2'))
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (+-comm (- ₁₊ x) (₁₊ a2')))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ a2') (₁₊ a2') (- ₁₊ x)))
      (Eq.trans (Eq.cong (_+ - ₁₊ x) (+-inverseˡ (₁₊ a2')))
        (+-identityˡ (- ₁₊ x)))))))

    cd1R : - ₁₊ b1' + nsum p-1 (- ₁₊ x) ≡ - ₁₊ a2'
    cd1R = Eq.trans (Eq.cong (- ₁₊ b1' +_) nfixx)
      (Eq.trans (Eq.cong (λ t → - t + ₁₊ x) (Eq.sym Beq))
      (Eq.trans (Eq.cong (_+ ₁₊ x)
          (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ x))))
      (Eq.trans (+-assoc (- ₁₊ a2') (- ₁₊ x) (₁₊ x))
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (+-inverseˡ (₁₊ x)))
        (+-identityʳ (- ₁₊ a2'))))))

    cd2R : (b2 + - ₁₊ b1') + nsum p-1 (- ₁₊ a2') ≡ b2 + - ₁₊ x
    cd2R = Eq.trans (Eq.cong ((b2 + - ₁₊ b1') +_) nfixa)
      (Eq.trans (+-assoc b2 (- ₁₊ b1') (₁₊ a2'))
        (Eq.cong (b2 +_) nBA))

    cd1L : - ₀ + - ₁₊ a2' ≡ - ₁₊ a2'
    cd1L = Eq.trans (Eq.cong (_+ - ₁₊ a2') -0#≈0#)
      (+-identityˡ (- ₁₊ a2'))

    cd2L : (b2 + - ₀) + - ₁₊ x ≡ b2 + - ₁₊ x
    cd2L = Eq.cong (_+ - ₁₊ x) (e0 b2)

    hdfixb : Hd' (₀ , ₁₊ x) ≡ (₁₊ x , - ₀)
    hdfixb = Eq.refl

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ x , - ₁₊ a2') , inj₂ ((₁₊ a2' , b2 + - ₁₊ x) , lm2))

    -- LHS.
    PADL = padof (₁ + - (Q .proj₁)) (- ₁₊ x * iA)

    PADLfix : ((ract3 ᵗ) (inj₂ ((₁₊ x , - ₀) ,
                inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) CZ) .proj₁ ≡ PADL
    PADLfix = Eq.trans (padSA x a2' (- ₀) (b2 + - ₀))
      (Eq.cong (λ s → H • (H ↑ • (CZ • (s • (H ^ 3 •
          (S^ (- ₁₊ x * iA) ↑ • (H ↑) ^ 3))))))
        (Eq.cong S^ vU))

    L-fix : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡ W3d • (ε • PADL)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₀ , v) ↓ᵏ (₁₊ m)) eq-X)
      (Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₁)
          (Eq.trans
            (Eq.cong₂ (λ v w → inj₂ (Hd' (₀ , v) ,
                inj₂ ((₁₊ a2' , w) , lm2)))
              eq-X Eq.refl)
            (Eq.cong (λ d → inj₂ (d ,
                inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
              hdfixb)))
        PADLfix))

    L-c : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₂)
        (Eq.trans
          (Eq.cong₂ (λ v w → inj₂ (Hd' (₀ , v) ,
              inj₂ ((₁₊ a2' , w) , lm2)))
            eq-X Eq.refl)
          (Eq.cong (λ d → inj₂ (d ,
              inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
            hdfixb)))
      (Eq.cong₂ (λ v w → inj₂ ((₁₊ x , v) , inj₂ ((₁₊ a2' , w) , lm2)))
        cd1L cd2L)

    -- RHS.
    PADR = padof (- ₁ + (Q ⁻¹) .proj₁) (- ₁ + (- ₁₊ x * iA))

    HD : Word (Gen (₂₊ m))
    HD = ZM Q • S^ ((Q ⁻¹) .proj₁)

    E₃raw = ((ract3 ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) (S ^ p-1)) .proj₁
    E₆raw = ((ract3 ᵗ) (inj₂ ((₁₊ x , - ₁₊ b1') ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (S ^ p-1)) .proj₁
    E₇raw = ((ract {₁₊ m} ᵗ)
              (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) S⁻¹) .proj₁

    REST5d = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    r1 : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , ₁₊ b1') , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (₁₊ b1') lm p-1)
        (Eq.trans (ract-S^-coset (₀ , ₁₊ b1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 (₁₊ b1')))))

    r3 : ((ract3 ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) (S⁻¹ ↓)) ≡
         (E₃raw , inj₂ ((₁₊ b1' , ₁₊ b1') , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ b1' , - ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ b1') (- ₀) (λ ()))
              (Eq.cong (₁₊ b1' ,_) bfix3)))))

    PADRfix : ((ract3 ᵗ) (inj₂ ((₁₊ b1' , ₁₊ b1') ,
                inj₂ ((₁₊ a2' , b2) , lm2))) CZ) .proj₁ ≡ PADR
    PADRfix = Eq.trans (padSA b1' a2' (₁₊ b1') b2)
      (Eq.cong₂
        (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
        (Eq.cong S^ vR)
        (Eq.cong (λ z → S^ z ↑) vS))

    r5 : ((ract3 ᵗ) (inj₂ ((₁₊ b1' , ₁₊ b1' + - ₁₊ a2') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (H ↓)) ≡
         (HD , inj₂ ((₁₊ x , - ₁₊ b1') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)))
    r5 = Eq.trans
      (Eq.cong (λ v → ((Hdir (₁₊ b1' , v) ↓ᵏ (₁₊ m)) ,
          inj₂ (Hd' (₁₊ b1' , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))))
        eq-X)
      (Eq.cong (λ w → (w , inj₂ ((₁₊ x , - ₁₊ b1') ,
          inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))))
        (Eq.trans (hpad b1' x) (Eq.cong (λ z → ZM Q • S^ z) vQinv)))

    r6 : ((ract3 ᵗ) (inj₂ ((₁₊ x , - ₁₊ b1') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (S⁻¹ ↓)) ≡
         (E₆raw , inj₂ ((₁₊ x , - ₁₊ a2') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ x , - ₁₊ b1') ,
          inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ x , - ₁₊ b1')
            (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)))
            (Eq.trans (it-dDS-nz p-1 (₁₊ x) (- ₁₊ b1') (λ ()))
              (Eq.cong (₁₊ x ,_) cd1R)))))

    r7 : ((ract3 ᵗ) (inj₂ ((₁₊ x , - ₁₊ a2') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (S⁻¹ ↑)) ≡
         (E₇raw ↑ , cF)
    r7 = Eq.trans
      (ract-↑-≡ (₁₊ x , - ₁₊ a2')
        (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ x , - ₁₊ a2') , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2 + - ₁₊ b1') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans
                (it-dDS-nz p-1 (₁₊ a2') (b2 + - ₁₊ b1') (λ ()))
                (Eq.cong (₁₊ a2' ,_) cd2R))))))

    R-fix : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            S ^ p-1 • ((Hdir (₀ , ₁₊ b1') ↓ᵏ (₁₊ m)) •
              (E₃raw • (PADR • (HD • (E₆raw • E₇raw ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5d)) .proj₁)
          r1)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → (Hdir (₀ , ₁₊ b1') ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (CZ • REST5d)) .proj₁)
          r3)
      (Eq.cong (λ t → E₃raw • t)
      (Eq.trans (Eq.cong₂ _•_ PADRfix Eq.refl)
      (Eq.cong (λ t → PADR • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          r5)
      (Eq.cong (λ t → HD • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → E₆raw • t) (Eq.cong proj₁ r7)))))))))))

    Rclean : S ^ p-1 • ((Hdir (₀ , ₁₊ b1') ↓ᵏ (₁₊ m)) •
               (E₃raw • (PADR • (HD • (E₆raw • E₇raw ↑))))) ≈
             S⁻¹ • (PADR • HD)
    Rclean =
      trans (cright left-unit)
      (trans (cright (trans (cleft
          (ract-S^-resid-a+ (₁₊ b1' , - ₀) lm p-1 (λ ()))) left-unit))
        (cright (cright (trans (cright
          (trans (cleft (ract-S^-resid-a+ (₁₊ x , - ₁₊ b1')
              (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) p-1 (λ ())))
          (trans left-unit
            (lemma-cong↑ E₇raw ε
              (ract-S^-resid-a+ (₁₊ a2' , b2 + - ₁₊ b1') lm2 p-1
                (λ ()))))))
          right-unit))))

    resid≈ : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (cright left-unit)
      (trans (idc11c Q (- ₁₊ x * iA))
      (sym (trans (refl' R-fix) Rclean))))

    R-c : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5d)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (CZ • REST5d)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          r5)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
        (Eq.cong proj₂ r7))))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
                (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
