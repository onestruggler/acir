------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₁₊a1',b1)/(₁₊a2',b2), branch αα:
-- b₁ ≡ a₂ and b₁ ≡ -a₁ together make the first clause-4 pad the
-- value-1 one, both middle H's escape as HH, and the second CZ is
-- top-conjugated.  What is left is the axiom plus cancellations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11h
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
  using (-0#≈0# ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S ; H↑3H↑≈ε)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (H5 ; SSinv ; SinvupS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime using (SdownW)

------------------------------------------------------------------------
-- The branch-αα residual identity.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑)

  private
    PAD1h : Word (Gen (₂₊ m))
    PAD1h = H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))

    W3h : Word (Gen (₂₊ m))
    W3h = H ↑ • (CZ • (H ↑) ^ 3)

    HWh : ∀ (w : Word (Gen (₁₊ m))) → H • w ↑ ≈ w ↑ • H
    HWh w = lemma-comm-H-w↑ w

    botup3 : (H ↑) ^ 3 • HH ≈ HH • (H ↑) ^ 3
    botup3 = sym (comm⇒pow-comm {w = H} {v = H ↑} 2 3
      (lemma-comm-H-w↑ H))

    SupHH : S {m} ↑ • HH ≈ HH • S ↑
    SupHH = sym (comm⇒pow-comm {w = H} {v = S ↑} 2 1
      (lemma-comm-H-w↑ S))

    SupCZ : S {m} ↑ • CZ ≈ CZ • S ↑
    SupCZ = sym (axiom comm-CZ-S↑)

    SinvHuph : S⁻¹ • H ↑ ≈ H ↑ • S⁻¹
    SinvHuph = comm⇒pow-comm {w = S} {v = H ↑} p-1 1
      (lemma-comm-S-w↑ H)

    fixdownh : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdownh = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

  id11h : PAD1h • (HH • W3h) ≈ HH • (S⁻¹ • (W3h • (H • S⁻¹)))
  id11h = begin
    PAD1h • (HH • W3h)
      ≈⟨ trans assoc (cright (trans assoc (cright (trans assoc
           (cright (trans assoc (cright (trans assoc
             (cright assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ •
      ((H ↑) ^ 3 • (HH • W3h)))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
           (trans (cleft botup3)
           (trans assoc
           (trans (cright (sym assoc))
           (trans (cright (cleft H↑3H↑≈ε))
             (cright left-unit))))))))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (HH • (CZ • (H ↑) ^ 3)))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft SupHH) assoc)))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (HH • (S ↑ • (CZ • (H ↑) ^ 3)))))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc) (cleft H5))))) ⟩
    H • (H ↑ • (CZ • (S • (H • (S ↑ • (CZ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft SupCZ) assoc)))))) ⟩
    H • (H ↑ • (CZ • (S • (H • (CZ • (S ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (axiom comm-CZ-S↓)) assoc))) ⟩
    H • (H ↑ • (S • (CZ • (H • (CZ • (S ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (trans (cright (sym assoc))
           (trans (sym assoc)
             (cleft (trans (axiom selinger-c11)
               (refl' fixdownh))))))) ⟩
    H • (H ↑ • (S • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))) •
      (S ↑ • (H ↑) ^ 3))))
      ≈⟨ cright (cright (trans (cright assoc)
           (trans (sym assoc) (trans (cleft SSinv) left-unit)))) ⟩
    H • (H ↑ • ((H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))) •
      (S ↑ • (H ↑) ^ 3)))
      ≈⟨ cright (cright (trans assoc (cright (trans assoc (cright
           (trans assoc (cright (trans assoc (cright assoc))))))))) ⟩
    H • (H ↑ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (S ↑ • (H ↑) ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft SinvupS) left-unit))))))))  ⟩
    H • (H ↑ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • (H ↑) ^ 3))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (HWh H))) assoc)) ⟩
    H • (H • (H ↑ • (S⁻¹ • (CZ • (H • (S⁻¹ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (sym SinvHuph)) assoc))) ⟩
    H • (H • (S⁻¹ • (H ↑ • (CZ • (H • (S⁻¹ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (cright (SdownW (H ^ 3)))
           (trans (sym assoc)
             (trans (cleft (HWh (H ^ 3))) assoc))))))) ⟩
    H • (H • (S⁻¹ • (H ↑ • (CZ • ((H ↑) ^ 3 • (H • S⁻¹))))))
      ≈⟨ sym (trans assoc (cright (cright (cright
           (trans assoc (cright assoc)))))) ⟩
    HH • (S⁻¹ • (W3h • (H • S⁻¹))) ∎

------------------------------------------------------------------------
-- The branch-αα orbit.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract3 = ract {₂₊ m}

    PAD1h' : Word (Gen (₂₊ m))
    PAD1h' = H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))

    W3h' : Word (Gen (₂₊ m))
    W3h' = H ↑ • (CZ • (H ↑) ^ 3)

  c11-go-aaαα : ∀ (b1 b2 : ℤ ₚ) (a1' a2' : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) → b1 + - ₁₊ a2' ≡ ₀ → b1 + ₁₊ a1' ≡ ₀ →
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-aaαα b1 b2 a1' a2' lm2 eqY eqZ = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    instA1 = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instA2 = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}

    iA1 = ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    iA2 = ((₁₊ a2' , λ ()) ⁻¹) .proj₁

    -- b₁ = a₂ = -a₁.
    b1A2 : b1 ≡ ₁₊ a2'
    b1A2 = Eq.trans (Eq.sym (+-identityʳ b1))
      (Eq.trans (Eq.cong (b1 +_) (Eq.sym (+-inverseˡ (₁₊ a2'))))
      (Eq.trans (Eq.sym (+-assoc b1 (- ₁₊ a2') (₁₊ a2')))
      (Eq.trans (Eq.cong (_+ ₁₊ a2') eqY) (+-identityˡ (₁₊ a2')))))

    b1nA1 : b1 ≡ - ₁₊ a1'
    b1nA1 = Eq.trans (Eq.sym (+-identityʳ b1))
      (Eq.trans (Eq.cong (b1 +_) (Eq.sym (+-inverseʳ (₁₊ a1'))))
      (Eq.trans (Eq.sym (+-assoc b1 (₁₊ a1') (- ₁₊ a1')))
      (Eq.trans (Eq.cong (_+ - ₁₊ a1') eqZ)
        (+-identityˡ (- ₁₊ a1')))))

    nA1 : - ₁₊ a1' ≡ ₁₊ a2'
    nA1 = Eq.trans (Eq.sym b1nA1) b1A2

    nA2 : - ₁₊ a2' ≡ ₁₊ a1'
    nA2 = Eq.trans (Eq.cong -_ (Eq.sym nA1)) (-‿involutive (₁₊ a1'))

    vU : - ₁₊ a2' * iA1 ≡ ₁
    vU = Eq.trans (Eq.cong (_* iA1) nA2) (lemma-⁻¹ʳ (₁₊ a1') {{instA1}})

    vV : - ₁₊ a1' * iA2 ≡ ₁
    vV = Eq.trans (Eq.cong (_* iA2) nA1) (lemma-⁻¹ʳ (₁₊ a2') {{instA2}})

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    bR1 : b1 + nsum p-1 (- ₁₊ a1') ≡ ₀
    bR1 = Eq.trans (Eq.cong (b1 +_) nfixa1) eqZ

    cd1L : - ₁₊ a1' + - ₁₊ a2' ≡ ₀
    cd1L = Eq.trans (-‿+-comm (₁₊ a1') (₁₊ a2'))
      (Eq.trans (Eq.cong -_
          (Eq.trans (Eq.cong (₁₊ a1' +_) (Eq.sym nA1))
            (+-inverseʳ (₁₊ a1'))))
        -0#≈0#)

    cd2L : (b2 + - ₁₊ a1') + - ₀ ≡ b2 + ₁₊ a2'
    cd2L = Eq.trans (e0 (b2 + - ₁₊ a1')) (Eq.cong (b2 +_) nA1)

    bR7 : (b2 + - ₀) + nsum p-1 (- ₁₊ a2') ≡ b2 + ₁₊ a2'
    bR7 = Eq.cong₂ _+_ (e0 b2) nfixa2

    cF : C (₃₊ m)
    cF = inj₂ ((₀ , ₀) , inj₂ ((₁₊ a2' , b2 + ₁₊ a2') , lm2))

    -- LHS.
    PADfix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) CZ) .proj₁ ≡ PAD1h'
    PADfix = Eq.trans (padSA a1' a2' b1 b2)
      (Eq.cong₂
        (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
        (Eq.cong S^ vU)
        (Eq.cong (λ z → S^ z ↑) vV))

    L-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡ PAD1h' • (HH • W3h')
    L-fix = Eq.cong₂ _•_ PADfix (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) eqY)
      (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2)))
          eqY)))

    L-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2)))
          eqY))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ a2' , w) , lm2)))
        cd1L cd2L)

    -- RHS.
    E₁raw = ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S ^ p-1)) .proj₁
    E₇raw = ((ract {₁₊ m} ᵗ)
              (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) S⁻¹) .proj₁

    REST5h = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    r1 : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↓)) ≡
         (E₁raw , inj₂ ((₁₊ a1' , ₀) , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , b1) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') b1 (λ ()))
              (Eq.cong (₁₊ a1' ,_) bR1)))))

    r3 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₁₊ a1') , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₁₊ a1') lm p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ a1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (it-dDS-a0 p-1 (- ₁₊ a1')))))

    r5 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1' + - ₁₊ a2') ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (H ↓)) ≡
         (H , inj₂ ((₀ , - ₀) ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
    r5 = Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ (₁₊ m)) ,
        inj₂ (Hd' (₀ , v) , inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))))
      cd1L

    r6 : ((ract3 ᵗ) (inj₂ ((₀ , - ₀) ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₀) ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₀ , - ₀) ,
          inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₀) (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₀)
            (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d ,
              inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
            (it-dDS-a0 p-1 (- ₀)))))

    r7 : ((ract3 ᵗ) (inj₂ ((₀ , - ₀) ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↑)) ≡
         (E₇raw ↑ , inj₂ ((₀ , - ₀) ,
           inj₂ ((₁₊ a2' , b2 + ₁₊ a2') , lm2)))
    r7 = Eq.trans
      (ract-↑-≡ (₀ , - ₀) (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , - ₀) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2 + - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') (b2 + - ₀) (λ ()))
                (Eq.cong (₁₊ a2' ,_) bR7))))))

    R-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            E₁raw • (HH • (S ^ p-1 • (W3h' •
              (H • (S ^ p-1 • E₇raw ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5h)) .proj₁)
          r1)
      (Eq.cong (λ t → E₁raw • t)
      (Eq.cong (λ t → HH • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (CZ • REST5h)) .proj₁)
          r3)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → W3h' • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          r5)
      (Eq.cong (λ t → H • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → S ^ p-1 • t) (Eq.cong proj₁ r7))))))))))

    Rclean : E₁raw • (HH • (S ^ p-1 • (W3h' •
               (H • (S ^ p-1 • E₇raw ↑))))) ≈
             HH • (S⁻¹ • (W3h' • (H • S⁻¹)))
    Rclean =
      trans (trans (cleft
          (ract-S^-resid-a+ (₁₊ a1' , b1) lm p-1 (λ ()))) left-unit)
        (cright (cright (cright (cright (trans (cright
          (lemma-cong↑ E₇raw ε
            (ract-S^-resid-a+ (₁₊ a2' , b2 + - ₀) lm2 p-1 (λ ()))))
          right-unit)))))

    resid≈ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans id11h
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡
          inj₂ ((₀ , - ₀) , inj₂ ((₁₊ a2' , b2 + ₁₊ a2') , lm2))
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5h)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (CZ • REST5h)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          r5)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
        (Eq.cong proj₂ r7))))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c
      (Eq.trans
        (Eq.cong (λ v → inj₂ ((₀ , v) ,
            inj₂ ((₁₊ a2' , b2 + ₁₊ a2') , lm2)))
          (Eq.sym -0#≈0#))
        (Eq.sym R-c))

