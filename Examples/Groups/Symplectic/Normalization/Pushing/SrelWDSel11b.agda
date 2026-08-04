------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₀,₁₊b1')/(₁₊a2',b2), branch α:
-- the middle slot b₁ - a₂ vanishes, so b₁ ≡ a₂, the clause-4 pad's two
-- S-slots both take the value -1, and the trailing H-escape is HH.
-- The two sides then differ only by an S⁻¹ crossing the CZ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11b
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
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S ; H↑3H↑≈ε)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (H5 ; SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)

------------------------------------------------------------------------
-- The branch-α residual identity.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑
                        ; lemma-comm-Sᵏ-w↑)

  private
    W3 : Word (Gen (₂₊ m))
    W3 = H ↑ • (CZ • (H ↑) ^ 3)

    PADm1 : Word (Gen (₂₊ m))
    PADm1 = H • (H ↑ • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ • (H ↑) ^ 3)))))

    HWb : ∀ (w : Word (Gen (₁₊ m))) → H • w ↑ ≈ w ↑ • H
    HWb w = lemma-comm-H-w↑ w

    SinvHb : S⁻¹ • H ↑ ≈ H ↑ • S⁻¹
    SinvHb = comm⇒pow-comm {w = S} {v = H ↑} p-1 1
      (lemma-comm-S-w↑ H)

    SdownCZb : S⁻¹ • CZ ≈ CZ • S⁻¹
    SdownCZb = comm⇒pow-comm {w = S} {v = CZ} p-1 1
      (sym (axiom comm-CZ-S↓))

    -- The bottom block HH • S⁻¹ passes through any lifted word.
    HHSup : ∀ (u : Word (Gen (₁₊ m))) →
      (HH • S⁻¹) • u ↑ ≈ u ↑ • (HH • S⁻¹)
    HHSup u =
      trans assoc
      (trans (cright (lemma-comm-Sᵏ-w↑ p-1 u))
      (trans (sym assoc)
      (trans (cleft (comm⇒pow-comm {w = H} {v = u ↑} 2 1
        (lemma-comm-H-w↑ u))) assoc)))

    fixdown11b : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdown11b = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

  idc11b : W3 • (H • W3) ≈ S⁻¹ • (PADm1 • (HH • S⁻¹))
  idc11b = begin
    W3 • (H • W3)
      ≈⟨ trans assoc (cright assoc) ⟩
    H ↑ • (CZ • ((H ↑) ^ 3 • (H • (H ↑ • (CZ • (H ↑) ^ 3)))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (sym (HWb (H ^ 3))))
           (trans assoc
           (trans (cright (sym assoc))
           (trans (cright (cleft H↑3H↑≈ε)) (cright left-unit))))))) ⟩
    H ↑ • (CZ • (H • (CZ • (H ↑) ^ 3)))
      ≈⟨ cright (trans (cright (sym assoc)) (sym assoc)) ⟩
    H ↑ • ((CZ • (H • CZ)) • (H ↑) ^ 3)
      ≈⟨ cright (cleft (trans (axiom selinger-c11) (refl' fixdown11b))) ⟩
    H ↑ • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))) •
      (H ↑) ^ 3)
      ≈⟨ cright (trans assoc (cright (trans assoc (cright (trans assoc
           (cright (trans assoc (cright (trans assoc
             (cright assoc)))))))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (H ↑) ^ 3)))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft SdownCZb) assoc)))) ⟩
    H ↑ • (S⁻¹ • (H • (CZ • (S⁻¹ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (H ↑) ^ 3)))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (cleft (sym H5)) assoc))))) ⟩
    H ↑ • (S⁻¹ • (H • (CZ • (S⁻¹ • (H ^ 3 • (HH • (S⁻¹ •
      (S⁻¹ ↑ • (H ↑) ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
           (trans (HHSup (S⁻¹ • H ^ 3)) assoc)))))))  ⟩
    H ↑ • (S⁻¹ • (H • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ •
      ((H ↑) ^ 3 • (HH • S⁻¹))))))))
      ≈⟨ trans (sym assoc) (trans (cleft (sym SinvHb)) assoc) ⟩
    S⁻¹ • (H ↑ • (H • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ •
      ((H ↑) ^ 3 • (HH • S⁻¹))))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (HWb H))) assoc)) ⟩
    S⁻¹ • (H • (H ↑ • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ •
      ((H ↑) ^ 3 • (HH • S⁻¹))))))))
      ≈⟨ sym (cright (trans assoc (cright (trans assoc (cright
           (trans assoc (cright (trans assoc (cright
             (trans assoc (cright assoc))))))))))) ⟩
    S⁻¹ • (PADm1 • (HH • S⁻¹)) ∎

------------------------------------------------------------------------
-- The branch-α orbit.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract3 = ract {₂₊ m}

    W3' : Word (Gen (₂₊ m))
    W3' = H ↑ • (CZ • (H ↑) ^ 3)

    PADm1' : Word (Gen (₂₊ m))
    PADm1' = H • (H ↑ • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ • (H ↑) ^ 3)))))

  c11-go-0b2α : ∀ (b2 : ℤ ₚ) (b1' a2' : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ₁₊ b1' + - ₁₊ a2' ≡ ₀ →
    ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-0b2α b2 b1' a2' lm2 eq-X = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    instB₁ = nztoℕ {y = ₁₊ b1'} {neq0 = λ ()}

    beq : ₁₊ b1' ≡ ₁₊ a2'
    beq = Eq.trans (Eq.sym (+-identityʳ (₁₊ b1')))
      (Eq.trans (Eq.cong (₁₊ b1' +_) (Eq.sym (+-inverseˡ (₁₊ a2'))))
      (Eq.trans (Eq.sym (+-assoc (₁₊ b1') (- ₁₊ a2') (₁₊ a2')))
      (Eq.trans (Eq.cong (_+ ₁₊ a2') eq-X)
        (+-identityˡ (₁₊ a2')))))

    nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    bfix3 : - ₀ + nsum p-1 (- ₁₊ b1') ≡ ₁₊ b1'
    bfix3 = Eq.trans (Eq.cong₂ _+_ -0#≈0#
        (Eq.trans (nsum-p-1 (- ₁₊ b1')) (-‿involutive (₁₊ b1'))))
      (+-identityˡ (₁₊ b1'))

    vα : - ₁₊ a2' * ((₁₊ b1' , λ ()) ⁻¹) .proj₁ ≡ - ₁
    vα = Eq.trans
      (Eq.cong (λ t → - t * ((₁₊ b1' , λ ()) ⁻¹) .proj₁) (Eq.sym beq))
      (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b1')
          (((₁₊ b1' , λ ()) ⁻¹) .proj₁)))
        (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ b1') {{instB₁}})))

    vβ : - ₁₊ b1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁ ≡ - ₁
    vβ = Eq.trans (Eq.cong (- ₁₊ b1' *_)
        (inv-cong (₁₊ a2' , λ ()) (₁₊ b1' , λ ()) (Eq.sym beq)))
      (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b1')
          (((₁₊ b1' , λ ()) ⁻¹) .proj₁)))
        (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ b1') {{instB₁}})))

    r7fix : (b2 + - ₁₊ b1') + nsum p-1 (- ₁₊ a2') ≡ b2
    r7fix = Eq.trans (Eq.cong₂ _+_
        (Eq.cong (b2 +_) (Eq.cong -_ beq)) nfixa2)
      (Eq.trans (+-assoc b2 (- ₁₊ a2') (₁₊ a2'))
      (Eq.trans (Eq.cong (b2 +_) (+-inverseˡ (₁₊ a2')))
        (+-identityʳ b2)))

    cF : C (₃₊ m)
    cF = inj₂ ((₀ , - ₁₊ a2') , inj₂ ((₁₊ a2' , b2) , lm2))

    -- LHS.
    L-fix : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡ W3' • (H • W3')
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₀ , v) ↓ᵏ (₁₊ m)) eq-X)
      (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ (Hd' (₀ , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
          eq-X)))

    L-c : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ (Hd' (₀ , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
          eq-X))
      (Eq.cong₂ (λ v u → inj₂ ((₀ , v) , inj₂ ((₁₊ a2' , u) , lm2)))
        (Eq.trans (Eq.cong (_+ - ₁₊ a2') -0#≈0#)
          (+-identityˡ (- ₁₊ a2')))
        (Eq.trans (Eq.cong (_+ - ₀) (e0 b2)) (e0 b2)))

    -- RHS letters.
    E₃raw = ((ract3 ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) (S ^ p-1)) .proj₁
    E₇raw = ((ract {₁₊ m} ᵗ)
              (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) S⁻¹) .proj₁

    REST5b = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

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

    PADfix : ((ract3 ᵗ) (inj₂ ((₁₊ b1' , ₁₊ b1') ,
                inj₂ ((₁₊ a2' , b2) , lm2))) CZ) .proj₁ ≡ PADm1'
    PADfix = Eq.trans (padSA b1' a2' (₁₊ b1') b2)
      (Eq.cong₂
        (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
        (Eq.trans (Eq.cong S^ vα) SIfix)
        (Eq.cong _↑ (Eq.trans (Eq.cong S^ vβ) SIfix)))

    r5 : ((ract3 ᵗ) (inj₂ ((₁₊ b1' , ₁₊ b1' + - ₁₊ a2') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (H ↓)) ≡
         (HH , inj₂ ((₀ , - ₁₊ b1') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)))
    r5 = Eq.cong (λ v → ((Hdir (₁₊ b1' , v) ↓ᵏ (₁₊ m)) ,
        inj₂ (Hd' (₁₊ b1' , v) ,
          inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))))
      eq-X

    r6 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ b1') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₁₊ b1') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₀ , - ₁₊ b1') ,
          inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₁₊ b1')
          (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ b1')
            (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)))
            (it-dDS-a0 p-1 (- ₁₊ b1')))))

    r7 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ b1') ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2))) (S⁻¹ ↑)) ≡
         (E₇raw ↑ , cF)
    r7 = Eq.trans
      (ract-↑-≡ (₀ , - ₁₊ b1')
        (inj₂ ((₁₊ a2' , b2 + - ₁₊ b1') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans
          (Eq.cong (λ c → inj₂ ((₀ , - ₁₊ b1') , c))
            (Eq.trans (ract-S^-coset (₁₊ a2' , b2 + - ₁₊ b1') lm2 p-1)
              (Eq.cong (λ d → inj₂ (d , lm2))
                (Eq.trans
                  (it-dDS-nz p-1 (₁₊ a2') (b2 + - ₁₊ b1') (λ ()))
                  (Eq.cong (₁₊ a2' ,_) r7fix)))))
          (Eq.cong (λ v → inj₂ ((₀ , v) , inj₂ ((₁₊ a2' , b2) , lm2)))
            (Eq.cong -_ beq))))

    R-fix : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            S ^ p-1 • ((Hdir (₀ , ₁₊ b1') ↓ᵏ (₁₊ m)) •
              (E₃raw • (PADm1' • (HH • (S ^ p-1 • E₇raw ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5b)) .proj₁)
          r1)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → (Hdir (₀ , ₁₊ b1') ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (CZ • REST5b)) .proj₁)
          r3)
      (Eq.cong (λ t → E₃raw • t)
      (Eq.trans (Eq.cong₂ _•_ PADfix Eq.refl)
      (Eq.cong (λ t → PADm1' • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          r5)
      (Eq.cong (λ t → HH • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → S ^ p-1 • t) (Eq.cong proj₁ r7)))))))))))

    Rclean : S ^ p-1 • ((Hdir (₀ , ₁₊ b1') ↓ᵏ (₁₊ m)) •
               (E₃raw • (PADm1' • (HH • (S ^ p-1 • E₇raw ↑))))) ≈
             S⁻¹ • (PADm1' • (HH • S⁻¹))
    Rclean =
      trans (cright left-unit)
      (trans (cright (trans (cleft
          (ract-S^-resid-a+ (₁₊ b1' , - ₀) lm p-1 (λ ()))) left-unit))
        (cright (cright (cright (trans (cright (lemma-cong↑ E₇raw ε
          (ract-S^-resid-a+ (₁₊ a2' , b2 + - ₁₊ b1') lm2 p-1 (λ ()))))
          right-unit)))))

    resid≈ : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans idc11b
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract3 ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5b)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (CZ • REST5b)) .proj₂)
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

