------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case αα: both shifted
-- slots vanish (b₂ ≡ a₁ ≡ -a₂), so the first pad's S-slots take the
-- value 1 and both middle escapes are HH/H; the identity closes by the
-- axiom after H↑⁵- and H⁴-cancellations and disjoint-wire commutation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10j
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
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (Sp-1-S ; SupSinv ; H5lift)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid

  private
    ract2 = ract {₂₊ m}

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

    PAD1c : Word (Gen (₂₊ m))
    PAD1c = H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))

    fixdownJ : S⁻¹ {m} ↑ •
        (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdownJ = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

    H3W : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
    H3W w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

  idαα : PAD1c • ((H ↑ • H ↑) • WD) ≈
         (H ↑ • H ↑) • (S⁻¹ ↑ • (WD • (H ↑ • S⁻¹ ↑)))
  idαα = begin
    PAD1c • ((H ↑ • H ↑) • WD)
      ≈⟨ trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ •
      ((H ↑) ^ 3 • ((H ↑ • H ↑) • WD)))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft H5lift))))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑ • WD))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (H3W S)) (trans assoc (cright
             (trans (sym assoc) (trans (cleft (H3W H)) assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S • (S ↑ • (H ↑ • (H ^ 3 • WD))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans assoc (trans (cright assoc)
           (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (axiom order-H)) left-unit)))))))))))  ⟩
    H • (H ↑ • (CZ • (S • (S ↑ • (H ↑ • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (lemma-comm-S-w↑ S))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (lemma-comm-S-w↑ H)) assoc)))))))) ⟩
    H • (H ↑ • (CZ • (S ↑ • (H ↑ • (S • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (axiom comm-CZ-S↓))) assoc)))))) ⟩
    H • (H ↑ • (CZ • (S ↑ • (H ↑ • (CZ • (S • H ^ 3))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (axiom comm-CZ-S↑)) assoc))) ⟩
    H • (H ↑ • (S ↑ • (CZ • (H ↑ • (CZ • (S • H ^ 3))))))
      ≈⟨ cright (cright (cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownJ))))))) ⟩
    H • (H ↑ • (S ↑ • ((S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (H ↑ • (S⁻¹ ↑ • S⁻¹)))))) • (S • H ^ 3))))
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft
           (trans (sym assoc) (trans (cleft SupSinv) left-unit)))
           assoc))) ⟩
    H • (H ↑ • (H ↑ • ((S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))) •
      (S • H ^ 3))))
      ≈⟨ cright (cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
             (cright (cright (cright assoc)))))))) ⟩
    H • (H ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • (S • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (Sp-1-S {₁₊ m})) left-unit)))))))) ⟩
    H • (H ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • H ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (cright (sym (H3W S⁻¹))) (trans (sym assoc)
             (trans (cleft (sym (H3W H))) assoc))))))) ⟩
    H • (H ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ trans (sym assoc) (trans (cleft (lemma-comm-H-w↑ H)) assoc) ⟩
    H ↑ • (H • (H ↑ • (S⁻¹ ↑ • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (lemma-comm-H-w↑ H)) assoc)) ⟩
    H ↑ • (H ↑ • (H • (S⁻¹ ↑ • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (lemma-comm-H-w↑ S⁻¹)) assoc))) ⟩
    H ↑ • (H ↑ • (S⁻¹ ↑ • (H • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ sym assoc ⟩
    (H ↑ • H ↑) • (S⁻¹ ↑ • (H • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑)))))
      ≈⟨ cright (cright (trans (cright (sym assoc)) (sym assoc))) ⟩
    (H ↑ • H ↑) • (S⁻¹ ↑ • (WD • (H ↑ • S⁻¹ ↑))) ∎

  c10-go-aaαα : ∀ (b1 b2 : ℤ ₚ) (a1' a2' : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    b2 + - ₁₊ a1' ≡ ₀ → b2 + ₁₊ a2' ≡ ₀ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-aaαα b1 b2 a1' a2' lm2 eq-Y eq-Z = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instA₂ = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}

    beqY : b2 ≡ ₁₊ a1'
    beqY = Eq.trans (Eq.sym (+-identityʳ b2))
      (Eq.trans (Eq.cong (b2 +_) (Eq.sym (+-inverseˡ (₁₊ a1'))))
      (Eq.trans (Eq.sym (+-assoc b2 (- ₁₊ a1') (₁₊ a1')))
      (Eq.trans (Eq.cong (_+ ₁₊ a1') eq-Y)
        (+-identityˡ (₁₊ a1')))))

    beqZ : b2 ≡ - ₁₊ a2'
    beqZ = Eq.trans (Eq.sym (+-identityʳ b2))
      (Eq.trans (Eq.cong (b2 +_) (Eq.sym (+-inverseʳ (₁₊ a2'))))
      (Eq.trans (Eq.sym (+-assoc b2 (₁₊ a2') (- ₁₊ a2')))
      (Eq.trans (Eq.cong (_+ - ₁₊ a2') eq-Z)
        (+-identityˡ (- ₁₊ a2')))))

    AA : ₁₊ a1' ≡ - ₁₊ a2'
    AA = Eq.trans (Eq.sym beqY) beqZ

    vu₁ : - ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁ ≡ ₁
    vu₁ = Eq.trans (Eq.cong (_* ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
        (Eq.sym AA))
      (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}})

    vv₁ : - ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁ ≡ ₁
    vv₁ = Eq.trans (Eq.cong (_* ((₁₊ a2' , λ ()) ⁻¹) .proj₁)
        (Eq.trans (Eq.cong -_ AA) (-‿involutive (₁₊ a2'))))
      (lemma-⁻¹ʳ (₁₊ a2') {{instA₂}})

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    zfix : - ₁₊ a2' + - ₁₊ a1' ≡ ₀
    zfix = Eq.trans (Eq.cong (_+ - ₁₊ a1') (Eq.sym AA))
      (+-inverseʳ (₁₊ a1'))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') , inj₂ ((₀ , ₀) , lm2))

    PADfixαα : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) CZ) .proj₁ ≡ PAD1c
    PADfixαα = Eq.trans (padSA a1' a2' b1 b2)
      (Eq.cong₂
        (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
        (Eq.cong S^ vu₁)
        (Eq.cong (λ z → S^ z ↑) vv₁))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            PAD1c • ((H ↑ • H ↑) • WD)
    L-fix = Eq.cong₂ _•_ PADfixαα (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₁₊ a2' , v) ↓ᵏ m) ↑) eq-Y)
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2)))
          eq-Y)))

    L-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2)))
          eq-Y))
      (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₀ , u) , lm2)))
        (e0 (b1 + - ₁₊ a2'))
        zfix)

    -- RHS letters.
    E₁raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , b2) , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
              inj₂ ((₀ , - ₀) , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1j : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          (E₁raw ↑ , inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , ₀) , lm2)))
    r1j = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') b2 (λ ()))
                (Eq.cong (₁₊ a2' ,_)
                  (Eq.trans (Eq.cong (b2 +_) nfixa2) eq-Z)))))))

    r3j : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₀ , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₀ , - ₁₊ a2') , lm2)))
    r3j = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₀ , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₁₊ a2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (- ₁₊ a2'))))))

    r5j : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₁₊ a2' + - ₁₊ a1') , lm2))) (H ↑)) ≡
          (H ↑ , inj₂ ((₁₊ a1' , b1 + - ₀) , inj₂ ((₀ , - ₀) , lm2)))
    r5j = Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ m) ↑ ,
        inj₂ ((₁₊ a1' , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2))))
      zfix

    r6j : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₀) , lm2))) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₀) , lm2)))
    r6j = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₀) (inj₂ ((₀ , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₀) lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₀) , c))
          (Eq.trans (ract-S^-coset (₀ , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₀))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            E₁raw ↑ • ((H ↑ • H ↑) • ((S ^ p-1) ↑ • (WD •
              (H ↑ • ((S ^ p-1) ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1j)
      (Eq.cong (λ t → E₁raw ↑ • t)
      (Eq.cong (λ t → (H ↑ • H ↑) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3j)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → WD • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5j)
      (Eq.cong (λ t → H ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6j)
      (Eq.cong ((S ^ p-1) ↑ •_)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₀) , lm2))) u) .proj₁)
          (↓-pow-S p-1)))))))))))

    Rclean : E₁raw ↑ • ((H ↑ • H ↑) • ((S ^ p-1) ↑ • (WD •
               (H ↑ • ((S ^ p-1) ↑ • E₇raw))))) ≈
             (H ↑ • H ↑) • (S⁻¹ ↑ • (WD • (H ↑ • S⁻¹ ↑)))
    Rclean =
      trans (trans (cleft (lemma-cong↑ E₁raw ε
          (ract-S^-resid-a+ (₁₊ a2' , b2) lm2 p-1 (λ ())))) left-unit)
      (cright (cright (cright (cright (trans (cright
          (ract-S^-resid-a+ (₁₊ a1' , b1 + - ₀)
            (inj₂ ((₀ , - ₀) , lm2)) p-1 (λ ())))
        right-unit)))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans idαα
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1j)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3j)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5j)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6j)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₀) , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₀)
          (inj₂ ((₀ , - ₀) , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , - ₀) , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₀) (λ ())))
        (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₀ , u) , lm2)))
          (Eq.trans (Eq.cong₂ _+_ (e0 b1) nfixa1)
            (Eq.cong (b1 +_) AA))
          -0#≈0#)))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
               .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)

