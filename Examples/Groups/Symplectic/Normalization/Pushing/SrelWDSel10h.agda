------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₀,₁₊b2'), branch β: the middle slot
-- x = b₂ - a₁ is nonzero, so both clause-4 pads carry general values
-- and the RHS middle escape is an hpad unit.  Both sides normalize to
-- the canonical form
--   H • (S⁻¹•H•S^v'•ZM(-r̂))↑ • CZ^(-q̂) • (H•S^r̂)↑ • S^u' • H³
-- by the Borel calculus, the axiom, and one derived-7 round.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10h
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
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ;
         -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (iexp ; ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime

------------------------------------------------------------------------
-- The value kit under eq-X : b₂ - a₁ ≡ x.

module XValues (a1' b2' x : Fin (₁₊ p-2))
  (eq-X : ₁₊ b2' + - ₁₊ a1' ≡ ₁₊ x) where

  A₁* B₂* X* : ℤ* ₚ
  A₁* = (₁₊ a1' , λ ())
  B₂* = (₁₊ b2' , λ ())
  X*  = (₁₊ x , λ ())

  iA₁ iB₂ iX : ℤ ₚ
  iA₁ = (A₁* ⁻¹) .proj₁
  iB₂ = (B₂* ⁻¹) .proj₁
  iX  = (X* ⁻¹) .proj₁

  q̂p r̂p : ℤ* ₚ
  q̂p = B₂* *' (X* ⁻¹)
  r̂p = X* *' (B₂* ⁻¹)

  uv vv u'v v'v r̂v q̂v : ℤ ₚ
  uv  = - ₁₊ x * iA₁
  vv  = - ₁₊ a1' * iX
  u'v = - ₁₊ b2' * iA₁
  v'v = - ₁₊ a1' * iB₂
  r̂v  = ₁₊ x * iB₂
  q̂v  = ₁₊ b2' * iX

  private
    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instB₂ = nztoℕ {y = ₁₊ b2'} {neq0 = λ ()}
    instX  = nztoℕ {y = ₁₊ x} {neq0 = λ ()}

  open Eq.≡-Reasoning

  wAB : ₁₊ a1' + ₁₊ x ≡ ₁₊ b2'
  wAB = begin
    ₁₊ a1' + ₁₊ x
      ≡⟨ Eq.cong (₁₊ a1' +_) (Eq.sym eq-X) ⟩
    ₁₊ a1' + (₁₊ b2' + - ₁₊ a1')
      ≡⟨ Eq.cong (₁₊ a1' +_) (+-comm (₁₊ b2') (- ₁₊ a1')) ⟩
    ₁₊ a1' + (- ₁₊ a1' + ₁₊ b2')
      ≡⟨ Eq.sym (+-assoc (₁₊ a1') (- ₁₊ a1') (₁₊ b2')) ⟩
    (₁₊ a1' + - ₁₊ a1') + ₁₊ b2'
      ≡⟨ Eq.cong (_+ ₁₊ b2') (+-inverseʳ (₁₊ a1')) ⟩
    ₀ + ₁₊ b2'
      ≡⟨ +-identityˡ (₁₊ b2') ⟩
    ₁₊ b2' ∎

  wXB : ₁₊ x + - ₁₊ b2' ≡ - ₁₊ a1'
  wXB = begin
    ₁₊ x + - ₁₊ b2'
      ≡⟨ Eq.cong (_+ - ₁₊ b2') (Eq.sym eq-X) ⟩
    (₁₊ b2' + - ₁₊ a1') + - ₁₊ b2'
      ≡⟨ Eq.cong (_+ - ₁₊ b2') (+-comm (₁₊ b2') (- ₁₊ a1')) ⟩
    (- ₁₊ a1' + ₁₊ b2') + - ₁₊ b2'
      ≡⟨ +-assoc (- ₁₊ a1') (₁₊ b2') (- ₁₊ b2') ⟩
    - ₁₊ a1' + (₁₊ b2' + - ₁₊ b2')
      ≡⟨ Eq.cong (- ₁₊ a1' +_) (+-inverseʳ (₁₊ b2')) ⟩
    - ₁₊ a1' + ₀
      ≡⟨ +-identityʳ (- ₁₊ a1') ⟩
    - ₁₊ a1' ∎

  w1 : - ₁ + uv ≡ u'v
  w1 = begin
    - ₁ + - ₁₊ x * iA₁
      ≡⟨ Eq.cong (- ₁ +_) (Eq.sym (-‿distribˡ-* (₁₊ x) iA₁)) ⟩
    - ₁ + - (₁₊ x * iA₁)
      ≡⟨ -‿+-comm ₁ (₁₊ x * iA₁) ⟩
    - (₁ + ₁₊ x * iA₁)
      ≡⟨ Eq.cong -_ (Eq.cong (_+ ₁₊ x * iA₁)
           (Eq.sym (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}}))) ⟩
    - (₁₊ a1' * iA₁ + ₁₊ x * iA₁)
      ≡⟨ Eq.cong -_ (Eq.sym (*-distribʳ-+ iA₁ (₁₊ a1') (₁₊ x))) ⟩
    - ((₁₊ a1' + ₁₊ x) * iA₁)
      ≡⟨ Eq.cong -_ (Eq.cong (_* iA₁) wAB) ⟩
    - (₁₊ b2' * iA₁)
      ≡⟨ -‿distribˡ-* (₁₊ b2') iA₁ ⟩
    - ₁₊ b2' * iA₁ ∎

  w2 : - ₁ + vv ≡ - (₁₊ b2' * iX)
  w2 = begin
    - ₁ + - ₁₊ a1' * iX
      ≡⟨ Eq.cong (- ₁ +_) (Eq.sym (-‿distribˡ-* (₁₊ a1') iX)) ⟩
    - ₁ + - (₁₊ a1' * iX)
      ≡⟨ -‿+-comm ₁ (₁₊ a1' * iX) ⟩
    - (₁ + ₁₊ a1' * iX)
      ≡⟨ Eq.cong -_ (Eq.cong (_+ ₁₊ a1' * iX)
           (Eq.sym (lemma-⁻¹ʳ (₁₊ x) {{instX}}))) ⟩
    - (₁₊ x * iX + ₁₊ a1' * iX)
      ≡⟨ Eq.cong -_ (Eq.sym (*-distribʳ-+ iX (₁₊ x) (₁₊ a1'))) ⟩
    - ((₁₊ x + ₁₊ a1') * iX)
      ≡⟨ Eq.cong -_ (Eq.cong (_* iX)
           (Eq.trans (+-comm (₁₊ x) (₁₊ a1')) wAB)) ⟩
    - (₁₊ b2' * iX) ∎

  w3 : - ₁ + r̂v ≡ v'v
  w3 = begin
    - ₁ + ₁₊ x * iB₂
      ≡⟨ +-comm (- ₁) (₁₊ x * iB₂) ⟩
    ₁₊ x * iB₂ + - ₁
      ≡⟨ Eq.cong (₁₊ x * iB₂ +_) (Eq.cong -_
           (Eq.sym (lemma-⁻¹ʳ (₁₊ b2') {{instB₂}}))) ⟩
    ₁₊ x * iB₂ + - (₁₊ b2' * iB₂)
      ≡⟨ Eq.cong (₁₊ x * iB₂ +_) (-‿distribˡ-* (₁₊ b2') iB₂) ⟩
    ₁₊ x * iB₂ + - ₁₊ b2' * iB₂
      ≡⟨ Eq.sym (*-distribʳ-+ iB₂ (₁₊ x) (- ₁₊ b2')) ⟩
    (₁₊ x + - ₁₊ b2') * iB₂
      ≡⟨ Eq.cong (_* iB₂) wXB ⟩
    - ₁₊ a1' * iB₂ ∎

  w5 : - (((-' q̂p) ⁻¹) .proj₁) ≡ r̂v
  w5 = Eq.trans (Eq.cong -_ (ineg q̂p (-' q̂p) Eq.refl))
    (Eq.trans (-‿involutive ((q̂p ⁻¹) .proj₁))
    (Eq.trans (iexp B₂* X*) (*-comm iB₂ (₁₊ x))))

  negneg : ∀ (s t : ℤ ₚ) → - s * - t ≡ s * t
  negneg s t = Eq.trans (Eq.sym (-‿distribˡ-* s (- t)))
    (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* s t)))
      (-‿involutive (s * t)))

  w7 : r̂v * (((-' (₁ , λ ())) ⁻¹) .proj₁ *
             ((-' (₁ , λ ())) ⁻¹) .proj₁) ≡ r̂v
  w7 = Eq.trans (Eq.cong (λ t → r̂v * (t * t)) aux-₁⁻¹)
    (Eq.trans (Eq.cong (r̂v *_) aux-₁²) (*-identityʳ r̂v))

  w8 : (r̂p *' (-' (₁ , λ ()))) .proj₁ ≡ (-' r̂p) .proj₁
  w8 = Eq.trans (Eq.sym (-‿distribʳ-* (r̂p .proj₁) ₁))
    (Eq.cong -_ (*-identityʳ (r̂p .proj₁)))

  w9 : ((-' r̂p) ⁻¹) .proj₁ ≡ - q̂v
  w9 = Eq.trans (ineg r̂p (-' r̂p) Eq.refl)
    (Eq.cong -_ (Eq.trans (iexp X* B₂*) (*-comm iX (₁₊ b2'))))

  w10 : ((q̂p ⁻¹) *' (-' (₁ , λ ()))) .proj₁ ≡ (-' r̂p) .proj₁
  w10 = Eq.trans (Eq.cong (_* - ₁)
      (Eq.trans (iexp B₂* X*) (*-comm iB₂ (₁₊ x))))
    (Eq.trans (Eq.sym (-‿distribʳ-* r̂v ₁))
      (Eq.cong -_ (*-identityʳ r̂v)))

  w11 : ((q̂p ⁻¹) ⁻¹) .proj₁ ≡ q̂v
  w11 = inv-involutive q̂p

  w12 : v'v * (((-' r̂p) ⁻¹) .proj₁ * ((-' r̂p) ⁻¹) .proj₁) ≡
        v'v * (q̂v * q̂v)
  w12 = Eq.cong (v'v *_)
    (Eq.trans (Eq.cong₂ _*_ w9 w9) (negneg q̂v q̂v))
------------------------------------------------------------------------
-- The two normal-form chains and idβ.

module _ {m : ℕ} (a1' b2' x : Fin (₁₊ p-2))
  (eq-X : ₁₊ b2' + - ₁₊ a1' ≡ ₁₊ x) where

  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open XValues a1' b2' x eq-X

  private
    module L0b = Lemmas0 (₁₊ m)

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

    PAD PAD' : Word (Gen (₂₊ m))
    PAD  = H • (H ↑ • (CZ • (S^ uv •
      (H ^ 3 • (S^ vv ↑ • (H ↑) ^ 3)))))
    PAD' = H • (H ↑ • (CZ • (S^ u'v •
      (H ^ 3 • (S^ v'v ↑ • (H ↑) ^ 3)))))

    fixdownH : S⁻¹ {m} ↑ •
        (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdownH = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

    -- Bottom letters commute past lifted words.
    SkW : ∀ (k : ℤ ₚ) (w : Word (Gen (₁₊ m))) →
      S^ k • w ↑ ≈ w ↑ • S^ k
    SkW k w = comm⇒pow-comm {w = S} {v = w ↑} (toℕ k) 1
      (lemma-comm-S-w↑ w)

    H3W : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
    H3W w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

    wSexp : v'v * (((q̂p ⁻¹) ⁻¹) .proj₁ * ((q̂p ⁻¹) ⁻¹) .proj₁) ≡
            v'v * (q̂v * q̂v)
    wSexp = Eq.cong (v'v *_) (Eq.cong₂ _*_ w11 w11)

    w7' : (v'v * (q̂v * q̂v)) *
      (((-' (₁ , λ ())) ⁻¹) .proj₁ * ((-' (₁ , λ ())) ⁻¹) .proj₁) ≡
      v'v * (q̂v * q̂v)
    w7' = Eq.trans (Eq.cong (λ t → (v'v * (q̂v * q̂v)) * (t * t)) aux-₁⁻¹)
      (Eq.trans (Eq.cong ((v'v * (q̂v * q̂v)) *_) aux-₁²)
        (*-identityʳ (v'v * (q̂v * q̂v))))

  CANβ : Word (Gen (₂₊ m))
  CANβ = H • (S⁻¹ ↑ • (H ↑ • (S^ v'v ↑ • (ZM (-' r̂p) ↑ •
    (CZ^ (- q̂v) • (H ↑ • (S^ r̂v ↑ • (S^ u'v • H ^ 3))))))))

  Lβ : WD • PAD ≈ CANβ
  Lβ = begin
    WD • PAD
      ≈⟨ assoc ⟩
    H • ((CZ • H ^ 3) • PAD)
      ≈⟨ cright assoc ⟩
    H • (CZ • (H ^ 3 • PAD))
      ≈⟨ cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (axiom order-H)) left-unit))))))) ⟩
    H • (CZ • (H ↑ • (CZ • (S^ uv •
      (H ^ 3 • (S^ vv ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownH))))) ⟩
    H • ((S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))) •
      (S^ uv • (H ^ 3 • (S^ vv ↑ • (H ↑) ^ 3))))
      ≈⟨ cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc)))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • (S^ uv • (H ^ 3 • (S^ vv ↑ • (H ↑) ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft (trans (cleft (refl'
               (Eq.sym (SIfix {₁₊ m}))))
             (trans (L0b.lemma-S^k+l (- ₁) uv)
               (refl' (Eq.cong S^ w1)))))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S^ u'v • (H ^ 3 • (S^ vv ↑ • (H ↑) ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (cright (trans (sym assoc)
             (trans (cleft (H3W (S^ vv)))
             (trans assoc (cright (H3W (H ^ 3)))))))
           (trans (sym assoc)
           (trans (cleft (SkW u'v (S^ vv)))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (SkW u'v (H ^ 3))) assoc))))))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S^ vv ↑ • ((H ↑) ^ 3 • (S^ u'v • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft (trans (cleft (refl'
               (Eq.cong _↑ (Eq.sym (SIfix {m})))))
             (trans (Sk+lup (- ₁) vv)
               (refl' (Eq.cong (λ t → S^ t ↑) w2))))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ •
      (S^ ((-' q̂p) .proj₁) ↑ • ((H ↑) ^ 3 • (S^ u'v • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (trans
           (cright (trans (cright assoc) (sym assoc)))
           (trans (sym assoc) (cleft (d7εup (-' q̂p))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      ((S^ (- (((-' q̂p) ⁻¹) .proj₁)) ↑ • (ZM (-' ((-' q̂p) ⁻¹)) ↑ •
        (H ↑ • S^ (- (((-' q̂p) ⁻¹) .proj₁)) ↑))) •
       ((H ↑ • H ↑) • (S^ u'v • H ^ 3)))))))
      ≈⟨ cright (cright (cright (cright (cright (cleft (trans
           (cleft (refl' (Eq.cong (λ t → S^ t ↑) w5)))
           (trans (cright (cleft (ZMvalup (-' ((-' q̂p) ⁻¹)) r̂p w5)))
             (cright (cright (cright (refl'
               (Eq.cong (λ t → S^ t ↑) w5))))))))))))  ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      ((S^ r̂v ↑ • (ZM r̂p ↑ • (H ↑ • S^ r̂v ↑))) •
       ((H ↑ • H ↑) • (S^ u'v • H ^ 3)))))))
      ≈⟨ cright (cright (cright (cright (cright (trans assoc
           (trans (cright assoc) (cright (cright assoc)))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (S^ r̂v ↑ • (ZM r̂p ↑ • (H ↑ • (S^ r̂v ↑ •
        ((H ↑ • H ↑) • (S^ u'v • H ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (trans (cright (cleft HHMup))
           (trans (sym assoc)
           (trans (cleft (SZmoveup r̂v (-' (₁ , λ ())) r̂v w7))
             assoc)))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (S^ r̂v ↑ • (ZM r̂p ↑ • (H ↑ • (ZM (-' (₁ , λ ())) ↑ •
        (S^ r̂v ↑ • (S^ u'v • H ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (trans
               (HMup (-' (₁ , λ ())))
               (cleft (ZMvalup ((-' (₁ , λ ())) ⁻¹) (-' (₁ , λ ()))
                 aux-₁⁻¹))))
             assoc)))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (S^ r̂v ↑ • (ZM r̂p ↑ • (ZM (-' (₁ , λ ())) ↑ •
        (H ↑ • (S^ r̂v ↑ • (S^ u'v • H ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (cleft (Zmulup r̂p (-' (₁ , λ ())) (-' r̂p) w8)))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (S^ r̂v ↑ • (ZM (-' r̂p) ↑ •
        (H ↑ • (S^ r̂v ↑ • (S^ u'v • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (comm-CZ-S^↑ r̂v))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (trans (cMup (-' r̂p))
                 (cright (refl' (Eq.cong CZ^ w9)))))
               assoc))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (S^ r̂v ↑ • (ZM (-' r̂p) ↑ •
      (CZ^ (- q̂v) • (H ↑ • (S^ r̂v ↑ • (S^ u'v • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (cleft (trans (cleft (refl'
               (Eq.cong _↑ (Eq.sym (SIfix {m})))))
             (trans (Sk+lup (- ₁) r̂v)
               (refl' (Eq.cong (λ t → S^ t ↑) w3)))))))) ⟩
    CANβ ∎

  Rβ : S⁻¹ ↑ • (PAD' • (ZM q̂p ↑ • S^ r̂v ↑)) ≈ CANβ
  Rβ = begin
    S⁻¹ ↑ • (PAD' • (ZM q̂p ↑ • S^ r̂v ↑))
      ≈⟨ cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc)))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (H ^ 3 • (S^ v'v ↑ •
      ((H ↑) ^ 3 • (ZM q̂p ↑ • S^ r̂v ↑))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (H3Mup q̂p)) assoc)))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (H ^ 3 • (S^ v'v ↑ •
      (ZM (q̂p ⁻¹) ↑ • ((H ↑) ^ 3 • S^ r̂v ↑))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (SZmoveup v'v (q̂p ⁻¹) (v'v * (q̂v * q̂v)) wSexp))
             assoc))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (H ^ 3 •
      (ZM (q̂p ⁻¹) ↑ • (S^ (v'v * (q̂v * q̂v)) ↑ •
        ((H ↑) ^ 3 • S^ r̂v ↑))))))))
      ≈⟨ trans (cright (cright (cright (cright (cright (cright
           (cright (cright (trans (cleft (sym assoc))
             (trans assoc (cleft HHMup)))))))))))
         (cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (SZmoveup
               (v'v * (q̂v * q̂v)) (-' (₁ , λ ()))
               (v'v * (q̂v * q̂v)) w7'))
             assoc))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (H ^ 3 •
      (ZM (q̂p ⁻¹) ↑ • (ZM (-' (₁ , λ ())) ↑ •
        (S^ (v'v * (q̂v * q̂v)) ↑ • (H ↑ • S^ r̂v ↑)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (cleft (Zmulup (q̂p ⁻¹) (-' (₁ , λ ())) (-' r̂p) w10)))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (H ^ 3 •
      (ZM (-' r̂p) ↑ • (S^ (v'v * (q̂v * q̂v)) ↑ •
        (H ↑ • S^ r̂v ↑))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (sym (SZmoveup v'v (-' r̂p)
                 (v'v * (q̂v * q̂v)) w12)))
               assoc))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (H ^ 3 •
      (S^ v'v ↑ • (ZM (-' r̂p) ↑ • (H ↑ • S^ r̂v ↑))))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (H3W (S^ v'v)))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (H3W (ZM (-' r̂p))))
               (trans assoc (cright (trans (sym assoc)
                 (trans (cleft (H3W H))
                 (trans assoc (cright (H3W (S^ r̂v)))))))))))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ u'v • (S^ v'v ↑ • (ZM (-' r̂p) ↑ •
      (H ↑ • (S^ r̂v ↑ • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (SkW u'v (S^ v'v)))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (SkW u'v (ZM (-' r̂p))))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (SkW u'v H))
               (trans assoc (cright (trans (sym assoc)
                 (trans (cleft (SkW u'v (S^ r̂v))) assoc))))))))))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S^ v'v ↑ • (ZM (-' r̂p) ↑ •
      (H ↑ • (S^ r̂v ↑ • (S^ u'v • H ^ 3))))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (comm-CZ-S^↑ v'v))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (trans (cMup (-' r̂p))
                 (cright (refl' (Eq.cong CZ^ w9)))))
               assoc)))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (S^ v'v ↑ • (ZM (-' r̂p) ↑ •
      (CZ^ (- q̂v) • (H ↑ • (S^ r̂v ↑ • (S^ u'v • H ^ 3))))))))
      ≈⟨ trans (sym assoc)
           (trans (cleft (sym (lemma-comm-H-w↑ S⁻¹))) assoc) ⟩
    CANβ ∎

  idβ : WD • PAD ≈ S⁻¹ ↑ • (PAD' • (ZM q̂p ↑ • S^ r̂v ↑))
  idβ = trans Lβ (sym Rβ)

