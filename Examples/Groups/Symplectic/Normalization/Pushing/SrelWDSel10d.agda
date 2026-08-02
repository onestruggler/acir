------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 branch B, part 1: the R-side normal form.  With
-- Sv = B + A ≠ 0 the right-hand orbit residual
-- (ZM q₁ • S^ r₁)↑ • W • (ZM q₂ • S^ r₂)↑ • S⁻¹ normalizes via the
-- Borel calculus to the canonical form
-- ZM (-q)↑ • S^(r·r₂)↑ • H↑ • CZ^(-q₂) • H↑ • S^ r₂ ↑ • S⁻¹.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10d
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
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿distribʳ-* ; -‿distribˡ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (iexp ; ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime

------------------------------------------------------------------------
-- The value kit shared by both normal-form chains.

module BValues (a2' b2'' w : Fin (₁₊ p-2))
  (eq-w : ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w) where

  A* B* Sv* : ℤ* ₚ
  A*  = (₁₊ a2' , λ ())
  B*  = (₁₊ b2'' , λ ())
  Sv* = (₁₊ w , λ ())

  iA iB iSv : ℤ ₚ
  iA  = (A* ⁻¹) .proj₁
  iB  = (B* ⁻¹) .proj₁
  iSv = (Sv* ⁻¹) .proj₁

  q* r* q₁* r₁* q₂* r₂* : ℤ* ₚ
  q*  = A* *' (B* ⁻¹)
  r*  = B* *' (A* ⁻¹)
  q₁* = A* *' (Sv* ⁻¹)
  r₁* = Sv* *' (A* ⁻¹)
  q₂* = Sv* *' (B* ⁻¹)
  r₂* = B* *' (Sv* ⁻¹)

  qv rv r₁v q₂v r₂v : ℤ ₚ
  qv  = ₁₊ a2' * iB
  rv  = ₁₊ b2'' * iA
  r₁v = ₁₊ w * iA
  q₂v = ₁₊ w * iB
  r₂v = ₁₊ b2'' * iSv

  private
    instA  = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}
    instB  = nztoℕ {y = ₁₊ b2''} {neq0 = λ ()}
    instSv = nztoℕ {y = ₁₊ w} {neq0 = λ ()}

  open Eq.≡-Reasoning

  -- (A/Sv)(Sv/B) ≡ A/B.
  v-q₁q₂ : (q₁* *' q₂*) .proj₁ ≡ q* .proj₁
  v-q₁q₂ = begin
    (₁₊ a2' * iSv) * (₁₊ w * iB)
      ≡⟨ *-assoc (₁₊ a2') iSv (₁₊ w * iB) ⟩
    ₁₊ a2' * (iSv * (₁₊ w * iB))
      ≡⟨ Eq.cong (₁₊ a2' *_) (Eq.sym (*-assoc iSv (₁₊ w) iB)) ⟩
    ₁₊ a2' * ((iSv * ₁₊ w) * iB)
      ≡⟨ Eq.cong (λ t → ₁₊ a2' * (t * iB))
           (lemma-⁻¹ˡ (₁₊ w) {{instSv}}) ⟩
    ₁₊ a2' * (₁ * iB)
      ≡⟨ Eq.cong (₁₊ a2' *_) (*-identityˡ iB) ⟩
    ₁₊ a2' * iB ∎

  -- r₁ · (1/q₂)² ≡ r · r₂.
  v-r₁q₂ : r₁v * (((q₂* ⁻¹) .proj₁) * ((q₂* ⁻¹) .proj₁)) ≡ rv * r₂v
  v-r₁q₂ = begin
    r₁v * (((q₂* ⁻¹) .proj₁) * ((q₂* ⁻¹) .proj₁))
      ≡⟨ Eq.cong (λ t → r₁v * (t * t)) (iexp Sv* B*) ⟩
    (₁₊ w * iA) * ((iSv * ₁₊ b2'') * (iSv * ₁₊ b2''))
      ≡⟨ Eq.cong (λ t → (₁₊ w * iA) * (t * t)) (*-comm iSv (₁₊ b2'')) ⟩
    (₁₊ w * iA) * ((₁₊ b2'' * iSv) * (₁₊ b2'' * iSv))
      ≡⟨ Eq.sym (*-assoc (₁₊ w * iA) (₁₊ b2'' * iSv) (₁₊ b2'' * iSv)) ⟩
    ((₁₊ w * iA) * (₁₊ b2'' * iSv)) * (₁₊ b2'' * iSv)
      ≡⟨ Eq.cong (_* (₁₊ b2'' * iSv)) claim ⟩
    ((₁₊ b2'' * iA)) * (₁₊ b2'' * iSv) ∎
    where
    claim : (₁₊ w * iA) * (₁₊ b2'' * iSv) ≡ ₁₊ b2'' * iA
    claim = begin
      (₁₊ w * iA) * (₁₊ b2'' * iSv)
        ≡⟨ Eq.cong (_* (₁₊ b2'' * iSv)) (*-comm (₁₊ w) iA) ⟩
      (iA * ₁₊ w) * (₁₊ b2'' * iSv)
        ≡⟨ *-assoc iA (₁₊ w) (₁₊ b2'' * iSv) ⟩
      iA * (₁₊ w * (₁₊ b2'' * iSv))
        ≡⟨ Eq.cong (iA *_) (Eq.cong (₁₊ w *_) (*-comm (₁₊ b2'') iSv)) ⟩
      iA * (₁₊ w * (iSv * ₁₊ b2''))
        ≡⟨ Eq.cong (iA *_) (Eq.sym (*-assoc (₁₊ w) iSv (₁₊ b2''))) ⟩
      iA * ((₁₊ w * iSv) * ₁₊ b2'')
        ≡⟨ Eq.cong (λ t → iA * (t * ₁₊ b2''))
             (lemma-⁻¹ʳ (₁₊ w) {{instSv}}) ⟩
      iA * (₁ * ₁₊ b2'')
        ≡⟨ Eq.cong (iA *_) (*-identityˡ (₁₊ b2'')) ⟩
      iA * ₁₊ b2''
        ≡⟨ *-comm iA (₁₊ b2'') ⟩
      ₁₊ b2'' * iA ∎

  -- q₂ · (-1) ≡ - q₂ under the (-1)-inverse.
  v-cneg : q₂v * (((-' (₁ , λ ())) ⁻¹) .proj₁) ≡ - q₂v
  v-cneg = begin
    q₂v * (((-' (₁ , λ ())) ⁻¹) .proj₁)
      ≡⟨ Eq.cong (q₂v *_) aux-₁⁻¹ ⟩
    q₂v * - ₁
      ≡⟨ Eq.sym (-‿distribʳ-* q₂v ₁) ⟩
    - (q₂v * ₁)
      ≡⟨ Eq.cong -_ (*-identityʳ q₂v) ⟩
    - q₂v ∎

  -- (r·r₂) · (1/(-1))² ≡ r·r₂.
  v-Sneg : (rv * r₂v) *
    ((((-' (₁ , λ ())) ⁻¹) .proj₁) * (((-' (₁ , λ ())) ⁻¹) .proj₁)) ≡
    rv * r₂v
  v-Sneg = begin
    (rv * r₂v) * ((((-' (₁ , λ ())) ⁻¹) .proj₁) *
                  (((-' (₁ , λ ())) ⁻¹) .proj₁))
      ≡⟨ Eq.cong (λ t → (rv * r₂v) * (t * t)) aux-₁⁻¹ ⟩
    (rv * r₂v) * (- ₁ * - ₁)
      ≡⟨ Eq.cong ((rv * r₂v) *_) aux-₁² ⟩
    (rv * r₂v) * ₁
      ≡⟨ *-identityʳ (rv * r₂v) ⟩
    rv * r₂v ∎

  -- q · (-1) ≡ - q.
  v-qneg : (q* *' (-' (₁ , λ ()))) .proj₁ ≡ (-' q*) .proj₁
  v-qneg = begin
    qv * - ₁
      ≡⟨ Eq.sym (-‿distribʳ-* qv ₁) ⟩
    - (qv * ₁)
      ≡⟨ Eq.cong -_ (*-identityʳ qv) ⟩
    - qv ∎

------------------------------------------------------------------------
-- The R-side normalization.

module _ {m : ℕ} (a2' b2'' w : Fin (₁₊ p-2))
  (eq-w : ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w) where

  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open BValues a2' b2'' w eq-w

  private
    h : Word (Gen (₂₊ m))
    h = H {m} ↑

    hp3 : Word (Gen (₂₊ m))
    hp3 = (H {m} ↑) ^ 3

    c : Word (Gen (₂₊ m))
    c = CZ

    W : Word (Gen (₂₊ m))
    W = h • (c • hp3)

  CANON : Word (Gen (₂₊ m))
  CANON = ZM (-' q*) ↑ •
    (S^ (rv * r₂v) ↑ • (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹)))))

  Rnorm : (ZM q₁* ↑ • S^ r₁v ↑) • (W • ((ZM q₂* ↑ • S^ r₂v ↑) • S⁻¹)) ≈
          CANON
  Rnorm = begin
    (ZM q₁* ↑ • S^ r₁v ↑) • (W • ((ZM q₂* ↑ • S^ r₂v ↑) • S⁻¹))
      ≈⟨ assoc ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ • (W • ((ZM q₂* ↑ • S^ r₂v ↑) • S⁻¹)))
      ≈⟨ cright (cright (trans assoc (cright (trans assoc
           (cright (cright assoc)))))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • (c • (hp3 • (ZM q₂* ↑ • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • (c • ((hp3 • ZM q₂* ↑) • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cright (cright (cleft (H3Mup q₂*))))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • (c • ((ZM (q₂* ⁻¹) ↑ • hp3) • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cright (cright assoc))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • (c • (ZM (q₂* ⁻¹) ↑ • (hp3 • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (cright (cright (sym assoc))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • ((c • ZM (q₂* ⁻¹) ↑) • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cright (cleft (cMup (q₂* ⁻¹))))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • ((ZM (q₂* ⁻¹) ↑ • CZ^ (((q₂* ⁻¹) ⁻¹) .proj₁)) •
        (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cright (cleft (cright (refl'
           (Eq.cong CZ^ (inv-involutive q₂*))))))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • ((ZM (q₂* ⁻¹) ↑ • CZ^ q₂v) • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cright assoc)) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (h • (ZM (q₂* ⁻¹) ↑ • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (cright (sym assoc)) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      ((h • ZM (q₂* ⁻¹) ↑) • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cleft (HMup (q₂* ⁻¹)))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      ((ZM ((q₂* ⁻¹) ⁻¹) ↑ • h) • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cleft (cleft
           (ZMvalup ((q₂* ⁻¹) ⁻¹) q₂* (inv-involutive q₂*))))) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      ((ZM q₂* ↑ • h) • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright assoc) ⟩
    ZM q₁* ↑ • (S^ r₁v ↑ •
      (ZM q₂* ↑ • (h • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (sym assoc) ⟩
    ZM q₁* ↑ • ((S^ r₁v ↑ • ZM q₂* ↑) •
      (h • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cleft (SZmoveup r₁v q₂* (rv * r₂v) v-r₁q₂)) ⟩
    ZM q₁* ↑ • ((ZM q₂* ↑ • S^ (rv * r₂v) ↑) •
      (h • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ sym assoc ⟩
    (ZM q₁* ↑ • (ZM q₂* ↑ • S^ (rv * r₂v) ↑)) •
      (h • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cleft (sym assoc) ⟩
    ((ZM q₁* ↑ • ZM q₂* ↑) • S^ (rv * r₂v) ↑) •
      (h • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cleft (cleft (Zmulup q₁* q₂* q* v-q₁q₂)) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • (CZ^ q₂v • (hp3 • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright (cright (cright (trans assoc (cright assoc)))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • (CZ^ q₂v • (h • (h • (h • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (cright (cright (sym assoc))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • (CZ^ q₂v • ((h • h) • (h • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (cright (cleft HHMup))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • (CZ^ q₂v • (ZM (-' (₁ , λ ())) ↑ • (h • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (cright (sym assoc)) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • ((CZ^ q₂v • ZM (-' (₁ , λ ())) ↑) • (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright (cright (cleft (cpowM (-' (₁ , λ ())) q₂v))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • ((ZM (-' (₁ , λ ())) ↑ •
        CZ^ (q₂v * (((-' (₁ , λ ())) ⁻¹) .proj₁))) •
        (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright (cright (cleft (cright (refl' (Eq.cong CZ^ v-cneg))))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • ((ZM (-' (₁ , λ ())) ↑ • CZ^ (- q₂v)) •
        (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright (cright assoc) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (h • (ZM (-' (₁ , λ ())) ↑ • (CZ^ (- q₂v) •
        (h • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ cright (sym assoc) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      ((h • ZM (-' (₁ , λ ())) ↑) • (CZ^ (- q₂v) •
        (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright (cleft (HMup (-' (₁ , λ ())))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      ((ZM ((-' (₁ , λ ())) ⁻¹) ↑ • h) • (CZ^ (- q₂v) •
        (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright (cleft (cleft (ZMvalup ((-' (₁ , λ ())) ⁻¹)
           (-' (₁ , λ ())) aux-₁⁻¹))) ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      ((ZM (-' (₁ , λ ())) ↑ • h) • (CZ^ (- q₂v) •
        (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cright assoc ⟩
    (ZM q* ↑ • S^ (rv * r₂v) ↑) •
      (ZM (-' (₁ , λ ())) ↑ • (h • (CZ^ (- q₂v) •
        (h • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ sym assoc ⟩
    ((ZM q* ↑ • S^ (rv * r₂v) ↑) • ZM (-' (₁ , λ ())) ↑) •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cleft assoc ⟩
    (ZM q* ↑ • (S^ (rv * r₂v) ↑ • ZM (-' (₁ , λ ())) ↑)) •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cleft (cright (SZmoveup (rv * r₂v) (-' (₁ , λ ()))
           (rv * r₂v) v-Sneg)) ⟩
    (ZM q* ↑ • (ZM (-' (₁ , λ ())) ↑ • S^ (rv * r₂v) ↑)) •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cleft (sym assoc) ⟩
    ((ZM q* ↑ • ZM (-' (₁ , λ ())) ↑) • S^ (rv * r₂v) ↑) •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ cleft (cleft (Zmulup q* (-' (₁ , λ ())) (-' q*) v-qneg)) ⟩
    (ZM (-' q*) ↑ • S^ (rv * r₂v) ↑) •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))
      ≈⟨ assoc ⟩
    ZM (-' q*) ↑ •
      (S^ (rv * r₂v) ↑ • (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))) ∎
