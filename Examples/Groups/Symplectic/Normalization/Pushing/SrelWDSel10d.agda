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
  using (-‿distribʳ-* ; -‿distribˡ-* ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (iexp ; ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)

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

------------------------------------------------------------------------
-- The L-side tail: H↑ • S^(-q₂)↑ • H↑³ collapses to the r₂-unit, by
-- three derived-7 rounds and Borel merges.

module TailValues (a2' b2'' w : Fin (₁₊ p-2))
  (eq-w : ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w) where

  open BValues a2' b2'' w eq-w public

  it₃f : ℤ ₚ
  it₃f = (r₂* ⁻¹) .proj₁

  private
    instR₂ = nztoℕ {y = r₂* .proj₁} {neq0 = r₂* .proj₂}

  vg' : - (((-' q₂*) ⁻¹) .proj₁) ≡ r₂v
  vg' = Eq.trans (Eq.cong -_ (ineg q₂* (-' q₂*) Eq.refl))
    (Eq.trans (-‿involutive ((q₂* ⁻¹) .proj₁))
    (Eq.trans (iexp Sv* B*) (*-comm iSv (₁₊ b2''))))

  vt1 : - it₃f * (r₂v * r₂v) ≡ - r₂v
  vt1 = Eq.trans (Eq.sym (-‿distribˡ-* it₃f (r₂v * r₂v)))
    (Eq.cong -_ (Eq.trans (Eq.sym (*-assoc it₃f r₂v r₂v))
      (Eq.trans (Eq.cong (_* r₂v)
          (lemma-⁻¹ˡ (r₂* .proj₁) {{instR₂}}))
        (*-identityˡ r₂v))))

  vbig : ((r₂* *' (r₂* ⁻¹)) *' (-' (₁ , λ ()))) .proj₁ ≡
         (-' (₁ , λ ())) .proj₁
  vbig = Eq.trans (Eq.cong (_* - ₁)
      (lemma-⁻¹ʳ (r₂* .proj₁) {{instR₂}}))
    (*-identityˡ (- ₁))

  vslot : - it₃f ≡ (-' q₂*) .proj₁
  vslot = Eq.cong -_
    (Eq.trans (iexp B* Sv*) (*-comm iB (₁₊ w)))

  vt5 : r₂v * (it₃f * it₃f) ≡ it₃f
  vt5 = Eq.trans (Eq.sym (*-assoc r₂v it₃f it₃f))
    (Eq.trans (Eq.cong (_* it₃f)
        (lemma-⁻¹ʳ (r₂* .proj₁) {{instR₂}}))
      (*-identityˡ it₃f))

  vneg-l : ((-' (₁ , λ ())) *' r₂*) .proj₁ ≡ (-' r₂*) .proj₁
  vneg-l = Eq.trans (*-comm (- ₁) r₂v)
    (Eq.trans (Eq.sym (-‿distribʳ-* r₂v ₁))
      (Eq.cong -_ (*-identityʳ r₂v)))

  negneg : ∀ (x y : ℤ ₚ) → - x * - y ≡ x * y
  negneg x y = Eq.trans (Eq.sym (-‿distribˡ-* x (- y)))
    (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* x y)))
      (-‿involutive (x * y)))

  vm3 : - r₂v * (((-' r₂*) ⁻¹) .proj₁ * ((-' r₂*) ⁻¹) .proj₁) ≡ - it₃f
  vm3 = Eq.trans (Eq.cong (λ t → - r₂v * (t * t))
      (ineg r₂* (-' r₂*) Eq.refl))
    (Eq.trans (Eq.cong (- r₂v *_) (negneg it₃f it₃f))
    (Eq.trans (Eq.sym (-‿distribˡ-* r₂v (it₃f * it₃f)))
      (Eq.cong -_ vt5)))

module _ {m : ℕ} (a2' b2'' w : Fin (₁₊ p-2))
  (eq-w : ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w) where

  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open TailValues a2' b2'' w eq-w

  private
    module L0m = Lemmas0 m

    h : Word (Gen (₂₊ m))
    h = H {m} ↑

    hp3 : Word (Gen (₂₊ m))
    hp3 = (H {m} ↑) ^ 3

  -- The M-headed derived-7, lifted.
  d7fullup : ∀ (x y : ℤ* ₚ) →
    ZM y ↑ • (H {m} ↑ • (S^ (x .proj₁) ↑ • H ↑)) ≈
    S^ (- ((x ⁻¹) .proj₁) * (y .proj₁ * y .proj₁)) ↑ •
      (ZM ((y *' (x ⁻¹)) *' (-' (₁ , λ ()))) ↑ •
        (H ↑ • S^ (- ((x ⁻¹) .proj₁)) ↑))
  d7fullup x y = lemma-cong↑
    (ZM y • (H • (S^ (x .proj₁) • H)))
    (S^ (- ((x ⁻¹) .proj₁) * (y .proj₁ * y .proj₁)) •
      (ZM ((y *' (x ⁻¹)) *' (-' (₁ , λ ()))) •
        (H • S^ (- ((x ⁻¹) .proj₁)))))
    (L0m.derived-7 (x .proj₁) (y .proj₁) (x .proj₂) (y .proj₂))

  Ttail : h • (S^ (- q₂v) ↑ • hp3) ≈
          ZM (-' r₂*) ↑ • (S^ it₃f ↑ • (h • S^ r₂v ↑))
  Ttail = begin
    h • (S^ (- q₂v) ↑ • hp3)
      ≈⟨ cright (sym assoc) ⟩
    h • ((S^ (- q₂v) ↑ • h) • (h • h))
      ≈⟨ sym assoc ⟩
    (h • (S^ (- q₂v) ↑ • h)) • (h • h)
      ≈⟨ cleft (d7εup (-' q₂*)) ⟩
    (S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑ •
      (ZM (-' ((-' q₂*) ⁻¹)) ↑ •
        (h • S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑))) • (h • h)
      ≈⟨ cleft (cleft (refl' (Eq.cong (λ t → S^ t ↑) vg'))) ⟩
    (S^ r₂v ↑ • (ZM (-' ((-' q₂*) ⁻¹)) ↑ •
      (h • S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑))) • (h • h)
      ≈⟨ cleft (cright (cleft (ZMvalup (-' ((-' q₂*) ⁻¹)) r₂* vg'))) ⟩
    (S^ r₂v ↑ • (ZM r₂* ↑ •
      (h • S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑))) • (h • h)
      ≈⟨ cleft (cright (cright (cright (refl'
           (Eq.cong (λ t → S^ t ↑) vg'))))) ⟩
    (S^ r₂v ↑ • (ZM r₂* ↑ • (h • S^ r₂v ↑))) • (h • h)
      ≈⟨ assoc ⟩
    S^ r₂v ↑ • ((ZM r₂* ↑ • (h • S^ r₂v ↑)) • (h • h))
      ≈⟨ cright assoc ⟩
    S^ r₂v ↑ • (ZM r₂* ↑ • ((h • S^ r₂v ↑) • (h • h)))
      ≈⟨ cright (cright assoc) ⟩
    S^ r₂v ↑ • (ZM r₂* ↑ • (h • (S^ r₂v ↑ • (h • h))))
      ≈⟨ cright (cright (cright (sym assoc))) ⟩
    S^ r₂v ↑ • (ZM r₂* ↑ • (h • ((S^ r₂v ↑ • h) • h)))
      ≈⟨ cright (cright (sym assoc)) ⟩
    S^ r₂v ↑ • (ZM r₂* ↑ • ((h • (S^ r₂v ↑ • h)) • h))
      ≈⟨ cright (sym assoc) ⟩
    S^ r₂v ↑ • ((ZM r₂* ↑ • (h • (S^ r₂v ↑ • h))) • h)
      ≈⟨ cright (cleft (d7fullup r₂* r₂*)) ⟩
    S^ r₂v ↑ • ((S^ (- it₃f * (r₂v * r₂v)) ↑ •
      (ZM ((r₂* *' (r₂* ⁻¹)) *' (-' (₁ , λ ()))) ↑ •
        (h • S^ (- it₃f) ↑))) • h)
      ≈⟨ cright (cleft (cleft (refl' (Eq.cong (λ t → S^ t ↑) vt1)))) ⟩
    S^ r₂v ↑ • ((S^ (- r₂v) ↑ •
      (ZM ((r₂* *' (r₂* ⁻¹)) *' (-' (₁ , λ ()))) ↑ •
        (h • S^ (- it₃f) ↑))) • h)
      ≈⟨ cright (cleft (cright (cleft (ZMvalup
           ((r₂* *' (r₂* ⁻¹)) *' (-' (₁ , λ ())))
           (-' (₁ , λ ())) vbig)))) ⟩
    S^ r₂v ↑ • ((S^ (- r₂v) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      (h • S^ (- it₃f) ↑))) • h)
      ≈⟨ cright (cleft (cright (cright (cright (refl'
           (Eq.cong (λ t → S^ t ↑) vslot)))))) ⟩
    S^ r₂v ↑ • ((S^ (- r₂v) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      (h • S^ ((-' q₂*) .proj₁) ↑))) • h)
      ≈⟨ cright assoc ⟩
    S^ r₂v ↑ • (S^ (- r₂v) ↑ • ((ZM (-' (₁ , λ ())) ↑ •
      (h • S^ ((-' q₂*) .proj₁) ↑)) • h))
      ≈⟨ cright (cright assoc) ⟩
    S^ r₂v ↑ • (S^ (- r₂v) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      ((h • S^ ((-' q₂*) .proj₁) ↑) • h)))
      ≈⟨ cright (cright (cright assoc)) ⟩
    S^ r₂v ↑ • (S^ (- r₂v) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      (h • (S^ ((-' q₂*) .proj₁) ↑ • h))))
      ≈⟨ sym assoc ⟩
    (S^ r₂v ↑ • S^ (- r₂v) ↑) • (ZM (-' (₁ , λ ())) ↑ •
      (h • (S^ ((-' q₂*) .proj₁) ↑ • h)))
      ≈⟨ cleft (trans (Sk+lup r₂v (- r₂v)) (refl'
           (Eq.cong (λ t → S^ t ↑) (+-inverseʳ r₂v)))) ⟩
    S^ ₀ ↑ • (ZM (-' (₁ , λ ())) ↑ •
      (h • (S^ ((-' q₂*) .proj₁) ↑ • h)))
      ≈⟨ left-unit ⟩
    ZM (-' (₁ , λ ())) ↑ • (h • (S^ ((-' q₂*) .proj₁) ↑ • h))
      ≈⟨ cright (d7εup (-' q₂*)) ⟩
    ZM (-' (₁ , λ ())) ↑ • (S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑ •
      (ZM (-' ((-' q₂*) ⁻¹)) ↑ •
        (h • S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑)))
      ≈⟨ cright (cleft (refl' (Eq.cong (λ t → S^ t ↑) vg'))) ⟩
    ZM (-' (₁ , λ ())) ↑ • (S^ r₂v ↑ •
      (ZM (-' ((-' q₂*) ⁻¹)) ↑ •
        (h • S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑)))
      ≈⟨ cright (cright (cleft (ZMvalup (-' ((-' q₂*) ⁻¹)) r₂* vg'))) ⟩
    ZM (-' (₁ , λ ())) ↑ • (S^ r₂v ↑ • (ZM r₂* ↑ •
      (h • S^ (- (((-' q₂*) ⁻¹) .proj₁)) ↑)))
      ≈⟨ cright (cright (cright (cright (refl'
           (Eq.cong (λ t → S^ t ↑) vg'))))) ⟩
    ZM (-' (₁ , λ ())) ↑ • (S^ r₂v ↑ • (ZM r₂* ↑ • (h • S^ r₂v ↑)))
      ≈⟨ cright (sym assoc) ⟩
    ZM (-' (₁ , λ ())) ↑ • ((S^ r₂v ↑ • ZM r₂* ↑) • (h • S^ r₂v ↑))
      ≈⟨ cright (cleft (SZmoveup r₂v r₂* it₃f vt5)) ⟩
    ZM (-' (₁ , λ ())) ↑ • ((ZM r₂* ↑ • S^ it₃f ↑) • (h • S^ r₂v ↑))
      ≈⟨ cright assoc ⟩
    ZM (-' (₁ , λ ())) ↑ • (ZM r₂* ↑ • (S^ it₃f ↑ • (h • S^ r₂v ↑)))
      ≈⟨ sym assoc ⟩
    (ZM (-' (₁ , λ ())) ↑ • ZM r₂* ↑) • (S^ it₃f ↑ • (h • S^ r₂v ↑))
      ≈⟨ cleft (Zmulup (-' (₁ , λ ())) r₂* (-' r₂*) vneg-l) ⟩
    ZM (-' r₂*) ↑ • (S^ it₃f ↑ • (h • S^ r₂v ↑)) ∎


------------------------------------------------------------------------
-- The value kit for the L-side normalization.

module LValues (a2' b2'' w : Fin (₁₊ p-2))
  (eq-w : ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w) where

  open TailValues a2' b2'' w eq-w public

  irf : ℤ ₚ
  irf = (r* ⁻¹) .proj₁

  private
    instA  = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}
    instB  = nztoℕ {y = ₁₊ b2''} {neq0 = λ ()}
    instSv = nztoℕ {y = ₁₊ w} {neq0 = λ ()}
    instR  = nztoℕ {y = r* .proj₁} {neq0 = r* .proj₂}

  open Eq.≡-Reasoning

  v-a : ((q* ⁻¹) *' (-' (₁ , λ ()))) .proj₁ ≡ (-' r*) .proj₁
  v-a = begin
    ((q* ⁻¹) .proj₁) * - ₁
      ≡⟨ Eq.cong (_* - ₁) (iexp A* B*) ⟩
    (iA * ₁₊ b2'') * - ₁
      ≡⟨ Eq.sym (-‿distribʳ-* (iA * ₁₊ b2'') ₁) ⟩
    - ((iA * ₁₊ b2'') * ₁)
      ≡⟨ Eq.cong -_ (Eq.trans (*-identityʳ (iA * ₁₊ b2''))
           (*-comm iA (₁₊ b2''))) ⟩
    - (₁₊ b2'' * iA) ∎

  v-b : - irf * ((((-' (r* ⁻¹)) ⁻¹) .proj₁) *
                 (((-' (r* ⁻¹)) ⁻¹) .proj₁)) ≡ - rv
  v-b = begin
    - irf * ((((-' (r* ⁻¹)) ⁻¹) .proj₁) * (((-' (r* ⁻¹)) ⁻¹) .proj₁))
      ≡⟨ Eq.cong (λ t → - irf * (t * t))
           (Eq.trans (ineg (r* ⁻¹) (-' (r* ⁻¹)) Eq.refl)
             (Eq.cong -_ (inv-involutive r*))) ⟩
    - irf * (- rv * - rv)
      ≡⟨ Eq.cong (- irf *_) (negneg rv rv) ⟩
    - irf * (rv * rv)
      ≡⟨ Eq.sym (-‿distribˡ-* irf (rv * rv)) ⟩
    - (irf * (rv * rv))
      ≡⟨ Eq.cong -_ (Eq.trans (Eq.sym (*-assoc irf rv rv))
           (Eq.trans (Eq.cong (_* rv)
               (lemma-⁻¹ˡ (r* .proj₁) {{instR}}))
             (*-identityˡ rv))) ⟩
    - rv ∎

  v-c : ((-' r*) *' (-' (r* ⁻¹))) .proj₁ ≡ ₁
  v-c = Eq.trans (negneg rv irf) (lemma-⁻¹ʳ (r* .proj₁) {{instR}})

  v-d : - rv + - ₁ ≡ - r₁v
  v-d = Eq.trans (-‿+-comm rv ₁) (Eq.cong -_ inner)
    where
    inner : rv + ₁ ≡ r₁v
    inner = begin
      rv + ₁
        ≡⟨ Eq.cong (rv +_) (Eq.sym (lemma-⁻¹ʳ (₁₊ a2') {{instA}})) ⟩
      ₁₊ b2'' * iA + ₁₊ a2' * iA
        ≡⟨ Eq.sym (*-distribʳ-+ iA (₁₊ b2'') (₁₊ a2')) ⟩
      (₁₊ b2'' + ₁₊ a2') * iA
        ≡⟨ Eq.cong (_* iA) eq-w ⟩
      ₁₊ w * iA ∎

  vAB : ₁₊ a2' + - ₁₊ w ≡ - ₁₊ b2''
  vAB = begin
    ₁₊ a2' + - ₁₊ w
      ≡⟨ Eq.cong (λ t → ₁₊ a2' + - t) (Eq.sym eq-w) ⟩
    ₁₊ a2' + - (₁₊ b2'' + ₁₊ a2')
      ≡⟨ Eq.cong (₁₊ a2' +_) (Eq.sym (-‿+-comm (₁₊ b2'') (₁₊ a2'))) ⟩
    ₁₊ a2' + (- ₁₊ b2'' + - ₁₊ a2')
      ≡⟨ Eq.cong (₁₊ a2' +_) (+-comm (- ₁₊ b2'') (- ₁₊ a2')) ⟩
    ₁₊ a2' + (- ₁₊ a2' + - ₁₊ b2'')
      ≡⟨ Eq.sym (+-assoc (₁₊ a2') (- ₁₊ a2') (- ₁₊ b2'')) ⟩
    (₁₊ a2' + - ₁₊ a2') + - ₁₊ b2''
      ≡⟨ Eq.cong (_+ - ₁₊ b2'') (+-inverseʳ (₁₊ a2')) ⟩
    ₀ + - ₁₊ b2''
      ≡⟨ +-identityˡ (- ₁₊ b2'') ⟩
    - ₁₊ b2'' ∎

  v-e : ((r₁* ⁻¹) .proj₁) + - ₁ ≡ - r₂v
  v-e = begin
    ((r₁* ⁻¹) .proj₁) + - ₁
      ≡⟨ Eq.cong₂ _+_ (iexp Sv* A*)
           (Eq.cong -_ (Eq.sym (lemma-⁻¹ˡ (₁₊ w) {{instSv}}))) ⟩
    iSv * ₁₊ a2' + - (iSv * ₁₊ w)
      ≡⟨ Eq.cong (iSv * ₁₊ a2' +_) (-‿distribʳ-* iSv (₁₊ w)) ⟩
    iSv * ₁₊ a2' + iSv * - ₁₊ w
      ≡⟨ Eq.sym (*-distribˡ-+ iSv (₁₊ a2') (- ₁₊ w)) ⟩
    iSv * (₁₊ a2' + - ₁₊ w)
      ≡⟨ Eq.cong (iSv *_) vAB ⟩
    iSv * - ₁₊ b2''
      ≡⟨ Eq.sym (-‿distribʳ-* iSv (₁₊ b2'')) ⟩
    - (iSv * ₁₊ b2'')
      ≡⟨ Eq.cong -_ (*-comm iSv (₁₊ b2'')) ⟩
    - r₂v ∎

  v-f : - ₁ + - irf ≡ - q₂v
  v-f = Eq.trans (-‿+-comm ₁ irf) (Eq.cong -_ inner)
    where
    inner : ₁ + irf ≡ q₂v
    inner = begin
      ₁ + irf
        ≡⟨ Eq.cong₂ _+_ (Eq.sym (lemma-⁻¹ʳ (₁₊ b2'') {{instB}}))
             (Eq.trans (iexp B* A*) (*-comm iB (₁₊ a2'))) ⟩
      ₁₊ b2'' * iB + ₁₊ a2' * iB
        ≡⟨ Eq.sym (*-distribʳ-+ iB (₁₊ b2'') (₁₊ a2')) ⟩
      (₁₊ b2'' + ₁₊ a2') * iB
        ≡⟨ Eq.cong (_* iB) eq-w ⟩
      ₁₊ w * iB ∎

  v-hc : (r₁* ⁻¹) .proj₁ ≡ q₁* .proj₁
  v-hc = Eq.trans (iexp Sv* A*) (*-comm iSv (₁₊ a2'))

  v-hz : - (((-' r₁*) ⁻¹) .proj₁) ≡ q₁* .proj₁
  v-hz = Eq.trans (Eq.cong -_ (ineg r₁* (-' r₁*) Eq.refl))
    (Eq.trans (-‿involutive ((r₁* ⁻¹) .proj₁)) v-hc)

  v-qq : (q₁* *' (-' q₂*)) .proj₁ ≡ (-' q*) .proj₁
  v-qq = begin
    (q₁* .proj₁) * - q₂v
      ≡⟨ Eq.sym (-‿distribʳ-* (q₁* .proj₁) q₂v) ⟩
    - (q₁* .proj₁ * q₂v)
      ≡⟨ Eq.cong -_ v-q₁q₂ ⟩
    - qv ∎

  v-hs : (q₁* .proj₁) * ((((-' q*) ⁻¹) .proj₁) *
                         (((-' q*) ⁻¹) .proj₁)) ≡ rv * r₂v
  v-hs = begin
    (q₁* .proj₁) * ((((-' q*) ⁻¹) .proj₁) * (((-' q*) ⁻¹) .proj₁))
      ≡⟨ Eq.cong (λ t → (q₁* .proj₁) * (t * t))
           (Eq.trans (ineg q* (-' q*) Eq.refl)
             (Eq.cong -_ (iexp A* B*))) ⟩
    (q₁* .proj₁) * (- (iA * ₁₊ b2'') * - (iA * ₁₊ b2''))
      ≡⟨ Eq.cong ((q₁* .proj₁) *_)
           (negneg (iA * ₁₊ b2'') (iA * ₁₊ b2'')) ⟩
    (₁₊ a2' * iSv) * ((iA * ₁₊ b2'') * (iA * ₁₊ b2''))
      ≡⟨ Eq.sym (*-assoc (₁₊ a2' * iSv) (iA * ₁₊ b2'') (iA * ₁₊ b2'')) ⟩
    ((₁₊ a2' * iSv) * (iA * ₁₊ b2'')) * (iA * ₁₊ b2'')
      ≡⟨ Eq.cong₂ _*_ claim (*-comm iA (₁₊ b2'')) ⟩
    (₁₊ b2'' * iSv) * (₁₊ b2'' * iA)
      ≡⟨ *-comm r₂v rv ⟩
    rv * r₂v ∎
    where
    claim : (₁₊ a2' * iSv) * (iA * ₁₊ b2'') ≡ ₁₊ b2'' * iSv
    claim = begin
      (₁₊ a2' * iSv) * (iA * ₁₊ b2'')
        ≡⟨ Eq.cong (_* (iA * ₁₊ b2'')) (*-comm (₁₊ a2') iSv) ⟩
      (iSv * ₁₊ a2') * (iA * ₁₊ b2'')
        ≡⟨ *-assoc iSv (₁₊ a2') (iA * ₁₊ b2'') ⟩
      iSv * (₁₊ a2' * (iA * ₁₊ b2''))
        ≡⟨ Eq.cong (iSv *_) (Eq.sym (*-assoc (₁₊ a2') iA (₁₊ b2''))) ⟩
      iSv * ((₁₊ a2' * iA) * ₁₊ b2'')
        ≡⟨ Eq.cong (λ t → iSv * (t * ₁₊ b2''))
             (lemma-⁻¹ʳ (₁₊ a2') {{instA}}) ⟩
      iSv * (₁ * ₁₊ b2'')
        ≡⟨ Eq.cong (iSv *_) (*-identityˡ (₁₊ b2'')) ⟩
      iSv * ₁₊ b2''
        ≡⟨ *-comm iSv (₁₊ b2'') ⟩
      ₁₊ b2'' * iSv ∎


------------------------------------------------------------------------
-- The L-side normalization and the branch-B residual identity.

module _ {m : ℕ} (a2' b2'' w : Fin (₁₊ p-2))
  (eq-w : ₁₊ b2'' + ₁₊ a2' ≡ ₁₊ w) where

  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open LValues a2' b2'' w eq-w

  private
    h : Word (Gen (₂₊ m))
    h = H {m} ↑

    hp3 : Word (Gen (₂₊ m))
    hp3 = (H {m} ↑) ^ 3

    c : Word (Gen (₂₊ m))
    c = CZ

    W : Word (Gen (₂₊ m))
    W = h • (c • hp3)

    q₁f ir₁f : ℤ ₚ
    q₁f  = q₁* .proj₁
    ir₁f = (r₁* ⁻¹) .proj₁

    v-hz0 : - (((-' r₁*) ⁻¹) .proj₁) ≡ ir₁f
    v-hz0 = Eq.trans (Eq.cong -_ (ineg r₁* (-' r₁*) Eq.refl))
      (-‿involutive ir₁f)

    v-ct : ((-' r₂*) ⁻¹) .proj₁ ≡ - q₂v
    v-ct = Eq.trans (ineg r₂* (-' r₂*) Eq.refl)
      (Eq.cong -_ (Eq.trans (iexp B* Sv*) (*-comm iB (₁₊ w))))

    fixdownL : S⁻¹ {m} ↑ • (h • (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
               S⁻¹ ↑ • (h • (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹)))))
    fixdownL = Eq.cong
      (λ u → S⁻¹ ↑ • (h • (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

  Lnorm : W • ((ZM q* ↑ • S^ rv ↑) • W) ≈ CANON a2' b2'' w eq-w
  Lnorm = begin
    W • ((ZM q* ↑ • S^ rv ↑) • W)
      ≈⟨ trans assoc (trans (cright assoc)
           (cright (cright (cright assoc)))) ⟩
    h • (c • (hp3 • (ZM q* ↑ • (S^ rv ↑ • W))))
      ≈⟨ cright (cright (sym assoc)) ⟩
    h • (c • ((hp3 • ZM q* ↑) • (S^ rv ↑ • W)))
      ≈⟨ cright (cright (cleft (H3Mup q*))) ⟩
    h • (c • ((ZM (q* ⁻¹) ↑ • hp3) • (S^ rv ↑ • W)))
      ≈⟨ cright (cright assoc) ⟩
    h • (c • (ZM (q* ⁻¹) ↑ • (hp3 • (S^ rv ↑ • W))))
      ≈⟨ cright (cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright (cright (sym assoc))))
           (trans (cright (cright (sym assoc))) (sym assoc))))))) ⟩
    h • (c • (ZM (q* ⁻¹) ↑ •
      ((h • h) • ((h • (S^ rv ↑ • h)) • (c • hp3)))))
      ≈⟨ cright (cright (cright (cleft HHMup))) ⟩
    h • (c • (ZM (q* ⁻¹) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      ((h • (S^ rv ↑ • h)) • (c • hp3)))))
      ≈⟨ cright (cright (cright (cright (cleft (d7εup r*))))) ⟩
    h • (c • (ZM (q* ⁻¹) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      ((S^ (- irf) ↑ • (ZM (-' (r* ⁻¹)) ↑ • (h • S^ (- irf) ↑))) •
        (c • hp3)))))
      ≈⟨ cright (cright (cright (cright (trans assoc
           (trans (cright assoc) (cright (cright assoc))))))) ⟩
    h • (c • (ZM (q* ⁻¹) ↑ • (ZM (-' (₁ , λ ())) ↑ •
      (S^ (- irf) ↑ • (ZM (-' (r* ⁻¹)) ↑ •
        (h • (S^ (- irf) ↑ • (c • hp3))))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (cleft (Zmulup (q* ⁻¹) (-' (₁ , λ ())) (-' r*) v-a)))) ⟩
    h • (c • (ZM (-' r*) ↑ • (S^ (- irf) ↑ • (ZM (-' (r* ⁻¹)) ↑ •
      (h • (S^ (- irf) ↑ • (c • hp3)))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (SZmoveup (- irf) (-' (r* ⁻¹)) (- rv) v-b))
             assoc)))) ⟩
    h • (c • (ZM (-' r*) ↑ • (ZM (-' (r* ⁻¹)) ↑ • (S^ (- rv) ↑ •
      (h • (S^ (- irf) ↑ • (c • hp3)))))))
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft
           (trans (Zmulup (-' r*) (-' (r* ⁻¹)) (₁ , λ ()) v-c) Mεup))
           left-unit))) ⟩
    h • (c • (S^ (- rv) ↑ • (h • (S^ (- irf) ↑ • (c • hp3)))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (comm-CZ-S^↑ (- rv))) assoc)) ⟩
    h • (S^ (- rv) ↑ • (c • (h • (S^ (- irf) ↑ • (c • hp3)))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (comm-CZ-S^↑ (- irf)))) assoc))))) ⟩
    h • (S^ (- rv) ↑ • (c • (h • (c • (S^ (- irf) ↑ • hp3)))))
      ≈⟨ cright (cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownL)))))) ⟩
    h • (S^ (- rv) ↑ • ((S⁻¹ ↑ • (h • (S⁻¹ ↑ • (c • (h •
      (S⁻¹ ↑ • S⁻¹)))))) • (S^ (- irf) ↑ • hp3)))
      ≈⟨ cright (trans (sym assoc) (cleft (trans (sym assoc)
           (trans (cleft (cright (refl'
               (Eq.cong _↑ (Eq.sym SIfix)))))
             (cleft (trans (Sk+lup (- rv) (- ₁))
               (refl' (Eq.cong (λ t → S^ t ↑) v-d)))))))) ⟩
    h • ((S^ (- r₁v) ↑ • (h • (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹)))))) •
      (S^ (- irf) ↑ • hp3))
      ≈⟨ sym assoc ⟩
    (h • (S^ (- r₁v) ↑ • (h • (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))))) •
      (S^ (- irf) ↑ • hp3)
      ≈⟨ cleft (trans (cright (sym assoc)) (sym assoc)) ⟩
    ((h • (S^ (- r₁v) ↑ • h)) • (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))) •
      (S^ (- irf) ↑ • hp3)
      ≈⟨ cleft (cleft (d7εup (-' r₁*))) ⟩
    ((S^ (- (((-' r₁*) ⁻¹) .proj₁)) ↑ • (ZM (-' ((-' r₁*) ⁻¹)) ↑ •
      (h • S^ (- (((-' r₁*) ⁻¹) .proj₁)) ↑))) •
      (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))) • (S^ (- irf) ↑ • hp3)
      ≈⟨ cleft (cleft (cleft (refl' (Eq.cong (λ t → S^ t ↑) v-hz)))) ⟩
    ((S^ q₁f ↑ • (ZM (-' ((-' r₁*) ⁻¹)) ↑ •
      (h • S^ (- (((-' r₁*) ⁻¹) .proj₁)) ↑))) •
      (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))) • (S^ (- irf) ↑ • hp3)
      ≈⟨ cleft (cleft (cright (cleft
           (ZMvalup (-' ((-' r₁*) ⁻¹)) q₁* v-hz)))) ⟩
    ((S^ q₁f ↑ • (ZM q₁* ↑ •
      (h • S^ (- (((-' r₁*) ⁻¹) .proj₁)) ↑))) •
      (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))) • (S^ (- irf) ↑ • hp3)
      ≈⟨ cleft (cleft (cright (cright (cright (refl'
           (Eq.cong (λ t → S^ t ↑) v-hz0)))))) ⟩
    ((S^ q₁f ↑ • (ZM q₁* ↑ • (h • S^ ir₁f ↑))) •
      (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))) • (S^ (- irf) ↑ • hp3)
      ≈⟨ cleft (trans assoc (trans (cright assoc)
           (cright (cright assoc)))) ⟩
    (S^ q₁f ↑ • (ZM q₁* ↑ • (h • (S^ ir₁f ↑ •
      (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹)))))))) • (S^ (- irf) ↑ • hp3)
      ≈⟨ trans assoc (trans (cright assoc)
           (cright (cright assoc))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • ((S^ ir₁f ↑ •
      (S⁻¹ ↑ • (c • (h • (S⁻¹ ↑ • S⁻¹))))) • (S^ (- irf) ↑ • hp3))))
      ≈⟨ cright (cright (cright (trans assoc (cright assoc)))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (S^ ir₁f ↑ • (S⁻¹ ↑ •
      ((c • (h • (S⁻¹ ↑ • S⁻¹))) • (S^ (- irf) ↑ • hp3))))))
      ≈⟨ cright (cright (cright (trans (sym assoc) (cleft
           (trans (cright (refl' (Eq.cong _↑ (Eq.sym SIfix))))
             (trans (Sk+lup ir₁f (- ₁))
               (refl' (Eq.cong (λ t → S^ t ↑) v-e)))))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (S^ (- r₂v) ↑ •
      ((c • (h • (S⁻¹ ↑ • S⁻¹))) • (S^ (- irf) ↑ • hp3)))))
      ≈⟨ cright (cright (cright (cright (trans assoc
           (cright (trans assoc (cright assoc))))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (S^ (- r₂v) ↑ • (c • (h •
      (S⁻¹ ↑ • (S⁻¹ • (S^ (- irf) ↑ • hp3))))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (comm-CZ-S^↑ (- r₂v)))) assoc)))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (S^ (- r₂v) ↑ • (h •
      (S⁻¹ ↑ • (S⁻¹ • (S^ (- irf) ↑ • hp3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (SdownW (S^ (- irf))))
             (trans assoc (cright (SdownW (H ^ 3)))))))))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (S^ (- r₂v) ↑ • (h •
      (S⁻¹ ↑ • (S^ (- irf) ↑ • (hp3 • S⁻¹))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft (trans (cleft (refl'
               (Eq.cong _↑ (Eq.sym SIfix))))
             (trans (Sk+lup (- ₁) (- irf))
               (refl' (Eq.cong (λ t → S^ t ↑) v-f))))))))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (S^ (- r₂v) ↑ • (h •
      (S^ (- q₂v) ↑ • (hp3 • S⁻¹)))))))
      ≈⟨ cright (cright (cright (cright (cright (trans
           (cright (sym assoc)) (sym assoc)))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (S^ (- r₂v) ↑ •
      ((h • (S^ (- q₂v) ↑ • hp3)) • S⁻¹)))))
      ≈⟨ cright (cright (cright (cright (cright (cleft
           (Ttail a2' b2'' w eq-w)))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (S^ (- r₂v) ↑ •
      ((ZM (-' r₂*) ↑ • (S^ it₃f ↑ • (h • S^ r₂v ↑))) • S⁻¹)))))
      ≈⟨ cright (cright (cright (cright (cright (trans assoc
           (trans (cright assoc) (cright (cright assoc)))))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (S^ (- r₂v) ↑ •
      (ZM (-' r₂*) ↑ • (S^ it₃f ↑ • (h • (S^ r₂v ↑ • S⁻¹))))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (SZmoveup (- r₂v) (-' r₂*) (- it₃f) vm3))
             assoc))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (ZM (-' r₂*) ↑ •
      (S^ (- it₃f) ↑ • (S^ it₃f ↑ • (h • (S^ r₂v ↑ • S⁻¹))))))))
      ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (trans (Sk+lup (- it₃f) it₃f)
               (refl' (Eq.cong (λ t → S^ t ↑) (+-inverseˡ it₃f)))))
             left-unit)))))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (c • (ZM (-' r₂*) ↑ •
      (h • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (trans (cMup (-' r₂*))
               (cright (refl' (Eq.cong CZ^ v-ct))))) assoc)))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (h • (ZM (-' r₂*) ↑ •
      (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (trans (HMup (-' r₂*))
               (cleft (ZMvalup ((-' r₂*) ⁻¹) (-' q₂*) v-ct))))
             assoc))) ⟩
    S^ q₁f ↑ • (ZM q₁* ↑ • (ZM (-' q₂*) ↑ •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))))
      ≈⟨ cright (trans (sym assoc)
           (cleft (Zmulup q₁* (-' q₂*) (-' q*) v-qq))) ⟩
    S^ q₁f ↑ • (ZM (-' q*) ↑ •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹)))))
      ≈⟨ trans (sym assoc) (trans (cleft
           (SZmoveup q₁f (-' q*) (rv * r₂v) v-hs)) assoc) ⟩
    ZM (-' q*) ↑ • (S^ (rv * r₂v) ↑ •
      (h • (CZ^ (- q₂v) • (h • (S^ r₂v ↑ • S⁻¹))))) ∎

  identityB : W • ((ZM q* ↑ • S^ rv ↑) • W) ≈
              (ZM q₁* ↑ • S^ r₁v ↑) •
                (W • ((ZM q₂* ↑ • S^ r₂v ↑) • S⁻¹))
  identityB = trans Lnorm (sym (Rnorm a2' b2'' w eq-w))

