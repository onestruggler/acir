------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case αβ: Y = b₂ - a₁
-- vanishes but Z = b₂ + a₂ ≡ z is nonzero (so z ≡ a₁ + a₂).  The
-- general clause-4 pad meets the a₂/z hpad unit; both sides normalize
-- to H • ZM(q̂₂)↑ • S^ r̂₂ ↑ • H↑ • CZ • S^ v₄ ↑ • H↑ • S⁻¹↑ • S^ u₄ • H³.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10k
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
  p-2 p-prime using (iexp ; ineg ; hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix ; Sp-1-S ; H5lift)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime

------------------------------------------------------------------------
-- The value kit under zAA : a₁ + a₂ ≡ z.

module ABValues (a1' a2' z : Fin (₁₊ p-2))
  (zAA : ₁₊ a1' + ₁₊ a2' ≡ ₁₊ z) where

  A₁* A₂* Z* : ℤ* ₚ
  A₁* = (₁₊ a1' , λ ())
  A₂* = (₁₊ a2' , λ ())
  Z*  = (₁₊ z , λ ())

  iA₁ iA₂ iZ : ℤ ₚ
  iA₁ = (A₁* ⁻¹) .proj₁
  iA₂ = (A₂* ⁻¹) .proj₁
  iZ  = (Z* ⁻¹) .proj₁

  q₂̂p r₂̂p : ℤ* ₚ
  q₂̂p = A₂* *' (Z* ⁻¹)
  r₂̂p = Z* *' (A₂* ⁻¹)

  u₁v v₁v u₄v v₄v r₂̂v : ℤ ₚ
  u₁v = - ₁₊ a2' * iA₁
  v₁v = - ₁₊ a1' * iA₂
  u₄v = - ₁₊ z * iA₁
  v₄v = - ₁₊ a1' * iZ
  r₂̂v = ₁₊ z * iA₂

  private
    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instA₂ = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}
    instZ  = nztoℕ {y = ₁₊ z} {neq0 = λ ()}

  open Eq.≡-Reasoning

  wA₂Z : ₁₊ a2' + - ₁₊ z ≡ - ₁₊ a1'
  wA₂Z = begin
    ₁₊ a2' + - ₁₊ z
      ≡⟨ Eq.cong (λ t → ₁₊ a2' + - t) (Eq.sym zAA) ⟩
    ₁₊ a2' + - (₁₊ a1' + ₁₊ a2')
      ≡⟨ Eq.cong (₁₊ a2' +_) (Eq.sym (-‿+-comm (₁₊ a1') (₁₊ a2'))) ⟩
    ₁₊ a2' + (- ₁₊ a1' + - ₁₊ a2')
      ≡⟨ Eq.cong (₁₊ a2' +_) (+-comm (- ₁₊ a1') (- ₁₊ a2')) ⟩
    ₁₊ a2' + (- ₁₊ a2' + - ₁₊ a1')
      ≡⟨ Eq.sym (+-assoc (₁₊ a2') (- ₁₊ a2') (- ₁₊ a1')) ⟩
    (₁₊ a2' + - ₁₊ a2') + - ₁₊ a1'
      ≡⟨ Eq.cong (_+ - ₁₊ a1') (+-inverseʳ (₁₊ a2')) ⟩
    ₀ + - ₁₊ a1'
      ≡⟨ +-identityˡ (- ₁₊ a1') ⟩
    - ₁₊ a1' ∎

  wα1 : v₁v + - ₁ ≡ - (₁₊ z * iA₂)
  wα1 = begin
    - ₁₊ a1' * iA₂ + - ₁
      ≡⟨ Eq.cong (- ₁₊ a1' * iA₂ +_) (Eq.cong -_
           (Eq.sym (lemma-⁻¹ʳ (₁₊ a2') {{instA₂}}))) ⟩
    - ₁₊ a1' * iA₂ + - (₁₊ a2' * iA₂)
      ≡⟨ Eq.cong (- ₁₊ a1' * iA₂ +_) (-‿distribˡ-* (₁₊ a2') iA₂) ⟩
    - ₁₊ a1' * iA₂ + - ₁₊ a2' * iA₂
      ≡⟨ Eq.sym (*-distribʳ-+ iA₂ (- ₁₊ a1') (- ₁₊ a2')) ⟩
    (- ₁₊ a1' + - ₁₊ a2') * iA₂
      ≡⟨ Eq.cong (_* iA₂) (Eq.trans (-‿+-comm (₁₊ a1') (₁₊ a2'))
           (Eq.cong -_ zAA)) ⟩
    - ₁₊ z * iA₂
      ≡⟨ Eq.sym (-‿distribˡ-* (₁₊ z) iA₂) ⟩
    - (₁₊ z * iA₂) ∎

  wα2 : - ₁ + u₁v ≡ u₄v
  wα2 = begin
    - ₁ + - ₁₊ a2' * iA₁
      ≡⟨ Eq.cong (_+ - ₁₊ a2' * iA₁) (Eq.cong -_
           (Eq.sym (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}}))) ⟩
    - (₁₊ a1' * iA₁) + - ₁₊ a2' * iA₁
      ≡⟨ Eq.cong (_+ - ₁₊ a2' * iA₁) (-‿distribˡ-* (₁₊ a1') iA₁) ⟩
    - ₁₊ a1' * iA₁ + - ₁₊ a2' * iA₁
      ≡⟨ Eq.sym (*-distribʳ-+ iA₁ (- ₁₊ a1') (- ₁₊ a2')) ⟩
    (- ₁₊ a1' + - ₁₊ a2') * iA₁
      ≡⟨ Eq.cong (_* iA₁) (Eq.trans (-‿+-comm (₁₊ a1') (₁₊ a2'))
           (Eq.cong -_ zAA)) ⟩
    - ₁₊ z * iA₁ ∎

  wα5 : - (((-' r₂̂p) ⁻¹) .proj₁) ≡ iZ * ₁₊ a2'
  wα5 = Eq.trans (Eq.cong -_ (ineg r₂̂p (-' r₂̂p) Eq.refl))
    (Eq.trans (-‿involutive ((r₂̂p ⁻¹) .proj₁)) (iexp Z* A₂*))

  wα6 : - (((-' r₂̂p) ⁻¹) .proj₁) ≡ q₂̂p .proj₁
  wα6 = Eq.trans wα5 (*-comm iZ (₁₊ a2'))

  wα3 : (iZ * ₁₊ a2') + - ₁ ≡ v₄v
  wα3 = begin
    iZ * ₁₊ a2' + - ₁
      ≡⟨ Eq.cong₂ _+_ (*-comm iZ (₁₊ a2'))
           (Eq.cong -_ (Eq.sym (lemma-⁻¹ʳ (₁₊ z) {{instZ}}))) ⟩
    ₁₊ a2' * iZ + - (₁₊ z * iZ)
      ≡⟨ Eq.cong (₁₊ a2' * iZ +_) (-‿distribˡ-* (₁₊ z) iZ) ⟩
    ₁₊ a2' * iZ + - ₁₊ z * iZ
      ≡⟨ Eq.sym (*-distribʳ-+ iZ (₁₊ a2') (- ₁₊ z)) ⟩
    (₁₊ a2' + - ₁₊ z) * iZ
      ≡⟨ Eq.cong (_* iZ) wA₂Z ⟩
    - ₁₊ a1' * iZ ∎

  wα4 : (iZ * ₁₊ a2') * (((q₂̂p ⁻¹) .proj₁) * ((q₂̂p ⁻¹) .proj₁)) ≡ r₂̂v
  wα4 = begin
    (iZ * ₁₊ a2') * (((q₂̂p ⁻¹) .proj₁) * ((q₂̂p ⁻¹) .proj₁))
      ≡⟨ Eq.cong (λ t → (iZ * ₁₊ a2') * (t * t)) (iexp A₂* Z*) ⟩
    (iZ * ₁₊ a2') * ((iA₂ * ₁₊ z) * (iA₂ * ₁₊ z))
      ≡⟨ Eq.sym (*-assoc (iZ * ₁₊ a2') (iA₂ * ₁₊ z) (iA₂ * ₁₊ z)) ⟩
    ((iZ * ₁₊ a2') * (iA₂ * ₁₊ z)) * (iA₂ * ₁₊ z)
      ≡⟨ Eq.cong (_* (iA₂ * ₁₊ z)) claim ⟩
    ₁ * (iA₂ * ₁₊ z)
      ≡⟨ Eq.trans (*-identityˡ (iA₂ * ₁₊ z)) (*-comm iA₂ (₁₊ z)) ⟩
    ₁₊ z * iA₂ ∎
    where
    claim : (iZ * ₁₊ a2') * (iA₂ * ₁₊ z) ≡ ₁
    claim = begin
      (iZ * ₁₊ a2') * (iA₂ * ₁₊ z)
        ≡⟨ *-assoc iZ (₁₊ a2') (iA₂ * ₁₊ z) ⟩
      iZ * (₁₊ a2' * (iA₂ * ₁₊ z))
        ≡⟨ Eq.cong (iZ *_) (Eq.sym (*-assoc (₁₊ a2') iA₂ (₁₊ z))) ⟩
      iZ * ((₁₊ a2' * iA₂) * ₁₊ z)
        ≡⟨ Eq.cong (λ t → iZ * (t * ₁₊ z))
             (lemma-⁻¹ʳ (₁₊ a2') {{instA₂}}) ⟩
      iZ * (₁ * ₁₊ z)
        ≡⟨ Eq.cong (iZ *_) (*-identityˡ (₁₊ z)) ⟩
      iZ * ₁₊ z
        ≡⟨ lemma-⁻¹ˡ (₁₊ z) {{instZ}} ⟩
      ₁ ∎

------------------------------------------------------------------------
-- The two chains and idαβ.

module _ {m : ℕ} (a1' a2' z : Fin (₁₊ p-2))
  (zAA : ₁₊ a1' + ₁₊ a2' ≡ ₁₊ z) where

  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open ABValues a1' a2' z zAA

  private
    module L0b = Lemmas0 (₁₊ m)

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

    PADg PADz : Word (Gen (₂₊ m))
    PADg = H • (H ↑ • (CZ • (S^ u₁v •
      (H ^ 3 • (S^ v₁v ↑ • (H ↑) ^ 3)))))
    PADz = H • (H ↑ • (CZ • (S^ u₄v •
      (H ^ 3 • (S^ v₄v ↑ • (H ↑) ^ 3)))))

    fixdownK : S⁻¹ {m} ↑ •
        (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdownK = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

    SkW : ∀ (k : ℤ ₚ) (w : Word (Gen (₁₊ m))) →
      S^ k • w ↑ ≈ w ↑ • S^ k
    SkW k w = comm⇒pow-comm {w = S} {v = w ↑} (toℕ k) 1
      (lemma-comm-S-w↑ w)

    SkCZ : ∀ (k : ℤ ₚ) → S^ k • CZ ≈ CZ • S^ k
    SkCZ k = comm⇒pow-comm {w = S} {v = CZ} (toℕ k) 1
      (sym (axiom comm-CZ-S↓))

    H3W : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
    H3W w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

  CANαβ : Word (Gen (₂₊ m))
  CANαβ = H • (ZM q₂̂p ↑ • (S^ r₂̂v ↑ • (H ↑ • (CZ • (S^ v₄v ↑ •
    (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3))))))))

  Lαβ : PADg • ((H ↑ • H ↑) • WD) ≈ CANαβ
  Lαβ = begin
    PADg • ((H ↑ • H ↑) • WD)
      ≈⟨ trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S^ u₁v • (H ^ 3 • (S^ v₁v ↑ •
      ((H ↑) ^ 3 • ((H ↑ • H ↑) • WD)))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft H5lift))))))) ⟩
    H • (H ↑ • (CZ • (S^ u₁v • (H ^ 3 • (S^ v₁v ↑ • (H ↑ • WD))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (H3W (S^ v₁v))) (trans assoc (cright
             (trans (sym assoc)
               (trans (cleft (H3W H)) assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S^ u₁v • (S^ v₁v ↑ • (H ↑ • (H ^ 3 • WD))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans assoc (trans (cright assoc)
           (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (axiom order-H)) left-unit)))))))))))  ⟩
    H • (H ↑ • (CZ • (S^ u₁v • (S^ v₁v ↑ • (H ↑ • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (SkW u₁v (S^ v₁v)))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (SkW u₁v H))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (SkCZ u₁v)) assoc)))))))))))) ⟩
    H • (H ↑ • (CZ • (S^ v₁v ↑ • (H ↑ • (CZ • (S^ u₁v • H ^ 3))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (comm-CZ-S^↑ v₁v)) assoc))) ⟩
    H • (H ↑ • (S^ v₁v ↑ • (CZ • (H ↑ • (CZ • (S^ u₁v • H ^ 3))))))
      ≈⟨ cright (cright (cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownK))))))) ⟩
    H • (H ↑ • (S^ v₁v ↑ • ((S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (H ↑ • (S⁻¹ ↑ • S⁻¹)))))) • (S^ u₁v • H ^ 3))))
      ≈⟨ cright (cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc)))))))))))) ⟩
    H • (H ↑ • (S^ v₁v ↑ • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (H ↑ • (S⁻¹ ↑ • (S⁻¹ • (S^ u₁v • H ^ 3))))))))))
      ≈⟨ cright (cright (trans (sym assoc) (cleft
           (trans (cright (refl' (Eq.cong _↑ (Eq.sym (SIfix {m})))))
           (trans (Sk+lup v₁v (- ₁))
             (refl' (Eq.cong (λ t → S^ t ↑) wα1))))))) ⟩
    H • (H ↑ • (S^ (- (₁₊ z * iA₂)) ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (H ↑ • (S⁻¹ ↑ • (S⁻¹ • (S^ u₁v • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (trans (sym assoc) (cleft
             (trans (cleft (refl' (Eq.sym (SIfix {₁₊ m}))))
             (trans (L0b.lemma-S^k+l (- ₁) u₁v)
               (refl' (Eq.cong S^ wα2))))))))))))) ⟩
    H • (H ↑ • (S^ (- (₁₊ z * iA₂)) ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3))))))))
      ≈⟨ cright (trans (cright (sym assoc)) (trans (sym assoc)
           (cleft (d7εup (-' r₂̂p))))) ⟩
    H • ((S^ (- (((-' r₂̂p) ⁻¹) .proj₁)) ↑ •
      (ZM (-' ((-' r₂̂p) ⁻¹)) ↑ •
        (H ↑ • S^ (- (((-' r₂̂p) ⁻¹) .proj₁)) ↑))) •
      (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3))))))
      ≈⟨ cright (trans (cleft (trans
           (cleft (refl' (Eq.cong (λ t → S^ t ↑) wα5)))
           (trans (cright (cleft (ZMvalup (-' ((-' r₂̂p) ⁻¹)) q₂̂p wα6)))
             (cright (cright (cright (refl'
               (Eq.cong (λ t → S^ t ↑) wα5))))))))
         (trans assoc (cright (trans assoc (cright assoc))))) ⟩
    H • (S^ (iZ * ₁₊ a2') ↑ • (ZM q₂̂p ↑ • (H ↑ •
      (S^ (iZ * ₁₊ a2') ↑ • (S⁻¹ ↑ • (CZ •
        (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc) (cleft
           (trans (cright (refl' (Eq.cong _↑ (Eq.sym (SIfix {m})))))
           (trans (Sk+lup (iZ * ₁₊ a2') (- ₁))
             (refl' (Eq.cong (λ t → S^ t ↑) wα3))))))))) ⟩
    H • (S^ (iZ * ₁₊ a2') ↑ • (ZM q₂̂p ↑ • (H ↑ •
      (S^ v₄v ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3))))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (SZmoveup (iZ * ₁₊ a2') q₂̂p r₂̂v wα4))
             assoc)) ⟩
    H • (ZM q₂̂p ↑ • (S^ r₂̂v ↑ • (H ↑ •
      (S^ v₄v ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (comm-CZ-S^↑ v₄v))) assoc))))) ⟩
    CANαβ ∎

  Rαβ : (ZM q₂̂p ↑ • S^ r₂̂v ↑) • (PADz • ((H ↑ • H ↑) • S⁻¹ ↑)) ≈ CANαβ
  Rαβ = begin
    (ZM q₂̂p ↑ • S^ r₂̂v ↑) • (PADz • ((H ↑ • H ↑) • S⁻¹ ↑))
      ≈⟨ trans assoc (cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc)))))))))))) ⟩
    ZM q₂̂p ↑ • (S^ r₂̂v ↑ • (H • (H ↑ • (CZ • (S^ u₄v •
      (H ^ 3 • (S^ v₄v ↑ • ((H ↑) ^ 3 • ((H ↑ • H ↑) • S⁻¹ ↑)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (trans (sym assoc) (cleft H5lift))))))))) ⟩
    ZM q₂̂p ↑ • (S^ r₂̂v ↑ • (H • (H ↑ • (CZ • (S^ u₄v •
      (H ^ 3 • (S^ v₄v ↑ • (H ↑ • S⁻¹ ↑))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (H3W (S^ v₄v)))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (H3W H))
             (trans assoc (cright (H3W S⁻¹)))))))))))))) ⟩
    ZM q₂̂p ↑ • (S^ r₂̂v ↑ • (H • (H ↑ • (CZ • (S^ u₄v •
      (S^ v₄v ↑ • (H ↑ • (S⁻¹ ↑ • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (SkW u₄v (S^ v₄v)))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (SkW u₄v H))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (SkW u₄v S⁻¹)) assoc)))))))))))))) ⟩
    ZM q₂̂p ↑ • (S^ r₂̂v ↑ • (H • (H ↑ • (CZ • (S^ v₄v ↑ •
      (H ↑ • (S⁻¹ ↑ • (S^ u₄v • H ^ 3))))))))
      ≈⟨ trans (cright (trans (sym assoc)
           (trans (cleft (sym (lemma-comm-H-w↑ (S^ r₂̂v)))) assoc)))
         (trans (sym assoc)
           (trans (cleft (sym (lemma-comm-H-w↑ (ZM q₂̂p)))) assoc)) ⟩
    CANαβ ∎

  idαβ : PADg • ((H ↑ • H ↑) • WD) ≈
         (ZM q₂̂p ↑ • S^ r₂̂v ↑) • (PADz • ((H ↑ • H ↑) • S⁻¹ ↑))
  idαβ = trans Lαβ (sym Rαβ)

------------------------------------------------------------------------
-- The αβ orbit assembly.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    WD' : Word (Gen (₂₊ m))
    WD' = H • (CZ • H ^ 3)

  c10-go-aaαβ : ∀ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    b2 + - ₁₊ a1' ≡ ₀ → b2 + ₁₊ a2' ≡ ₁₊ z →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-aaαβ b1 b2 a1' a2' z lm2 eq-Y eq-Z = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    beqY : b2 ≡ ₁₊ a1'
    beqY = Eq.trans (Eq.sym (+-identityʳ b2))
      (Eq.trans (Eq.cong (b2 +_) (Eq.sym (+-inverseˡ (₁₊ a1'))))
      (Eq.trans (Eq.sym (+-assoc b2 (- ₁₊ a1') (₁₊ a1')))
      (Eq.trans (Eq.cong (_+ ₁₊ a1') eq-Y)
        (+-identityˡ (₁₊ a1')))))

    zAA' : ₁₊ a1' + ₁₊ a2' ≡ ₁₊ z
    zAA' = Eq.trans (Eq.cong (_+ ₁₊ a2') (Eq.sym beqY)) eq-Z

    open ABValues a1' a2' z zAA' using (q₂̂p ; r₂̂v)

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    wNegZ : - ₁₊ a2' + - ₁₊ a1' ≡ - ₁₊ z
    wNegZ = Eq.trans (+-comm (- ₁₊ a2') (- ₁₊ a1'))
      (Eq.trans (-‿+-comm (₁₊ a1') (₁₊ a2')) (Eq.cong -_ zAA'))

    wZA : - ₁₊ a2' + ₁₊ z ≡ ₁₊ a1'
    wZA = Eq.trans (Eq.cong (- ₁₊ a2' +_) (Eq.sym zAA'))
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (+-comm (₁₊ a1') (₁₊ a2')))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ a2') (₁₊ a2') (₁₊ a1')))
      (Eq.trans (Eq.cong (_+ ₁₊ a1') (+-inverseˡ (₁₊ a2')))
        (+-identityˡ (₁₊ a1')))))

    wZneg : - ₁₊ z + ₁₊ a1' ≡ - ₁₊ a2'
    wZneg = Eq.trans (Eq.cong (_+ ₁₊ a1')
        (Eq.trans (Eq.cong -_ (Eq.sym zAA'))
        (Eq.trans (Eq.sym (-‿+-comm (₁₊ a1') (₁₊ a2')))
          (+-comm (- ₁₊ a1') (- ₁₊ a2')))))
      (Eq.trans (+-assoc (- ₁₊ a2') (- ₁₊ a1') (₁₊ a1'))
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (+-inverseˡ (₁₊ a1')))
        (+-identityʳ (- ₁₊ a2'))))

    r7αβ : (b1 + - ₁₊ z) + nsum p-1 (- ₁₊ a1') ≡ b1 + - ₁₊ a2'
    r7αβ = Eq.trans (Eq.cong ((b1 + - ₁₊ z) +_) nfixa1)
      (Eq.trans (+-assoc b1 (- ₁₊ z) (₁₊ a1'))
        (Eq.cong (b1 +_) wZneg))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') , inj₂ ((₀ , - ₁₊ z) , lm2))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            (H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹)
              .proj₁) • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹)
              .proj₁) ↑ • (H ↑) ^ 3)))))) • ((H ↑ • H ↑) • WD')
    L-fix = Eq.cong₂ _•_ (padSA a1' a2' b1 b2) (Eq.cong₂ _•_
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
        wNegZ)

    E₁raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , b2) , lm2)) S⁻¹) .proj₁
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ z , - ₁₊ a2') , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
              inj₂ ((₀ , - ₁₊ z) , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1k : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          (E₁raw ↑ , inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , ₁₊ z) , lm2)))
    r1k = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') b2 (λ ()))
                (Eq.cong (₁₊ a2' ,_)
                  (Eq.trans (Eq.cong (b2 +_) nfixa2) eq-Z)))))))

    r3k : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ z , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
          (E₃raw ↑ , inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ z , ₁₊ a1') , lm2)))
    r3k = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₁₊ z , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ z , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ z) (- ₁₊ a2') (λ ()))
                (Eq.cong (₁₊ z ,_)
                  (Eq.trans (Eq.cong (- ₁₊ a2' +_)
                      (Eq.trans (nsum-p-1 (- ₁₊ z))
                        (-‿involutive (₁₊ z))))
                    wZA)))))))

    r5k : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₁₊ z , ₁₊ a1' + - ₁₊ a1') , lm2))) (H ↑)) ≡
          ((H ↑ • H ↑) ,
           inj₂ ((₁₊ a1' , b1 + - ₁₊ z) , inj₂ ((₀ , - ₁₊ z) , lm2)))
    r5k = Eq.cong (λ v → ((Hdir (₁₊ z , v) ↓ᵏ m) ↑ ,
        inj₂ ((₁₊ a1' , b1 + - ₁₊ z) , inj₂ (Hd' (₁₊ z , v) , lm2))))
      (+-inverseʳ (₁₊ a1'))

    r6k : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₀ , - ₁₊ z) , lm2))) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₀ , - ₁₊ z) , lm2)))
    r6k = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₁₊ z) (inj₂ ((₀ , - ₁₊ z) , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₁₊ z) lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₁₊ z) , c))
          (Eq.trans (ract-S^-coset (₀ , - ₁₊ z) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₁₊ z))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            E₁raw ↑ • ((ZM q₂̂p • S^ r₂̂v) ↑ • (E₃raw ↑ •
              ((H • (H ↑ • (CZ • (S^ (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹)
                .proj₁) • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹)
                .proj₁) ↑ • (H ↑) ^ 3)))))) •
               ((H ↑ • H ↑) • ((S ^ p-1) ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1k)
      (Eq.cong (λ t → E₁raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_ (Eq.cong _↑ (hpad a2' z)) Eq.refl)
      (Eq.cong (λ t → (ZM q₂̂p • S^ r₂̂v) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3k)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_ (padSA a1' z b1 (₁₊ a1')) Eq.refl)
      (Eq.cong (λ t → (H • (H ↑ • (CZ • (S^ (- ₁₊ z *
          ((₁₊ a1' , λ ()) ⁻¹) .proj₁) • (H ^ 3 • (S^ (- ₁₊ a1' *
          ((₁₊ z , λ ()) ⁻¹) .proj₁) ↑ • (H ↑) ^ 3)))))) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5k)
      (Eq.cong (λ t → (H ↑ • H ↑) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6k)
      (Eq.cong ((S ^ p-1) ↑ •_)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₀ , - ₁₊ z) , lm2))) u) .proj₁)
          (↓-pow-S p-1)))))))))))))

    Rclean : E₁raw ↑ • ((ZM q₂̂p • S^ r₂̂v) ↑ • (E₃raw ↑ •
               ((H • (H ↑ • (CZ • (S^ (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹)
                 .proj₁) • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹)
                 .proj₁) ↑ • (H ↑) ^ 3)))))) •
                ((H ↑ • H ↑) • ((S ^ p-1) ↑ • E₇raw))))) ≈
             (ZM q₂̂p ↑ • S^ r₂̂v ↑) •
               ((H • (H ↑ • (CZ • (S^ (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹)
                 .proj₁) • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹)
                 .proj₁) ↑ • (H ↑) ^ 3)))))) •
                ((H ↑ • H ↑) • S⁻¹ ↑))
    Rclean =
      trans (trans (cleft (lemma-cong↑ E₁raw ε
          (ract-S^-resid-a+ (₁₊ a2' , b2) lm2 p-1 (λ ())))) left-unit)
      (cright (trans (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ z , - ₁₊ a2') lm2 p-1 (λ ()))))
          left-unit)
        (cright (cright (trans (cright
            (ract-S^-resid-a+ (₁₊ a1' , b1 + - ₁₊ z)
              (inj₂ ((₀ , - ₁₊ z) , lm2)) p-1 (λ ())))
          right-unit)))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (idαβ a1' a2' z zAA')
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1k)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3k)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5k)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6k)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₀ , - ₁₊ z) , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₁₊ z)
          (inj₂ ((₀ , - ₁₊ z) , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , - ₁₊ z) , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₁₊ z) (λ ())))
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , v) ,
            inj₂ ((₀ , - ₁₊ z) , lm2)))
          r7αβ)))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
               .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)

