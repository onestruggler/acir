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
  p-2 p-prime using (iexp ; ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
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
