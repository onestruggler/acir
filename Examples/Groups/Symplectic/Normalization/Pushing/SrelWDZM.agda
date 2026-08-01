------------------------------------------------------------------------
-- Presentations of groups
--
-- Well-definedness of the coset action on the group-specific axioms
-- (the srel case of ⁻¹[⇑]-wd'' in Normalization.agda), one axiom at a
-- time.  For an axiom u === t we must show the threaded action agrees:
-- (ract ᵗ) c u ≋ (ract ᵗ) c t.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Sum using (inj₁ ; inj₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)
import Relation.Binary.Reasoning.Setoid as SR
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_%_ ; m%n<n ; %-distribˡ-+ ; m*n%n≡0 ; m<n⇒m%n≡m ; m%n%n≡m%n)
open import Data.Product using (∃)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<)
import Data.Nat.Properties as NP
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (A-dir-S-power)
import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (M-↓ᵏ)

------------------------------------------------------------------------
-- ℤ*-value lemmas for collapsing products of Hdir escapes
-- ZM (u/v) • S^ (v/u): quotients telescope, inverse values expand.

quotient-mul : ∀ (U V W : ℤ* ₚ) →
  ((U *' (V ⁻¹)) *' (V *' (W ⁻¹))) .proj₁ ≡ (U *' (W ⁻¹)) .proj₁
quotient-mul U V W =
  Eq.trans (*-assoc u iv (v * iw))
  (Eq.trans (Eq.cong (u *_) (Eq.sym (*-assoc iv v iw)))
  (Eq.trans (Eq.cong (λ t → u * (t * iw))
              (lemma-⁻¹ˡ v {{nztoℕ {y = v} {neq0 = V .proj₂}}}))
            (Eq.cong (u *_) (*-identityˡ iw))))
  where
  u  = U .proj₁
  v  = V .proj₁
  iv = (V ⁻¹) .proj₁
  iw = (W ⁻¹) .proj₁

-- Inverse of a quotient V/W.
iexp : ∀ (V W : ℤ* ₚ) →
  ((V *' (W ⁻¹)) ⁻¹) .proj₁ ≡ (V ⁻¹) .proj₁ * W .proj₁
iexp V W = Eq.trans (inv-distrib V (W ⁻¹))
             (Eq.cong ((V ⁻¹) .proj₁ *_) (inv-involutive W))

-- Inverse value under negation of the argument.
ineg : ∀ (U Y : ℤ* ₚ) → Y .proj₁ ≡ - (U .proj₁) →
  (Y ⁻¹) .proj₁ ≡ - ((U ⁻¹) .proj₁)
ineg U Y eq = Eq.trans (inv-cong Y (-' U) eq) (inv-neg-comm U)

-- The core telescope: (b/a) · (a⁻¹/b⁻¹-squared) collapses.
ring-core : ∀ (A* B* : ℤ* ₚ) →
  let a = A* .proj₁ ; b = B* .proj₁
      ia = (A* ⁻¹) .proj₁ ; ib = (B* ⁻¹) .proj₁ in
  (b * ia) * ((ib * a) * (ib * a)) ≡ a * ib
ring-core A* B* =
  Eq.trans (Eq.cong (_* (X * X)) (Eq.sym iX-val))
  (Eq.trans (Eq.sym (*-assoc iX-e X X))
  (Eq.trans (Eq.cong (_* X)
              (lemma-⁻¹ˡ X {{nztoℕ {y = X} {neq0 = X* .proj₂}}}))
  (Eq.trans (*-identityˡ X) (*-comm ib a))))
  where
  a  = A* .proj₁
  b  = B* .proj₁
  ia = (A* ⁻¹) .proj₁
  ib = (B* ⁻¹) .proj₁
  X* : ℤ* ₚ
  X* = (B* ⁻¹) *' A*
  X  = X* .proj₁
  iX-e = (X* ⁻¹) .proj₁
  iX-val : (X* ⁻¹) .proj₁ ≡ b * ia
  iX-val = Eq.trans (inv-distrib (B* ⁻¹) A*)
             (Eq.cong (_* ((A* ⁻¹) .proj₁)) (inv-involutive B*))

------------------------------------------------------------------------
-- Merging (ZM q • S^ r) units at any width, via Lemmas0.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open SR word-setoid
  open Lemmas0 j

  unit-merge : ∀ (q₁ q₂ : ℤ* ₚ) (r₁ r₂ : ℤ ₚ) →
    (ZM q₁ • S^ r₁) • (ZM q₂ • S^ r₂) ≈
    ZM (q₁ *' q₂) •
    S^ (r₁ * (((q₂ ⁻¹) .proj₁) * ((q₂ ⁻¹) .proj₁)) + r₂)
  unit-merge q₁ q₂ r₁ r₂ = begin
    (ZM q₁ • S^ r₁) • (ZM q₂ • S^ r₂)
      ≈⟨ assoc ⟩
    ZM q₁ • (S^ r₁ • (ZM q₂ • S^ r₂))
      ≈⟨ cright (sym assoc) ⟩
    ZM q₁ • ((S^ r₁ • ZM q₂) • S^ r₂)
      ≈⟨ cright (cleft (lemma-S^kM (q₂ .proj₁) r₁ (q₂ .proj₂))) ⟩
    ZM q₁ • ((ZM q₂ • S^ (r₁ * i₂²)) • S^ r₂)
      ≈⟨ cright assoc ⟩
    ZM q₁ • (ZM q₂ • (S^ (r₁ * i₂²) • S^ r₂))
      ≈⟨ cright (cright (lemma-S^k+l (r₁ * i₂²) r₂)) ⟩
    ZM q₁ • (ZM q₂ • S^ (r₁ * i₂² + r₂))
      ≈⟨ sym assoc ⟩
    (ZM q₁ • ZM q₂) • S^ (r₁ * i₂² + r₂)
      ≈⟨ cleft (axiom (M-mul q₁ q₂)) ⟩
    ZM (q₁ *' q₂) • S^ (r₁ * i₂² + r₂) ∎
    where
    i₂² = ((q₂ ⁻¹) .proj₁) * ((q₂ ⁻¹) .proj₁)

  unit-ε : ∀ (q : ℤ* ₚ) (r : ℤ ₚ) → q .proj₁ ≡ ₁ → r ≡ ₀ →
    ZM q • S^ r ≈ ε
  unit-ε q r q1 r0 = begin
    ZM q • S^ r          ≈⟨ cong (aux-MM (q .proj₂) (λ ()) q1)
                                 (refl' (Eq.cong S^ r0)) ⟩
    ZM (₁ , λ ()) • ε    ≈⟨ right-unit ⟩
    ZM (₁ , λ ())        ≈⟨ sym lemma-M1 ⟩
    ε ∎

  unit-≈M : ∀ (q q' : ℤ* ₚ) (r : ℤ ₚ) → q .proj₁ ≡ q' .proj₁ → r ≡ ₀ →
    ZM q • S^ r ≈ ZM q'
  unit-≈M q q' r vq r0 =
    trans (cong (aux-MM (q .proj₂) (q' .proj₂) vq) (refl' (Eq.cong S^ r0)))
          right-unit

  HH≈M : HH ≈ ZM (-' (₁ , λ ()))
  HH≈M = lemma-HH-M-1

------------------------------------------------------------------------
-- The fully nonzero order-H inj₂ residual: four ZM-unit escapes merge
-- into ZM 1 • S^ 0.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)

  hpad : ∀ (u v : Fin (₁₊ p-2)) →
    (Hdir (₁₊ u , ₁₊ v) ↓ᵏ m) ≡
    ZM ((₁₊ u , λ ()) *' ((₁₊ v , λ ()) ⁻¹)) •
    S^ (₁₊ v * ((₁₊ u , λ ()) ⁻¹) .proj₁)
  hpad u v = Eq.cong₂ _•_
    (M-↓ᵏ ((₁₊ u , λ ()) *' ((₁₊ v , λ ()) ⁻¹)) m)
    (S^-↓ᵏ (₁₊ v * ((₁₊ u , λ ()) ⁻¹) .proj₁) m)

  dpad : {d d' : D} → d ≡ d' → (Hdir d ↓ᵏ m) ≡ (Hdir d' ↓ᵏ m)
  dpad = Eq.cong (λ v → Hdir v ↓ᵏ m)

  orderH-resid-nn : ∀ (a' b' y z : Fin (₁₊ p-2)) →
    - ₁₊ a' ≡ ₁₊ y → - ₁₊ b' ≡ ₁₊ z →
    (Hdir (₁₊ a' , ₁₊ b') ↓ᵏ m) •
    ((Hdir (₁₊ b' , - ₁₊ a') ↓ᵏ m) •
     ((Hdir (- ₁₊ a' , - ₁₊ b') ↓ᵏ m) •
      (Hdir (- ₁₊ b' , - - ₁₊ a') ↓ᵏ m))) ≈ ε
  orderH-resid-nn a' b' y z eq-y eq-z =
    trans (refl'ᵣ (Eq.cong₂ _•_ (hpad a' b')
            (Eq.cong₂ _•_ (Eq.trans (dpad (Eq.cong (₁₊ b' ,_) eq-y)) (hpad b' y))
            (Eq.cong₂ _•_ (Eq.trans (dpad (Eq.cong₂ _,_ eq-y eq-z)) (hpad y z))
                          (Eq.trans (dpad (Eq.cong₂ _,_ eq-z (-‿involutive (₁₊ a'))))
                                    (hpad z a'))))))
    (trans (cong refl (cong refl (unit-merge q₃ q₄ r₃ r₄)))
    (trans (cong refl (unit-merge q₂ q₃₄ r₂ R₃₄))
    (trans (unit-merge q₁ q₂₃₄ r₁ R₂₃₄)
           (unit-ε Q R Q≡1 R≡0))))
    where
    A* B* Y* Z* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    B* = (₁₊ b' , λ ())
    Y* = (₁₊ y , λ ())
    Z* = (₁₊ z , λ ())
    iA = (A* ⁻¹) .proj₁
    iB = (B* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    iZ = (Z* ⁻¹) .proj₁

    q₁ = A* *' (B* ⁻¹)
    q₂ = B* *' (Y* ⁻¹)
    q₃ = Y* *' (Z* ⁻¹)
    q₄ = Z* *' (A* ⁻¹)
    r₁ = ₁₊ b' * iA
    r₂ = ₁₊ y * iB
    r₃ = ₁₊ z * iY
    r₄ = ₁₊ a' * iZ

    q₃₄ = q₃ *' q₄
    R₃₄ = r₃ * (((q₄ ⁻¹) .proj₁) * ((q₄ ⁻¹) .proj₁)) + r₄
    q₂₃₄ = q₂ *' q₃₄
    R₂₃₄ = r₂ * (((q₃₄ ⁻¹) .proj₁) * ((q₃₄ ⁻¹) .proj₁)) + R₃₄
    Q = q₁ *' q₂₃₄
    R = r₁ * (((q₂₃₄ ⁻¹) .proj₁) * ((q₂₃₄ ⁻¹) .proj₁)) + R₂₃₄

    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    Q≡1 : Q .proj₁ ≡ ₁
    Q≡1 = Eq.trans
      (Eq.cong (λ t → q₁ .proj₁ * (q₂ .proj₁ * t)) (quotient-mul Y* Z* A*))
      (Eq.trans (Eq.cong (q₁ .proj₁ *_) (quotient-mul B* Y* A*))
      (Eq.trans (quotient-mul A* B* A*)
                (lemma-⁻¹ʳ (₁₊ a') {{inst-a}})))

    iY≡ : iY ≡ - iA
    iY≡ = ineg A* Y* (Eq.sym eq-y)
    iZ≡ : iZ ≡ - iB
    iZ≡ = ineg B* Z* (Eq.sym eq-z)

    iq₄≡ : (q₄ ⁻¹) .proj₁ ≡ - iB * ₁₊ a'
    iq₄≡ = Eq.trans (iexp Z* A*) (Eq.cong (_* ₁₊ a') iZ≡)

    negp : - iB * ₁₊ a' ≡ - (iB * ₁₊ a')
    negp = Eq.sym (-‿distribˡ-* iB (₁₊ a'))

    T34 : R₃₄ ≡ ₀
    T34 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.cong₂ _*_
          (Eq.cong₂ _*_ (Eq.sym eq-z) iY≡)
          (Eq.cong₂ _*_ (Eq.trans iq₄≡ negp) (Eq.trans iq₄≡ negp)))
        (Eq.cong (₁₊ a' *_) iZ≡))
      (Eq.trans
        (Eq.cong₂ _+_
          (Eq.cong₂ _*_ (negneg-* (₁₊ b') iA)
                        (negneg-* (iB * ₁₊ a') (iB * ₁₊ a')))
          (Eq.sym (-‿distribʳ-* (₁₊ a') iB)))
      (Eq.trans
        (Eq.cong (_+ - (₁₊ a' * iB)) (ring-core A* B*))
        (+-inverseʳ (₁₊ a' * iB))))

    q34-1 : q₃₄ .proj₁ ≡ - ₁
    q34-1 = Eq.trans (quotient-mul Y* Z* A*)
            (Eq.trans (Eq.cong (_* iA) (Eq.sym eq-y))
            (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a') iA))
                      (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))))

    iq34-1 : (q₃₄ ⁻¹) .proj₁ ≡ - ₁
    iq34-1 = Eq.trans (inv-cong q₃₄ (-' (₁ , λ ())) q34-1)
             (Eq.trans (inv-neg-comm (₁ , λ ())) (Eq.cong -_ inv-₁))

    R234 : R₂₃₄ ≡ ₁₊ y * iB
    R234 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.cong ((₁₊ y * iB) *_)
          (Eq.trans (Eq.cong₂ _*_ iq34-1 iq34-1)
          (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))))
        T34)
      (Eq.trans (Eq.cong₂ _+_ (*-identityʳ (₁₊ y * iB)) Eq.refl)
                (+-identityʳ (₁₊ y * iB)))

    iq234 : (q₂₃₄ ⁻¹) .proj₁ ≡ iB * ₁₊ a'
    iq234 = Eq.trans
      (inv-cong q₂₃₄ (B* *' (A* ⁻¹))
        (Eq.trans (Eq.cong (q₂ .proj₁ *_) (quotient-mul Y* Z* A*))
                  (quotient-mul B* Y* A*)))
      (iexp B* A*)

    R≡0 : R ≡ ₀
    R≡0 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.cong ((₁₊ b' * iA) *_) (Eq.cong₂ _*_ iq234 iq234))
        R234)
      (Eq.trans
        (Eq.cong₂ _+_ (ring-core A* B*)
          (Eq.trans (Eq.cong (_* iB) (Eq.sym eq-y))
                    (Eq.sym (-‿distribˡ-* (₁₊ a') iB))))
      (+-inverseʳ (₁₊ a' * iB)))

------------------------------------------------------------------------
-- comm-HHS residuals on inj₂ cosets with a ≠ 0.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)
  open PP ((₁₊ m) QRel,_===_)

  commHHS-a0-resid : ∀ (a' y : Fin (₁₊ p-2)) → - ₁₊ a' ≡ ₁₊ y →
    (Hdir (₁₊ a' , ₀) ↓ᵏ m) •
    ((Hdir (₀ , - ₁₊ a') ↓ᵏ m) • dir-of-DS (- ₁₊ a' , - ₀))
    ≈
    dir-of-DS (₁₊ a' , ₀) •
    ((Hdir (₁₊ a' , ₀ + - ₁₊ a') ↓ᵏ m) •
     (Hdir (₀ + - ₁₊ a' , - ₁₊ a') ↓ᵏ m))
  commHHS-a0-resid a' y eq-y =
    trans
      (trans
        (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
          (dpad (Eq.cong (₀ ,_) eq-y))
          (Eq.cong (λ v → dir-of-DS v) (Eq.cong₂ _,_ eq-y -0#≈0#)))))
        (trans (cong refl left-unit) (trans right-unit HH≈M)))
      (sym (trans
        (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
          (Eq.trans (dpad (Eq.cong (₁₊ a' ,_) (Eq.trans (+-0ˡ _) eq-y)))
                    (hpad a' y))
          (Eq.trans (dpad (Eq.cong₂ _,_ (Eq.trans (+-0ˡ _) eq-y) eq-y))
                    (hpad y y)))))
        (trans left-unit
        (trans (unit-merge ((₁₊ a' , λ ()) *' ((₁₊ y , λ ()) ⁻¹))
                           ((₁₊ y , λ ()) *' ((₁₊ y , λ ()) ⁻¹))
                           (₁₊ y * ((₁₊ a' , λ ()) ⁻¹) .proj₁)
                           (₁₊ y * ((₁₊ y , λ ()) ⁻¹) .proj₁))
               (unit-≈M
                 (((₁₊ a' , λ ()) *' ((₁₊ y , λ ()) ⁻¹)) *'
                  ((₁₊ y , λ ()) *' ((₁₊ y , λ ()) ⁻¹)))
                 (-' (₁ , λ ()))
                 ((₁₊ y * ((₁₊ a' , λ ()) ⁻¹) .proj₁) *
                   (((((₁₊ y , λ ()) *' ((₁₊ y , λ ()) ⁻¹)) ⁻¹) .proj₁) *
                    ((((₁₊ y , λ ()) *' ((₁₊ y , λ ()) ⁻¹)) ⁻¹) .proj₁))
                  + (₁₊ y * ((₁₊ y , λ ()) ⁻¹) .proj₁))
                 Q'v R'0)))))
    where
    A* Y* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    Y* = (₁₊ y , λ ())
    iA = (A* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}
    inst-y = nztoℕ {y = ₁₊ y} {neq0 = λ ()}

    iY≡ : iY ≡ - iA
    iY≡ = ineg A* Y* (Eq.sym eq-y)

    Q'v : ((A* *' (Y* ⁻¹)) *' (Y* *' (Y* ⁻¹))) .proj₁ ≡ (-' (₁ , λ ())) .proj₁
    Q'v = Eq.trans (quotient-mul A* Y* Y*)
          (Eq.trans (Eq.cong (₁₊ a' *_) iY≡)
          (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ a') iA))
                    (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))))

    iq₂'1 : ((Y* *' (Y* ⁻¹)) ⁻¹) .proj₁ ≡ ₁
    iq₂'1 = Eq.trans (iexp Y* Y*)
            (Eq.trans (*-comm iY (₁₊ y)) (lemma-⁻¹ʳ (₁₊ y) {{inst-y}}))

    R'0 : (₁₊ y * iA) *
            (((Y* *' (Y* ⁻¹)) ⁻¹) .proj₁ * ((Y* *' (Y* ⁻¹)) ⁻¹) .proj₁)
          + (₁₊ y * iY) ≡ ₀
    R'0 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong ((₁₊ y * iA) *_)
            (Eq.trans (Eq.cong₂ _*_ iq₂'1 iq₂'1) (*-identityˡ ₁)))
          (*-identityʳ (₁₊ y * iA)))
        Eq.refl)
      (Eq.trans (Eq.sym (*-distribˡ-+ (₁₊ y) iA iY))
      (Eq.trans (Eq.cong (₁₊ y *_)
          (Eq.trans (Eq.cong (iA +_) iY≡) (+-inverseʳ iA)))
        (*-zeroʳ (₁₊ y))))

  commHHS-nn0-resid : ∀ (a' b' y : Fin (₁₊ p-2)) →
    - ₁₊ a' ≡ ₁₊ y → ₁₊ b' + - ₁₊ a' ≡ ₀ →
    (Hdir (₁₊ a' , ₁₊ b') ↓ᵏ m) •
    ((Hdir (₁₊ b' , - ₁₊ a') ↓ᵏ m) • dir-of-DS (- ₁₊ a' , - ₁₊ b'))
    ≈
    dir-of-DS (₁₊ a' , ₁₊ b') •
    ((Hdir (₁₊ a' , ₁₊ b' + - ₁₊ a') ↓ᵏ m) •
     (Hdir (₁₊ b' + - ₁₊ a' , - ₁₊ a') ↓ᵏ m))
  commHHS-nn0-resid a' b' y eq-y Xeq =
    trans
      (trans
        (refl'ᵣ (Eq.cong₂ _•_ (hpad a' b')
          (Eq.cong₂ _•_
            (Eq.trans (dpad (Eq.cong (₁₊ b' ,_) eq-y)) (hpad b' y))
            (Eq.cong (λ v → dir-of-DS v)
              (Eq.cong₂ _,_ eq-y (Eq.trans eq-z' Eq.refl))))))
        (trans (cong refl right-unit)
        (trans (unit-merge (A* *' (B* ⁻¹)) (B* *' (Y* ⁻¹))
                 (₁₊ b' * iA) (₁₊ y * iB))
               (unit-≈M ((A* *' (B* ⁻¹)) *' (B* *' (Y* ⁻¹))) (-' (₁ , λ ()))
                 ((₁₊ b' * iA) *
                   ((((B* *' (Y* ⁻¹)) ⁻¹) .proj₁) *
                    (((B* *' (Y* ⁻¹)) ⁻¹) .proj₁))
                  + (₁₊ y * iB))
                 QLv RL0))))
      (sym (trans
        (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
          (dpad (Eq.cong (₁₊ a' ,_) Xeq))
          (dpad (Eq.cong₂ _,_ Xeq eq-y)))))
        (trans left-unit (trans right-unit HH≈M))))
    where
    A* B* Y* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    B* = (₁₊ b' , λ ())
    Y* = (₁₊ y , λ ())
    iA = (A* ⁻¹) .proj₁
    iB = (B* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    -- placeholder equality reused for the ε-slot value (z not needed here)
    eq-z' : (- ₁₊ b') ≡ (- ₁₊ b')
    eq-z' = Eq.refl

    iY≡ : iY ≡ - iA
    iY≡ = ineg A* Y* (Eq.sym eq-y)

    QLv : ((A* *' (B* ⁻¹)) *' (B* *' (Y* ⁻¹))) .proj₁ ≡ (-' (₁ , λ ())) .proj₁
    QLv = Eq.trans (quotient-mul A* B* Y*)
          (Eq.trans (Eq.cong (₁₊ a' *_) iY≡)
          (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ a') iA))
                    (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))))

    iq₂v : ((B* *' (Y* ⁻¹)) ⁻¹) .proj₁ ≡ - (iB * ₁₊ a')
    iq₂v = Eq.trans (iexp B* Y*)
           (Eq.trans (Eq.cong (iB *_) (Eq.sym eq-y))
                     (Eq.sym (-‿distribʳ-* iB (₁₊ a'))))

    RL0 : (₁₊ b' * iA) *
            ((((B* *' (Y* ⁻¹)) ⁻¹) .proj₁) * (((B* *' (Y* ⁻¹)) ⁻¹) .proj₁))
          + (₁₊ y * iB) ≡ ₀
    RL0 = Eq.trans
      (Eq.cong₂ _+_
        (Eq.cong ((₁₊ b' * iA) *_)
          (Eq.trans (Eq.cong₂ _*_ iq₂v iq₂v)
                    (negneg-* (iB * ₁₊ a') (iB * ₁₊ a'))))
        (Eq.trans (Eq.cong (_* iB) (Eq.sym eq-y))
                  (Eq.sym (-‿distribˡ-* (₁₊ a') iB))))
      (Eq.trans (Eq.cong (_+ - (₁₊ a' * iB)) (ring-core A* B*))
                (+-inverseʳ (₁₊ a' * iB)))

  commHHS-nnw-resid : ∀ (a' b' y w : Fin (₁₊ p-2)) →
    - ₁₊ a' ≡ ₁₊ y → ₁₊ b' + - ₁₊ a' ≡ ₁₊ w →
    (Hdir (₁₊ a' , ₁₊ b') ↓ᵏ m) •
    ((Hdir (₁₊ b' , - ₁₊ a') ↓ᵏ m) • dir-of-DS (- ₁₊ a' , - ₁₊ b'))
    ≈
    dir-of-DS (₁₊ a' , ₁₊ b') •
    ((Hdir (₁₊ a' , ₁₊ b' + - ₁₊ a') ↓ᵏ m) •
     (Hdir (₁₊ b' + - ₁₊ a' , - ₁₊ a') ↓ᵏ m))
  commHHS-nnw-resid a' b' y w eq-y Xeq =
    trans
      (trans
        (refl'ᵣ (Eq.cong₂ _•_ (hpad a' b')
          (Eq.cong₂ _•_
            (Eq.trans (dpad (Eq.cong (₁₊ b' ,_) eq-y)) (hpad b' y))
            (Eq.cong (λ v → dir-of-DS v) (Eq.cong (_, - ₁₊ b') eq-y)))))
        (trans (cong refl right-unit)
        (trans (unit-merge (A* *' (B* ⁻¹)) (B* *' (Y* ⁻¹))
                 (₁₊ b' * iA) (₁₊ y * iB))
               (unit-≈M ((A* *' (B* ⁻¹)) *' (B* *' (Y* ⁻¹))) (-' (₁ , λ ()))
                 ((₁₊ b' * iA) *
                   ((((B* *' (Y* ⁻¹)) ⁻¹) .proj₁) *
                    (((B* *' (Y* ⁻¹)) ⁻¹) .proj₁))
                  + (₁₊ y * iB))
                 QLv RL0))))
      (sym (trans
        (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
          (Eq.trans (dpad (Eq.cong (₁₊ a' ,_) Xeq)) (hpad a' w))
          (Eq.trans (dpad (Eq.cong₂ _,_ Xeq eq-y)) (hpad w y)))))
        (trans left-unit
        (trans (unit-merge (A* *' (W* ⁻¹)) (W* *' (Y* ⁻¹))
                 (₁₊ w * iA) (₁₊ y * iW))
               (unit-≈M ((A* *' (W* ⁻¹)) *' (W* *' (Y* ⁻¹))) (-' (₁ , λ ()))
                 ((₁₊ w * iA) *
                   ((((W* *' (Y* ⁻¹)) ⁻¹) .proj₁) *
                    (((W* *' (Y* ⁻¹)) ⁻¹) .proj₁))
                  + (₁₊ y * iW))
                 QRv RR0)))))
    where
    A* B* Y* W* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    B* = (₁₊ b' , λ ())
    Y* = (₁₊ y , λ ())
    W* = (₁₊ w , λ ())
    iA = (A* ⁻¹) .proj₁
    iB = (B* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    iW = (W* ⁻¹) .proj₁
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    iY≡ : iY ≡ - iA
    iY≡ = ineg A* Y* (Eq.sym eq-y)

    neg-tail : ∀ (u : ℤ ₚ) → u ≡ ₁₊ a' * iY →
      u ≡ (-' (₁ , λ ())) .proj₁
    neg-tail u eq = Eq.trans eq
          (Eq.trans (Eq.cong (₁₊ a' *_) iY≡)
          (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ a') iA))
                    (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))))

    QLv : ((A* *' (B* ⁻¹)) *' (B* *' (Y* ⁻¹))) .proj₁ ≡ (-' (₁ , λ ())) .proj₁
    QLv = neg-tail _ (quotient-mul A* B* Y*)

    QRv : ((A* *' (W* ⁻¹)) *' (W* *' (Y* ⁻¹))) .proj₁ ≡ (-' (₁ , λ ())) .proj₁
    QRv = neg-tail _ (quotient-mul A* W* Y*)

    phase-0 : ∀ (V* : ℤ* ₚ) (b : Fin (₁₊ p-2)) → V* .proj₁ ≡ ₁₊ b →
      (₁₊ b * iA) *
        ((((V* *' (Y* ⁻¹)) ⁻¹) .proj₁) * (((V* *' (Y* ⁻¹)) ⁻¹) .proj₁))
      + (₁₊ y * (V* ⁻¹) .proj₁) ≡ ₀
    phase-0 V* b Veq = Eq.trans
      (Eq.cong₂ _+_
        (Eq.cong ((₁₊ b * iA) *_)
          (Eq.trans (Eq.cong₂ _*_ iq₂v iq₂v)
                    (negneg-* (iV * ₁₊ a') (iV * ₁₊ a'))))
        (Eq.trans (Eq.cong (_* iV) (Eq.sym eq-y))
                  (Eq.sym (-‿distribˡ-* (₁₊ a') iV))))
      (Eq.trans (Eq.cong (_+ - (₁₊ a' * iV)) core')
                (+-inverseʳ (₁₊ a' * iV)))
      where
      iV = (V* ⁻¹) .proj₁
      iq₂v : ((V* *' (Y* ⁻¹)) ⁻¹) .proj₁ ≡ - (iV * ₁₊ a')
      iq₂v = Eq.trans (iexp V* Y*)
             (Eq.trans (Eq.cong (iV *_) (Eq.sym eq-y))
                       (Eq.sym (-‿distribʳ-* iV (₁₊ a'))))
      core' : (₁₊ b * iA) * ((iV * ₁₊ a') * (iV * ₁₊ a')) ≡ ₁₊ a' * iV
      core' = Eq.trans
        (Eq.cong (λ t → (t * iA) * ((iV * ₁₊ a') * (iV * ₁₊ a')))
          (Eq.sym Veq))
        (ring-core A* V*)

    RL0 = phase-0 B* b' Eq.refl
    RR0 = phase-0 W* w Eq.refl

------------------------------------------------------------------------
-- Letters as ZM-units, and ℤp sum-fixing lemmas for the (S•H)³ orbit.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open Lemmas0 j

  S≈unit : S ≈ ZM (₁ , λ ()) • S^ ₁
  S≈unit = trans (sym left-unit) (cong lemma-M1 refl)

  HH≈unit : HH ≈ ZM (-' (₁ , λ ())) • S^ ₀
  HH≈unit = trans lemma-HH-M-1
    (sym (unit-≈M (-' (₁ , λ ())) (-' (₁ , λ ())) ₀ Eq.refl Eq.refl))

sndZ-lem : ∀ (a' b' w z : Fin (₁₊ p-2)) →
  ₁₊ b' + - ₁₊ a' ≡ ₁₊ w → - ₁₊ b' ≡ ₁₊ z →
  - ₁₊ a' + - ₁₊ w ≡ ₁₊ z
sndZ-lem a' b' w z Xeq eq-z =
  Eq.trans (-‿+-comm (₁₊ a') (₁₊ w))
  (Eq.trans (Eq.cong -_
    (Eq.trans (Eq.cong (₁₊ a' +_) (Eq.sym Xeq))
    (Eq.trans (Eq.cong (₁₊ a' +_) (+-comm (₁₊ b') (- ₁₊ a')))
    (Eq.trans (Eq.sym (+-assoc (₁₊ a') (- ₁₊ a') (₁₊ b')))
    (Eq.trans (Eq.cong (_+ ₁₊ b') (+-inverseʳ (₁₊ a')))
              (+-0ˡ (₁₊ b')))))))
    eq-z)

sndA-lem : ∀ (a' b' w z : Fin (₁₊ p-2)) →
  ₁₊ b' + - ₁₊ a' ≡ ₁₊ w → - ₁₊ b' ≡ ₁₊ z →
  - ₁₊ w + - ₁₊ z ≡ ₁₊ a'
sndA-lem a' b' w z Xeq eq-z =
  Eq.trans (-‿+-comm (₁₊ w) (₁₊ z))
  (Eq.trans (Eq.cong -_
    (Eq.trans (Eq.cong₂ _+_ (Eq.sym Xeq) (Eq.sym eq-z))
    (Eq.trans (Eq.cong (_+ - ₁₊ b') (+-comm (₁₊ b') (- ₁₊ a')))
    (Eq.trans (+-assoc (- ₁₊ a') (₁₊ b') (- ₁₊ b'))
    (Eq.trans (Eq.cong (- ₁₊ a' +_) (+-inverseʳ (₁₊ b')))
              (+-identityʳ (- ₁₊ a')))))))
    (-‿involutive (₁₊ a')))

------------------------------------------------------------------------
-- order-SH inj₂ residuals: the (S•H)³ orbit escapes collapse through
-- the ZM-unit calculus.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)

  private
    one' : ℤ* ₚ
    one' = (₁ , λ ())
    m1' : ℤ* ₚ
    m1' = -' (₁ , λ ())

  orderSH-resid-0b : ∀ (b' z : Fin (₁₊ p-2)) → - ₁₊ b' ≡ ₁₊ z →
    (S • ε) •
    ((ε • (Hdir (₁₊ b' , - ₀ + - ₁₊ b') ↓ᵏ m)) •
     (dir-of-DS (- ₀ + - ₁₊ b' , - ₁₊ b') •
      (Hdir (d-of-DS (- ₀ + - ₁₊ b' , - ₁₊ b')) ↓ᵏ m))) ≈ ε
  orderSH-resid-0b b' z eq-z =
    trans (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
        (Eq.cong₂ _•_ Eq.refl
          (Eq.trans (dpad (Eq.cong (₁₊ b' ,_) w34)) (hpad b' z)))
        (Eq.cong₂ _•_
          (Eq.cong (λ v → dir-of-DS v) (Eq.cong₂ _,_ w34 eq-z))
          (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS v) ↓ᵏ m)
                      (Eq.cong₂ _,_ w34 eq-z))
                    (dpad (Eq.cong (₁₊ z ,_) (+-inverseʳ (₁₊ z)))))))))
    (trans (cong right-unit (cong left-unit left-unit))
    (trans (cong S≈unit (cong refl HH≈unit))
    (trans (cong refl (unit-merge qB m1' rB ₀))
    (trans (unit-merge one' (qB *' m1') ₁ RB)
           (unit-ε QQ RR Qv Rv)))))
    where
    B* Z* : ℤ* ₚ
    B* = (₁₊ b' , λ ())
    Z* = (₁₊ z , λ ())
    iB = (B* ⁻¹) .proj₁
    iZ = (Z* ⁻¹) .proj₁
    inst-b = nztoℕ {y = ₁₊ b'} {neq0 = λ ()}

    w34 : - ₀ + - ₁₊ b' ≡ ₁₊ z
    w34 = Eq.trans (Eq.cong₂ _+_ -0#≈0# eq-z) (+-0ˡ (₁₊ z))

    qB = B* *' (Z* ⁻¹)
    rB = ₁₊ z * iB
    RB = rB * (((m1' ⁻¹) .proj₁) * ((m1' ⁻¹) .proj₁)) + ₀
    QQ = one' *' (qB *' m1')
    RR = ₁ * ((((qB *' m1') ⁻¹) .proj₁) * (((qB *' m1') ⁻¹) .proj₁)) + RB

    iZ≡ : iZ ≡ - iB
    iZ≡ = ineg B* Z* (Eq.sym eq-z)

    qv : qB .proj₁ ≡ - ₁
    qv = Eq.trans (Eq.cong (₁₊ b' *_) iZ≡)
         (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ b') iB))
                   (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ b') {{inst-b}})))

    qv2 : (qB *' m1') .proj₁ ≡ ₁
    qv2 = Eq.trans (Eq.cong (_* (- ₁)) qv)
          (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))

    Qv : QQ .proj₁ ≡ ₁
    Qv = Eq.trans (*-identityˡ ((qB *' m1') .proj₁)) qv2

    r-eq : rB ≡ - ₁
    r-eq = Eq.trans (Eq.cong (_* iB) (Eq.sym eq-z))
           (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b') iB))
                     (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ b') {{inst-b}})))

    iQ≡ : ((qB *' m1') ⁻¹) .proj₁ ≡ ₁
    iQ≡ = Eq.trans (inv-cong (qB *' m1') one' qv2) inv-₁

    i₋≡ : ((m1' ⁻¹) .proj₁) ≡ - ₁
    i₋≡ = Eq.trans (inv-neg-comm (₁ , λ ())) (Eq.cong -_ inv-₁)

    Rv : RR ≡ ₀
    Rv = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong (₁ *_) (Eq.cong₂ _*_ iQ≡ iQ≡))
         (Eq.trans (Eq.cong (₁ *_) (*-identityˡ ₁)) (*-identityˡ ₁)))
        (Eq.trans (+-identityʳ (rB * (((m1' ⁻¹) .proj₁) * ((m1' ⁻¹) .proj₁))))
         (Eq.trans (Eq.cong₂ _*_ r-eq (Eq.cong₂ _*_ i₋≡ i₋≡))
          (Eq.trans (Eq.cong ((- ₁) *_) (negneg-* ₁ ₁))
           (Eq.trans (Eq.cong ((- ₁) *_) (*-identityˡ ₁))
                     (*-identityʳ (- ₁)))))))
      (+-inverseʳ ₁)

  orderSH-resid-a0 : ∀ (a' y : Fin (₁₊ p-2)) → - ₁₊ a' ≡ ₁₊ y →
    (ε • (Hdir (₁₊ a' , ₀ + - ₁₊ a') ↓ᵏ m)) •
    ((dir-of-DS (₀ + - ₁₊ a' , - ₁₊ a') •
      (Hdir (d-of-DS (₀ + - ₁₊ a' , - ₁₊ a')) ↓ᵏ m)) •
     (dir-of-DS (Hd' (d-of-DS (₀ + - ₁₊ a' , - ₁₊ a'))) •
      (Hdir (d-of-DS (Hd' (d-of-DS (₀ + - ₁₊ a' , - ₁₊ a')))) ↓ᵏ m))) ≈ ε
  orderSH-resid-a0 a' y eq-y =
    trans (refl'ᵣ (Eq.cong₂ _•_
        (Eq.cong₂ _•_ Eq.refl
          (Eq.trans (dpad (Eq.cong (₁₊ a' ,_) X-fix)) (hpad a' y)))
        (Eq.cong₂ _•_
          (Eq.cong₂ _•_
            (Eq.cong (λ v → dir-of-DS (v , - ₁₊ a')) X-fix)
            (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS (v , - ₁₊ a')) ↓ᵏ m) X-fix)
                      (dpad (Eq.cong (₁₊ y ,_) snd-fix))))
          (Eq.cong₂ _•_
            (Eq.trans (Eq.cong (λ v → dir-of-DS (Hd' (d-of-DS (v , - ₁₊ a')))) X-fix)
                      (Eq.cong (λ v → dir-of-DS v) (Eq.cong (_, - ₁₊ y) snd-fix)))
            (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS (Hd' (d-of-DS (v , - ₁₊ a')))) ↓ᵏ m) X-fix)
             (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS v) ↓ᵏ m)
                         (Eq.cong (_, - ₁₊ y) snd-fix))
                       (dpad (Eq.cong (₀ ,_) eq3))))))))
    (trans (cong left-unit (cong left-unit right-unit))
    (trans (cong refl (cong HH≈unit S≈unit))
    (trans (cong refl (unit-merge m1' one' ₀ ₁))
    (trans (unit-merge qA (m1' *' one') rA R₂₃)
           (unit-ε QQ RR Qv Rv)))))
    where
    A* Y* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    Y* = (₁₊ y , λ ())
    iA = (A* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    X-fix : ₀ + - ₁₊ a' ≡ ₁₊ y
    X-fix = Eq.trans (+-0ˡ (- ₁₊ a')) eq-y

    snd-fix : - ₁₊ a' + - ₁₊ y ≡ ₀
    snd-fix = Eq.trans (Eq.cong (_+ - ₁₊ y) eq-y) (+-inverseʳ (₁₊ y))

    eq3 : - ₁₊ y ≡ ₁₊ a'
    eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))

    qA = A* *' (Y* ⁻¹)
    rA = ₁₊ y * iA
    R₂₃ = ₀ * (((one' ⁻¹) .proj₁) * ((one' ⁻¹) .proj₁)) + ₁
    QQ = qA *' (m1' *' one')
    RR = rA * ((((m1' *' one') ⁻¹) .proj₁) * (((m1' *' one') ⁻¹) .proj₁)) + R₂₃

    iY≡ : iY ≡ - iA
    iY≡ = ineg A* Y* (Eq.sym eq-y)

    qv : qA .proj₁ ≡ - ₁
    qv = Eq.trans (Eq.cong (₁₊ a' *_) iY≡)
         (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ a') iA))
                   (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}})))

    mv : (m1' *' one') .proj₁ ≡ - ₁
    mv = *-identityʳ (- ₁)

    Qv : QQ .proj₁ ≡ ₁
    Qv = Eq.trans (Eq.cong₂ _*_ qv mv)
         (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))

    rA-eq : rA ≡ - ₁
    rA-eq = Eq.trans (Eq.cong (_* iA) (Eq.sym eq-y))
            (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a') iA))
                      (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}})))

    i₋≡ : ((m1' ⁻¹) .proj₁) ≡ - ₁
    i₋≡ = Eq.trans (inv-neg-comm (₁ , λ ())) (Eq.cong -_ inv-₁)

    iq₂≡ : (((m1' *' one') ⁻¹) .proj₁) ≡ - ₁
    iq₂≡ = Eq.trans (inv-cong (m1' *' one') m1' mv) i₋≡

    Rv : RR ≡ ₀
    Rv = Eq.trans
      (Eq.cong₂ _+_
        (Eq.trans (Eq.cong₂ _*_ rA-eq
            (Eq.trans (Eq.cong₂ _*_ iq₂≡ iq₂≡)
             (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))))
          (*-identityʳ (- ₁)))
        (+-0ˡ ₁))
      (+-inverseˡ ₁)

  orderSH-resid-nn0 : ∀ (a' b' y : Fin (₁₊ p-2)) → - ₁₊ a' ≡ ₁₊ y →
    ₁₊ b' + - ₁₊ a' ≡ ₀ →
    (ε • (Hdir (₁₊ a' , ₁₊ b' + - ₁₊ a') ↓ᵏ m)) •
    ((dir-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a') •
      (Hdir (d-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a')) ↓ᵏ m)) •
     (dir-of-DS (Hd' (d-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a'))) •
      (Hdir (d-of-DS (Hd' (d-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a')))) ↓ᵏ m))) ≈ ε
  orderSH-resid-nn0 a' b' y eq-y Xeq =
    trans (refl'ᵣ (Eq.cong₂ _•_
        (Eq.cong₂ _•_ Eq.refl (dpad (Eq.cong (₁₊ a' ,_) Xeq)))
        (Eq.cong₂ _•_
          (Eq.cong₂ _•_
            (Eq.cong (λ v → dir-of-DS v) (Eq.cong₂ _,_ Xeq eq-y))
            (Eq.cong (λ v → Hdir (d-of-DS v) ↓ᵏ m) (Eq.cong₂ _,_ Xeq eq-y)))
          (Eq.cong₂ _•_
            (Eq.cong (λ v → dir-of-DS (Hd' (d-of-DS v))) (Eq.cong₂ _,_ Xeq eq-y))
            (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS (Hd' (d-of-DS v))) ↓ᵏ m)
                        (Eq.cong₂ _,_ Xeq eq-y))
             (Eq.trans (dpad (Eq.cong (₁₊ y ,_) snd2-fix))
                       (hpad y a')))))))
    (trans (cong left-unit (cong right-unit left-unit))
    (trans (cong HH≈unit (cong S≈unit refl))
    (trans (cong refl (unit-merge one' qA2 ₁ rA2))
    (trans (unit-merge m1' (one' *' qA2) ₀ R₂₃)
           (unit-ε QQ RR Qv Rv)))))
    where
    A* Y* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    Y* = (₁₊ y , λ ())
    iA = (A* ⁻¹) .proj₁
    iY = (Y* ⁻¹) .proj₁
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}

    eq3 : - ₁₊ y ≡ ₁₊ a'
    eq3 = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))

    snd2-fix : - ₀ + - ₁₊ y ≡ ₁₊ a'
    snd2-fix = Eq.trans (Eq.cong₂ _+_ -0#≈0# eq3) (+-0ˡ (₁₊ a'))

    qA2 = Y* *' (A* ⁻¹)
    rA2 = ₁₊ a' * iY
    R₂₃ = ₁ * (((qA2' ⁻¹) .proj₁) * ((qA2' ⁻¹) .proj₁)) + rA2
      where qA2' = qA2
    QQ = m1' *' (one' *' qA2)
    RR = ₀ * ((((one' *' qA2) ⁻¹) .proj₁) * (((one' *' qA2) ⁻¹) .proj₁)) +
         (₁ * ((((qA2) ⁻¹) .proj₁) * (((qA2) ⁻¹) .proj₁)) + rA2)

    iY≡ : iY ≡ - iA
    iY≡ = ineg A* Y* (Eq.sym eq-y)

    qv : qA2 .proj₁ ≡ - ₁
    qv = Eq.trans (Eq.cong (_* iA) (Eq.sym eq-y))
         (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a') iA))
                   (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}})))

    m1v : (one' *' qA2) .proj₁ ≡ - ₁
    m1v = Eq.trans (*-identityˡ (qA2 .proj₁)) qv

    Qv : QQ .proj₁ ≡ ₁
    Qv = Eq.trans (Eq.cong ((- ₁) *_) m1v)
         (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))

    i₋≡ : ((m1' ⁻¹) .proj₁) ≡ - ₁
    i₋≡ = Eq.trans (inv-neg-comm (₁ , λ ())) (Eq.cong -_ inv-₁)

    r-eq : rA2 ≡ - ₁
    r-eq = Eq.trans (Eq.cong (₁₊ a' *_) iY≡)
           (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ a') iA))
                     (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a') {{inst-a}})))

    iq≡ : (((qA2) ⁻¹) .proj₁) ≡ - ₁
    iq≡ = Eq.trans (inv-cong qA2 m1' qv) i₋≡

    Rv : RR ≡ ₀
    Rv = Eq.trans (+-0ˡ (₁ * ((((qA2) ⁻¹) .proj₁) * (((qA2) ⁻¹) .proj₁)) + rA2))
      (Eq.trans (Eq.cong₂ _+_
          (Eq.trans (Eq.cong (₁ *_)
              (Eq.trans (Eq.cong₂ _*_ iq≡ iq≡)
               (Eq.trans (negneg-* ₁ ₁) (*-identityˡ ₁))))
            (*-identityˡ ₁))
          r-eq)
        (+-inverseʳ ₁))

  orderSH-resid-nnw : ∀ (a' b' y z w : Fin (₁₊ p-2)) →
    - ₁₊ a' ≡ ₁₊ y → - ₁₊ b' ≡ ₁₊ z → ₁₊ b' + - ₁₊ a' ≡ ₁₊ w →
    (ε • (Hdir (₁₊ a' , ₁₊ b' + - ₁₊ a') ↓ᵏ m)) •
    ((dir-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a') •
      (Hdir (d-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a')) ↓ᵏ m)) •
     (dir-of-DS (Hd' (d-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a'))) •
      (Hdir (d-of-DS (Hd' (d-of-DS (₁₊ b' + - ₁₊ a' , - ₁₊ a')))) ↓ᵏ m))) ≈ ε
  orderSH-resid-nnw a' b' y z w eq-y eq-z Xeq =
    trans (refl'ᵣ (Eq.cong₂ _•_
        (Eq.cong₂ _•_ Eq.refl
          (Eq.trans (dpad (Eq.cong (₁₊ a' ,_) Xeq)) (hpad a' w)))
        (Eq.cong₂ _•_
          (Eq.cong₂ _•_
            (Eq.cong (λ v → dir-of-DS (v , - ₁₊ a')) Xeq)
            (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS (v , - ₁₊ a')) ↓ᵏ m) Xeq)
             (Eq.trans (dpad (Eq.cong (₁₊ w ,_) sndZ))
                       (hpad w z))))
          (Eq.cong₂ _•_
            (Eq.trans (Eq.cong (λ v → dir-of-DS (Hd' (d-of-DS (v , - ₁₊ a')))) Xeq)
                      (Eq.cong (λ v → dir-of-DS v) (Eq.cong (_, - ₁₊ w) sndZ)))
            (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS (Hd' (d-of-DS (v , - ₁₊ a')))) ↓ᵏ m) Xeq)
             (Eq.trans (Eq.cong (λ v → Hdir (d-of-DS v) ↓ᵏ m)
                         (Eq.cong (_, - ₁₊ w) sndZ))
              (Eq.trans (dpad (Eq.cong (₁₊ z ,_) sndA))
                        (hpad z a'))))))))
    (trans (cong left-unit (cong left-unit left-unit))
    (trans (cong refl (unit-merge q₂ q₃ r₂ r₃))
    (trans (unit-merge q₁ (q₂ *' q₃) r₁ R₂₃)
           (unit-ε QQ RR Qv Rv))))
    where
    A* B* Z* W* : ℤ* ₚ
    A* = (₁₊ a' , λ ())
    B* = (₁₊ b' , λ ())
    Z* = (₁₊ z , λ ())
    W* = (₁₊ w , λ ())
    iA = (A* ⁻¹) .proj₁
    iB = (B* ⁻¹) .proj₁
    iZ = (Z* ⁻¹) .proj₁
    iW = (W* ⁻¹) .proj₁
    inst-a = nztoℕ {y = ₁₊ a'} {neq0 = λ ()}
    inst-b = nztoℕ {y = ₁₊ b'} {neq0 = λ ()}
    inst-z = nztoℕ {y = ₁₊ z} {neq0 = λ ()}
    inst-w = nztoℕ {y = ₁₊ w} {neq0 = λ ()}

    sndZ : - ₁₊ a' + - ₁₊ w ≡ ₁₊ z
    sndZ = sndZ-lem a' b' w z Xeq eq-z

    sndA : - ₁₊ w + - ₁₊ z ≡ ₁₊ a'
    sndA = sndA-lem a' b' w z Xeq eq-z

    q₁ = A* *' (W* ⁻¹)
    q₂ = W* *' (Z* ⁻¹)
    q₃ = Z* *' (A* ⁻¹)
    r₁ = ₁₊ w * iA
    r₂ = ₁₊ z * iW
    r₃ = ₁₊ a' * iZ
    R₂₃ = r₂ * ((((q₃) ⁻¹) .proj₁) * (((q₃) ⁻¹) .proj₁)) + r₃
    QQ = q₁ *' (q₂ *' q₃)
    RR = r₁ * ((((q₂ *' q₃) ⁻¹) .proj₁) * (((q₂ *' q₃) ⁻¹) .proj₁)) + R₂₃

    Qv : QQ .proj₁ ≡ ₁
    Qv = Eq.trans (Eq.cong (q₁ .proj₁ *_) (quotient-mul W* Z* A*))
         (Eq.trans (quotient-mul A* W* A*)
                   (lemma-⁻¹ʳ (₁₊ a') {{inst-a}}))

    iQ₂₃≡ : ((q₂ *' q₃) ⁻¹) .proj₁ ≡ iW * ₁₊ a'
    iQ₂₃≡ = Eq.trans (inv-cong (q₂ *' q₃) (W* *' (A* ⁻¹)) (quotient-mul W* Z* A*))
                     (iexp W* A*)

    outer : r₁ * ((((q₂ *' q₃) ⁻¹) .proj₁) * (((q₂ *' q₃) ⁻¹) .proj₁)) ≡
            ₁₊ a' * iW
    outer = Eq.trans (Eq.cong ((₁₊ w * iA) *_) (Eq.cong₂ _*_ iQ₂₃≡ iQ₂₃≡))
                     (ring-core A* W*)

    iq₃≡ : ((q₃) ⁻¹) .proj₁ ≡ iZ * ₁₊ a'
    iq₃≡ = iexp Z* A*

    zP : ₁₊ z * (iZ * ₁₊ a') ≡ ₁₊ a'
    zP = Eq.trans (Eq.sym (*-assoc (₁₊ z) iZ (₁₊ a')))
         (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ʳ (₁₊ z) {{inst-z}}))
                   (*-identityˡ (₁₊ a')))

    step1 : r₂ * ((((q₃) ⁻¹) .proj₁) * (((q₃) ⁻¹) .proj₁)) ≡
            (iW * ₁₊ a') * (iZ * ₁₊ a')
    step1 = Eq.trans (Eq.cong ((₁₊ z * iW) *_) (Eq.cong₂ _*_ iq₃≡ iq₃≡))
      (Eq.trans (Eq.cong (_* ((iZ * ₁₊ a') * (iZ * ₁₊ a'))) (*-comm (₁₊ z) iW))
      (Eq.trans (*-assoc iW (₁₊ z) ((iZ * ₁₊ a') * (iZ * ₁₊ a')))
      (Eq.trans (Eq.cong (iW *_) (Eq.sym (*-assoc (₁₊ z) (iZ * ₁₊ a') (iZ * ₁₊ a'))))
      (Eq.trans (Eq.cong (λ t → iW * (t * (iZ * ₁₊ a'))) zP)
                (Eq.sym (*-assoc iW (₁₊ a') (iZ * ₁₊ a')))))))

    aw-b : ₁₊ a' + ₁₊ w ≡ ₁₊ b'
    aw-b = Eq.trans (Eq.cong (₁₊ a' +_) (Eq.sym Xeq))
      (Eq.trans (Eq.cong (₁₊ a' +_) (+-comm (₁₊ b') (- ₁₊ a')))
      (Eq.trans (Eq.sym (+-assoc (₁₊ a') (- ₁₊ a') (₁₊ b')))
      (Eq.trans (Eq.cong (_+ ₁₊ b') (+-inverseʳ (₁₊ a')))
                (+-0ˡ (₁₊ b')))))

    iZ≡ : iZ ≡ - iB
    iZ≡ = ineg B* Z* (Eq.sym eq-z)

    iba : (iB * ₁₊ a') * ₁₊ b' ≡ ₁₊ a'
    iba = Eq.trans (*-assoc iB (₁₊ a') (₁₊ b'))
      (Eq.trans (Eq.cong (iB *_) (*-comm (₁₊ a') (₁₊ b')))
      (Eq.trans (Eq.sym (*-assoc iB (₁₊ b') (₁₊ a')))
      (Eq.trans (Eq.cong (_* ₁₊ a') (lemma-⁻¹ˡ (₁₊ b') {{inst-b}}))
                (*-identityˡ (₁₊ a')))))

    d6 : (iB * ₁₊ a') * (iW * ₁₊ b') ≡ ₁₊ a' * iW
    d6 = Eq.trans (Eq.cong ((iB * ₁₊ a') *_) (*-comm iW (₁₊ b')))
      (Eq.trans (Eq.sym (*-assoc (iB * ₁₊ a') (₁₊ b') iW))
                (Eq.cong (_* iW) iba))

    step2 : (iW * ₁₊ a') * (iZ * ₁₊ a') + r₃ ≡ - (₁₊ a' * iW)
    step2 = Eq.trans
      (Eq.cong₂ _+_ (*-comm (iW * ₁₊ a') (iZ * ₁₊ a'))
        (Eq.trans (*-comm (₁₊ a') iZ)
                  (Eq.sym (*-identityʳ (iZ * ₁₊ a')))))
      (Eq.trans (Eq.sym (*-distribˡ-+ (iZ * ₁₊ a') (iW * ₁₊ a') ₁))
      (Eq.trans (Eq.cong ((iZ * ₁₊ a') *_)
          (Eq.trans (Eq.cong ((iW * ₁₊ a') +_)
              (Eq.sym (lemma-⁻¹ˡ (₁₊ w) {{inst-w}})))
          (Eq.trans (Eq.sym (*-distribˡ-+ iW (₁₊ a') (₁₊ w)))
                    (Eq.cong (iW *_) aw-b))))
      (Eq.trans (Eq.cong (_* (iW * ₁₊ b'))
          (Eq.trans (Eq.cong (_* ₁₊ a') iZ≡)
                    (Eq.sym (-‿distribˡ-* iB (₁₊ a')))))
      (Eq.trans (Eq.sym (-‿distribˡ-* (iB * ₁₊ a') (iW * ₁₊ b')))
                (Eq.cong -_ d6)))))

    Rv : RR ≡ ₀
    Rv = Eq.trans
      (Eq.cong₂ _+_ outer (Eq.trans (Eq.cong₂ _+_ step1 Eq.refl) step2))
      (+-inverseʳ (₁₊ a' * iW))
