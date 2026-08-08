{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The `↓ᵏ`-widening congruence for the symplectic Clifford presentation:
-- if w ≈ v at width n, then (w ↓ᵏ k) ≈ (v ↓ᵏ k) at width n + k.  (`↓ᵏ`
-- pads k extra wires on top, leaving the gates on wires 0..n-1.)
--
-- This is the general-width analogue of the built-in `↑`-congruence
-- (Circuit.Base.lemma-cong↑) and lets any fixed-width (e.g. Gen 2) box
-- lemma be lifted to arbitrary width (₂₊ n) by widening its conclusion.
--
-- The structural half is a straight induction on the ≈-derivation
-- (mirroring lemma-cong↑); the axiom half (wd-≈) walks the Lift-Relation
-- derivation: `srel` re-applies the (∀ {n}) axiom at the wider width
-- (bridging any `_^_` via pow-↓ᵏ), `cong↑` uses ↑↓ᵏ-comm + lemma-cong↑,
-- and `comm₁`/`comm₂` re-apply the structural commuting rule.
------------------------------------------------------------------------

open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as ℕ
open import Data.Fin using (toℕ)
open import Data.Product using (_,_ ; proj₁)

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.CongDownK (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- `↓ᵏ` commutes with `_^_` and with `_↑`.

pow-↓ᵏ : ∀ (w : Circuit n) (j k : ℕ) → (w ^ j) ↓ᵏ k ≡ (w ↓ᵏ k) ^ j
pow-↓ᵏ w 0        k = Eq.refl
pow-↓ᵏ w (₁₊ 0)  k = Eq.refl
pow-↓ᵏ w (₂₊ j)  k = Eq.cong ((w ↓ᵏ k) •_) (pow-↓ᵏ w (₁₊ j) k)

-- (w ↑) ↓ᵏ k ≡ (w ↓ᵏ k) ↑ : on a single generator both sides are
-- (x ↧ᵏ k) ↥, definitionally.
↑↓ᵏ-comm : ∀ (w : Circuit n) (k : ℕ) → (w ↑) ↓ᵏ k ≡ (w ↓ᵏ k) ↑
↑↓ᵏ-comm [ x ]ʷ  k = Eq.refl
↑↓ᵏ-comm ε       k = Eq.refl
↑↓ᵏ-comm (w • v) k = Eq.cong₂ _•_ (↑↓ᵏ-comm w k) (↑↓ᵏ-comm v k)

-- Composition of `↓ᵏ` for a bottom-wire (Gen 1) word: widening by 1 then
-- by k is widening by 1+k.  On a single gate₁ letter both sides are that
-- same letter, definitionally.
↓ᵏ-↓ᵏ-1 : ∀ (w : Circuit 1) (k : ℕ) → (w ↓ᵏ 1) ↓ᵏ k ≡ w ↓ᵏ (₁₊ k)
↓ᵏ-↓ᵏ-1 [ gate₁ h ]ʷ k = Eq.refl
↓ᵏ-↓ᵏ-1 [ gate₀ () ↥ ]ʷ k
↓ᵏ-↓ᵏ-1 ε            k = Eq.refl
↓ᵏ-↓ᵏ-1 (w • v)      k = Eq.cong₂ _•_ (↓ᵏ-↓ᵏ-1 w k) (↓ᵏ-↓ᵏ-1 v k)

------------------------------------------------------------------------
-- `↓ᵏ`-invariance of the gadget words that appear in the axioms.

-- S^ / CZ^ / S⁻¹ are powers of a single gate, so ↓ᵏ passes straight
-- through them (pow-↓ᵏ, with S ↓ᵏ k = S etc. definitionally).
S^-↓ᵏ : ∀ (j : ℤ ₚ) (k : ℕ) → (S^ {n} j) ↓ᵏ k ≡ S^ j
S^-↓ᵏ j k = pow-↓ᵏ S (toℕ j) k

CZ^-↓ᵏ : ∀ (j : ℤ ₚ) (k : ℕ) → (CZ^ {n} j) ↓ᵏ k ≡ CZ^ j
CZ^-↓ᵏ j k = pow-↓ᵏ CZ (toℕ j) k

M-↓ᵏ : ∀ (x : ℤ* ₚ) (k : ℕ) → (M {n} x) ↓ᵏ k ≡ M x
M-↓ᵏ x k = Eq.cong₂ _•_ (S^-↓ᵏ (x .proj₁) k)
             (Eq.cong₂ _•_ Eq.refl
               (Eq.cong₂ _•_ (S^-↓ᵏ ((x ⁻¹) .proj₁) k)
                 (Eq.cong₂ _•_ Eq.refl
                   (Eq.cong₂ _•_ (S^-↓ᵏ (x .proj₁) k) Eq.refl))))

M↑-↓ᵏ : ∀ (x : ℤ* ₚ) (k : ℕ) → (M {n} x ↑) ↓ᵏ k ≡ M x ↑
M↑-↓ᵏ x k = Eq.trans (↑↓ᵏ-comm (M x) k) (Eq.cong _↑ (M-↓ᵏ x k))

S⁻¹-↓ᵏ : ∀ (k : ℕ) → (S⁻¹ {n}) ↓ᵏ k ≡ S⁻¹
S⁻¹-↓ᵏ k = pow-↓ᵏ S p-1 k

S⁻¹↑-↓ᵏ : ∀ (k : ℕ) → (S⁻¹ {n} ↑) ↓ᵏ k ≡ S⁻¹ ↑
S⁻¹↑-↓ᵏ k = Eq.trans (↑↓ᵏ-comm S⁻¹ k) (Eq.cong _↑ (S⁻¹-↓ᵏ k))

------------------------------------------------------------------------
-- The axiom half: the raw relation is closed under ↓ᵏ.

wd-≈ : ∀ (k : ℕ) {w v : Circuit n} → (n QRel, w === v) →
  let open PB ((n ℕ.+ k) QRel,_===_) using (_≈_)
  in (w ↓ᵏ k) ≈ (v ↓ᵏ k)
wd-≈ k (cong↑ r)  =
  PB.trans (PB.refl' _ (↑↓ᵏ-comm _ k))
    (PB.trans (lemma-cong↑ _ _ (wd-≈ k r)) (PB.sym (PB.refl' _ (↑↓ᵏ-comm _ k))))
wd-≈ k (comm₁ h g) = PB.axiom (comm₁ h _)
wd-≈ k (comm₂ h g) = PB.axiom (comm₂ h _)
-- SRel axioms:
wd-≈ k (srel Base.order-S)     = PB.trans (PB.refl' _ (pow-↓ᵏ S p k))          (PB.axiom (srel Base.order-S))
wd-≈ k (srel Base.order-H)     = PB.trans (PB.refl' _ (pow-↓ᵏ H 4 k))          (PB.axiom (srel Base.order-H))
wd-≈ k (srel Base.order-SH)    = PB.trans (PB.refl' _ (pow-↓ᵏ (S • H) 3 k))    (PB.axiom (srel Base.order-SH))
wd-≈ k (srel Base.comm-HHS)    = PB.axiom (srel Base.comm-HHS)
wd-≈ k (srel Base.order-CZ)    = PB.trans (PB.refl' _ (pow-↓ᵏ CZ p k))         (PB.axiom (srel Base.order-CZ))
wd-≈ k (srel Base.comm-CZ-S↓)  = PB.axiom (srel Base.comm-CZ-S↓)
wd-≈ k (srel Base.comm-CZ-S↑)  = PB.axiom (srel Base.comm-CZ-S↑)
wd-≈ k (srel Base.selinger-c12) = PB.axiom (srel Base.selinger-c12)
wd-≈ k (srel Base.selinger-c13) = PB.axiom (srel Base.selinger-c13)
wd-≈ k (srel Base.selinger-c14) = PB.trans (PB.refl' _ (pow-↓ᵏ (⊤⊥ ↑ • CZ ↓) 3 k)) (PB.axiom (srel Base.selinger-c14))
wd-≈ k (srel Base.selinger-c15) = PB.trans (PB.refl' _ (pow-↓ᵏ (⊥⊤ ↓ • CZ ↑) 3 k)) (PB.axiom (srel Base.selinger-c15))
-- Power/M cases:
wd-≈ k (srel (Base.M-mul x y))  =
  PB.trans (PB.refl' _ (Eq.cong₂ _•_ (M-↓ᵏ x k) (M-↓ᵏ y k)))
    (PB.trans (PB.axiom (srel (Base.M-mul x y)))
      (PB.sym (PB.refl' _ (M-↓ᵏ (x *' y) k))))
wd-≈ k (srel (Base.semi-MS x))  =
  PB.trans (PB.refl' _ (Eq.cong₂ _•_ (M-↓ᵏ x k) Eq.refl))
    (PB.trans (PB.axiom (srel (Base.semi-MS x)))
      (PB.sym (PB.refl' _ (Eq.cong₂ _•_ (S^-↓ᵏ (x ^2) k) (M-↓ᵏ x k)))))
wd-≈ k (srel (Base.semi-M↑CZ x)) =
  PB.trans (PB.refl' _ (Eq.cong₂ _•_ (M↑-↓ᵏ x k) Eq.refl))
    (PB.trans (PB.axiom (srel (Base.semi-M↑CZ x)))
      (PB.sym (PB.refl' _ (Eq.cong₂ _•_ (CZ^-↓ᵏ (x ^1) k) (M↑-↓ᵏ x k)))))
wd-≈ k (srel (Base.semi-M↓CZ x)) =
  PB.trans (PB.refl' _ (Eq.cong₂ _•_ (M-↓ᵏ x k) Eq.refl))
    (PB.trans (PB.axiom (srel (Base.semi-M↓CZ x)))
      (PB.sym (PB.refl' _ (Eq.cong₂ _•_ (CZ^-↓ᵏ (x ^1) k) (M-↓ᵏ x k)))))
wd-≈ k (srel Base.selinger-c10) =
  PB.trans (PB.axiom (srel Base.selinger-c10))
    (PB.sym (PB.refl' _
      (Eq.cong₂ _•_ (S⁻¹↑-↓ᵏ k)
        (Eq.cong₂ _•_ Eq.refl
          (Eq.cong₂ _•_ (S⁻¹↑-↓ᵏ k)
            (Eq.cong₂ _•_ Eq.refl
              (Eq.cong₂ _•_ Eq.refl
                (Eq.cong₂ _•_ (S⁻¹↑-↓ᵏ k) (S⁻¹-↓ᵏ k)))))))))
wd-≈ k (srel Base.selinger-c11) =
  PB.trans (PB.axiom (srel Base.selinger-c11))
    (PB.sym (PB.refl' _
      (Eq.cong₂ _•_ (S⁻¹-↓ᵏ k)
        (Eq.cong₂ _•_ Eq.refl
          (Eq.cong₂ _•_ (S⁻¹-↓ᵏ k)
            (Eq.cong₂ _•_ Eq.refl
              (Eq.cong₂ _•_ Eq.refl
                (Eq.cong₂ _•_ (S⁻¹-↓ᵏ k) (S⁻¹↑-↓ᵏ k)))))))))

------------------------------------------------------------------------
-- The ≈-congruence: straight induction on the derivation (cf. lemma-cong↑).

cong↓ᵏ : ∀ (k : ℕ) (w v : Circuit n) →
  let open PB (n QRel,_===_) using (_≈_)
      open PB ((n ℕ.+ k) QRel,_===_) using () renaming (_≈_ to _≈↓_)
  in w ≈ v → (w ↓ᵏ k) ≈↓ (v ↓ᵏ k)
cong↓ᵏ k w v PB.refl          = PB.refl
cong↓ᵏ k w v (PB.sym p)       = PB.sym (cong↓ᵏ k v w p)
cong↓ᵏ k w v (PB.trans p q)   = PB.trans (cong↓ᵏ k _ _ p) (cong↓ᵏ k _ _ q)
cong↓ᵏ k w v (PB.cong p q)    = PB.cong  (cong↓ᵏ k _ _ p) (cong↓ᵏ k _ _ q)
cong↓ᵏ k w v PB.assoc         = PB.assoc
cong↓ᵏ k w v PB.left-unit     = PB.left-unit
cong↓ᵏ k w v PB.right-unit    = PB.right-unit
cong↓ᵏ k w v (PB.axiom x)     = wd-≈ k x
