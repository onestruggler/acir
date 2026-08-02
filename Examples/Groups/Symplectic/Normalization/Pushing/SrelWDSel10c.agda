------------------------------------------------------------------------
-- Presentations of groups
--
-- The Borel calculus for selinger-c10 branch B: units ZM x • S^ k move
-- through H-powers (semi-HM, its H³ variant, derived-7 with a trivial
-- M-head) and through CZ-powers (semi-M↑CZ iterated), all lifted to
-- the top wire.  These normalize both sides of the branch-B residual
-- identity to the canonical form Z↑ • S↑ • H↑ • CZ^ • H↑ • S↑ • S⁻¹.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
  renaming (_*_ to _*ℕ_ ; _+_ to _+ℕ_)
open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n)
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
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-cong↑)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿distribʳ-*)

import Data.Nat.Properties as NP

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ
  p-2 p-prime using (pow-↑)

------------------------------------------------------------------------
-- Width-generic Borel movers.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open Lemmas0 j
  open SR word-setoid

  -- Merge two ZM's into a target pair.
  Zmul : ∀ (x y z : ℤ* ₚ) → (x *' y) .proj₁ ≡ z .proj₁ →
    ZM x • ZM y ≈ ZM z
  Zmul x y z v =
    trans (axiom (M-mul x y)) (aux-MM ((x *' y) .proj₂) (z .proj₂) v)

  -- Slide an S-power right past a ZM, with a target exponent.
  SZmove : ∀ (k : ℤ ₚ) (x : ℤ* ₚ) (l : ℤ ₚ) →
    k * (((x ⁻¹) .proj₁) * ((x ⁻¹) .proj₁)) ≡ l →
    S^ k • ZM x ≈ ZM x • S^ l
  SZmove k x l v =
    trans (lemma-S^kM (x .proj₁) k (x .proj₂))
          (cright (refl' (Eq.cong S^ v)))

  -- H³ conjugates ZM by inversion, like H does.
  H3M : ∀ (x : ℤ* ₚ) → H ^ 3 • ZM x ≈ ZM (x ⁻¹) • H ^ 3
  H3M x = begin
    H ^ 3 • ZM x                     ≈⟨ assoc ⟩
    H • ((H • H) • ZM x)             ≈⟨ cright assoc ⟩
    H • (H • (H • ZM x))             ≈⟨ cright (cright (semi-HM x)) ⟩
    H • (H • (ZM (x ⁻¹) • H))        ≈⟨ cright (sym assoc) ⟩
    H • ((H • ZM (x ⁻¹)) • H)        ≈⟨ cright (cleft (semi-HM (x ⁻¹))) ⟩
    H • ((ZM ((x ⁻¹) ⁻¹) • H) • H)   ≈⟨ cright (cleft (cleft
        (aux-MM (((x ⁻¹) ⁻¹) .proj₂) (x .proj₂) (inv-involutive x)))) ⟩
    H • ((ZM x • H) • H)             ≈⟨ cright assoc ⟩
    H • (ZM x • (H • H))             ≈⟨ sym assoc ⟩
    (H • ZM x) • (H • H)             ≈⟨ cleft (semi-HM x) ⟩
    (ZM (x ⁻¹) • H) • (H • H)        ≈⟨ assoc ⟩
    ZM (x ⁻¹) • (H • (H • H))        ∎

  -- H • S^x • H in Borel-conjugated form (derived-7 with M(1) head).
  d7ε : ∀ (x : ℤ* ₚ) →
    let ix = (x ⁻¹) .proj₁ in
    H • (S^ (x .proj₁) • H) ≈
    S^ (- ix) • (ZM (-' (x ⁻¹)) • (H • S^ (- ix)))
  d7ε x =
    trans (sym left-unit)
    (trans (cleft lemma-M1)
    (trans (derived-7 (x .proj₁) ₁ (x .proj₂) (λ ()))
    (trans (cleft (refl' (Eq.cong S^ vS)))
           (cright (cleft (aux-MM
             ((((₁ , λ ()) *' (x ⁻¹)) *' (-' (₁ , λ ()))) .proj₂)
             ((-' (x ⁻¹)) .proj₂) vZ))))))
    where
    ix = (x ⁻¹) .proj₁
    vS : - ix * (₁ * ₁) ≡ - ix
    vS = Eq.trans (Eq.cong (- ix *_) (*-identityˡ ₁)) (*-identityʳ (- ix))
    vZ : (((₁ , λ ()) *' (x ⁻¹)) *' (-' (₁ , λ ()))) .proj₁ ≡ - ix
    vZ = Eq.trans (Eq.cong (_* - ₁) (*-identityˡ ix))
         (Eq.trans (Eq.sym (-‿distribʳ-* ix ₁))
                   (Eq.cong -_ (*-identityʳ ix)))

------------------------------------------------------------------------
-- Lifted movers and the CZ-power slide, at width ₂₊ m.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid

  private
    module L0m = Lemmas0 m
    module PBm = PB ((₁₊ m) QRel,_===_)

  HMup : ∀ (x : ℤ* ₚ) → H {m} ↑ • ZM x ↑ ≈ ZM (x ⁻¹) ↑ • H ↑
  HMup x = lemma-cong↑ (H • ZM x) (ZM (x ⁻¹) • H) (L0m.semi-HM x)

  H3Mup : ∀ (x : ℤ* ₚ) → (H {m} ↑) ^ 3 • ZM x ↑ ≈ ZM (x ⁻¹) ↑ • (H ↑) ^ 3
  H3Mup x = lemma-cong↑ (H ^ 3 • ZM x) (ZM (x ⁻¹) • H ^ 3) (H3M x)

  Zmulup : ∀ (x y z : ℤ* ₚ) → (x *' y) .proj₁ ≡ z .proj₁ →
    ZM {m} x ↑ • ZM y ↑ ≈ ZM z ↑
  Zmulup x y z v = lemma-cong↑ (ZM x • ZM y) (ZM z) (Zmul x y z v)

  SZmoveup : ∀ (k : ℤ ₚ) (x : ℤ* ₚ) (l : ℤ ₚ) →
    k * (((x ⁻¹) .proj₁) * ((x ⁻¹) .proj₁)) ≡ l →
    S^ k ↑ • ZM {m} x ↑ ≈ ZM x ↑ • S^ l ↑
  SZmoveup k x l v = lemma-cong↑ (S^ k • ZM x) (ZM x • S^ l) (SZmove k x l v)

  Sk+lup : ∀ (k l : ℤ ₚ) → (S^ {m} k) ↑ • S^ l ↑ ≈ S^ (k + l) ↑
  Sk+lup k l = lemma-cong↑ (S^ k • S^ l) (S^ (k + l)) (L0m.lemma-S^k+l k l)

  d7εup : ∀ (x : ℤ* ₚ) →
    let ix = (x ⁻¹) .proj₁ in
    H {m} ↑ • (S^ (x .proj₁) ↑ • H ↑) ≈
    S^ (- ix) ↑ • (ZM (-' (x ⁻¹)) ↑ • (H ↑ • S^ (- ix) ↑))
  d7εup x = lemma-cong↑
    (H • (S^ (x .proj₁) • H))
    (S^ (- ((x ⁻¹) .proj₁)) •
      (ZM (-' (x ⁻¹)) • (H • S^ (- ((x ⁻¹) .proj₁)))))
    (d7ε x)

  HHMup : H {m} ↑ • H ↑ ≈ ZM (-' (₁ , λ ())) ↑
  HHMup = lemma-cong↑ (H • H) (ZM (-' (₁ , λ ()))) L0m.lemma-HH-M-1

  Mεup : ZM {m} (₁ , λ ()) ↑ ≈ ε
  Mεup = lemma-cong↑ (ZM (₁ , λ ())) ε (PBm.sym L0m.lemma-M1)

  ZMvalup : ∀ (x y : ℤ* ₚ) → x .proj₁ ≡ y .proj₁ → ZM {m} x ↑ ≈ ZM y ↑
  ZMvalup x y v = lemma-cong↑ (ZM x) (ZM y)
    (L0m.aux-MM (x .proj₂) (y .proj₂) v)

  -- CZ-power collapse modulo p.
  CZpow-% : ∀ k → CZ {m} ^ k ≈ CZ ^ (k % p)
  CZpow-% k = begin
    CZ ^ k
      ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k p) ⟩
    CZ ^ (k % p +ℕ (k / p) *ℕ p)
      ≈⟨ ^-+ CZ (k % p) ((k / p) *ℕ p) ⟩
    CZ ^ (k % p) • CZ ^ ((k / p) *ℕ p)
      ≈⟨ cright (refl' (Eq.cong (CZ ^_) (NP.*-comm (k / p) p))) ⟩
    CZ ^ (k % p) • CZ ^ (p *ℕ (k / p))
      ≈⟨ sym (cright (^^ CZ p (k / p))) ⟩
    CZ ^ (k % p) • (CZ ^ p) ^ (k / p)
      ≈⟨ cright (^-cong (CZ ^ p) ε (k / p) (axiom order-CZ)) ⟩
    CZ ^ (k % p) • ε ^ (k / p)
      ≈⟨ cright (ε^k=ε (k / p)) ⟩
    CZ ^ (k % p) • ε
      ≈⟨ right-unit ⟩
    CZ ^ (k % p) ∎

  -- semi-M↑CZ iterated over an ℕ-power of CZ.
  MupCZ^ : ∀ (x : ℤ* ₚ) (k : ℕ) →
    ZM x ↑ • CZ {m} ^ k ≈ CZ ^ (k *ℕ toℕ (x .proj₁)) • ZM x ↑
  MupCZ^ x zero = trans right-unit (sym left-unit)
  MupCZ^ x (suc zero) =
    trans (axiom (semi-M↑CZ x))
          (cleft (refl' (Eq.cong (CZ ^_)
            (Eq.sym (NP.*-identityˡ (toℕ (x .proj₁)))))))
  MupCZ^ x (suc (suc k)) =
    trans (sym assoc)
    (trans (cleft (trans (axiom (semi-M↑CZ x))
      (cleft (refl' (Eq.cong (CZ ^_)
        (Eq.sym (NP.*-identityˡ (toℕ (x .proj₁)))))))))
    (trans assoc
    (trans (cright (MupCZ^ x (suc k)))
    (trans (sym assoc)
           (cleft (trans (sym (^-+ CZ (1 *ℕ toℕ (x .proj₁))
               (suc k *ℕ toℕ (x .proj₁))))
             (refl' (Eq.cong (CZ ^_)
               (Eq.sym (NP.*-distribʳ-+ (toℕ (x .proj₁)) 1 (suc k)))))))))))

  -- The value-level slide: ZM x ↑ • CZ^ k ≈ CZ^ (k·x) • ZM x ↑.
  MupCZval : ∀ (x : ℤ* ₚ) (k : ℤ ₚ) →
    ZM x ↑ • (CZ^ {m} k) ≈ CZ^ (k * x .proj₁) • ZM x ↑
  MupCZval x k =
    trans (MupCZ^ x (toℕ k))
          (cleft (trans (CZpow-% (toℕ k *ℕ toℕ (x .proj₁)))
                        (refl' (Eq.cong (CZ ^_)
                          (lemma-toℕ-% k (x .proj₁))))))

  -- A CZ-power moves right past ZM x ↑ at the cost of an x⁻¹ factor.
  cpowM : ∀ (x : ℤ* ₚ) (j : ℤ ₚ) →
    (CZ^ {m} j) • ZM x ↑ ≈ ZM x ↑ • CZ^ (j * ((x ⁻¹) .proj₁))
  cpowM x j =
    sym (trans (MupCZval x (j * ((x ⁻¹) .proj₁)))
               (cleft (refl' (Eq.cong CZ^ v))))
    where
    ix = (x ⁻¹) .proj₁
    v : (j * ix) * x .proj₁ ≡ j
    v = Eq.trans (*-assoc j ix (x .proj₁))
        (Eq.trans (Eq.cong (j *_)
            (lemma-⁻¹ˡ (x .proj₁)
              {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂}}}))
          (*-identityʳ j))

  -- Single-CZ version.
  cMup : ∀ (x : ℤ* ₚ) →
    CZ {m} • ZM x ↑ ≈ ZM x ↑ • CZ^ ((x ⁻¹) .proj₁)
  cMup x = trans (cpowM x ₁)
                 (cright (refl' (Eq.cong CZ^
                   (*-identityˡ ((x ⁻¹) .proj₁)))))

  -- CZ commutes with lifted S-powers.
  comm-CZ-S^↑ : ∀ (t : ℤ ₚ) → CZ {m} • S^ t ↑ ≈ S^ t ↑ • CZ
  comm-CZ-S^↑ t =
    trans (cright (refl' (Eq.sym (pow-↑ S (toℕ t)))))
    (trans (comm⇒pow-comm {w = CZ} {v = S ↑} 1 (toℕ t) (axiom comm-CZ-S↑))
           (cleft (refl' (pow-↑ S (toℕ t)))))

  -- Bottom S⁻¹ commutes with any lifted word and with CZ-powers.
  SdownW : ∀ (w : Word (Gen (₁₊ m))) → S⁻¹ • w ↑ ≈ w ↑ • S⁻¹
  SdownW w = comm⇒pow-comm {w = S} {v = w ↑} p-1 1 (lemma-comm-S-w↑ w)

  SdownCZ^ : ∀ (k : ℕ) → S⁻¹ • CZ {m} ^ k ≈ CZ ^ k • S⁻¹
  SdownCZ^ k = comm⇒pow-comm {w = S} {v = CZ} p-1 k
    (sym (axiom comm-CZ-S↓))
