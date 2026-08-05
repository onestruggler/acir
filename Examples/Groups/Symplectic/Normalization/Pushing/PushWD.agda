------------------------------------------------------------------------
-- Presentations of groups
--
-- Well-definedness of the coset action on DEGENERATE cosets (inj₁ ml')
-- — the engine-level campaign.
--
-- On inj₁ ml' every bottom unary gate routes through Push.ml'-bot-push:
-- the A box emits an S-power j (PushLM1.A-dir-S-power) and a residual
-- box a', then S^ j cascades through the M column and B-vector
-- (PushMbS.mbSⁿ), which is where the real complexity lives.
--
-- The wedge: on an a ≠ 0 box the S-gate emits j = ₀ (A-dir-S-power's
-- (₁₊ _ , _) S-gen clauses), so mbSⁿ 0 fires — the M column and the
-- B-vector are untouched and the escape is ε, all DEFINITIONALLY.  The
-- entire S-orbit on such a coset is the width-1 A-box orbit, and
-- order-S at inj₁ closes on the a ≠ 0 branch by the same nsum
-- arithmetic as at width 1 (srel-wd {zero}).
--
-- The (₀ , ₁₊ b) branch emits j = b⁻²-powers and genuinely cascades
-- through mb-S (each B box re-emitting Rof residuals into the M
-- column); its well-definedness needs an order-p theorem for the
-- cascade and remains open, as do the H-driven axioms (kH ≠ ₀ on fully
-- nonzero boxes).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.PushWD
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-‿involutive)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1
  p-2 p-prime using (A-dir-S-power)
import Examples.Groups.Symplectic.Normalization.Pushing.Push
  p-2 p-prime as Push
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (itf ; mbSⁿm ; mbSⁿ-orderp)

------------------------------------------------------------------------
-- Congruence through inj₁, invariant in the (judgementally irrelevant)
-- A-box nonzeroness proof — the width-≥2 analogue of c1-eq.

inj₁-a-eq : ∀ {m : ℕ} {dv : Vec D (₁₊ m)} {e : E} {bv : Vec B (₁₊ m)}
  {x y : ℤ ₚ × ℤ ₚ} {nx : x ≢ (₀ , ₀)} {ny : y ≢ (₀ , ₀)} →
  x ≡ y →
  _≡_ {A = C (₂₊ m)}
    (inj₁ ((dv , e) , (bv , (x , nx))))
    (inj₁ ((dv , e) , (bv , (y , ny))))
inj₁-a-eq Eq.refl = Eq.refl

------------------------------------------------------------------------
-- The single S-step on an a ≠ 0 box: nothing escapes, nothing moves but
-- the A box.  Definitional after the b-split (both the j = ₀ clause of
-- A-dir-S-power and the mbSⁿ 0 base fire by computation).

ract-S-inj₁-a+ : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (b : ℤ ₚ) (nz : (₁₊ a₀ , b) ≢ (₀ , ₀)) →
  ract {₁₊ m} (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b) , nz)))) (gate₁ S-gate)
  ≡ (ε , inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b + - ₁₊ a₀) , λ ()))))
ract-S-inj₁-a+ dv e bv a₀ ₀      nz = Eq.cong (ε ,_) (inj₁-a-eq Eq.refl)
ract-S-inj₁-a+ dv e bv a₀ (₁₊ _) nz = Eq.cong (ε ,_) (inj₁-a-eq Eq.refl)

------------------------------------------------------------------------
-- The S-power orbit, coset component: b shifts by nsum j (- a₀), all
-- else fixed.  The word S ^ j threads step-FIRST (w • u runs w before
-- u), so the recursion follows S ^ (2+j) = S • S ^ (1+j).

ract-S^-inj₁-a+-coset : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (b : ℤ ₚ) (nz : (₁₊ a₀ , b) ≢ (₀ , ₀)) (j : ℕ) →
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b) , nz)))) (S ^ j)) .proj₂
  ≡ inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b + nsum j (- ₁₊ a₀)) , λ ())))
ract-S^-inj₁-a+-coset dv e bv a₀ b nz zero =
  inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) (Eq.sym (+-identityʳ b)))
ract-S^-inj₁-a+-coset dv e bv a₀ b nz (suc zero) =
  Eq.trans (Eq.cong proj₂ (ract-S-inj₁-a+ dv e bv a₀ b nz))
    (inj₁-a-eq (Eq.cong (λ t → ₁₊ a₀ , b + t)
      (Eq.sym (+-identityʳ (- ₁₊ a₀)))))
ract-S^-inj₁-a+-coset {m} dv e bv a₀ b nz (suc (suc j)) =
  Eq.trans
    (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (S ^ suc j)) .proj₂)
      (Eq.cong proj₂ (ract-S-inj₁-a+ dv e bv a₀ b nz)))
  (Eq.trans
    (ract-S^-inj₁-a+-coset dv e bv a₀ (b + - ₁₊ a₀) (λ ()) (suc j))
    (inj₁-a-eq (Eq.cong (₁₊ a₀ ,_)
      (+-assoc b (- ₁₊ a₀) (nsum (suc j) (- ₁₊ a₀))))))

------------------------------------------------------------------------
-- The S-power orbit, residual component: a tower of ε's.

ract-S^-inj₁-a+-resid : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (b : ℤ ₚ) (nz : (₁₊ a₀ , b) ≢ (₀ , ₀)) (j : ℕ) →
  let open PB ((₁₊ m) QRel,_===_) in
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b) , nz)))) (S ^ j)) .proj₁ ≈ ε
ract-S^-inj₁-a+-resid {m} dv e bv a₀ b nz zero = refl
  where open PB ((₁₊ m) QRel,_===_)
ract-S^-inj₁-a+-resid {m} dv e bv a₀ b nz (suc zero) =
  refl' (Eq.cong proj₁ (ract-S-inj₁-a+ dv e bv a₀ b nz))
  where open PB ((₁₊ m) QRel,_===_)
ract-S^-inj₁-a+-resid {m} dv e bv a₀ b nz (suc (suc j)) =
  trans (cong (refl' (Eq.cong proj₁ step))
    (trans (refl' (Eq.cong
        (λ c → ((ract {₁₊ m} ᵗ) c (S ^ suc j)) .proj₁)
        (Eq.cong proj₂ step)))
      (ract-S^-inj₁-a+-resid dv e bv a₀ (b + - ₁₊ a₀) (λ ()) (suc j))))
    left-unit
  where
  open PB ((₁₊ m) QRel,_===_)
  step = ract-S-inj₁-a+ dv e bv a₀ b nz

------------------------------------------------------------------------
-- order-S at inj₁, a ≠ 0 branch: the p-fold b-shift closes (nsum-p≡0)
-- and every escape is ε.  This is the first degenerate-coset case of
-- srel-wd discharged at general width.

------------------------------------------------------------------------
-- order-H on half-zero boxes: the quarter turn (α,β) ↦ (β,−α) keeps a
-- half-zero box half-zero, and A-dir-S-power is ₀ on both half-zero
-- H-clauses, so the whole 4-cycle stays in the A box.  Stuck negated
-- components are rewritten into constructor form mid-orbit (elim-suc at
-- the call site, inj₁-a-eq here), exactly as at width 1.

-- (₀ , −₁₊a) ≢ (₀,₀): the second component is a negated successor.
nz-0- : ∀ (a : Fin (₁₊ p-2)) →
  _≢_ {A = ℤ ₚ × ℤ ₚ} (₀ , - ₁₊ a) (₀ , ₀)
nz-0- a eq = neg≢0 (₁₊ a) (λ ()) (Eq.cong proj₂ eq)

-- The two half-zero H-steps (escape ε, M column and B-vector untouched).
ract-H-inj₁-0b : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) →
  ract {₁₊ m} (inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz)))) (gate₁ H-gate)
  ≡ (ε , inj₁ ((dv , e) , (bv , ((₁₊ b₀ , ₀) , λ ()))))
ract-H-inj₁-0b dv e bv b₀ nz = Eq.cong (ε ,_) (inj₁-a-eq Eq.refl)

ract-H-inj₁-a0 : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀)) →
  ract {₁₊ m} (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz)))) (gate₁ H-gate)
  ≡ (ε , inj₁ ((dv , e) , (bv , ((₀ , - ₁₊ a₀) , nz-0- a₀))))
ract-H-inj₁-a0 dv e bv a₀ nz = Eq.cong (ε ,_) (inj₁-a-eq Eq.refl)

------------------------------------------------------------------------
-- The two order-H orbits.  The hypotheses (y , eq-y) put the stuck
-- negated components into constructor form, mirroring srel-wd {zero}'s
-- elim-suc call shape.

orderH-inj₁-0b : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ b₀ ≡ ₁₊ y) →
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz)))) (H ^ 4))
  ≋
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz)))) ε)
orderH-inj₁-0b {m} dv e bv b₀ nz y eq-y = resid≈ , coset≡
  where
  open PB ((₁₊ m) QRel,_===_)

  c₁ = inj₁ ((dv , e) , (bv , ((₁₊ b₀ , ₀) , λ ())))
  c₂ = inj₁ ((dv , e) , (bv , ((₀ , ₁₊ y) , λ ())))
  c₃ = inj₁ ((dv , e) , (bv , ((₁₊ y , ₀) , λ ())))

  s₁ = ract-H-inj₁-0b dv e bv b₀ nz
  s₂ : ract {₁₊ m} c₁ (gate₁ H-gate) ≡ (ε , c₂)
  s₂ = Eq.trans (ract-H-inj₁-a0 dv e bv b₀ (λ ()))
    (Eq.cong (ε ,_) (inj₁-a-eq (Eq.cong (₀ ,_) eq-y)))
  s₃ : ract {₁₊ m} c₂ (gate₁ H-gate) ≡ (ε , c₃)
  s₃ = ract-H-inj₁-0b dv e bv y (λ ())
  s₄fix : (₀ , - ₁₊ y) ≡ (₀ , ₁₊ b₀)
  s₄fix = Eq.cong (₀ ,_)
    (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ b₀)))
  s₄ : ract {₁₊ m} c₃ (gate₁ H-gate)
       ≡ (ε , inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz))))
  s₄ = Eq.trans (ract-H-inj₁-a0 dv e bv y (λ ()))
    (Eq.cong (ε ,_) (inj₁-a-eq s₄fix))

  coset≡ : ((ract {₁₊ m} ᵗ)
      (inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz)))) (H ^ 4)) .proj₂
    ≡ inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz)))
  coset≡ =
    Eq.trans (Eq.cong (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 3)) .proj₂) s₁)
    (Eq.trans (Eq.cong (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 2)) .proj₂) s₂)
    (Eq.trans (Eq.cong (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 1)) .proj₂) s₃)
      (Eq.cong proj₂ s₄)))

  resid≈ : ((ract {₁₊ m} ᵗ)
      (inj₁ ((dv , e) , (bv , ((₀ , ₁₊ b₀) , nz)))) (H ^ 4)) .proj₁ ≈ ε
  resid≈ =
    trans (cong (refl' (Eq.cong proj₁ s₁))
      (trans (refl' (Eq.cong
          (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 3)) .proj₁) s₁))
      (trans (cong (refl' (Eq.cong proj₁ s₂))
        (trans (refl' (Eq.cong
            (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 2)) .proj₁) s₂))
        (trans (cong (refl' (Eq.cong proj₁ s₃))
          (trans (refl' (Eq.cong
              (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 1)) .proj₁) s₃))
            (refl' (Eq.cong proj₁ s₄))))
          left-unit)))
        left-unit)))
      left-unit

orderH-inj₁-a0 : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  (y₂ : Fin (₁₊ p-2)) (eq-y₂ : - ₁₊ y ≡ ₁₊ y₂) →
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz)))) (H ^ 4))
  ≋
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz)))) ε)
orderH-inj₁-a0 {m} dv e bv a₀ nz y eq-y y₂ eq-y₂ = resid≈ , coset≡
  where
  open PB ((₁₊ m) QRel,_===_)

  c₁ = inj₁ ((dv , e) , (bv , ((₀ , ₁₊ y) , λ ())))
  c₂ = inj₁ ((dv , e) , (bv , ((₁₊ y , ₀) , λ ())))
  c₃ = inj₁ ((dv , e) , (bv , ((₀ , ₁₊ y₂) , λ ())))

  s₁ : ract {₁₊ m} (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz))))
         (gate₁ H-gate) ≡ (ε , c₁)
  s₁ = Eq.trans (ract-H-inj₁-a0 dv e bv a₀ nz)
    (Eq.cong (ε ,_) (inj₁-a-eq (Eq.cong (₀ ,_) eq-y)))
  s₂ : ract {₁₊ m} c₁ (gate₁ H-gate) ≡ (ε , c₂)
  s₂ = ract-H-inj₁-0b dv e bv y (λ ())
  s₃ : ract {₁₊ m} c₂ (gate₁ H-gate) ≡ (ε , c₃)
  s₃ = Eq.trans (ract-H-inj₁-a0 dv e bv y (λ ()))
    (Eq.cong (ε ,_) (inj₁-a-eq (Eq.cong (₀ ,_) eq-y₂)))
  s₄fix : (₁₊ y₂ , ₀) ≡ (₁₊ a₀ , ₀)
  s₄fix = Eq.cong (_, ₀)
    (Eq.trans (Eq.sym eq-y₂)
      (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))))
  s₄ : ract {₁₊ m} c₃ (gate₁ H-gate)
       ≡ (ε , inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz))))
  s₄ = Eq.trans (ract-H-inj₁-0b dv e bv y₂ (λ ()))
    (Eq.cong (ε ,_) (inj₁-a-eq s₄fix))

  coset≡ : ((ract {₁₊ m} ᵗ)
      (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz)))) (H ^ 4)) .proj₂
    ≡ inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz)))
  coset≡ =
    Eq.trans (Eq.cong (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 3)) .proj₂) s₁)
    (Eq.trans (Eq.cong (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 2)) .proj₂) s₂)
    (Eq.trans (Eq.cong (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 1)) .proj₂) s₃)
      (Eq.cong proj₂ s₄)))

  resid≈ : ((ract {₁₊ m} ᵗ)
      (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , ₀) , nz)))) (H ^ 4)) .proj₁ ≈ ε
  resid≈ =
    trans (cong (refl' (Eq.cong proj₁ s₁))
      (trans (refl' (Eq.cong
          (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 3)) .proj₁) s₁))
      (trans (cong (refl' (Eq.cong proj₁ s₂))
        (trans (refl' (Eq.cong
            (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 2)) .proj₁) s₂))
        (trans (cong (refl' (Eq.cong proj₁ s₃))
          (trans (refl' (Eq.cong
              (λ pr → ((ract {₁₊ m} ᵗ) (pr .proj₂) (H ^ 1)) .proj₁) s₃))
            (refl' (Eq.cong proj₁ s₄))))
          left-unit)))
        left-unit)))
      left-unit

------------------------------------------------------------------------
-- order-S at inj₁, a ≠ 0 branch.

orderS-inj₁-a+ : ∀ {m : ℕ} (dv : Vec D (₁₊ m)) (e : E) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (b : ℤ ₚ) (nz : (₁₊ a₀ , b) ≢ (₀ , ₀)) →
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b) , nz)))) (S ^ p))
  ≋
  ((ract {₁₊ m} ᵗ)
     (inj₁ ((dv , e) , (bv , ((₁₊ a₀ , b) , nz)))) ε)
orderS-inj₁-a+ {m} dv e bv a₀ b nz =
  ract-S^-inj₁-a+-resid dv e bv a₀ b nz p ,
  Eq.trans (ract-S^-inj₁-a+-coset dv e bv a₀ b nz p)
    (inj₁-a-eq (Eq.cong (₁₊ a₀ ,_)
      (Eq.trans (Eq.cong (b +_) (nsum-p≡0 (- ₁₊ a₀)))
        (+-identityʳ b))))

------------------------------------------------------------------------
-- order-S at inj₁, (₀ , ₁₊ b) branch, COSET half.  The S-step leaves
-- the A box (and its nonzeroness proof) literally unchanged and emits
-- the fixed exponent kS0 = b⁻² into the mb-S cascade (mbSⁿ), so the
-- p-fold orbit on the M column is the p-th iterate of the cascade's
-- M-update — the identity, by the cascade order-p theorem
-- (MbSOrder.mbSⁿ-orderp).  The residual half (the accumulated cascade
-- escapes ≈ ε) is the ↑-faithfulness obligation and remains open.

-- The fixed S-power exponent emitted by a (₀ , ₁₊ b₀) box.
kS0 : ∀ {m : ℕ} (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) → ℤ ₚ
kS0 {m} b₀ nz =
  A-dir-S-power {₁₊ m} ((₀ , ₁₊ b₀) , nz) (gate₁ S-gate)
    (Push.bws1 {₁₊ m} S-gate) .proj₁

-- The S-power orbit, coset component: t cascade steps on the M column,
-- everything else fixed.  Each single step is definitional (the A-box
-- clauses fire on the constructor-form box), so the orbit is a direct
-- recursion on t.
ract-S^-inj₁-0b-coset : ∀ {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) (t : ℕ) →
  ((ract {₁₊ m} ᵗ)
     (inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz)))) (S ^ t)) .proj₂
  ≡ inj₁ ( itf (λ z → mbSⁿm (toℕ (kS0 {m} b₀ nz)) z bv) t mm
         , (bv , ((₀ , ₁₊ b₀) , nz)))
ract-S^-inj₁-0b-coset mm bv b₀ nz zero          = Eq.refl
ract-S^-inj₁-0b-coset mm bv b₀ nz (suc zero)    = Eq.refl
ract-S^-inj₁-0b-coset {m} mm bv b₀ nz (suc (suc t)) =
  ract-S^-inj₁-0b-coset
    (mbSⁿm (toℕ (kS0 {m} b₀ nz)) mm bv) bv b₀ nz (suc t)

-- The p-fold orbit closes on the coset.
orderS-inj₁-0b-coset : ∀ {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀)) →
  ((ract {₁₊ m} ᵗ)
     (inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz)))) (S ^ p)) .proj₂
  ≡ inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz)))
orderS-inj₁-0b-coset {m} mm bv b₀ nz =
  Eq.trans (ract-S^-inj₁-0b-coset mm bv b₀ nz p)
    (Eq.cong (λ z → inj₁ (z , (bv , ((₀ , ₁₊ b₀) , nz))))
      (mbSⁿ-orderp (toℕ (kS0 {m} b₀ nz)) bv mm))
