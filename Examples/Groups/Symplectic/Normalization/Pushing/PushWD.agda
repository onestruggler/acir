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
-- cascade and remains open, as do the H-driven axioms (kHn ≠ ₀ on fully
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
  using (-‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1
  p-2 p-prime using (A-dir-S-power)
import Examples.Groups.Symplectic.Normalization.Pushing.Push
  p-2 p-prime as Push
open import Examples.Groups.Symplectic.Normalization.Pushing.MbSOrder
  p-2 p-prime using (itf ; mbSⁿm ; mbSⁿ-orderp ; chainΦ ; chain-0 ; sumZ ;
                     neg-core ; +-swap)
open import Data.List using () renaming ([] to []ᴸ ; _∷_ to _∷ᴸ_)

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

------------------------------------------------------------------------
-- order-H at inj₁, fully nonzero box, COSET half.  The H 4-cycle
-- (a,b) → (b,−a) → (−a,−b) → (−b,a) → (a,b) emits the S-power
-- exponents [ab]⁻¹, −[ab]⁻¹, [ab]⁻¹, −[ab]⁻¹ into the mb-S cascade;
-- they sum to zero, so the M column returns by MbSOrder.chain-0.  The
-- stuck negated components are put in constructor form by the caller's
-- elim-suc hypotheses (y, z, w), mirroring srel-wd {zero}'s call shape.

-- ⁻¹'s value component depends only on the value component (the
-- nonzeroness proof feeds an η-unit instance).
inv-val-cong : ∀ (x y : ℤ* ₚ) → x .proj₁ ≡ y .proj₁ →
  (x ⁻¹) .proj₁ ≡ (y ⁻¹) .proj₁
inv-val-cong (v , nzv) (v' , nzv') Eq.refl = Eq.refl

-- The fixed exponent emitted by a fully nonzero (₁₊ α , ₁₊ β) box
-- under H, and the judgemental resolution of its clause meta.
kHn : ∀ {m : ℕ} (α β : Fin (₁₊ p-2)) (nzx : (₁₊ α , ₁₊ β) ≢ (₀ , ₀)) → ℤ ₚ
kHn {m} α β nzx =
  A-dir-S-power {₁₊ m} ((₁₊ α , ₁₊ β) , nzx) (gate₁ H-gate)
    (Push.bws1 {₁₊ m} H-gate) .proj₁

kHn-val : ∀ {m : ℕ} (α β : Fin (₁₊ p-2)) (nzx : (₁₊ α , ₁₊ β) ≢ (₀ , ₀)) →
  kHn {m} α β nzx ≡ (((₁₊ α , λ ()) *' (₁₊ β , λ ())) ⁻¹) .proj₁
kHn-val α β nzx = Eq.refl

-- The (₀ , ₁₊ β) S-exponent is the square of the inverse.
sqInv : Fin (₁₊ p-2) → ℤ ₚ
sqInv β = ((₁₊ β , λ ()) ⁻¹) .proj₁ * ((₁₊ β , λ ()) ⁻¹) .proj₁

kS0-val : ∀ {m : ℕ} (β : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ β) ≢ (₀ , ₀)) →
  kS0 {m} β nz ≡ sqInv β
kS0-val β nz = Eq.refl

-- On a (₁₊ β , ₁₊ u) box with ₁₊ u = − ₁₊ β, the H-exponent is the
-- NEGATED inverse square — the partner that cancels a kS0 emission.
kHn-negsq : ∀ {m : ℕ} (β u : Fin (₁₊ p-2)) (equ : - ₁₊ β ≡ ₁₊ u)
  (nzx : (₁₊ β , ₁₊ u) ≢ (₀ , ₀)) →
  kHn {m} β u nzx ≡ - sqInv β
kHn-negsq {m} β u equ nzx =
  Eq.trans (kHn-val {m} β u nzx)
  (Eq.trans (inv-val-cong ((₁₊ β , λ ()) *' (₁₊ u , λ ()))
      (-' ((₁₊ β , λ ()) *' (₁₊ β , λ ())))
      (Eq.trans (Eq.cong (₁₊ β *_) (Eq.sym equ))
                (Eq.sym (-‿distribʳ-* (₁₊ β) (₁₊ β)))))
  (Eq.trans (inv-neg-comm ((₁₊ β , λ ()) *' (₁₊ β , λ ())))
            (Eq.cong -_ (inv-distrib (₁₊ β , λ ()) (₁₊ β , λ ())))))

module OrderH-nn {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ b₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  (z : Fin (₁₊ p-2)) (eq-z : - ₁₊ b₀ ≡ ₁₊ z)
  (w : Fin (₁₊ p-2)) (eq-w : - ₁₊ y ≡ ₁₊ w)
  where

  private
    j₁ = kHn {m} a₀ b₀ nz
    j₂ = kHn {m} b₀ y (λ ())
    j₃ = kHn {m} y z (λ ())
    j₄ = kHn {m} z w (λ ())

    x* : ℤ* ₚ
    x* = (₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())

    J : ℤ ₚ
    J = (x* ⁻¹) .proj₁

    -- ₁₊ w ≡ ₁₊ a₀ (two negations cancel).
    wEq : ₁₊ w ≡ ₁₊ a₀
    wEq = Eq.trans (Eq.sym eq-w)
      (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀)))

    -- − ₁₊ z ≡ ₁₊ b₀.
    zEq : - ₁₊ z ≡ ₁₊ b₀
    zEq = Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b₀))

    j₁≡ : j₁ ≡ J
    j₁≡ = kHn-val {m} a₀ b₀ nz

    j₂≡ : j₂ ≡ - J
    j₂≡ = Eq.trans (kHn-val {m} b₀ y (λ ()))
      (Eq.trans (inv-val-cong ((₁₊ b₀ , λ ()) *' (₁₊ y , λ ())) (-' x*)
        (Eq.trans (Eq.cong (₁₊ b₀ *_) (Eq.sym eq-y))
        (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ b₀) (₁₊ a₀)))
                  (Eq.cong -_ (*-comm (₁₊ b₀) (₁₊ a₀))))))
        (inv-neg-comm x*))

    j₃≡ : j₃ ≡ J
    j₃≡ = Eq.trans (kHn-val {m} y z (λ ()))
      (inv-val-cong ((₁₊ y , λ ()) *' (₁₊ z , λ ())) x*
        (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-y) (Eq.sym eq-z))
        (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a₀) (- ₁₊ b₀)))
        (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* (₁₊ a₀) (₁₊ b₀))))
                  (-‿involutive (₁₊ a₀ * ₁₊ b₀))))))

    j₄≡ : j₄ ≡ - J
    j₄≡ = Eq.trans (kHn-val {m} z w (λ ()))
      (Eq.trans (inv-val-cong ((₁₊ z , λ ()) *' (₁₊ w , λ ())) (-' x*)
        (Eq.trans (Eq.cong₂ _*_ (Eq.sym eq-z) wEq)
        (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b₀) (₁₊ a₀)))
                  (Eq.cong -_ (*-comm (₁₊ b₀) (₁₊ a₀))))))
        (inv-neg-comm x*))

    sum0 : sumZ (j₁ ∷ᴸ j₂ ∷ᴸ j₃ ∷ᴸ j₄ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ j₁≡ (Eq.cong₂ _+_ j₂≡
        (Eq.cong₂ _+_ j₃≡ (Eq.cong₂ _+_ j₄≡ Eq.refl))))
      (Eq.trans (Eq.cong (λ t → J + (- J + (J + t))) (+-identityʳ (- J)))
      (Eq.trans (Eq.cong (λ t → J + (- J + t)) (+-inverseʳ J))
      (Eq.trans (Eq.cong (J +_) (+-identityʳ (- J)))
                (+-inverseʳ J))))

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    m₁ = Φ j₁ mm
    m₂ = Φ j₂ m₁
    m₃ = Φ j₃ m₂

    c₀ c₁ c₂ c₃ : C (₂₊ m)
    c₀ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    c₁ = inj₁ (m₁ , (bv , ((₁₊ b₀ , ₁₊ y) , λ ())))
    c₂ = inj₁ (m₂ , (bv , ((₁₊ y , ₁₊ z) , λ ())))
    c₃ = inj₁ (m₃ , (bv , ((₁₊ z , ₁₊ w) , λ ())))

    s₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ H-gate)) ≡ c₁
    s₁ = inj₁-a-eq (Eq.cong (₁₊ b₀ ,_) eq-y)

    s₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    s₂ = inj₁-a-eq (Eq.cong (₁₊ y ,_) eq-z)

    s₃ : proj₂ (ract {₁₊ m} c₂ (gate₁ H-gate)) ≡ c₃
    s₃ = inj₁-a-eq (Eq.cong (₁₊ z ,_) eq-w)

    s₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate))
         ≡ inj₁ (Φ j₄ m₃ , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    s₄ = inj₁-a-eq (Eq.cong₂ _,_ wEq zEq)

  -- The 4-cycle closes on the coset.
  orderH-inj₁-nn-coset :
    ((ract {₁₊ m} ᵗ) c₀ (H ^ 4)) .proj₂ ≡ c₀
  orderH-inj₁-nn-coset =
    Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (H ^ 3)) .proj₂) s₁)
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (H ^ 2)) .proj₂) s₂)
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (H ^ 1)) .proj₂) s₃)
    (Eq.trans s₄
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (chain-0 (j₁ ∷ᴸ j₂ ∷ᴸ j₃ ∷ᴸ j₄ ∷ᴸ []ᴸ) mm bv sum0)))))

------------------------------------------------------------------------
-- order-SH at inj₁, half-zero boxes, COSET halves.  The (S•H)³ orbit
-- on a half-zero box emits exactly two cancelling exponents — an
-- inverse square (kS0, on the (₀,β) stop) and its negation (kHn on the
-- (β , −β) stop) — so the M column closes by chain-0.  All other stops
-- emit ₀ and leave the M column untouched definitionally.

-- Threading one S•H pair through the coset.
SH-pair : ∀ {m : ℕ} (c c' c'' : C (₂₊ m)) →
  proj₂ (ract {₁₊ m} c (gate₁ S-gate)) ≡ c' →
  proj₂ (ract {₁₊ m} c' (gate₁ H-gate)) ≡ c'' →
  ((ract {₁₊ m} ᵗ) c (S • H)) .proj₂ ≡ c''
SH-pair {m} c c' c'' eqS eqH =
  Eq.trans (Eq.cong (λ cc → proj₂ (ract {₁₊ m} cc (gate₁ H-gate))) eqS) eqH

module OrderSH-0b {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (z : Fin (₁₊ p-2)) (eq-z : - ₁₊ b₀ ≡ ₁₊ z)
  where

  private
    j₁ = kS0 {m} b₀ nz
    j₄ = kHn {m} b₀ z (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    m₁ = Φ j₁ mm

    zEq : - ₁₊ z ≡ ₁₊ b₀
    zEq = Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b₀))

    sum0 : sumZ (j₁ ∷ᴸ j₄ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ (kS0-val {m} b₀ nz)
        (Eq.cong₂ _+_ (kHn-negsq {m} b₀ z eq-z (λ ())) Eq.refl))
      (Eq.trans (Eq.cong (sqInv b₀ +_) (+-identityʳ (- sqInv b₀)))
                (+-inverseʳ (sqInv b₀)))

    c₀ c₁ c₂ c₃ c₄ c₅ : C (₂₊ m)
    c₀ = inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz)))
    c₁ = inj₁ (m₁ , (bv , ((₀ , ₁₊ b₀) , nz)))
    c₂ = inj₁ (m₁ , (bv , ((₁₊ b₀ , ₀) , λ ())))
    c₃ = inj₁ (m₁ , (bv , ((₁₊ b₀ , ₁₊ z) , λ ())))
    c₄ = inj₁ (Φ j₄ m₁ , (bv , ((₁₊ z , ₁₊ z) , λ ())))
    c₅ = inj₁ (Φ j₄ m₁ , (bv , ((₁₊ z , ₀) , λ ())))

    s₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ c₁
    s₁ = Eq.refl

    s₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    s₂ = inj₁-a-eq Eq.refl

    s₃ : proj₂ (ract {₁₊ m} c₂ (gate₁ S-gate)) ≡ c₃
    s₃ = inj₁-a-eq (Eq.cong (₁₊ b₀ ,_)
      (Eq.trans (+-identityˡ (- ₁₊ b₀)) eq-z))

    s₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    s₄ = inj₁-a-eq (Eq.cong (₁₊ z ,_) eq-z)

    s₅ : proj₂ (ract {₁₊ m} c₄ (gate₁ S-gate)) ≡ c₅
    s₅ = inj₁-a-eq (Eq.cong (₁₊ z ,_) (+-inverseʳ (₁₊ z)))

    s₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate))
         ≡ inj₁ (Φ j₄ m₁ , (bv , ((₀ , ₁₊ b₀) , nz)))
    s₆ = inj₁-a-eq (Eq.cong (₀ ,_) zEq)

  orderSH-inj₁-0b-coset :
    ((ract {₁₊ m} ᵗ) c₀ ((S • H) ^ 3)) .proj₂ ≡ c₀
  orderSH-inj₁-0b-coset =
    Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c ((S • H) ^ 2)) .proj₂)
      (SH-pair c₀ c₁ c₂ s₁ s₂))
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (S • H)) .proj₂)
      (SH-pair c₂ c₃ c₄ s₃ s₄))
    (Eq.trans (SH-pair c₄ c₅ _ s₅ s₆)
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₀ , ₁₊ b₀) , nz))))
        (chain-0 (j₁ ∷ᴸ j₄ ∷ᴸ []ᴸ) mm bv sum0))))

module OrderSH-a0 {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  where

  private
    j₂ = kHn {m} a₀ y (λ ())
    j₅ = kS0 {m} a₀ (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    m₂ = Φ j₂ mm

    yEq : - ₁₊ y ≡ ₁₊ a₀
    yEq = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

    sum0 : sumZ (j₂ ∷ᴸ j₅ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ (kHn-negsq {m} a₀ y eq-y (λ ()))
        (Eq.cong₂ _+_ (kS0-val {m} a₀ (λ ())) Eq.refl))
      (Eq.trans (Eq.cong (- sqInv a₀ +_) (+-identityʳ (sqInv a₀)))
                (+-inverseˡ (sqInv a₀)))

    c₀ c₁ c₂ c₃ c₄ c₅ : C (₂₊ m)
    c₀ = inj₁ (mm , (bv , ((₁₊ a₀ , ₀) , nz)))
    c₁ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ y) , λ ())))
    c₂ = inj₁ (m₂ , (bv , ((₁₊ y , ₁₊ y) , λ ())))
    c₃ = inj₁ (m₂ , (bv , ((₁₊ y , ₀) , λ ())))
    c₄ = inj₁ (m₂ , (bv , ((₀ , ₁₊ a₀) , λ ())))
    c₅ = inj₁ (Φ j₅ m₂ , (bv , ((₀ , ₁₊ a₀) , λ ())))

    s₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ c₁
    s₁ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_)
      (Eq.trans (+-identityˡ (- ₁₊ a₀)) eq-y))

    s₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    s₂ = inj₁-a-eq (Eq.cong (₁₊ y ,_) eq-y)

    s₃ : proj₂ (ract {₁₊ m} c₂ (gate₁ S-gate)) ≡ c₃
    s₃ = inj₁-a-eq (Eq.cong (₁₊ y ,_) (+-inverseʳ (₁₊ y)))

    s₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    s₄ = inj₁-a-eq (Eq.cong (₀ ,_) yEq)

    s₅ : proj₂ (ract {₁₊ m} c₄ (gate₁ S-gate)) ≡ c₅
    s₅ = Eq.refl

    s₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate))
         ≡ inj₁ (Φ j₅ m₂ , (bv , ((₁₊ a₀ , ₀) , nz)))
    s₆ = inj₁-a-eq Eq.refl

  orderSH-inj₁-a0-coset :
    ((ract {₁₊ m} ᵗ) c₀ ((S • H) ^ 3)) .proj₂ ≡ c₀
  orderSH-inj₁-a0-coset =
    Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c ((S • H) ^ 2)) .proj₂)
      (SH-pair c₀ c₁ c₂ s₁ s₂))
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (S • H)) .proj₂)
      (SH-pair c₂ c₃ c₄ s₃ s₄))
    (Eq.trans (SH-pair c₄ c₅ _ s₅ s₆)
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₁₊ a₀ , ₀) , nz))))
        (chain-0 (j₂ ∷ᴸ j₅ ∷ᴸ []ᴸ) mm bv sum0))))

-- The diagonal branch: fully nonzero box with b − a ≡ 0 (so b = a).
module OrderSH-nn0 {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ b₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  (Xeq : ₁₊ b₀ + - ₁₊ a₀ ≡ ₀)
  where

  private
    j₃ = kS0 {m} y (λ ())
    j₆ = kHn {m} y a₀ (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    m₃ = Φ j₃ mm

    yEq : - ₁₊ y ≡ ₁₊ a₀
    yEq = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

    aEqb : ₁₊ a₀ ≡ ₁₊ b₀
    aEqb = Eq.trans (Eq.sym (+-identityˡ (₁₊ a₀)))
      (Eq.trans (Eq.cong (_+ ₁₊ a₀) (Eq.sym Xeq))
      (Eq.trans (+-assoc (₁₊ b₀) (- ₁₊ a₀) (₁₊ a₀))
      (Eq.trans (Eq.cong (₁₊ b₀ +_) (+-inverseˡ (₁₊ a₀)))
                (+-identityʳ (₁₊ b₀)))))

    sum0 : sumZ (j₃ ∷ᴸ j₆ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ (kS0-val {m} y (λ ()))
        (Eq.cong₂ _+_ (kHn-negsq {m} y a₀ yEq (λ ())) Eq.refl))
      (Eq.trans (Eq.cong (sqInv y +_) (+-identityʳ (- sqInv y)))
                (+-inverseʳ (sqInv y)))

    c₀ c₁ c₂ c₃ c₄ c₅ : C (₂₊ m)
    c₀ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    c₁ = inj₁ (mm , (bv , ((₁₊ a₀ , ₀) , λ ())))
    c₂ = inj₁ (mm , (bv , ((₀ , ₁₊ y) , λ ())))
    c₃ = inj₁ (m₃ , (bv , ((₀ , ₁₊ y) , λ ())))
    c₄ = inj₁ (m₃ , (bv , ((₁₊ y , ₀) , λ ())))
    c₅ = inj₁ (m₃ , (bv , ((₁₊ y , ₁₊ a₀) , λ ())))

    s₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ c₁
    s₁ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) Xeq)

    s₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    s₂ = inj₁-a-eq (Eq.cong (₀ ,_) eq-y)

    s₃ : proj₂ (ract {₁₊ m} c₂ (gate₁ S-gate)) ≡ c₃
    s₃ = Eq.refl

    s₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    s₄ = inj₁-a-eq Eq.refl

    s₅ : proj₂ (ract {₁₊ m} c₄ (gate₁ S-gate)) ≡ c₅
    s₅ = inj₁-a-eq (Eq.cong (₁₊ y ,_)
      (Eq.trans (+-identityˡ (- ₁₊ y)) yEq))

    s₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate))
         ≡ inj₁ (Φ j₆ m₃ , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    s₆ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) (Eq.trans yEq aEqb))

  orderSH-inj₁-nn0-coset :
    ((ract {₁₊ m} ᵗ) c₀ ((S • H) ^ 3)) .proj₂ ≡ c₀
  orderSH-inj₁-nn0-coset =
    Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c ((S • H) ^ 2)) .proj₂)
      (SH-pair c₀ c₁ c₂ s₁ s₂))
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (S • H)) .proj₂)
      (SH-pair c₂ c₃ c₄ s₃ s₄))
    (Eq.trans (SH-pair c₄ c₅ _ s₅ s₆)
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (chain-0 (j₃ ∷ᴸ j₆ ∷ᴸ []ᴸ) mm bv sum0))))

------------------------------------------------------------------------
-- The fully nonzero, off-diagonal order-SH branch.  The orbit visits
-- three fully nonzero H-stops whose exponents are (uv)⁻¹, (vs)⁻¹,
-- (su)⁻¹ for u = a, v = b − a, s = − b; since u + v + s = 0 they sum
-- to zero (the classical 3-cycle identity, inv-3sum).

-- − (v + − u) + v ≡ u.
neg-core₂ : ∀ (u v : ℤ ₚ) → - (v + - u) + v ≡ u
neg-core₂ u v =
  Eq.trans (Eq.cong (_+ v)
    (Eq.trans (Eq.sym (-‿+-comm v (- u)))
              (Eq.cong (- v +_) (-‿involutive u))))
  (Eq.trans (Eq.cong (_+ v) (+-comm (- v) u))
  (Eq.trans (+-assoc u (- v) v)
  (Eq.trans (Eq.cong (u +_) (+-inverseˡ v)) (+-identityʳ u))))

-- u + v + s ≡ 0 ⟹ (uv)⁻¹ + ((vs)⁻¹ + ((su)⁻¹ + 0)) ≡ 0.
inv-3sum : ∀ (u v s : ℤ* ₚ) →
  u .proj₁ + (v .proj₁ + s .proj₁) ≡ ₀ →
  ((u *' v) ⁻¹) .proj₁ +
    (((v *' s) ⁻¹) .proj₁ + (((s *' u) ⁻¹) .proj₁ + ₀)) ≡ ₀
inv-3sum u@(uv₁ , nzu) v@(vv , nzv) s@(sv , nzs) hyp =
  Eq.trans (Eq.cong₂ _+_ r₁ (Eq.cong₂ _+_ r₂
    (Eq.trans (Eq.cong (_+ ₀) r₃) (+-identityʳ (K * vv)))))
  (Eq.trans (Eq.cong (K * sv +_) (Eq.sym (*-distribˡ-+ K uv₁ vv)))
  (Eq.trans (Eq.sym (*-distribˡ-+ K sv (uv₁ + vv)))
  (Eq.trans (Eq.cong (K *_) hyp')
            (*-zeroʳ K))))
  where
  iu = (u ⁻¹) .proj₁
  iv = (v ⁻¹) .proj₁
  is = (s ⁻¹) .proj₁
  K  = iu * (iv * is)

  iuu : iu * uv₁ ≡ ₁
  iuu = lemma-⁻¹ˡ uv₁ {{nztoℕ {y = uv₁} {neq0 = nzu}}}
  ivv : iv * vv ≡ ₁
  ivv = lemma-⁻¹ˡ vv {{nztoℕ {y = vv} {neq0 = nzv}}}
  iss : is * sv ≡ ₁
  iss = lemma-⁻¹ˡ sv {{nztoℕ {y = sv} {neq0 = nzs}}}

  r₁ : ((u *' v) ⁻¹) .proj₁ ≡ K * sv
  r₁ = Eq.trans (inv-distrib u v) (Eq.sym
    (Eq.trans (*-assoc iu (iv * is) sv)
    (Eq.trans (Eq.cong (iu *_) (*-assoc iv is sv))
    (Eq.trans (Eq.cong (λ t → iu * (iv * t)) iss)
              (Eq.cong (iu *_) (*-identityʳ iv))))))

  r₂ : ((v *' s) ⁻¹) .proj₁ ≡ K * uv₁
  r₂ = Eq.trans (inv-distrib v s) (Eq.sym
    (Eq.trans (*-assoc iu (iv * is) uv₁)
    (Eq.trans (Eq.cong (iu *_) (*-comm (iv * is) uv₁))
    (Eq.trans (Eq.sym (*-assoc iu uv₁ (iv * is)))
    (Eq.trans (Eq.cong (_* (iv * is)) iuu)
              (*-identityˡ (iv * is)))))))

  r₃ : ((s *' u) ⁻¹) .proj₁ ≡ K * vv
  r₃ = Eq.trans (inv-distrib s u) (Eq.sym
    (Eq.trans (*-assoc iu (iv * is) vv)
    (Eq.trans (Eq.cong (iu *_)
      (Eq.trans (Eq.cong (_* vv) (*-comm iv is))
      (Eq.trans (*-assoc is iv vv)
      (Eq.trans (Eq.cong (is *_) ivv) (*-identityʳ is)))))
              (*-comm iu is))))

  hyp' : sv + (uv₁ + vv) ≡ ₀
  hyp' = Eq.trans (+-comm sv (uv₁ + vv))
    (Eq.trans (+-assoc uv₁ vv sv) hyp)

-- − x · − y ≡ x · y.
neg-neg-* : ∀ (x y : ℤ ₚ) → - x * - y ≡ x * y
neg-neg-* x y = Eq.trans (Eq.sym (-‿distribˡ-* x (- y)))
  (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* x y))) (-‿involutive (x * y)))

-- sqInv is invariant under negating the argument.
sqInv-neg : ∀ (β u : Fin (₁₊ p-2)) (equ : - ₁₊ β ≡ ₁₊ u) →
  sqInv u ≡ sqInv β
sqInv-neg β u equ =
  Eq.trans (Eq.cong₂ _*_ iEq iEq)
    (neg-neg-* (((₁₊ β , λ ()) ⁻¹) .proj₁) (((₁₊ β , λ ()) ⁻¹) .proj₁))
  where
  iEq : ((₁₊ u , λ ()) ⁻¹) .proj₁ ≡ - (((₁₊ β , λ ()) ⁻¹) .proj₁)
  iEq = Eq.trans (inv-val-cong (₁₊ u , λ ()) (-' (₁₊ β , λ ())) (Eq.sym equ))
                 (inv-neg-comm (₁₊ β , λ ()))

-- Diagonal H-exponent: kHn β β is the inverse square.
kHn-diag : ∀ {m : ℕ} (β : Fin (₁₊ p-2)) (nzx : (₁₊ β , ₁₊ β) ≢ (₀ , ₀)) →
  kHn {m} β β nzx ≡ sqInv β
kHn-diag {m} β nzx =
  Eq.trans (kHn-val {m} β β nzx) (inv-distrib (₁₊ β , λ ()) (₁₊ β , λ ()))

-- H-exponent on a (β , −γ) box: the negated inverse of βγ.
kHn-neg : ∀ {m : ℕ} (β γ u : Fin (₁₊ p-2)) (equ : - ₁₊ γ ≡ ₁₊ u)
  (nzx : (₁₊ β , ₁₊ u) ≢ (₀ , ₀)) →
  kHn {m} β u nzx ≡ - (((₁₊ β , λ ()) *' (₁₊ γ , λ ())) ⁻¹) .proj₁
kHn-neg {m} β γ u equ nzx =
  Eq.trans (kHn-val {m} β u nzx)
  (Eq.trans (inv-val-cong ((₁₊ β , λ ()) *' (₁₊ u , λ ()))
      (-' ((₁₊ β , λ ()) *' (₁₊ γ , λ ())))
      (Eq.trans (Eq.cong (₁₊ β *_) (Eq.sym equ))
                (Eq.sym (-‿distribʳ-* (₁₊ β) (₁₊ γ)))))
    (inv-neg-comm ((₁₊ β , λ ()) *' (₁₊ γ , λ ()))))

-- Thread three bottom unary gates through the coset.
thread3 : ∀ {m : ℕ} (g₁ g₂ g₃ : SympGate 1) (c c₁ c₂ c₃ : C (₂₊ m)) →
  proj₂ (ract {₁₊ m} c (gate₁ g₁)) ≡ c₁ →
  proj₂ (ract {₁₊ m} c₁ (gate₁ g₂)) ≡ c₂ →
  proj₂ (ract {₁₊ m} c₂ (gate₁ g₃)) ≡ c₃ →
  ((ract {₁₊ m} ᵗ)
     c ([ gate₁ g₁ ]ʷ • ([ gate₁ g₂ ]ʷ • [ gate₁ g₃ ]ʷ))) .proj₂ ≡ c₃
thread3 {m} g₁ g₂ g₃ c c₁ c₂ c₃ e₁ e₂ e₃ =
  Eq.trans (Eq.cong
    (λ cc → ((ract {₁₊ m} ᵗ) cc ([ gate₁ g₂ ]ʷ • [ gate₁ g₃ ]ʷ)) .proj₂) e₁)
  (Eq.trans (Eq.cong (λ cc → proj₂ (ract {₁₊ m} cc (gate₁ g₃))) e₂) e₃)

module OrderSH-nnw {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ b₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  (z : Fin (₁₊ p-2)) (eq-z : - ₁₊ b₀ ≡ ₁₊ z)
  (w : Fin (₁₊ p-2)) (Xeq : ₁₊ b₀ + - ₁₊ a₀ ≡ ₁₊ w)
  (t : Fin (₁₊ p-2)) (eq-t : - ₁₊ w ≡ ₁₊ t)
  where

  private
    j₂ = kHn {m} a₀ w (λ ())
    j₄ = kHn {m} w z (λ ())
    j₆ = kHn {m} z a₀ (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    m₂ = Φ j₂ mm
    m₄ = Φ j₄ m₂

    zEq : - ₁₊ z ≡ ₁₊ b₀
    zEq = Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b₀))

    yw-eq : ₁₊ y + - ₁₊ w ≡ ₁₊ z
    yw-eq = Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-y) (Eq.cong -_ (Eq.sym Xeq)))
      (Eq.trans (neg-core (₁₊ a₀) (₁₊ b₀)) eq-z)

    zt-eq : ₁₊ t + - ₁₊ z ≡ ₁₊ a₀
    zt-eq = Eq.trans
      (Eq.cong₂ _+_ (Eq.trans (Eq.sym eq-t) (Eq.cong -_ (Eq.sym Xeq))) zEq)
      (neg-core₂ (₁₊ a₀) (₁₊ b₀))

    Σ3 : ₁₊ a₀ + (₁₊ w + ₁₊ z) ≡ ₀
    Σ3 = Eq.trans (Eq.cong (₁₊ a₀ +_)
        (Eq.trans (Eq.cong₂ _+_ (Eq.sym Xeq) (Eq.sym eq-z))
        (Eq.trans (+-swap (₁₊ b₀) (- ₁₊ a₀) (- ₁₊ b₀))
        (Eq.trans (Eq.cong (_+ - ₁₊ a₀) (+-inverseʳ (₁₊ b₀)))
                  (+-identityˡ (- ₁₊ a₀))))))
      (+-inverseʳ (₁₊ a₀))

    sum0 : sumZ (j₂ ∷ᴸ j₄ ∷ᴸ j₆ ∷ᴸ []ᴸ) ≡ ₀
    sum0 = Eq.trans
      (Eq.cong₂ _+_ (kHn-val {m} a₀ w (λ ()))
        (Eq.cong₂ _+_ (kHn-val {m} w z (λ ()))
          (Eq.cong₂ _+_ (kHn-val {m} z a₀ (λ ())) Eq.refl)))
      (inv-3sum (₁₊ a₀ , λ ()) (₁₊ w , λ ()) (₁₊ z , λ ()) Σ3)

    c₀ c₁ c₂ c₃ c₄ c₅ : C (₂₊ m)
    c₀ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    c₁ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ w) , λ ())))
    c₂ = inj₁ (m₂ , (bv , ((₁₊ w , ₁₊ y) , λ ())))
    c₃ = inj₁ (m₂ , (bv , ((₁₊ w , ₁₊ z) , λ ())))
    c₄ = inj₁ (m₄ , (bv , ((₁₊ z , ₁₊ t) , λ ())))
    c₅ = inj₁ (m₄ , (bv , ((₁₊ z , ₁₊ a₀) , λ ())))

    s₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ c₁
    s₁ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) Xeq)

    s₂ : proj₂ (ract {₁₊ m} c₁ (gate₁ H-gate)) ≡ c₂
    s₂ = inj₁-a-eq (Eq.cong (₁₊ w ,_) eq-y)

    s₃ : proj₂ (ract {₁₊ m} c₂ (gate₁ S-gate)) ≡ c₃
    s₃ = inj₁-a-eq (Eq.cong (₁₊ w ,_) yw-eq)

    s₄ : proj₂ (ract {₁₊ m} c₃ (gate₁ H-gate)) ≡ c₄
    s₄ = inj₁-a-eq (Eq.cong (₁₊ z ,_) eq-t)

    s₅ : proj₂ (ract {₁₊ m} c₄ (gate₁ S-gate)) ≡ c₅
    s₅ = inj₁-a-eq (Eq.cong (₁₊ z ,_) zt-eq)

    s₆ : proj₂ (ract {₁₊ m} c₅ (gate₁ H-gate))
         ≡ inj₁ (Φ j₆ m₄ , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    s₆ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) zEq)

  orderSH-inj₁-nnw-coset :
    ((ract {₁₊ m} ᵗ) c₀ ((S • H) ^ 3)) .proj₂ ≡ c₀
  orderSH-inj₁-nnw-coset =
    Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c ((S • H) ^ 2)) .proj₂)
      (SH-pair c₀ c₁ c₂ s₁ s₂))
    (Eq.trans (Eq.cong (λ c → ((ract {₁₊ m} ᵗ) c (S • H)) .proj₂)
      (SH-pair c₂ c₃ c₄ s₃ s₄))
    (Eq.trans (SH-pair c₄ c₅ _ s₅ s₆)
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (chain-0 (j₂ ∷ᴸ j₄ ∷ᴸ j₆ ∷ᴸ []ᴸ) mm bv sum0))))

------------------------------------------------------------------------
-- comm-HHS at inj₁, COSET halves: both action orders land on the same
-- coset.  On each branch every emitted chain sums to zero, so both
-- sides' M columns return to mm (chain-0) and the boxes agree after
-- normalising stuck negations.

module CommHHS-0b {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (b₀ : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ b₀ ≡ ₁₊ y)
  where

  private
    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    jEq : kS0 {m} y (λ ()) ≡ kS0 {m} b₀ nz
    jEq = Eq.trans (kS0-val {m} y (λ ()))
      (Eq.trans (sqInv-neg b₀ y eq-y) (Eq.sym (kS0-val {m} b₀ nz)))

    c₀ cL₁ cL₂ cF cR₁ : C (₂₊ m)
    c₀  = inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz)))
    cL₁ = inj₁ (mm , (bv , ((₁₊ b₀ , ₀) , λ ())))
    cL₂ = inj₁ (mm , (bv , ((₀ , ₁₊ y) , λ ())))
    cF  = inj₁ (Φ (kS0 {m} b₀ nz) mm , (bv , ((₀ , ₁₊ y) , λ ())))
    cR₁ = inj₁ (Φ (kS0 {m} b₀ nz) mm , (bv , ((₀ , ₁₊ b₀) , nz)))

    sL₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ H-gate)) ≡ cL₁
    sL₁ = inj₁-a-eq Eq.refl
    sL₂ : proj₂ (ract {₁₊ m} cL₁ (gate₁ H-gate)) ≡ cL₂
    sL₂ = inj₁-a-eq (Eq.cong (₀ ,_) eq-y)
    sL₃ : proj₂ (ract {₁₊ m} cL₂ (gate₁ S-gate)) ≡ cF
    sL₃ = Eq.cong (λ j → inj₁ (Φ j mm , (bv , ((₀ , ₁₊ y) , λ ())))) jEq

    sR₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ cR₁
    sR₁ = Eq.refl
    sR₂ : proj₂ (ract {₁₊ m} cR₁ (gate₁ H-gate))
          ≡ inj₁ (Φ (kS0 {m} b₀ nz) mm , (bv , ((₁₊ b₀ , ₀) , λ ())))
    sR₂ = inj₁-a-eq Eq.refl
    sR₃ : proj₂ (ract {₁₊ m}
            (inj₁ (Φ (kS0 {m} b₀ nz) mm , (bv , ((₁₊ b₀ , ₀) , λ ()))))
            (gate₁ H-gate)) ≡ cF
    sR₃ = inj₁-a-eq (Eq.cong (₀ ,_) eq-y)

  commHHS-inj₁-0b-coset :
    ((ract {₁₊ m} ᵗ) c₀ (H • H • S)) .proj₂
    ≡ ((ract {₁₊ m} ᵗ) c₀ (S • H • H)) .proj₂
  commHHS-inj₁-0b-coset =
    Eq.trans (thread3 H-gate H-gate S-gate c₀ cL₁ cL₂ cF sL₁ sL₂ sL₃)
      (Eq.sym (thread3 S-gate H-gate H-gate c₀ cR₁
        (inj₁ (Φ (kS0 {m} b₀ nz) mm , (bv , ((₁₊ b₀ , ₀) , λ ()))))
        cF sR₁ sR₂ sR₃))

module CommHHS-a0 {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₀) ≢ (₀ , ₀))
  (y : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  where

  private
    j₂ = kHn {m} a₀ y (λ ())
    j₃ = kHn {m} y y (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    yEq : - ₁₊ y ≡ ₁₊ a₀
    yEq = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

    sum0 : sumZ (j₂ ∷ᴸ j₃ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ (kHn-neg {m} a₀ a₀ y eq-y (λ ()))
        (Eq.cong₂ _+_
          (Eq.trans (kHn-diag {m} y (λ ())) (sqInv-neg a₀ y eq-y))
          Eq.refl))
      (Eq.trans (Eq.cong₂ _+_
          (Eq.cong -_ (inv-distrib (₁₊ a₀ , λ ()) (₁₊ a₀ , λ ())))
          (+-identityʳ (sqInv a₀)))
        (+-inverseˡ (sqInv a₀)))

    c₀ cL₁ cL₂ cF cR₁ cR₂ : C (₂₊ m)
    c₀  = inj₁ (mm , (bv , ((₁₊ a₀ , ₀) , nz)))
    cL₁ = inj₁ (mm , (bv , ((₀ , ₁₊ y) , λ ())))
    cL₂ = inj₁ (mm , (bv , ((₁₊ y , ₀) , λ ())))
    cF  = inj₁ (mm , (bv , ((₁₊ y , ₁₊ a₀) , λ ())))
    cR₁ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ y) , λ ())))
    cR₂ = inj₁ (Φ j₂ mm , (bv , ((₁₊ y , ₁₊ y) , λ ())))

    sL₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ H-gate)) ≡ cL₁
    sL₁ = inj₁-a-eq (Eq.cong (₀ ,_) eq-y)
    sL₂ : proj₂ (ract {₁₊ m} cL₁ (gate₁ H-gate)) ≡ cL₂
    sL₂ = inj₁-a-eq Eq.refl
    sL₃ : proj₂ (ract {₁₊ m} cL₂ (gate₁ S-gate)) ≡ cF
    sL₃ = inj₁-a-eq (Eq.cong (₁₊ y ,_)
      (Eq.trans (+-identityˡ (- ₁₊ y)) yEq))

    sR₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ cR₁
    sR₁ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_)
      (Eq.trans (+-identityˡ (- ₁₊ a₀)) eq-y))
    sR₂ : proj₂ (ract {₁₊ m} cR₁ (gate₁ H-gate)) ≡ cR₂
    sR₂ = inj₁-a-eq (Eq.cong (₁₊ y ,_) eq-y)
    sR₃ : proj₂ (ract {₁₊ m} cR₂ (gate₁ H-gate))
          ≡ inj₁ (Φ j₃ (Φ j₂ mm) , (bv , ((₁₊ y , ₁₊ a₀) , λ ())))
    sR₃ = inj₁-a-eq (Eq.cong (₁₊ y ,_) yEq)

  commHHS-inj₁-a0-coset :
    ((ract {₁₊ m} ᵗ) c₀ (H • H • S)) .proj₂
    ≡ ((ract {₁₊ m} ᵗ) c₀ (S • H • H)) .proj₂
  commHHS-inj₁-a0-coset =
    Eq.trans (thread3 H-gate H-gate S-gate c₀ cL₁ cL₂ cF sL₁ sL₂ sL₃)
      (Eq.sym (Eq.trans
        (thread3 S-gate H-gate H-gate c₀ cR₁ cR₂
          (inj₁ (Φ j₃ (Φ j₂ mm) , (bv , ((₁₊ y , ₁₊ a₀) , λ ()))))
          sR₁ sR₂ sR₃)
        (Eq.cong (λ zz → inj₁ (zz , (bv , ((₁₊ y , ₁₊ a₀) , λ ()))))
          (chain-0 (j₂ ∷ᴸ j₃ ∷ᴸ []ᴸ) mm bv sum0))))


module CommHHS-nn0 {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ b₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y z : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y) (eq-z : - ₁₊ b₀ ≡ ₁₊ z)
  (Xeq : ₁₊ b₀ + - ₁₊ a₀ ≡ ₀)
  where

  private
    j₁ = kHn {m} a₀ b₀ nz
    j₂ = kHn {m} b₀ y (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    aEqb : ₁₊ a₀ ≡ ₁₊ b₀
    aEqb = Eq.trans (Eq.sym (+-identityˡ (₁₊ a₀)))
      (Eq.trans (Eq.cong (_+ ₁₊ a₀) (Eq.sym Xeq))
      (Eq.trans (+-assoc (₁₊ b₀) (- ₁₊ a₀) (₁₊ a₀))
      (Eq.trans (Eq.cong (₁₊ b₀ +_) (+-inverseˡ (₁₊ a₀)))
                (+-identityʳ (₁₊ b₀)))))

    zy0 : ₁₊ z + - ₁₊ y ≡ ₀
    zy0 = Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-z) (Eq.cong -_ (Eq.sym eq-y)))
      (Eq.trans (Eq.cong (- ₁₊ b₀ +_) (-‿involutive (₁₊ a₀)))
      (Eq.trans (Eq.cong (- ₁₊ b₀ +_) aEqb) (+-inverseˡ (₁₊ b₀))))

    sum0 : sumZ (j₁ ∷ᴸ j₂ ∷ᴸ []ᴸ) ≡ ₀
    sum0 =
      Eq.trans (Eq.cong₂ _+_ (kHn-val {m} a₀ b₀ nz)
        (Eq.cong₂ _+_
          (Eq.trans (kHn-neg {m} b₀ a₀ y eq-y (λ ()))
            (Eq.cong -_ (inv-val-cong
              ((₁₊ b₀ , λ ()) *' (₁₊ a₀ , λ ()))
              ((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ()))
              (*-comm (₁₊ b₀) (₁₊ a₀)))))
          Eq.refl))
      (Eq.trans (Eq.cong
          ((((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁ +_)
          (+-identityʳ (- ((((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁))))
        (+-inverseʳ ((((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁)))

    c₀ cL₁ cL₂ cF cR₁ cR₂ : C (₂₊ m)
    c₀  = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    cL₁ = inj₁ (Φ j₁ mm , (bv , ((₁₊ b₀ , ₁₊ y) , λ ())))
    cL₂ = inj₁ (Φ j₂ (Φ j₁ mm) , (bv , ((₁₊ y , ₁₊ z) , λ ())))
    cF  = inj₁ (mm , (bv , ((₁₊ y , ₀) , λ ())))
    cR₁ = inj₁ (mm , (bv , ((₁₊ a₀ , ₀) , λ ())))
    cR₂ = inj₁ (mm , (bv , ((₀ , ₁₊ y) , λ ())))

    sL₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ H-gate)) ≡ cL₁
    sL₁ = inj₁-a-eq (Eq.cong (₁₊ b₀ ,_) eq-y)
    sL₂ : proj₂ (ract {₁₊ m} cL₁ (gate₁ H-gate)) ≡ cL₂
    sL₂ = inj₁-a-eq (Eq.cong (₁₊ y ,_) eq-z)
    sL₃ : proj₂ (ract {₁₊ m} cL₂ (gate₁ S-gate)) ≡ cF
    sL₃ = Eq.trans
      (inj₁-a-eq (Eq.cong (₁₊ y ,_) zy0))
      (Eq.cong (λ zz → inj₁ (zz , (bv , ((₁₊ y , ₀) , λ ()))))
        (chain-0 (j₁ ∷ᴸ j₂ ∷ᴸ []ᴸ) mm bv sum0))

    sR₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ cR₁
    sR₁ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) Xeq)
    sR₂ : proj₂ (ract {₁₊ m} cR₁ (gate₁ H-gate)) ≡ cR₂
    sR₂ = inj₁-a-eq (Eq.cong (₀ ,_) eq-y)
    sR₃ : proj₂ (ract {₁₊ m} cR₂ (gate₁ H-gate)) ≡ cF
    sR₃ = inj₁-a-eq Eq.refl

  commHHS-inj₁-nn0-coset :
    ((ract {₁₊ m} ᵗ) c₀ (H • H • S)) .proj₂
    ≡ ((ract {₁₊ m} ᵗ) c₀ (S • H • H)) .proj₂
  commHHS-inj₁-nn0-coset =
    Eq.trans (thread3 H-gate H-gate S-gate c₀ cL₁ cL₂ cF sL₁ sL₂ sL₃)
      (Eq.sym (thread3 S-gate H-gate H-gate c₀ cR₁ cR₂ cF sR₁ sR₂ sR₃))

module CommHHS-nnw {m : ℕ} (mm : M (₂₊ m)) (bv : Vec B (₁₊ m))
  (a₀ b₀ : Fin (₁₊ p-2)) (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀))
  (y z w : Fin (₁₊ p-2)) (eq-y : - ₁₊ a₀ ≡ ₁₊ y)
  (eq-z : - ₁₊ b₀ ≡ ₁₊ z) (Xeq : ₁₊ b₀ + - ₁₊ a₀ ≡ ₁₊ w)
  where

  private
    j₁ = kHn {m} a₀ b₀ nz
    j₂ = kHn {m} b₀ y (λ ())
    j₁ʳ = kHn {m} a₀ w (λ ())
    j₂ʳ = kHn {m} w y (λ ())

    Φ : ℤ ₚ → M (₂₊ m) → M (₂₊ m)
    Φ j zz = mbSⁿm (toℕ j) zz bv

    yEq : - ₁₊ y ≡ ₁₊ a₀
    yEq = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a₀))

    sum0L : sumZ (j₁ ∷ᴸ j₂ ∷ᴸ []ᴸ) ≡ ₀
    sum0L =
      Eq.trans (Eq.cong₂ _+_ (kHn-val {m} a₀ b₀ nz)
        (Eq.cong₂ _+_
          (Eq.trans (kHn-neg {m} b₀ a₀ y eq-y (λ ()))
            (Eq.cong -_ (inv-val-cong
              ((₁₊ b₀ , λ ()) *' (₁₊ a₀ , λ ()))
              ((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ()))
              (*-comm (₁₊ b₀) (₁₊ a₀)))))
          Eq.refl))
      (Eq.trans (Eq.cong
          ((((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁ +_)
          (+-identityʳ (- ((((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁))))
        (+-inverseʳ ((((₁₊ a₀ , λ ()) *' (₁₊ b₀ , λ ())) ⁻¹) .proj₁)))

    sum0R : sumZ (j₁ʳ ∷ᴸ j₂ʳ ∷ᴸ []ᴸ) ≡ ₀
    sum0R =
      Eq.trans (Eq.cong₂ _+_ (kHn-val {m} a₀ w (λ ()))
        (Eq.cong₂ _+_
          (Eq.trans (kHn-neg {m} w a₀ y eq-y (λ ()))
            (Eq.cong -_ (inv-val-cong
              ((₁₊ w , λ ()) *' (₁₊ a₀ , λ ()))
              ((₁₊ a₀ , λ ()) *' (₁₊ w , λ ()))
              (*-comm (₁₊ w) (₁₊ a₀)))))
          Eq.refl))
      (Eq.trans (Eq.cong
          ((((₁₊ a₀ , λ ()) *' (₁₊ w , λ ())) ⁻¹) .proj₁ +_)
          (+-identityʳ (- ((((₁₊ a₀ , λ ()) *' (₁₊ w , λ ())) ⁻¹) .proj₁))))
        (+-inverseʳ ((((₁₊ a₀ , λ ()) *' (₁₊ w , λ ())) ⁻¹) .proj₁)))

    -- Both final boxes normalise to (₁₊ y , − ₁₊ b₀ + ₁₊ a₀).
    zy-canon : ₁₊ z + - ₁₊ y ≡ - ₁₊ b₀ + ₁₊ a₀
    zy-canon = Eq.cong₂ _+_ (Eq.sym eq-z) yEq

    wz-eq : - ₁₊ w ≡ - ₁₊ b₀ + ₁₊ a₀
    wz-eq = Eq.trans (Eq.cong -_ (Eq.sym Xeq))
      (Eq.trans (Eq.sym (-‿+-comm (₁₊ b₀) (- ₁₊ a₀)))
        (Eq.cong (- ₁₊ b₀ +_) (-‿involutive (₁₊ a₀))))

    c₀ cL₁ cL₂ cF cR₁ cR₂ : C (₂₊ m)
    c₀  = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz)))
    cL₁ = inj₁ (Φ j₁ mm , (bv , ((₁₊ b₀ , ₁₊ y) , λ ())))
    cL₂ = inj₁ (Φ j₂ (Φ j₁ mm) , (bv , ((₁₊ y , ₁₊ z) , λ ())))
    cF  = inj₁ (mm , (bv , ((₁₊ y , - ₁₊ b₀ + ₁₊ a₀) , λ ())))
    cR₁ = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ w) , λ ())))
    cR₂ = inj₁ (Φ j₁ʳ mm , (bv , ((₁₊ w , ₁₊ y) , λ ())))

    sL₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ H-gate)) ≡ cL₁
    sL₁ = inj₁-a-eq (Eq.cong (₁₊ b₀ ,_) eq-y)
    sL₂ : proj₂ (ract {₁₊ m} cL₁ (gate₁ H-gate)) ≡ cL₂
    sL₂ = inj₁-a-eq (Eq.cong (₁₊ y ,_) eq-z)
    sL₃ : proj₂ (ract {₁₊ m} cL₂ (gate₁ S-gate)) ≡ cF
    sL₃ = Eq.trans
      (inj₁-a-eq (Eq.cong (₁₊ y ,_) zy-canon))
      (Eq.cong
        (λ zz → inj₁ (zz , (bv , ((₁₊ y , - ₁₊ b₀ + ₁₊ a₀) , λ ()))))
        (chain-0 (j₁ ∷ᴸ j₂ ∷ᴸ []ᴸ) mm bv sum0L))

    sR₁ : proj₂ (ract {₁₊ m} c₀ (gate₁ S-gate)) ≡ cR₁
    sR₁ = inj₁-a-eq (Eq.cong (₁₊ a₀ ,_) Xeq)
    sR₂ : proj₂ (ract {₁₊ m} cR₁ (gate₁ H-gate)) ≡ cR₂
    sR₂ = inj₁-a-eq (Eq.cong (₁₊ w ,_) eq-y)
    sR₃ : proj₂ (ract {₁₊ m} cR₂ (gate₁ H-gate)) ≡ cF
    sR₃ = Eq.trans
      (inj₁-a-eq (Eq.cong (₁₊ y ,_) wz-eq))
      (Eq.cong
        (λ zz → inj₁ (zz , (bv , ((₁₊ y , - ₁₊ b₀ + ₁₊ a₀) , λ ()))))
        (chain-0 (j₁ʳ ∷ᴸ j₂ʳ ∷ᴸ []ᴸ) mm bv sum0R))

  commHHS-inj₁-nnw-coset :
    ((ract {₁₊ m} ᵗ) c₀ (H • H • S)) .proj₂
    ≡ ((ract {₁₊ m} ᵗ) c₀ (S • H • H)) .proj₂
  commHHS-inj₁-nnw-coset =
    Eq.trans (thread3 H-gate H-gate S-gate c₀ cL₁ cL₂ cF sL₁ sL₂ sL₃)
      (Eq.sym (thread3 S-gate H-gate H-gate c₀ cR₁ cR₂ cF sR₁ sR₂ sR₃))
