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

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime

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
