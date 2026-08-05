------------------------------------------------------------------------
-- Presentations of groups
--
-- Width-2 well-definedness pairs, assembled: with Strategy B armed at
-- width 2 (StrategyB2.wd-from-coset, via the completed width-1 tower),
-- each width-2 srel-wd obligation follows from its coset (≡) half
-- alone.  This module pairs the proved coset-half dispatchers with
-- wd-from-coset into full ≋ theorems — the width-2 instances of the
-- SrelWD holes for the sealed unary families.
--
-- (The kHn-heavy families (order-H/SH, comm-HHS) have per-branch coset
-- halves in PushWD but sealing their dispatchers blows up the checker;
-- they are assembled per-branch at their eventual fill sites.  The CZ
-- families' remaining coset halves are the parked engine cluster.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using ([])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C ; ract ; _≋_ ; elim-suc ; neg≢0)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM
  p-2 p-prime using ( orderS-inj₁-coset ; semiMS-inj₁-coset
                    ; Mmul-inj₁-coset-full
                    ; commCZS↑-w2-coset ; commCZS↓-w2-0b-coset )
open import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM2
  p-2 p-prime using (commCZS↓-w2-a+-coset ; module OrdCZ-0b)
import Examples.Groups.Symplectic.Normalization.Pushing.PushWDM3
  p-2 p-prime as PW3
import Examples.Groups.Symplectic.Normalization.Pushing.StrategyB2
  p-2 p-prime as SB2

------------------------------------------------------------------------
-- The sealed unary families at inj₁ cosets: full ≋ pairs at width 2.

order-S-wd2-inj₁ : ∀ (ml' : ML' 2) →
  (ract {1} ᵗ) (inj₁ ml') (S ^ p) ≋ (ract {1} ᵗ) (inj₁ ml') ε
order-S-wd2-inj₁ ml' =
  SB2.wd-from-coset (inj₁ ml') (srel Base.order-S) (orderS-inj₁-coset ml')

M-mul-wd2-inj₁ : ∀ (x* y* : ℤ* ₚ) (ml' : ML' 2) →
  (ract {1} ᵗ) (inj₁ ml') (ZM x* • ZM y*) ≋
  (ract {1} ᵗ) (inj₁ ml') (ZM (x* *' y*))
M-mul-wd2-inj₁ x* y* ml' =
  SB2.wd-from-coset (inj₁ ml') (srel (Base.M-mul x* y*))
    (Mmul-inj₁-coset-full x* y* ml')

semi-MS-wd2-inj₁ : ∀ (x* : ℤ* ₚ) (ml' : ML' 2) →
  (ract {1} ᵗ) (inj₁ ml') (ZM x* • S) ≋
  (ract {1} ᵗ) (inj₁ ml') (S^ (x* ^2) • ZM x*)
semi-MS-wd2-inj₁ x* ml' =
  SB2.wd-from-coset (inj₁ ml') (srel (Base.semi-MS x*))
    (semiMS-inj₁-coset x* ml')

------------------------------------------------------------------------
-- The CZ families at inj₂ (d , width-1) cosets: full ≋ pairs from the
-- proved width-2 coset halves.

-- comm-CZ-S↑: the coset half covers every A-box shape — the whole
-- {suc zero} inj₂ hole of SrelWD, as a theorem.
comm-CZ-S↑-wd2-inj₂ : ∀ (d : D) (e : E) (ab : ℤ ₚ × ℤ ₚ)
  (nz : ab ≢ (₀ , ₀)) →
  let c = inj₂ (d , (([] , e) , ([] , (ab , nz)))) in
  (ract {1} ᵗ) c (CZ • S ↑) ≋ (ract {1} ᵗ) c (S ↑ • CZ)
comm-CZ-S↑-wd2-inj₂ d e ab nz =
  SB2.wd-from-coset (inj₂ (d , (([] , e) , ([] , (ab , nz)))))
    (srel Base.comm-CZ-S↑) (commCZS↑-w2-coset d e ab nz)

-- comm-CZ-S↓: the two branch lemmas, dispatched over the A box.
comm-CZ-S↓-wd2-inj₂ : ∀ (d : D) (e : E) (ab : ℤ ₚ × ℤ ₚ)
  (nz : ab ≢ (₀ , ₀)) →
  let c = inj₂ (d , (([] , e) , ([] , (ab , nz)))) in
  (ract {1} ᵗ) c (CZ • S ↓) ≋ (ract {1} ᵗ) c (S ↓ • CZ)
comm-CZ-S↓-wd2-inj₂ d e (₀ , ₀) nz = ⊥-elim (nz auto)
comm-CZ-S↓-wd2-inj₂ d e (₀ , ₁₊ b) nz =
  SB2.wd-from-coset (inj₂ (d , (([] , e) , ([] , ((₀ , ₁₊ b) , nz)))))
    (srel Base.comm-CZ-S↓) (commCZS↓-w2-0b-coset d e b nz)
comm-CZ-S↓-wd2-inj₂ d e (₁₊ α' , β) nz =
  elim-suc (- ₁₊ α') (neg≢0 (₁₊ α') λ ()) λ y eq-y →
  SB2.wd-from-coset (inj₂ (d , (([] , e) , ([] , ((₁₊ α' , β) , nz)))))
    (srel Base.comm-CZ-S↓) (commCZS↓-w2-a+-coset d e α' β nz y eq-y)

-- order-CZ at inj₂, A box (₀,b): the collapse-free orbit branch.
order-CZ-wd2-inj₂-0b : ∀ (b : Fin (₁₊ p-2)) (nz : (₀ , ₁₊ b) ≢ (₀ , ₀))
  (d : D) (e : E) →
  let c = inj₂ (d , (([] , e) , ([] , ((₀ , ₁₊ b) , nz)))) in
  (ract {1} ᵗ) c (CZ ^ p) ≋ (ract {1} ᵗ) c ε
order-CZ-wd2-inj₂-0b b nz d e =
  SB2.wd-from-coset (inj₂ (d , (([] , e) , ([] , ((₀ , ₁₊ b) , nz)))))
    (srel Base.order-CZ) (OrdCZ-0b.ordCZ-w2-0b-coset b nz d e)

-- order-CZ at inj₁: the four proved branch families (the fifth,
-- (a=0,c≠0) shape-crossing, is parked).  Cosets are the branch
-- modules' cst shapes (pinned nonzero proofs).
order-CZ-wd2-inj₁-c0 : ∀ (a' : Fin (₁₊ p-2)) (d₀ : D) (e dd b : ℤ ₚ) →
  let c = PW3.OrdCZ-inj₁-c0.cst a' dd b e d₀ in
  (ract {1} ᵗ) c (CZ ^ p) ≋ (ract {1} ᵗ) c ε
order-CZ-wd2-inj₁-c0 a' d₀ e dd b =
  SB2.wd-from-coset (PW3.OrdCZ-inj₁-c0.cst a' dd b e d₀)
    (srel Base.order-CZ) (PW3.OrdCZ-inj₁-c0.ordCZ-inj₁-c0-coset a' d₀ e dd b)

order-CZ-wd2-inj₁-00 : ∀ (b' : Fin (₁₊ p-2)) (e : E) (da db : ℤ ₚ) →
  let c = PW3.OrdCZ-inj₁-00.cst b' e (da , db) in
  (ract {1} ᵗ) c (CZ ^ p) ≋ (ract {1} ᵗ) c ε
order-CZ-wd2-inj₁-00 b' e da db =
  SB2.wd-from-coset (PW3.OrdCZ-inj₁-00.cst b' e (da , db))
    (srel Base.order-CZ) (PW3.OrdCZ-inj₁-00.ordCZ-inj₁-00-coset b' e da db)

order-CZ-wd2-inj₁-0d : ∀ (b' dd' : Fin (₁₊ p-2)) (e : E) (da db : ℤ ₚ) →
  let c = PW3.OrdCZ-inj₁-0d.cst b' dd' e (da , db) in
  (ract {1} ᵗ) c (CZ ^ p) ≋ (ract {1} ᵗ) c ε
order-CZ-wd2-inj₁-0d b' dd' e da db =
  SB2.wd-from-coset (PW3.OrdCZ-inj₁-0d.cst b' dd' e (da , db))
    (srel Base.order-CZ)
    (PW3.OrdCZ-inj₁-0d.ordCZ-inj₁-0d-coset b' dd' e da db)

order-CZ-wd2-inj₁-cc : ∀ (a₀ c₁' : Fin (₁₊ p-2)) (dd b e da db : ℤ ₚ) →
  let c = PW3.OrdCZ-inj₁-cc.cst a₀ c₁' dd b e da db in
  (ract {1} ᵗ) c (CZ ^ p) ≋ (ract {1} ᵗ) c ε
order-CZ-wd2-inj₁-cc a₀ c₁' dd b e da db =
  SB2.wd-from-coset (PW3.OrdCZ-inj₁-cc.cst a₀ c₁' dd b e da db)
    (srel Base.order-CZ)
    (PW3.OrdCZ-inj₁-cc.ordCZ-inj₁-cc-coset a₀ c₁' dd b e da db)
