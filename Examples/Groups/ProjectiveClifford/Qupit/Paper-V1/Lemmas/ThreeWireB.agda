{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The remote CZ at three wires, part 2 of 2: Selinger's c12-c15.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ< ; toℕ-injective)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ThreeWireB
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
open Lemmas-Clifford
  using (lemma-↑^ ; lemma-Induction ; lemma-Inductionˡ
        ; lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Hᵏ-w↑
        ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑ ; lemma-comm-CZ-w↑)

private
  variable
    n : ℕ

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ExConj p-3 p-prime g* g-gen

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ThreeWireA p-3 p-prime g* g-gen as TA

module Three-Wire-B (n : ℕ) where

  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation (₁₊ n)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₂ = PB ((₂₊ n) QRel,_===_)

  open Group-Lemmas ((₃₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₃₊ n})
    using (•-cancelʳ ; •-cancelˡ)

  open TA.Three-Wire-A n public

  ------------------------------------------------------------------------
  -- The upper half-swap commutes with CZ02
  --
  -- The mirror of lemma-comm-ₕ|ₕ-CZ↑, one wire up.  ₕ|ₕ ↑ is
  -- H ↑ • CZ ↑ • H ↑; the two CZs commute by the lemma above, and H ↑
  -- against CZ02 is a conjugation: writing CZ02 as Ex ↑ • CZ • Ex ↑, the
  -- swap carries H ↑ to H ↑ ↑, which clears CZ structurally, and the
  -- second swap carries it back.

  private
    ex↑-H↑↑ : Ex ↑ • H ↑ ↑ ≈ H ↑ • Ex ↑
    ex↑-H↑↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-H↑ n)

    ex↑-H↑ : Ex ↑ • H ↑ ≈ H ↑ ↑ • Ex ↑
    ex↑-H↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-H n)

  lemma-comm-H↑-CZ02 : H ↑ • CZ02 ≈ CZ02 • H ↑
  lemma-comm-H↑-CZ02 = begin
    H ↑ • CZ02
      ≈⟨ cright sym lemma-CZ02' ⟩
    H ↑ • (Ex ↑ • (CZ • Ex ↑))
      ≈⟨ sym assoc ⟩
    (H ↑ • Ex ↑) • (CZ • Ex ↑)
      ≈⟨ cleft sym ex↑-H↑↑ ⟩
    (Ex ↑ • H ↑ ↑) • (CZ • Ex ↑)
      ≈⟨ by-assoc auto ⟩
    Ex ↑ • ((H ↑ ↑ • CZ) • Ex ↑)
      ≈⟨ cright cleft axiom comm-CZ ⟩
    Ex ↑ • ((CZ • H ↑ ↑) • Ex ↑)
      ≈⟨ cright assoc ⟩
    Ex ↑ • (CZ • (H ↑ ↑ • Ex ↑))
      ≈⟨ cright cright sym ex↑-H↑ ⟩
    Ex ↑ • (CZ • (Ex ↑ • H ↑))
      ≈⟨ by-assoc auto ⟩
    (Ex ↑ • (CZ • Ex ↑)) • H ↑
      ≈⟨ cleft lemma-CZ02' ⟩
    CZ02 • H ↑ ∎

  lemma-comm-ₕ|ₕ↑-CZ02 :
    (H ↑ • CZ ↑ • H ↑) • CZ02 ≈ CZ02 • (H ↑ • CZ ↑ • H ↑)
  lemma-comm-ₕ|ₕ↑-CZ02 = begin
    (H ↑ • CZ ↑ • H ↑) • CZ02
      ≈⟨ by-assoc auto ⟩
    H ↑ • (CZ ↑ • (H ↑ • CZ02))
      ≈⟨ cright cright lemma-comm-H↑-CZ02 ⟩
    H ↑ • (CZ ↑ • (CZ02 • H ↑))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((CZ ↑ • CZ02) • H ↑)
      ≈⟨ cright cleft lemma-comm-CZ↑-CZ02 ⟩
    H ↑ • ((CZ02 • CZ ↑) • H ↑)
      ≈⟨ sym assoc ⟩
    (H ↑ • (CZ02 • CZ ↑)) • H ↑
      ≈⟨ cleft sym assoc ⟩
    ((H ↑ • CZ02) • CZ ↑) • H ↑
      ≈⟨ cleft cleft lemma-comm-H↑-CZ02 ⟩
    ((CZ02 • H ↑) • CZ ↑) • H ↑
      ≈⟨ by-assoc auto ⟩
    CZ02 • (H ↑ • CZ ↑ • H ↑) ∎

  lemma-c13-right : ⊥⊤ • (CZ ↑ • ⊤⊥) ≈ CZ02
  lemma-c13-right = begin
    ⊥⊤ • (CZ ↑ • ⊤⊥)
      ≈⟨ cleft lemma-⊥⊤-simple ⟩
    (Ex • ₕ|ₕ) • (CZ ↑ • ⊤⊥)
      ≈⟨ cright cright lemma-⊤⊥-simple ⟩
    (Ex • ₕ|ₕ) • (CZ ↑ • (ₕ|ₕ • Ex))
      ≈⟨ by-assoc auto ⟩
    Ex • (((ₕ|ₕ • CZ ↑) • ₕ|ₕ) • Ex)
      ≈⟨ cright cleft cleft lemma-comm-ₕ|ₕ-CZ↑ ⟩
    Ex • (((CZ ↑ • ₕ|ₕ) • ₕ|ₕ) • Ex)
      ≈⟨ cright cleft assoc ⟩
    Ex • ((CZ ↑ • (ₕ|ₕ • ₕ|ₕ)) • Ex)
      ≈⟨ cright cleft cright lemma-ₕ|ₕ-invol ⟩
    Ex • ((CZ ↑ • ε) • Ex)
      ≈⟨ cright cleft right-unit ⟩
    Ex • (CZ ↑ • Ex) ∎

  ------------------------------------------------------------------------
  -- The other half of c13, and c13 itself
  --
  -- One wire up, with lemma-comm-ₕ|ₕ↑-CZ02 in place of lemma-comm-ₕ|ₕ-CZ↑
  -- and lemma-CZ02' in place of the definition of CZ02.  Both sides of
  -- c13 are CZ02, so the rule is the two halves glued.

  lemma-c13-left : ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑) ≈ CZ02
  lemma-c13-left = begin
    ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑)
      ≈⟨ cleft (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-simple n)) ⟩
    ((H ↑ • CZ ↑ • H ↑) • Ex ↑) • (CZ • ⊥⊤ {n} ↑)
      ≈⟨ cright cright (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊥⊤-simple n)) ⟩
    ((H ↑ • CZ ↑ • H ↑) • Ex ↑) • (CZ • (Ex ↑ • (H ↑ • CZ ↑ • H ↑)))
      ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ ↑ • H ↑) • ((Ex ↑ • (CZ • Ex ↑)) • (H ↑ • CZ ↑ • H ↑))
      ≈⟨ cright cleft lemma-CZ02' ⟩
    (H ↑ • CZ ↑ • H ↑) • (CZ02 • (H ↑ • CZ ↑ • H ↑))
      ≈⟨ sym assoc ⟩
    ((H ↑ • CZ ↑ • H ↑) • CZ02) • (H ↑ • CZ ↑ • H ↑)
      ≈⟨ cleft lemma-comm-ₕ|ₕ↑-CZ02 ⟩
    (CZ02 • (H ↑ • CZ ↑ • H ↑)) • (H ↑ • CZ ↑ • H ↑)
      ≈⟨ assoc ⟩
    CZ02 • ((H ↑ • CZ ↑ • H ↑) • (H ↑ • CZ ↑ • H ↑))
      ≈⟨ cright (lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)) ⟩
    CZ02 • ε
      ≈⟨ right-unit ⟩
    CZ02 ∎

  lemma-selinger-c13 :
    ⊤⊥ {n} ↑ • CZ ↓ • ⊥⊤ {n} ↑ ≈ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  lemma-selinger-c13 = trans lemma-c13-left (sym lemma-c13-right)

  ------------------------------------------------------------------------
  -- c13 as a commutation rule
  --
  -- Since ⊥⊤ ↑ inverts ⊤⊥ ↑, the conjugation form of c13 is equivalently
  -- a rule for moving ⊤⊥ ↑ across a CZ, which turns it from CZ into
  -- CZ02.  This is the form c14 uses: its element ⊤⊥ ↑ • CZ becomes
  -- CZ02 • ⊤⊥ ↑, so cubing it is a question about how ⊤⊥ ↑ moves across
  -- CZ02 — the one step c14 still lacks.

  ------------------------------------------------------------------------
  -- The identity c14 turns on
  --
  --     CZ • ₕ|ₕ ↑ • CZ • ₕ|ₕ ↑ ≈ CZ02
  --
  -- i.e. conjugating CZ by the upper half-swap gives CZ⁻¹ • CZ02.  This
  -- is where C18 enters, and it is the only place in the c13/c14 story
  -- that needs an axiom beyond what c13 used.
  --
  -- The half-swap is M₋₁ • CX (lemma-ₕ|ₕ-CX), so C18 applies directly:
  -- it moves CX ↑ across the CZ at the cost of a CZ02.  The two CX ↑ that
  -- are left sandwich a multiplier, and that sandwich collapses back to
  -- the multiplier because the half-swap is an involution.  What remains
  -- is a multiplier passing two CZs, rescaling one of them to its inverse
  -- and commuting with the other.

  private
    -- The multiplier on wire 1 commutes with CZ02, which lives on wires
    -- 0 and 2.  Syntactically: write CZ02 with the upper swap, which
    -- carries the multiplier to wire 2, where it clears CZ by the
    -- word-level structural rule, and carry it back.
    ex↑-M↑↑ : Ex ↑ • (M₋₁ {n}) ↑ ↑ ≈ M₋₁ ↑ • Ex ↑
    ex↑-M↑↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-M↑ n -'₁)

    M↑↑-ex↑ : (M₋₁ {n}) ↑ ↑ • Ex ↑ ≈ Ex ↑ • M₋₁ ↑
    M↑↑-ex↑ = begin
      (M₋₁ {n}) ↑ ↑ • Ex ↑
        ≈⟨ sym left-unit ⟩
      ε • ((M₋₁ {n}) ↑ ↑ • Ex ↑)
        ≈⟨ cleft sym lemma-Ex↑-Ex↑ ⟩
      (Ex ↑ • Ex ↑) • ((M₋₁ {n}) ↑ ↑ • Ex ↑)
        -- explicit assoc throughout this section: M₋₁ carries a symbolic
        -- power, so to-list is stuck and by-assoc cannot re-bracket it
        ≈⟨ assoc ⟩
      Ex ↑ • (Ex ↑ • ((M₋₁ {n}) ↑ ↑ • Ex ↑))
        ≈⟨ cright sym assoc ⟩
      Ex ↑ • ((Ex ↑ • (M₋₁ {n}) ↑ ↑) • Ex ↑)
        ≈⟨ cright cleft ex↑-M↑↑ ⟩
      Ex ↑ • ((M₋₁ ↑ • Ex ↑) • Ex ↑)
        ≈⟨ cright assoc ⟩
      Ex ↑ • (M₋₁ ↑ • (Ex ↑ • Ex ↑))
        ≈⟨ cright cright lemma-Ex↑-Ex↑ ⟩
      Ex ↑ • (M₋₁ ↑ • ε)
        ≈⟨ cright right-unit ⟩
      Ex ↑ • M₋₁ ↑ ∎

    lemma-M₋₁↑-CZ02 : M₋₁ ↑ • CZ02 ≈ CZ02 • M₋₁ ↑
    lemma-M₋₁↑-CZ02 = begin
      M₋₁ ↑ • CZ02
        ≈⟨ cright sym lemma-CZ02' ⟩
      M₋₁ ↑ • (Ex ↑ • (CZ • Ex ↑))
        ≈⟨ sym assoc ⟩
      (M₋₁ ↑ • Ex ↑) • (CZ • Ex ↑)
        ≈⟨ cleft sym ex↑-M↑↑ ⟩
      (Ex ↑ • (M₋₁ {n}) ↑ ↑) • (CZ • Ex ↑)
        ≈⟨ assoc ⟩
      Ex ↑ • ((M₋₁ {n}) ↑ ↑ • (CZ • Ex ↑))
        ≈⟨ cright sym assoc ⟩
      Ex ↑ • (((M₋₁ {n}) ↑ ↑ • CZ) • Ex ↑)
        ≈⟨ cright cleft sym (lemma-comm-CZ-w↑ (M₋₁ {n})) ⟩
      Ex ↑ • ((CZ • (M₋₁ {n}) ↑ ↑) • Ex ↑)
        ≈⟨ cright assoc ⟩
      Ex ↑ • (CZ • ((M₋₁ {n}) ↑ ↑ • Ex ↑))
        ≈⟨ cright cright M↑↑-ex↑ ⟩
      Ex ↑ • (CZ • (Ex ↑ • M₋₁ ↑))
        ≈⟨ cright sym assoc ⟩
      Ex ↑ • ((CZ • Ex ↑) • M₋₁ ↑)
        ≈⟨ sym assoc ⟩
      (Ex ↑ • (CZ • Ex ↑)) • M₋₁ ↑
        ≈⟨ cleft lemma-CZ02' ⟩
      CZ02 • M₋₁ ↑ ∎

    -- The half-swap is an involution, and it is M₋₁ ↑ • CX ↑, so the two
    -- CX ↑ sandwiching a multiplier collapse back to that multiplier.
    ₕ|ₕ↑-CX : M₋₁ ↑ • CX ↑ ≈ ₕ|ₕ ↑
    ₕ|ₕ↑-CX = lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-CX n)

    M₋₁↑-invol : M₋₁ ↑ • M₋₁ ↑ ≈ ε
    M₋₁↑-invol = lemma-cong↑ _ _ (One-Wire.lemma-M₋₁^2 (₁₊ n))

    lemma-CX↑-M₋₁↑ : CX ↑ • (M₋₁ ↑ • CX ↑) ≈ M₋₁ ↑
    lemma-CX↑-M₋₁↑ = •-cancelˡ {g = M₋₁ ↑} (begin
      M₋₁ ↑ • (CX ↑ • (M₋₁ ↑ • CX ↑))
        ≈⟨ sym assoc ⟩
      (M₋₁ ↑ • CX ↑) • (M₋₁ ↑ • CX ↑)
        ≈⟨ cong ₕ|ₕ↑-CX ₕ|ₕ↑-CX ⟩
      ₕ|ₕ ↑ • ₕ|ₕ ↑
        ≈⟨ lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n) ⟩
      ε
        ≈⟨ sym M₋₁↑-invol ⟩
      M₋₁ ↑ • M₋₁ ↑ ∎)

  -- Conjugating CZ by the upper half-swap gives the inverse of CZ • CZ02.
  -- Stated inverse-free, that is this.
  lemma-c14-key : CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑))) ≈ ε
  lemma-c14-key = begin
    CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑)))
      ≈⟨ cright cright cong (sym ₕ|ₕ↑-CX) (cright sym ₕ|ₕ↑-CX) ⟩
    CZ • (CZ02 • ((M₋₁ ↑ • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑))))
      -- explicit assoc, not by-assoc: M₋₁'s symbolic power blocks to-list
      ≈⟨ cright sym assoc ⟩
    CZ • ((CZ02 • (M₋₁ ↑ • CX ↑)) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cleft sym assoc ⟩
    CZ • (((CZ02 • M₋₁ ↑) • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cleft cleft sym lemma-M₋₁↑-CZ02 ⟩
    CZ • (((M₋₁ ↑ • CZ02) • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cleft assoc ⟩
    CZ • ((M₋₁ ↑ • (CZ02 • CX ↑)) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright assoc ⟩
    CZ • (M₋₁ ↑ • ((CZ02 • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑))))
      ≈⟨ cright cright sym assoc ⟩
    CZ • (M₋₁ ↑ • (((CZ02 • CX ↑) • CZ) • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cright cleft assoc ⟩
    CZ • (M₋₁ ↑ • ((CZ02 • (CX ↑ • CZ)) • (M₋₁ ↑ • CX ↑)))
      -- the axiom, right to left
      ≈⟨ cright cright cleft sym (axiom semi-CX↑-CZ↓) ⟩
    CZ • (M₋₁ ↑ • ((CZ • CX ↑) • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cright assoc ⟩
    CZ • (M₋₁ ↑ • (CZ • (CX ↑ • (M₋₁ ↑ • CX ↑))))
      ≈⟨ cright cright cright lemma-CX↑-M₋₁↑ ⟩
    CZ • (M₋₁ ↑ • (CZ • M₋₁ ↑))
      ≈⟨ cright sym assoc ⟩
    CZ • ((M₋₁ ↑ • CZ) • M₋₁ ↑)
      ≈⟨ cright cleft lemma-M₋₁↑-CZ ⟩
    CZ • ((CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑) • M₋₁ ↑)
      ≈⟨ cright assoc ⟩
    CZ • (CZ ^ toℕ (-'₁ .proj₁) • (M₋₁ ↑ • M₋₁ ↑))
      ≈⟨ cright cright M₋₁↑-invol ⟩
    CZ • (CZ ^ toℕ (-'₁ .proj₁) • ε)
      ≈⟨ cright right-unit ⟩
    CZ • CZ ^ toℕ (-'₁ .proj₁)
      ≈⟨ lemma-CZ-CZ₋₁ ⟩
    ε ∎

  lemma-⊤⊥↑-CZ : ⊤⊥ {n} ↑ • CZ ≈ CZ02 • ⊤⊥ {n} ↑
  lemma-⊤⊥↑-CZ = begin
    ⊤⊥ {n} ↑ • CZ
      ≈⟨ sym right-unit ⟩
    (⊤⊥ {n} ↑ • CZ) • ε
      ≈⟨ cright sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊥⊤-⊤⊥ n)) ⟩
    (⊤⊥ {n} ↑ • CZ) • (⊥⊤ {n} ↑ • ⊤⊥ {n} ↑)
      ≈⟨ by-assoc auto ⟩
    (⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑)) • ⊤⊥ {n} ↑
      ≈⟨ cleft lemma-c13-left ⟩
    CZ02 • ⊤⊥ {n} ↑ ∎

  ------------------------------------------------------------------------
  -- c14
  --
  -- Write A for ⊤⊥ ↑.  Conjugation by A sends CZ to CZ02 (that is c13,
  -- as lemma-⊤⊥↑-CZ) and CZ02 to the inverse of CZ • CZ02 (that is
  -- lemma-c14-key).  A has order 3, so cubing A • CZ telescopes: pushing
  -- the three A's rightwards leaves CZ02 • (CZ • CZ02)⁻¹ • CZ, which is ε.
  --
  -- The inverses are real words here — CZ ⁻¹ is CZ ^ p-1 — so this section
  -- uses explicit assoc throughout, to-list being stuck on them.

  private
    CZ⁻ : Word (Gen (₃₊ n))
    CZ⁻ = CZ ^ p-1

    lemma-CZ-CZ⁻ : CZ • CZ⁻ ≈ ε
    lemma-CZ-CZ⁻ = begin
      CZ • CZ ^ p-1       ≈⟨ sym (^-+ CZ 1 p-1) ⟩
      CZ ^ (1 Nat.+ p-1)  ≈⟨ axiom order-CZ ⟩
      ε ∎

    lemma-CZ⁻-CZ : CZ⁻ • CZ ≈ ε
    lemma-CZ⁻-CZ = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ (1 Nat.+ p-1)  ≈⟨ axiom order-CZ ⟩
      ε ∎

    -- lemma-c14-key with one half-swap cancelled off the right.
    key' : CZ • (CZ02 • (ₕ|ₕ ↑ • CZ)) ≈ ₕ|ₕ ↑
    key' = •-cancelʳ {h = ₕ|ₕ ↑} (begin
      (CZ • (CZ02 • (ₕ|ₕ ↑ • CZ))) • ₕ|ₕ ↑
        ≈⟨ assoc ⟩
      CZ • ((CZ02 • (ₕ|ₕ ↑ • CZ)) • ₕ|ₕ ↑)
        ≈⟨ cright assoc ⟩
      CZ • (CZ02 • ((ₕ|ₕ ↑ • CZ) • ₕ|ₕ ↑))
        ≈⟨ cright cright assoc ⟩
      CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑)))
        ≈⟨ lemma-c14-key ⟩
      ε
        ≈⟨ sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)) ⟩
      ₕ|ₕ ↑ • ₕ|ₕ ↑ ∎)

    -- Ex ↑ carries CZ02 to CZ, since CZ02 is Ex ↑ • CZ • Ex ↑.
    ex↑-CZ02 : Ex ↑ • CZ02 ≈ CZ • Ex ↑
    ex↑-CZ02 = begin
      Ex ↑ • CZ02
        ≈⟨ cright sym lemma-CZ02' ⟩
      Ex ↑ • (Ex ↑ • (CZ • Ex ↑))
        ≈⟨ sym assoc ⟩
      (Ex ↑ • Ex ↑) • (CZ • Ex ↑)
        ≈⟨ cleft lemma-Ex↑-Ex↑ ⟩
      ε • (CZ • Ex ↑)
        ≈⟨ left-unit ⟩
      CZ • Ex ↑ ∎

    ⊤⊥↑-split : ⊤⊥ {n} ↑ ≈ ₕ|ₕ ↑ • Ex ↑
    ⊤⊥↑-split = lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-simple n)

  -- Conjugation by ⊤⊥ ↑ sends CZ02 to the inverse of CZ • CZ02.
  lemma-⊤⊥↑-CZ02 : CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02)) ≈ ⊤⊥ {n} ↑
  lemma-⊤⊥↑-CZ02 = begin
    CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02))
      ≈⟨ cright cright cleft ⊤⊥↑-split ⟩
    CZ • (CZ02 • ((ₕ|ₕ ↑ • Ex ↑) • CZ02))
      ≈⟨ cright cright assoc ⟩
    CZ • (CZ02 • (ₕ|ₕ ↑ • (Ex ↑ • CZ02)))
      ≈⟨ cright cright cright ex↑-CZ02 ⟩
    CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • Ex ↑)))
      ≈⟨ cright cright sym assoc ⟩
    CZ • (CZ02 • ((ₕ|ₕ ↑ • CZ) • Ex ↑))
      ≈⟨ cright sym assoc ⟩
    CZ • ((CZ02 • (ₕ|ₕ ↑ • CZ)) • Ex ↑)
      ≈⟨ sym assoc ⟩
    (CZ • (CZ02 • (ₕ|ₕ ↑ • CZ))) • Ex ↑
      ≈⟨ cleft key' ⟩
    ₕ|ₕ ↑ • Ex ↑
      ≈⟨ sym ⊤⊥↑-split ⟩
    ⊤⊥ {n} ↑ ∎

  private
    -- The three ways ⊤⊥ ↑ moves across the two CZs and their inverses.
    A·CZ02 : ⊤⊥ {n} ↑ • CZ02 ≈ (CZ02⁻ • CZ⁻) • ⊤⊥ {n} ↑
    A·CZ02 = begin
      ⊤⊥ {n} ↑ • CZ02
        ≈⟨ sym left-unit ⟩
      ε • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft sym lemma-CZ02⁻-CZ02 ⟩
      (CZ02⁻ • CZ02) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft cright sym left-unit ⟩
      (CZ02⁻ • (ε • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft cright cleft sym lemma-CZ⁻-CZ ⟩
      (CZ02⁻ • ((CZ⁻ • CZ) • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft cright assoc ⟩
      (CZ02⁻ • (CZ⁻ • (CZ • CZ02))) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft sym assoc ⟩
      ((CZ02⁻ • CZ⁻) • (CZ • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ assoc ⟩
      (CZ02⁻ • CZ⁻) • ((CZ • CZ02) • (⊤⊥ {n} ↑ • CZ02))
        ≈⟨ cright assoc ⟩
      (CZ02⁻ • CZ⁻) • (CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02)))
        ≈⟨ cright lemma-⊤⊥↑-CZ02 ⟩
      (CZ02⁻ • CZ⁻) • ⊤⊥ {n} ↑ ∎

    -- Right-multiplying lemma-⊤⊥↑-CZ02 by CZ02 ⁻¹.
    A·CZ02⁻ : ⊤⊥ {n} ↑ • CZ02⁻ ≈ (CZ • CZ02) • ⊤⊥ {n} ↑
    A·CZ02⁻ = begin
      ⊤⊥ {n} ↑ • CZ02⁻
        ≈⟨ cleft sym lemma-⊤⊥↑-CZ02 ⟩
      (CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02))) • CZ02⁻
        ≈⟨ assoc ⟩
      CZ • ((CZ02 • (⊤⊥ {n} ↑ • CZ02)) • CZ02⁻)
        ≈⟨ cright assoc ⟩
      CZ • (CZ02 • ((⊤⊥ {n} ↑ • CZ02) • CZ02⁻))
        ≈⟨ cright cright assoc ⟩
      CZ • (CZ02 • (⊤⊥ {n} ↑ • (CZ02 • CZ02⁻)))
        ≈⟨ cright cright cright lemma-CZ02-CZ02⁻ ⟩
      CZ • (CZ02 • (⊤⊥ {n} ↑ • ε))
        ≈⟨ cright cright right-unit ⟩
      CZ • (CZ02 • ⊤⊥ {n} ↑)
        ≈⟨ sym assoc ⟩
      (CZ • CZ02) • ⊤⊥ {n} ↑ ∎

    -- c13 iterated: A moves across CZ ⁻¹ turning it into CZ02 ⁻¹.
    A·CZ⁻ : ⊤⊥ {n} ↑ • CZ⁻ ≈ CZ02⁻ • ⊤⊥ {n} ↑
    A·CZ⁻ = lemma-Induction lemma-⊤⊥↑-CZ p-1

    tb : Word (Gen (₃₊ n))
    tb = ⊤⊥ {n} ↑

    tb³ : (tb • tb) • tb ≈ ε
    tb³ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-cube3 n)

    -- The collapse.  Each A meeting a CZ02 on its right emits
    -- CZ02 ⁻¹ • CZ ⁻¹ and moves past it; the emitted factors cancel
    -- against the CZ02 and CZ already standing to the left, and after
    -- three such moves only the cube of A is left.
    cube-collapse : (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb)) ≈ ε
    cube-collapse = begin
      (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb))
        ≈⟨ assoc ⟩
      CZ02 • (tb • ((CZ02 • tb) • (CZ02 • tb)))
        ≈⟨ cright sym assoc ⟩
      CZ02 • ((tb • (CZ02 • tb)) • (CZ02 • tb))
        ≈⟨ cright cleft sym assoc ⟩
      CZ02 • (((tb • CZ02) • tb) • (CZ02 • tb))
        ≈⟨ cright cleft cleft A·CZ02 ⟩
      CZ02 • ((((CZ02⁻ • CZ⁻) • tb) • tb) • (CZ02 • tb))
        ≈⟨ cright cleft assoc ⟩
      CZ02 • (((CZ02⁻ • CZ⁻) • (tb • tb)) • (CZ02 • tb))
        ≈⟨ cright assoc ⟩
      CZ02 • ((CZ02⁻ • CZ⁻) • ((tb • tb) • (CZ02 • tb)))
        ≈⟨ cright assoc ⟩
      CZ02 • (CZ02⁻ • (CZ⁻ • ((tb • tb) • (CZ02 • tb))))
        ≈⟨ sym assoc ⟩
      (CZ02 • CZ02⁻) • (CZ⁻ • ((tb • tb) • (CZ02 • tb)))
        ≈⟨ cleft lemma-CZ02-CZ02⁻ ⟩
      ε • (CZ⁻ • ((tb • tb) • (CZ02 • tb)))
        ≈⟨ left-unit ⟩
      CZ⁻ • ((tb • tb) • (CZ02 • tb))
        ≈⟨ cright assoc ⟩
      CZ⁻ • (tb • (tb • (CZ02 • tb)))
        ≈⟨ cright cright sym assoc ⟩
      CZ⁻ • (tb • ((tb • CZ02) • tb))
        ≈⟨ cright cright cleft A·CZ02 ⟩
      CZ⁻ • (tb • (((CZ02⁻ • CZ⁻) • tb) • tb))
        ≈⟨ cright cright cleft assoc ⟩
      CZ⁻ • (tb • ((CZ02⁻ • (CZ⁻ • tb)) • tb))
        ≈⟨ cright cright assoc ⟩
      CZ⁻ • (tb • (CZ02⁻ • ((CZ⁻ • tb) • tb)))
        ≈⟨ cright sym assoc ⟩
      CZ⁻ • ((tb • CZ02⁻) • ((CZ⁻ • tb) • tb))
        ≈⟨ cright cleft A·CZ02⁻ ⟩
      CZ⁻ • (((CZ • CZ02) • tb) • ((CZ⁻ • tb) • tb))
        ≈⟨ cright assoc ⟩
      CZ⁻ • ((CZ • CZ02) • (tb • ((CZ⁻ • tb) • tb)))
        ≈⟨ cright assoc ⟩
      CZ⁻ • (CZ • (CZ02 • (tb • ((CZ⁻ • tb) • tb))))
        ≈⟨ sym assoc ⟩
      (CZ⁻ • CZ) • (CZ02 • (tb • ((CZ⁻ • tb) • tb)))
        ≈⟨ cleft lemma-CZ⁻-CZ ⟩
      ε • (CZ02 • (tb • ((CZ⁻ • tb) • tb)))
        ≈⟨ left-unit ⟩
      CZ02 • (tb • ((CZ⁻ • tb) • tb))
        ≈⟨ cright cright assoc ⟩
      CZ02 • (tb • (CZ⁻ • (tb • tb)))
        ≈⟨ cright sym assoc ⟩
      CZ02 • ((tb • CZ⁻) • (tb • tb))
        ≈⟨ cright cleft A·CZ⁻ ⟩
      CZ02 • ((CZ02⁻ • tb) • (tb • tb))
        ≈⟨ cright assoc ⟩
      CZ02 • (CZ02⁻ • (tb • (tb • tb)))
        ≈⟨ sym assoc ⟩
      (CZ02 • CZ02⁻) • (tb • (tb • tb))
        ≈⟨ cleft lemma-CZ02-CZ02⁻ ⟩
      ε • (tb • (tb • tb))
        ≈⟨ left-unit ⟩
      tb • (tb • tb)
        ≈⟨ sym assoc ⟩
      (tb • tb) • tb
        ≈⟨ tb³ ⟩
      ε ∎

  lemma-selinger-c14 : (⊤⊥ {n} ↑ • CZ ↓) ^ 3 ≈ ε
  lemma-selinger-c14 = begin
    (tb • CZ) • ((tb • CZ) • (tb • CZ))
      ≈⟨ cong lemma-⊤⊥↑-CZ (cong lemma-⊤⊥↑-CZ lemma-⊤⊥↑-CZ) ⟩
    (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb))
      ≈⟨ cube-collapse ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- c15, by transporting c14 along the transposition of wires 0 and 2
  --
  -- T = Ex • Ex ↑ • Ex exchanges wires 0 and 2 and fixes wire 1.  So it
  -- fixes H ↑, exchanges CZ with CZ ↑ (lemma-T-CZ) and exchanges the two
  -- swaps, hence carries ⊤⊥ ↑ to ⊥⊤ — which turns c14's element into
  -- c15's.  Since T is an involution, conjugating a cube is the cube of
  -- the conjugate, so c15 is c14 read through T.

  private
    -- Conjugation by T merges: it is a homomorphism, T • T being ε.
    merge : ∀ {X Y} → (T • (X • T)) • (T • (Y • T)) ≈ T • ((X • Y) • T)
    merge {X} {Y} = begin
      (T • (X • T)) • (T • (Y • T))
        ≈⟨ assoc ⟩
      T • ((X • T) • (T • (Y • T)))
        ≈⟨ cright assoc ⟩
      T • (X • (T • (T • (Y • T))))
        ≈⟨ cright cright sym assoc ⟩
      T • (X • ((T • T) • (Y • T)))
        ≈⟨ cright cright cleft lemma-T-T ⟩
      T • (X • (ε • (Y • T)))
        ≈⟨ cright cright left-unit ⟩
      T • (X • (Y • T))
        ≈⟨ cright sym assoc ⟩
      T • ((X • Y) • T) ∎

    -- T fixes wire 1, so it commutes with H ↑.
    lemma-T-H↑ : T • H ↑ ≈ H ↑ • T
    lemma-T-H↑ = begin
      (Ex • Ex ↑ • Ex) • H ↑
        ≈⟨ by-assoc auto ⟩
      Ex • (Ex ↑ • (Ex • H ↑))
        ≈⟨ cright cright lemma-Ex-H↑ ⟩
      Ex • (Ex ↑ • (H • Ex))
        ≈⟨ cright sym assoc ⟩
      Ex • ((Ex ↑ • H) • Ex)
        ≈⟨ cright cleft sym (lemma-comm-H-w↑ Ex) ⟩
      Ex • ((H • Ex ↑) • Ex)
        ≈⟨ by-assoc auto ⟩
      (Ex • H) • (Ex ↑ • Ex)
        ≈⟨ cleft lemma-Ex-H ⟩
      (H ↑ • Ex) • (Ex ↑ • Ex)
        ≈⟨ by-assoc auto ⟩
      H ↑ • (Ex • Ex ↑ • Ex) ∎

    lemma-T-CZ↑ : T • (CZ ↑ • T) ≈ CZ
    lemma-T-CZ↑ = begin
      T • (CZ ↑ • T)
        ≈⟨ cright cleft sym lemma-T-CZ ⟩
      T • ((T • (CZ • T)) • T)
        ≈⟨ cright assoc ⟩
      T • (T • ((CZ • T) • T))
        ≈⟨ sym assoc ⟩
      (T • T) • ((CZ • T) • T)
        ≈⟨ cleft lemma-T-T ⟩
      ε • ((CZ • T) • T)
        ≈⟨ left-unit ⟩
      (CZ • T) • T
        ≈⟨ assoc ⟩
      CZ • (T • T)
        ≈⟨ cright lemma-T-T ⟩
      CZ • ε
        ≈⟨ right-unit ⟩
      CZ ∎

    -- yang-baxter gives the other spelling of T, and the two swaps then
    -- cancel in pairs.
    lemma-T-Ex↑ : T • (Ex ↑ • T) ≈ Ex
    lemma-T-Ex↑ = begin
      T • (Ex ↑ • T)
        ≈⟨ cleft sym (axiom yang-baxter) ⟩
      (Ex ↑ • Ex ↓ • Ex ↑) • (Ex ↑ • T)
        ≈⟨ by-assoc auto ⟩
      Ex ↑ • (Ex • ((Ex ↑ • Ex ↑) • T))
        ≈⟨ cright cright cleft lemma-Ex↑-Ex↑ ⟩
      Ex ↑ • (Ex • (ε • T))
        ≈⟨ cright cright left-unit ⟩
      Ex ↑ • (Ex • T)
        ≈⟨ by-assoc auto ⟩
      Ex ↑ • ((Ex • Ex) • (Ex ↑ • Ex))
        ≈⟨ cright cleft lemma-Ex-Ex ⟩
      Ex ↑ • (ε • (Ex ↑ • Ex))
        ≈⟨ cright left-unit ⟩
      Ex ↑ • (Ex ↑ • Ex)
        ≈⟨ sym assoc ⟩
      (Ex ↑ • Ex ↑) • Ex
        ≈⟨ cleft lemma-Ex↑-Ex↑ ⟩
      ε • Ex
        ≈⟨ left-unit ⟩
      Ex ∎

    lemma-T-ₕ|ₕ↑ : T • ((H ↑ • CZ ↑ • H ↑) • T) ≈ ʰ|ʰ
    lemma-T-ₕ|ₕ↑ = begin
      T • ((H ↑ • CZ ↑ • H ↑) • T)
        ≈⟨ cright cleft sym assoc ⟩
      T • (((H ↑ • CZ ↑) • H ↑) • T)
        ≈⟨ cright assoc ⟩
      T • ((H ↑ • CZ ↑) • (H ↑ • T))
        ≈⟨ cright cright sym lemma-T-H↑ ⟩
      T • ((H ↑ • CZ ↑) • (T • H ↑))
        ≈⟨ cright assoc ⟩
      T • (H ↑ • (CZ ↑ • (T • H ↑)))
        ≈⟨ sym assoc ⟩
      (T • H ↑) • (CZ ↑ • (T • H ↑))
        ≈⟨ cleft lemma-T-H↑ ⟩
      (H ↑ • T) • (CZ ↑ • (T • H ↑))
        ≈⟨ assoc ⟩
      H ↑ • (T • (CZ ↑ • (T • H ↑)))
        ≈⟨ cright cright sym assoc ⟩
      H ↑ • (T • ((CZ ↑ • T) • H ↑))
        ≈⟨ cright sym assoc ⟩
      H ↑ • ((T • (CZ ↑ • T)) • H ↑)
        ≈⟨ cright cleft lemma-T-CZ↑ ⟩
      H ↑ • (CZ • H ↑) ∎

    lemma-T-⊤⊥↑ : T • (⊤⊥ {n} ↑ • T) ≈ ⊥⊤
    lemma-T-⊤⊥↑ = begin
      T • (⊤⊥ {n} ↑ • T)
        ≈⟨ cright cleft ⊤⊥↑-split ⟩
      T • ((ₕ|ₕ ↑ • Ex ↑) • T)
        ≈⟨ sym merge ⟩
      (T • (ₕ|ₕ ↑ • T)) • (T • (Ex ↑ • T))
        ≈⟨ cong lemma-T-ₕ|ₕ↑ lemma-T-Ex↑ ⟩
      ʰ|ʰ • Ex
        ≈⟨ cleft sym lemma-ʰ|ʰ-conj ⟩
      (Ex • (ₕ|ₕ • Ex)) • Ex
        ≈⟨ assoc ⟩
      Ex • ((ₕ|ₕ • Ex) • Ex)
        ≈⟨ cright assoc ⟩
      Ex • (ₕ|ₕ • (Ex • Ex))
        ≈⟨ cright cright lemma-Ex-Ex ⟩
      Ex • (ₕ|ₕ • ε)
        ≈⟨ cright right-unit ⟩
      Ex • ₕ|ₕ
        ≈⟨ sym lemma-⊥⊤-simple ⟩
      ⊥⊤ ∎

  lemma-selinger-c15 : (⊥⊤ ↓ • CZ ↑) ^ 3 ≈ ε
  lemma-selinger-c15 = begin
    (⊥⊤ • CZ ↑) • ((⊥⊤ • CZ ↑) • (⊥⊤ • CZ ↑))
      ≈⟨ cong conj (cong conj conj) ⟩
    (T • ((tb • CZ) • T)) • ((T • ((tb • CZ) • T)) • (T • ((tb • CZ) • T)))
      ≈⟨ cright merge ⟩
    (T • ((tb • CZ) • T)) • (T • (((tb • CZ) • (tb • CZ)) • T))
      ≈⟨ merge ⟩
    T • (((tb • CZ) • ((tb • CZ) • (tb • CZ))) • T)
      ≈⟨ cright cleft lemma-selinger-c14 ⟩
    T • (ε • T)
      ≈⟨ cright left-unit ⟩
    T • T
      ≈⟨ lemma-T-T ⟩
    ε ∎
    where
    conj : ⊥⊤ • CZ ↑ ≈ T • ((tb • CZ) • T)
    conj = begin
      ⊥⊤ • CZ ↑
        ≈⟨ cong (sym lemma-T-⊤⊥↑) (sym lemma-T-CZ) ⟩
      (T • (tb • T)) • (T • (CZ • T))
        ≈⟨ merge ⟩
      T • ((tb • CZ) • T) ∎

  lemma-⊥⊤↑-CZ02 : ⊥⊤ {n} ↑ • CZ02 ≈ CZ • ⊥⊤ {n} ↑
  lemma-⊥⊤↑-CZ02 = •-cancelˡ {g = ⊤⊥ {n} ↑} (begin
    ⊤⊥ {n} ↑ • (⊥⊤ {n} ↑ • CZ02)
      ≈⟨ sym assoc ⟩
    (⊤⊥ {n} ↑ • ⊥⊤ {n} ↑) • CZ02
      ≈⟨ cleft (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-⊥⊤ n)) ⟩
    ε • CZ02
      ≈⟨ left-unit ⟩
    CZ02
      ≈⟨ sym right-unit ⟩
    CZ02 • ε
      ≈⟨ cright sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-⊥⊤ n)) ⟩
    CZ02 • (⊤⊥ {n} ↑ • ⊥⊤ {n} ↑)
      ≈⟨ sym assoc ⟩
    (CZ02 • ⊤⊥ {n} ↑) • ⊥⊤ {n} ↑
      ≈⟨ cleft sym lemma-⊤⊥↑-CZ ⟩
    (⊤⊥ {n} ↑ • CZ) • ⊥⊤ {n} ↑
      ≈⟨ assoc ⟩
    ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑) ∎)
