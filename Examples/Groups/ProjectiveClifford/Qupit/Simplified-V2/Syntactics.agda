{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- A *simplified* relation set for the qudit Clifford group mod scalars,
-- an analogue of `Examples.Groups.Symplectic.Simplified.Syntactics`
-- for `Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics`.
--
-- Simplification strategy (applied per relation):
--   (1) push the X and Z (Pauli) parts of both sides to the right-most
--       position and cancel them as far as possible;
--   (2) use only the basic gates S, H, CZ as much as possible
--       (in particular, prefer S over R = S · Z^½);
--   (3) keep the original structure as much as possible.
--
-- The generators and all the derived words (X, Z, R, M, Mg, …) are
-- inherited unchanged from Simplified-V1; only the *relation
-- set* `_QRel,_===_` is redefined.
--
-- NOTE: this file states the proposed simplified presentation only.
-- Proving it equivalent to `Clifford-Relations._QRel,_===_` (an
-- isomorphism `id`, in the style of `Iso3`) is the next step.
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Product using (_,_ ; proj₁ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)

import Circuit.Base
open import Data.Nat.Primality

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import Notations


module Examples.Groups.ProjectiveClifford.Qupit.Simplified-V2.Syntactics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open Primitive-Root-Modp' g* g-gen

-- Inherit the generators (S, H, CZ, ↥) and every derived word
-- (X, Z, X⁻¹, Z⁻¹, S⁻¹, Z^, X^, R, R^, M, M₋₁, Mg, Mg^, ⊤⊥, ⊥⊤, …)
-- from the original Clifford presentation.
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen
-- The axiom names below used to be constructors on both sides, and Agda
-- lets constructor names overload.  Since Clifford-Relations moved onto
-- Circuit.Base.Lift-Relation its axioms are pattern synonyms, which do
-- not overload, so each shared name has to be hidden explicitly — the
-- same list Simplified-Lemmas/Part3 already carries.
open Clifford-Relations hiding
  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-MR ; order-SH ; comm-HHSHHS
  ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15 ; comm-H ; comm-S ; comm-CZ ; cong↑ ; lemma-cong↑
  ; srel ; comm₁ ; comm₂ ; module Base )


module Simplified-Relations where

  -- The bare S,H multiplier of Mg = M g′ and the leftover Pauli exponent
  -- ½(g-1), used only to state the simplified semi-MR relation.  Kept
  -- `private` so they don't collide with the local copies in Mg-Simplify /
  -- Mg-Simplify-S (they are definitionally equal to those, so the iso still
  -- lines up).
  private
    Wg : ∀ {n} -> Word (Gen (₁₊ n))
    Wg = S ^ toℕ (g* .proj₁) • H • S ^ toℕ ((g* ⁻¹) .proj₁) • H • S ^ toℕ (g* .proj₁) • H

    zX : ℕ
    zX = toℕ ((g* .proj₁ + (- 1ₚ)) * 1/2)

  -- Group-specific axioms only.  cong↑ and the gate commutations are
  -- the same for every circuit presentation and come from
  -- Circuit.Base.Lift-Relation below.
  module Base where
    infix 4 _SRel,_===_
    data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

      ----------------------------------------------------------------
      -- (A) Single-qudit symplectic layer — already in basic S, H.
      --     No X/Z present: kept verbatim.
      ----------------------------------------------------------------
      order-S :       ∀ {n} → (₁₊ n) SRel,  S ^ p === ε
      order-SH :      ∀ {n} → (₁₊ n) SRel,  (S • H) ^ 3 === ε
      comm-HHSHHS :   ∀ {n} → (₁₊ n) SRel,  H • H • S • H • H • S === S • H • H • S • H • H

      ----------------------------------------------------------------
      -- (B) Metaplectic layer.
      --     order-H / M-power pin down the "diagonal" subgroup; kept verbatim.
      --
      --     All three semi-M relations are stated in their *simplified* form: the
      --     metaplectic Mg = M g′ is replaced by its bare S,H multiplier
      --     Wg = S^g·H·S^(g⁻¹)·H·S^g·H, with Mg's own Pauli pushed out and
      --     cancelled.  semi-MR is further reduced to its fully-collected form,
      --     using the basic S (not R = S·Z^½) and a single Z^(g-1) tail (the
      --     left-over Z^½ has been cross-cancelled):
      --
      --     All three now carry their Pauli at the right-most position:
      --
      --        semi-MR   :  Wg  · S  = S^(g²) · Wg  · Z^(g-1)
      --        semi-M↑CZ :  Wg↑ · CZ = CZ^g  · Wg↑ · Z↓^(½(g-1))
      --        semi-M↓CZ :  Wg  · CZ = CZ^g  · Wg  · Z↑^(½(g-1))
      --
      --     The S-form semi-MR is the `final-semi-MR` theorem of
      --     Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.SemiM; the CZ ones are the `final-semi-M*CZ`
      --     theorems (all soundness, in the original Clifford presentation).
      --     The original Mg-forms are recovered as the `completeness-semi-M*`
      --     lemmas of Examples.Groups.ProjectiveClifford.Qupit.Simplified-V2.SemiM (the S-form is first turned back
      --     into the R-form by `SemiS-rev.lemma-semi-MR`).
      --
      --     The completeness proofs of the two CZ relations need Z↔CZ
      --     commutation, which is NOT a consequence of selinger + Pauli (it would
      --     otherwise loop back through the metaplectic relations).  We therefore
      --     add Z↔CZ as the explicit Pauli-layer axioms comm-Z-CZ / comm-Z↑-CZ
      --     (see (C) below) — both hold in the Clifford presentation as theorems,
      --     so the two presentations remain isomorphic.
      ----------------------------------------------------------------
      order-H :       ∀ {n} → (₁₊ n) SRel,  H ^ 2 === M₋₁
      M-power : ∀ {n} (k : ℤ ₚ) → (₁₊ n) SRel,  Mg^ k === M (g^ k)
      semi-MR :       ∀ {n} → (₁₊ n) SRel,  Wg • S === S ^ toℕ (g * g) • Wg • Z ^ toℕ (g + (- 1ₚ))
      semi-M↑CZ :     ∀ {n} → (₂₊ n) SRel,  Wg ↑ • CZ === CZ^ g • Wg ↑ • (Z ↓) ^ zX
      semi-M↓CZ :     ∀ {n} → (₂₊ n) SRel,  Wg • CZ === CZ^ g • Wg • (Z ↑) ^ zX

      ----------------------------------------------------------------
      -- (C) Pauli layer — the canonical transport rules for X, Z.
      --     X and Z are already at the right-most positions, nothing
      --     to cancel: these *define* the Pauli action, kept verbatim.
      --
      --     comm-Z-CZ / comm-Z↑-CZ ("CZ is diagonal": it commutes with the
      --     Z Paulis on both qudits) are NEW axioms.  They are theorems in the
      --     original Clifford presentation (proved there via the metaplectic
      --     relations), but in the Simplified presentation they cannot be
      --     re-derived from selinger + Pauli alone, and they are exactly what is
      --     needed to break the circularity in the semi-M↑CZ / semi-M↓CZ
      --     completeness proofs.  One per qudit: neither follows from the other.
      ----------------------------------------------------------------
      comm-X-Z :      ∀ {n} → (₁₊ n) SRel,  X • Z === Z • X
      rel-X↑-CZ :     ∀ {n} → (₂₊ n) SRel,  CZ • X ↑ === X ↑ • Z ↓ • CZ
      rel-X↓-CZ :     ∀ {n} → (₂₊ n) SRel,  CZ • X ↓ === X ↓ • Z ↑ • CZ
      comm-Z-CZ :     ∀ {n} → (₂₊ n) SRel,  Z • CZ === CZ • Z
      comm-Z↑-CZ :    ∀ {n} → (₂₊ n) SRel,  Z ↑ • CZ === CZ • Z ↑

      ----------------------------------------------------------------
      -- (D) CZ layer (no X/Z): kept verbatim.
      ----------------------------------------------------------------
      order-CZ :      ∀ {n} → (₂₊ n) SRel,  CZ ^ p === ε
      comm-CZ-S↓ :    ∀ {n} → (₂₊ n) SRel,  CZ • S ↓ === S ↓ • CZ
      comm-CZ-S↑ :    ∀ {n} → (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ

      ----------------------------------------------------------------
      -- (E) The two "selinger" CZ–H–CZ relations: this is where the
      --     strategy actually changes something.
      --
      --     Original (Clifford-Relations), using R = S · Z^½ :
      --        CZ • H↑ • CZ
      --          === R↑⁻¹ • H↑ • R↑⁻¹ • CZ • H↑ • R↑⁻¹ • R↓⁻¹
      --
      --     Replace every R⁻¹ by the basic S⁻¹ (= R⁻¹ · Z^½), push the
      --     resulting Z-halves to the right and cancel.  The symplectic
      --     part is exactly the `Examples.Groups.Symplectic.Simplified.Syntactics` relation; the
      --     leftover Pauli collapses to a single tail X↑ · Z↑ (the Z↓
      --     halves cancel).  Result (basic gates, Pauli right-most):
      --
      --        CZ • H↑ • CZ • X↑ • Z↑
      --          === S⁻¹↑ • H↑ • S⁻¹↑ • CZ • H↑ • S⁻¹↑ • S⁻¹↓
      --
      --     (and ↑↔↓ for c11, with tail X↓ · Z↓).
      --
      --     [proposed; the Pauli tail still needs to be verified.]
      ----------------------------------------------------------------
      selinger-c10 :  ∀ {n} → (₂₊ n) SRel,
        CZ • H ↑ • CZ • X ↑ • Z ↑ === S ↑ ^ p-1 • H ↑ • S ↑ ^ p-1 • CZ • H ↑ • S ↑ ^ p-1 • S ↓ ^ p-1
      selinger-c11 :  ∀ {n} → (₂₊ n) SRel,
        CZ • H ↓ • CZ • X ↓ • Z ↓ === S ↓ ^ p-1 • H ↓ • S ↓ ^ p-1 • CZ • H ↓ • S ↓ ^ p-1 • S ↑ ^ p-1

      ----------------------------------------------------------------
      -- (F) Three-qudit selinger relations (no X/Z): kept verbatim.
      ----------------------------------------------------------------
      selinger-c12 :  ∀ {n} → (₃₊ n) SRel,  CZ ↑ • CZ === CZ • CZ ↑
      selinger-c13 :  ∀ {n} → (₃₊ n) SRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
      selinger-c14 :  ∀ {n} → (₃₊ n) SRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
      selinger-c15 :  ∀ {n} → (₃₊ n) SRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

  -- Full relation: the axioms above plus the structural rules.
  private module SC = Circuit.Base SympGate
  private module LR = SC.Lift-Relation Base._SRel,_===_

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → WRel (Gen n)
  _QRel,_===_ = LR._VRel,_===_

  open LR public using (srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑)

  -- Pattern synonyms, so the axiom names keep working in both
  -- expression and pattern position.
  pattern order-S      = srel Base.order-S
  pattern order-SH     = srel Base.order-SH
  pattern comm-HHSHHS  = srel Base.comm-HHSHHS
  pattern order-H      = srel Base.order-H
  pattern M-power      k = srel (Base.M-power k)
  pattern semi-MR      = srel Base.semi-MR
  pattern semi-M↑CZ    = srel Base.semi-M↑CZ
  pattern semi-M↓CZ    = srel Base.semi-M↓CZ
  pattern comm-X-Z     = srel Base.comm-X-Z
  pattern rel-X↑-CZ    = srel Base.rel-X↑-CZ
  pattern rel-X↓-CZ    = srel Base.rel-X↓-CZ
  pattern comm-Z-CZ    = srel Base.comm-Z-CZ
  pattern comm-Z↑-CZ   = srel Base.comm-Z↑-CZ
  pattern order-CZ     = srel Base.order-CZ
  pattern comm-CZ-S↓   = srel Base.comm-CZ-S↓
  pattern comm-CZ-S↑   = srel Base.comm-CZ-S↑
  pattern selinger-c10 = srel Base.selinger-c10
  pattern selinger-c11 = srel Base.selinger-c11
  pattern selinger-c12 = srel Base.selinger-c12
  pattern selinger-c13 = srel Base.selinger-c13
  pattern selinger-c14 = srel Base.selinger-c14
  pattern selinger-c15 = srel Base.selinger-c15

  -- Definitions, not synonyms: as a synonym the implicit x is a meta
  -- the goal need not determine.  Pattern-position uses match comm₁/comm₂.
  comm-H : ∀ {n} {x : Gen (₁₊ n)} → (₂₊ n) QRel, [ x ↥ ]ʷ • H === H • [ x ↥ ]ʷ
  comm-H {x = x} = comm₁ H-gate x

  comm-S : ∀ {n} {x : Gen (₁₊ n)} → (₂₊ n) QRel, [ x ↥ ]ʷ • S === S • [ x ↥ ]ʷ
  comm-S {x = x} = comm₁ S-gate x

  comm-CZ : ∀ {n} {x : Gen (₁₊ n)} → (₃₊ n) QRel, [ x ↥ ↥ ]ʷ • CZ === CZ • [ x ↥ ↥ ]ʷ
  comm-CZ {x = x} = comm₂ CZ-gate x
