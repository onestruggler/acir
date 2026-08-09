------------------------------------------------------------------------
-- Presentations of groups
--
-- fwd-tw: the twisted symplectic relators of the Clifford extension
-- presentation hold among the derived Figure-8 words.
--
-- The extension presentation of Qubit.Presentation carries, for each
-- axiom r̄ of the simplified symplectic rule set, the twisted relation
--
--     [ u ]ᵣ  =  [ corr r̄ ]ₗ • [ v ]ᵣ       (RelTwist.tw r̄),
--
-- where corr r̄ is the Pauli correction picked up on lifting r̄ to
-- Clifford.  Translating with f turns it into a plain equation between
-- gate words, which this module derives in Figure 8 mod scalars.
--
-- At p = 2 the multiplicative group ℤ*₂ is trivial, so every M-generator
-- degenerates to the scalar M₋₁ = Mg = (SH)³, which C4 sets to ε.  That
-- one fact discharges order-H, M-power, semi-MS and semi-M↑CZ /
-- semi-M↓CZ.  The remaining axioms are their Figure-8 namesakes:
--
--   order-S     — the one relator with a correction: S² = Z;
--   order-CZ    — C5;    comm-CZ-S↓ / comm-CZ-S↑ — C6 / C7;
--   selinger-c10 / c11 — C10 / C11 after one use of C7 / C6;
--   selinger-c12 … c15 — C12 … C15, verbatim;
--   cong↑ / comm₁ / comm₂ — the structural rules, shared by both
--                           rule sets through Circuit.Base.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Relators where

open import Data.Nat using (ℕ ; zero)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ ; wmap)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; S ; H ; CZ ; _↑ ; _↓)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; SH ; _CRel,_===_ ; srel ; comm₁ ; comm₂ ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; Z₀ ; corr ; shiftPauli)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations
  using ( _QRel,_===_ ; M₋₁
        ; order-S ; order-H ; M-power ; semi-MS ; semi-M↑CZ ; semi-M↓CZ
        ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑
        ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13
        ; selinger-c14 ; selinger-c15)
  renaming (srel to ssrel ; cong↑ to scong↑ ; comm₁ to scomm₁ ; comm₂ to scomm₂)

open import Examples.Groups.Clifford.Qubit.Selinger.Translation
  using (f ; pauliGen→word ; Pw ; fₗ≡Pw ; Z-gen)
open import Examples.Groups.Clifford.Qubit.Selinger.PauliVec using (P-Z ; Z₀≡)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Two translation laws

-- (f ʷ) is the identity on right-embedded gate words.
fᵣ≡id : (w : Word (Gen n)) → (f ʷ) [ w ]ᵣ ≡ w
fᵣ≡id [ x ]ʷ  = Eq.refl
fᵣ≡id ε       = Eq.refl
fᵣ≡id (u • v) rewrite fᵣ≡id u | fᵣ≡id v = Eq.refl

-- Shifting a Pauli correction up one qubit shifts its translation.
Pw-shift : (w : Word (PauliGen n)) → Pw (shiftPauli w) ≡ (Pw w ↑)
Pw-shift {zero}  [ () ]ʷ
Pw-shift {₁₊ k} [ y ]ʷ = Eq.refl
Pw-shift ε             = Eq.refl
Pw-shift (u • v)       = Eq.cong₂ _•_ (Pw-shift u) (Pw-shift v)

------------------------------------------------------------------------
-- The scalar
--
-- At p = 2 every M-generator is M₋₁ = SHSHSH, which C4 kills.  Hence the
-- scalar drops out of the relators that only say it is central.

module Scalar (m : ℕ) where

  private Γ = (₁₊ m) CRel,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  -- M₋₁ = (SH)³ = ε.
  M≈ε : M₋₁ {m} ≈ ε
  M≈ε = trans (by-assoc auto) (axiom (srel MS.c4))

  -- order-S is the one relator with a correction: S² = Z.
  orderS : (S ^ 2) ≈ (Pw (Z₀ {m}) • ε)
  orderS =
    sym (trans right-unit
          (trans (refl' (Eq.cong Pw (Z₀≡ {m}))) (refl' (P-Z {m}))))

  -- order-H reads H² = M₋₁, and both sides are ε.
  orderH : (H ^ 2) ≈ (ε • M₋₁ {m})
  orderH = trans (axiom (srel MS.c2)) (sym (trans left-unit M≈ε))

  -- M-power at the two exponents of ℤ₂.
  mpow₀ : ε ≈ (ε • M₋₁ {m})
  mpow₀ = sym (trans left-unit M≈ε)

  mpow₁ : M₋₁ {m} ≈ (ε • M₋₁ {m})
  mpow₁ = sym left-unit

  -- The scalar is central, and trivially so.
  central : (a : Word (Gen (₁₊ m))) → (M₋₁ {m} • a) ≈ (ε • (a • M₋₁ {m}))
  central a =
    trans (cleft M≈ε)
      (trans left-unit
        (sym (trans left-unit (trans (cright M≈ε) right-unit))))

-- The same, one wire up: semi-M↑CZ multiplies by the shifted scalar.
module Scalar↑ (m : ℕ) where

  private Γ = (₂₊ m) CRel,_===_
  open PB Γ

  M↑≈ε : (M₋₁ {m} ↑) ≈ ε
  M↑≈ε = lemma-cong↑ _ _ (Scalar.M≈ε m)

  central↑ : (a : Word (Gen (₂₊ m))) →
             ((M₋₁ {m} ↑) • a) ≈ (ε • (a • (M₋₁ {m} ↑)))
  central↑ a =
    trans (cleft M↑≈ε)
      (trans left-unit
        (sym (trans left-unit (trans (cright M↑≈ε) right-unit))))

------------------------------------------------------------------------
-- The two-qubit Selinger relators
--
-- C10 and C11 of the simplified rule set differ from their Figure-8
-- namesakes by one transposition of CZ with S on the untouched wire.

module Sel (m : ℕ) where

  private Γ = (₂₊ m) CRel,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  c10 : (CZ • H ↑ • CZ) ≈ (ε • (S ↑ • H ↑ • S ↑ • CZ • H ↑ • S ↑ • S))
  c10 = begin
    CZ • H ↑ • CZ
      ≈⟨ axiom (srel MS.c10) ⟩
    SH ↑ • CZ • (S • H • S) ↑ • S
      ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑) • ((CZ • S ↑) • (H ↑ • S ↑ • S))
      ≈⟨ cright (cleft (sym (axiom (srel MS.c7)))) ⟩
    (S ↑ • H ↑) • ((S ↑ • CZ) • (H ↑ • S ↑ • S))
      ≈⟨ by-assoc auto ⟩
    S ↑ • H ↑ • S ↑ • CZ • H ↑ • S ↑ • S
      ≈⟨ sym left-unit ⟩
    ε • (S ↑ • H ↑ • S ↑ • CZ • H ↑ • S ↑ • S)
      ∎

  c11 : (CZ • H • CZ) ≈ (ε • (S • H • S • CZ • H • S • S ↑))
  c11 = begin
    CZ • H • CZ
      ≈⟨ axiom (srel MS.c11) ⟩
    SH • CZ • (S • H • S) • S ↑
      ≈⟨ by-assoc auto ⟩
    (S • H) • ((CZ • S) • (H • S • S ↑))
      ≈⟨ cright (cleft (sym (axiom (srel MS.c6)))) ⟩
    (S • H) • ((S • CZ) • (H • S • S ↑))
      ≈⟨ by-assoc auto ⟩
    S • H • S • CZ • H • S • S ↑
      ≈⟨ sym left-unit ⟩
    ε • (S • H • S • CZ • H • S • S ↑)
      ∎

------------------------------------------------------------------------
-- The twisted relators, translated

tw-word : {u v : Word (Gen n)} (r̄ : (n QRel,_===_) u v) →
          PB._≈_ (n CRel,_===_) u (Pw (corr r̄) • v)

tw-word (ssrel order-S)       = Scalar.orderS _
tw-word (ssrel order-H)       = Scalar.orderH _
tw-word (ssrel (M-power ₀))   = Scalar.mpow₀ _
tw-word (ssrel (M-power ₁))   = Scalar.mpow₁ _
tw-word (ssrel semi-MS)       = Scalar.central _ _
tw-word (ssrel semi-M↑CZ)     = Scalar↑.central↑ _ _
tw-word (ssrel semi-M↓CZ)     = Scalar.central _ _
tw-word (ssrel order-CZ)      =
  PB.trans (PB.axiom (srel MS.c5)) (PB.sym PB.left-unit)
tw-word (ssrel comm-CZ-S↓)    =
  PB.trans (PB.sym (PB.axiom (srel MS.c6))) (PB.sym PB.left-unit)
tw-word (ssrel comm-CZ-S↑)    =
  PB.trans (PB.sym (PB.axiom (srel MS.c7))) (PB.sym PB.left-unit)
tw-word (ssrel selinger-c10)  = Sel.c10 _
tw-word (ssrel selinger-c11)  = Sel.c11 _
tw-word (ssrel selinger-c12)  =
  PB.trans (PB.axiom (srel MS.c12)) (PB.sym PB.left-unit)
tw-word (ssrel selinger-c13)  =
  PB.trans (PB.axiom (srel MS.c13)) (PB.sym PB.left-unit)
tw-word (ssrel selinger-c14)  =
  PB.trans (PB.axiom (srel MS.c14)) (PB.sym PB.left-unit)
tw-word (ssrel selinger-c15)  =
  PB.trans (PB.axiom (srel MS.c15)) (PB.sym PB.left-unit)
tw-word {₁₊ k} (scong↑ {w = u} {v = v} r) =
  Eq.subst (λ □ → PB._≈_ ((₁₊ k) CRel,_===_) (u ↑) (□ • (v ↑)))
           (Eq.sym (Pw-shift (corr r))) (lemma-cong↑ _ _ (tw-word r))
tw-word (scomm₁ h g)          =
  PB.trans (PB.axiom (comm₁ h g)) (PB.sym PB.left-unit)
tw-word (scomm₂ h g)          =
  PB.trans (PB.axiom (comm₂ h g)) (PB.sym PB.left-unit)

------------------------------------------------------------------------
-- fwd-tw, in the shape Qubit.Selinger.Iso's F-WD asks for

fwd-tw : {u v : Word (Gen n)} (r̄ : (n QRel,_===_) u v) →
         PB._≈_ (n CRel,_===_)
                ((f ʷ) [ u ]ᵣ) ((f ʷ) ([ corr r̄ ]ₗ • [ v ]ᵣ))
fwd-tw {n} {u} {v} r̄ =
  Eq.subst₂ (PB._≈_ (n CRel,_===_))
            (Eq.sym (fᵣ≡id u))
            (Eq.sym (Eq.cong₂ _•_ (fₗ≡Pw (corr r̄)) (fᵣ≡id v)))
            (tw-word r̄)
