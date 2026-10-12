{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Paper-V0's rules, from Paper-V1's.
--
-- Paper-V1 is Paper-V0 with the multiplier respelled, from the R-word
-- RHR x x⁻¹ to the S-word SHS' x⁻¹ x.  Over any relation with Paper-V1's
-- four one-wire rules other than semi-MR, the bridge between the two
-- spellings (XZ.One-Wire-Group.XM-bridge) turns each Paper-V1 rule that
-- mentions the multiplier into its Paper-V0 form, and the rules that do
-- not mention it are the same words in both.  So any such relation
-- supplies Paper-V0's rules, and with them the whole Paper-V0 calculus
-- of Paper-V0.Lemmas.
--
-- Two clients.  Paper-V1.Iso proves Paper-V0's axioms in Paper-V1 with
-- the one-rule facts below.  Reduced builds Paper-V0's rule records with
-- Records, and so gets the Paper-V0 calculus — and in it cz-slide and
-- yang-baxter, which Reduced does not have as rules — over its own
-- relation.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.V0Rules
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- Paper-V1's words, opened; Paper-V0's multiplier words, qualified.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen
open Clifford-Relations
  using (R ; R^ ; M ; XM ; M₋₁ ; XM₋₁ ; XMg ; XMg^)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as V0

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  p-3 p-prime g* g-gen as OWm
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  p-3 p-prime g* g-gen as XZm
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.TwoWire
  p-3 p-prime g* g-gen as TW0
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.ThreeWire
  p-3 p-prime g* g-gen as TH0

private
  module V0R = V0.Clifford-Relations

module V0-Rules
  (Γ : (n : ℕ) → WRel (Gen n))
  (order-S     : ∀ {n} → let open PB (Γ (₁₊ n)) in S ^ p ≈ ε)
  (order-H     : ∀ {n} → let open PB (Γ (₁₊ n)) in H ^ 2 ≈ XM₋₁)
  (M-power     : ∀ {n} → let open PB (Γ (₁₊ n)) in ∀ k → XMg^ k ≈ XM (g^ k))
  (comm-HHSHHS : ∀ {n} → let open PB (Γ (₁₊ n)) in
                 H • H • S • H • H • S ≈ S • H • H • S • H • H)
  (gl          : ∀ {n} → Grouplike (Γ n))
  (lemma-cong↑ : ∀ {n} (w v : Word (Gen n)) →
                 PB._≈_ (Γ n) w v → PB._≈_ (Γ (₁₊ n)) (w ↑) (v ↑))
  where

  private
    module O (n : ℕ) =
      OWm.One-Wire n (Γ (₁₊ n)) order-S order-H M-power comm-HHSHHS
    module G (n : ℕ) =
      XZm.One-Wire-Group n (Γ (₁₊ n)) order-S order-H M-power comm-HHSHHS
        (gl {₁₊ n})

  ------------------------------------------------------------------------
  -- The one-wire rules

  -- The bridge: Paper-V0's R-word for XM x is Paper-V1's S-word.
  XM-bridge : ∀ {n} (x : ℤ* ₚ) → PB._≈_ (Γ (₁₊ n)) (V0R.XM x) (XM x)
  XM-bridge {n} = G.XM-bridge n

  -- order-H is lemma-M₋₁-R: Paper-V0's M₋₁ *is* the R-word
  -- RHR (-1) (-1), once both exponents are identified with p-1 (the
  -- first by lemma-toℕ-1ₚ, the second because -1 is its own inverse).
  v0-order-H : ∀ {n} → PB._≈_ (Γ (₁₊ n)) (H ^ 2) V0R.M₋₁
  v0-order-H {n} = PB.trans (PB.sym (G.lemma-M₋₁-R n)) (PB.refl' _ eqn)
    where
    eqn : R ^ p-1 • (H • (R ^ p-1 • (H • (R ^ p-1 • H)))) ≡ V0R.M₋₁
    eqn = Eq.sym
      (Eq.cong₂ (λ a b → R ^ a • (H • (R ^ b • (H • (R ^ a • H)))))
         lemma-toℕ-1ₚ
         (Eq.trans (Eq.cong toℕ aux-₁⁻¹) lemma-toℕ-1ₚ))

  -- M-power, with XMg rewritten across the bridge on both sides.
  v0-M-power : ∀ {n} k → PB._≈_ (Γ (₁₊ n)) (V0R.XMg^ k) (V0R.XM (g^ k))
  v0-M-power {n} k =
    trans (^-cong _ _ (toℕ k) (XM-bridge g′))
      (trans (M-power k) (sym (XM-bridge (g^ k))))
    where
    open PB (Γ (₁₊ n))
    open PP (Γ (₁₊ n)) using (^-cong)

  -- order-SH: under the S-spelling M₁ is the word (S • H) ^ 3, so it is
  -- M-power at k = 0 (OneWire.lemma-order-SH).
  v0-order-SH : ∀ {n} → PB._≈_ (Γ (₁₊ n)) ((S • H) ^ 3) ε
  v0-order-SH {n} = O.lemma-order-SH n

  -- semi-MR, from its R-spelling over Paper-V1's multiplier word.
  v0-semi-MR : ∀ {n} → let open PB (Γ (₁₊ n)) in
               XMg • R^ (g * g) ≈ R • XMg →
               V0R.XMg • V0R.R^ (g * g) ≈ V0R.R • V0R.XMg
  v0-semi-MR {n} r = trans (cleft XM-bridge g′) (trans r (cright sym (XM-bridge g′)))
    where open PB (Γ (₁₊ n))

  ------------------------------------------------------------------------
  -- The two-wire rule that mentions the multiplier

  v0-semi-M↑CZ : ∀ {n} → let open PB (Γ (₂₊ n)) in
                 XMg ↑ • CZ^ g ≈ CZ • XMg ↑ →
                 V0R.XMg ↑ • CZ^ g ≈ CZ • V0R.XMg ↑
  v0-semi-M↑CZ {n} r = trans (cleft bridge↑) (trans r (cright sym bridge↑))
    where
    open PB (Γ (₂₊ n))
    bridge↑ = lemma-cong↑ _ _ (XM-bridge {n} g′)

  ------------------------------------------------------------------------
  -- Paper-V0's rule records
  --
  -- Every other rule Paper-V0's calculus takes is the same word in both
  -- spellings, so it is passed through as it stands.

  module Records
    (order-CZ     : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ ^ p ≈ ε)
    (order-Ex     : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex ^ 2 ≈ ε)
    (comm-CZ-S↑   : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ • S ↑ ≈ S ↑ • CZ)
    (semi-M↑CZ    : ∀ {n} → let open PB (Γ (₂₊ n)) in
                    XMg ↑ • CZ^ g ≈ CZ • XMg ↑)
    (semi-Ex-S↑   : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex • S ↑ ≈ S ↓ • Ex)
    (semi-Ex-H↑   : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex • H ↑ ≈ H ↓ • Ex)
    (blake-c12    : ∀ {n} → let open PB (Γ (₂₊ n)) in
                    (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ≈ CZ)
    (semi-CX↑-CZ↓ : ∀ {n} → let open PB (Γ (₃₊ n)) in
                    CZ ↓ • CX ↑ ≈ CZ02 • CX ↑ • CZ ↓)
    (comm₁        : ∀ {n} (h : SympGate 1) (x : Gen (₁₊ n)) →
                    let open PB (Γ (₂₊ n)) in
                    [ x ↥ ]ʷ • [ gate₁ h ]ʷ ≈ [ gate₁ h ]ʷ • [ x ↥ ]ʷ)
    (comm₂        : ∀ {n} (h : SympGate 2) (x : Gen (₁₊ n)) →
                    let open PB (Γ (₃₊ n)) in
                    [ x ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ≈ [ gate₂ h ]ʷ • [ x ↥ ↥ ]ʷ)
    where

    two-wire-rules : TW0.Two-Wire-Rules Γ
    two-wire-rules = record
      { order-S     = order-S
      ; order-H     = v0-order-H
      ; M-power     = v0-M-power
      ; comm-HHSHHS = comm-HHSHHS
      ; order-CZ    = order-CZ
      ; order-Ex    = order-Ex
      ; comm-CZ-S↑  = comm-CZ-S↑
      ; semi-M↑CZ   = v0-semi-M↑CZ semi-M↑CZ
      ; semi-Ex-S↑  = semi-Ex-S↑
      ; semi-Ex-H↑  = semi-Ex-H↑
      ; blake-c12   = blake-c12
      ; comm₁       = comm₁
      ; lemma-cong↑ = lemma-cong↑
      }

    three-wire-rules : TH0.Three-Wire-Rules Γ
    three-wire-rules = record
      { two-wire     = two-wire-rules
      ; semi-CX↑-CZ↓ = semi-CX↑-CZ↓
      ; comm₂        = comm₂
      }
