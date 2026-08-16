------------------------------------------------------------------------
-- Presentations of groups
--
-- The sixteen Paper-V0 rules, as equations in ℤ/pℤ.
--
-- Clifford.Qupit.SemRealises reduces `Realises` — the last hypothesis of
-- Clifford.Qupit.Presentation — to `SRel-Φ`: for each of the sixteen
-- group-specific rules u === v, the phases satisfy
--
--     Φ u ≡ srel-corrℤ r + Φ v.
--
-- Ten of them are proved there (Rules₁, Rules₂, Rules₃); this file
-- supplies the other six and assembles the dispatcher.  Nothing is left
-- open afterwards.
--
--   * order-H, M-power, semi-MR — the multiplier rules.  All three are
--     written over R-powers and H, and R = S·Z^½ has NO Pauli, so
--     SemLocal's `Free` covers them without any phase being computed:
--     both sides are ₀.
--   * order-SH — the one rule that carries a correction.  SemLocal's
--     `has-SH3` computes its phase as -h·σ² = -⅛, and SemSHExp shows
--     that (p²-1)/8 is that same residue.
--   * blake-c12 — the only remaining two-wire rule.  It is not
--     Pauli-free (three S-blocks), but every Pauli in it is pure-Z and
--     pure-Z Paulis do not see each other, which is SemZBlock.
--   * order-S — SemRealises' own (Rules₁), listed here only because the
--     dispatcher has to name it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.SemSRel
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Fin using (fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (proj₁ ; proj₂)
import Relation.Binary.PropositionalEquality as Eq

open import Algebra.Properties.Ring (+-*-ring p-2) using ([-x][-y]≈xy)
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (mult ; mult-toℕ)

open import Word.Base using (ε ; _•_ ; _^_)

-- The primitive root, under the names the multiplier rules use.
open PrimeModulus' p-2 p-prime using ()
  renaming (module Primitive-Root-Modp' to PR)
open PR g* g-gen using (g′ ; g^_)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.SemRealises
  p-3 p-prime g* g-gen as RL
import Examples.Groups.Clifford.Qupit.SemLocal
  p-3 p-prime g* g-gen as SL
import Examples.Groups.Clifford.Qupit.SemZBlock
  p-3 p-prime g* g-gen as ZB
import Examples.Groups.Clifford.Qupit.SemFE p-3 p-prime g* g-gen as FE
import Examples.Groups.Clifford.Qupit.SemSHExp p-3 p-prime as SHE

------------------------------------------------------------------------
-- modp is mult
--
-- SemRealises transports a residue into words over ω through `modp`,
-- which reads a natural through `_% p`; SemSHExp computes with `mult`,
-- the k-fold sum of ₁.  They agree, mult being blind to multiples of p.

modp≡mult : ∀ k → RL.modp k ≡ mult k
modp≡mult k =
  Eq.trans (Eq.sym (mult-toℕ (RL.modp k)))
    (Eq.trans (Eq.cong mult (toℕ-fromℕ< (m%n<n k p)))
              (Eq.sym (SHE.mult-mod k)))

------------------------------------------------------------------------
-- The one-wire rules

module OneWire (n : ℕ) where

  open SL.Local n
  open RL.Width (₁₊ n) using (Φ ; Φ-ε)

  private
    -- Two phase-free sides satisfy an uncorrected rule's equation.
    free-both : ∀ {u v} → Free u → Free v → Φ u ≡ ₀ + Φ v
    free-both {u} {v} fu fv =
      Eq.trans (free-Φ fu)
        (Eq.sym (Eq.trans (Eq.cong (₀ +_) (free-Φ fv)) (+-identityʳ ₀)))

  ----------------------------------------------------------------------
  -- order-H, M-power, semi-MR
  --
  -- H is Pauli-free and so is every power of R, so the multiplier words
  -- M and XM are, and all three rules close without computation.

  order-H-Φ : Φ (Pap.H {n} ^ 2) ≡ ₀ + Φ (QS.CR.M₋₁ {n})
  order-H-Φ = free-both (free-^ free-H 2) (free-M -'₁)

  M-power-Φ : ∀ (k : ℤ ₚ) →
              Φ (QS.CR.XMg^ k {n}) ≡ ₀ + Φ (QS.CR.XM {n} (g^ k))
  M-power-Φ k = free-both (free-^ (free-XM g′) (toℕ k)) (free-XM (g^ k))

  semi-MR-Φ : Φ (QS.CR.XMg {n} • QS.CR.R^ {n} (g * g))
                ≡ ₀ + Φ (QS.CR.R {n} • QS.CR.XMg)
  semi-MR-Φ = free-both (free-• (free-XM g′) (free-R^ (g * g)))
                        (free-• free-R (free-XM g′))

  ----------------------------------------------------------------------
  -- order-SH
  --
  -- The one rule with a phase.  `has-SH3` gives it as -h·σ², σ being
  -- -h; `[-x][-y]≈xy` turns σ² into h², and SemSHExp identifies -h³
  -- with the residue of (p² - 1)/8.

  order-SH-Φ : Φ ((Pap.S {n} • Pap.H) ^ 3)
                 ≡ RL.modp QS.sh-exponent + Φ ε
  order-SH-Φ =
    Eq.trans (Has.phase has-SH3)
      (Eq.trans (Eq.cong (λ z → - (SL.h * z)) ([-x][-y]≈xy SL.h SL.h))
        (Eq.sym (Eq.trans (Eq.cong (RL.modp QS.sh-exponent +_) Φ-ε)
                  (Eq.trans (+-identityʳ (RL.modp QS.sh-exponent))
                    (Eq.trans (modp≡mult QS.sh-exponent) SHE.sh-value)))))

------------------------------------------------------------------------
-- blake-c12
--
-- Five blocks, each pure-Z, each phase-free; the products contribute
-- nothing because pure-Z Paulis have vanishing sform.

blake-block : ∀ (n : ℕ) →
  ZB.ZBlock ((Pap.S {n} ^ p-1) Pap.↑ • (Pap.S {₁₊ n} ^ p-1) Pap.↓
             • Pap.CX {n} ^ p-1 • Pap.S {₁₊ n} Pap.↓ • Pap.CX {n})
blake-block n =
  ZB.zb-• (ZB.zb-↑ (ZB.zb-^ ZB.zb-S p-1))
    (ZB.zb-• (ZB.zb-^ ZB.zb-S p-1)
      (ZB.zb-• (ZB.zb-^ ZB.zb-CX p-1)
        (ZB.zb-• ZB.zb-S ZB.zb-CX)))

blake-c12-Φ : ∀ (n : ℕ) →
  RL.Width.Φ (₂₊ n) ((Pap.S {n} ^ p-1) Pap.↑ • (Pap.S {₁₊ n} ^ p-1) Pap.↓
                     • Pap.CX {n} ^ p-1 • Pap.S {₁₊ n} Pap.↓ • Pap.CX {n})
    ≡ ₀ + RL.Width.Φ (₂₊ n) (Pap.CZ {n})
blake-c12-Φ n =
  Eq.trans (ZB.ZBlock.zphase (blake-block n))
    (Eq.sym (Eq.trans (Eq.cong (₀ +_) (RL.Width.Φ-gate (₂₊ n) _))
                      (+-identityʳ ₀)))

------------------------------------------------------------------------
-- The sixteen, dispatched
--
-- Ten come from SemRealises' own Rules₁ / Rules₂ / Rules₃, six from
-- above.  This is the whole of what `Realises` was reduced to.

srel-Φ : RL.SRel-Φ
srel-Φ (QS.CB.order-S {n})      = RL.Rules₁.order-S-Φ n
srel-Φ (QS.CB.order-H {n})      = OneWire.order-H-Φ n
srel-Φ (QS.CB.M-power {n} k)    = OneWire.M-power-Φ n k
srel-Φ (QS.CB.semi-MR {n})      = OneWire.semi-MR-Φ n
srel-Φ (QS.CB.order-SH {n})     = OneWire.order-SH-Φ n
srel-Φ (QS.CB.comm-HHSHHS {n})  = RL.Rules₁.comm-HHSHHS-Φ n
srel-Φ (QS.CB.order-CZ {n})     = RL.Rules₂.order-CZ-Φ n
srel-Φ (QS.CB.order-Ex {n})     = RL.Rules₂.order-Ex-Φ n
srel-Φ (QS.CB.comm-CZ-S↑ {n})   = RL.Rules₂.comm-CZ-S↑-Φ n
srel-Φ (QS.CB.semi-M↑CZ {n})    = RL.Rules₂.semi-M↑CZ-Φ n
srel-Φ (QS.CB.semi-Ex-S↑ {n})   = RL.Rules₂.semi-Ex-S↑-Φ n
srel-Φ (QS.CB.semi-Ex-H↑ {n})   = RL.Rules₂.semi-Ex-H↑-Φ n
srel-Φ (QS.CB.blake-c12 {n})    = blake-c12-Φ n
srel-Φ (QS.CB.yang-baxter {n})  = RL.Rules₃.yang-baxter-Φ n
srel-Φ (QS.CB.cz-slide {n})     = RL.Rules₃.cz-slide-Φ n
srel-Φ (QS.CB.semi-CX↑-CZ↓ {n}) = RL.Rules₃.semi-CX↑-CZ↓-Φ n

------------------------------------------------------------------------
-- ... hence Realises, unconditionally

realises : ∀ (n : ℕ) → RL.PE.Realises n (FE.generator-data n)
realises = RL.realises-srel srel-Φ
