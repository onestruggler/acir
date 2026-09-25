------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic steps of Equations (278)–(280), one width down
--
-- The paper takes them by Lemma 5.1.  Here each is an equality of
-- semantics at width 3 + k, decided by the controlled forms of CForm
-- with the payload on the wires 0, 1, 2; completeness at that width
-- (GeneralN.ZXPass's parameter) turns it into an equation, and the
-- derivation at width 4 + k uses it one wire up, or placed on the
-- wires other than 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.SemZX where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals

------------------------------------------------------------------------
-- The gates one width down

-- The box on wire 1 with a control on wire 0; the H gate it makes
-- between P ⊗ P on the wires 0 1 (H on wire 0, box on wire 1); and the
-- H gate with H on wire 1 and box on wire 0.
B₁₀ HG₀₁ HG′ : ∀ k → Circuit (₃₊ k)
B₁₀ k  = Ex-conj (Λ□ (₂₊ k))
HG₀₁ k = PP ↓ • B₁₀ k • PP ↓
HG′ k  = PP ↓ • Λ□ (₂₊ k) • PP ↓

-- The multi-controlled ZX and XZ on wire 1, controlled by the wires 2 ….
ZX₁ XZ₁ : ∀ k → Circuit (₃₊ k)
ZX₁ k = ΛZX (₁₊ k) ↑
XZ₁ k = ΛXZ (₁₊ k) ↑

------------------------------------------------------------------------
-- Their forms, with the payload on the wires 0 1 2

module Forms (k : ℕ) where

  ex : CF {3} {k} Ex
  ex = cf-loc′ Ex Ex₀₁ᴸ Ex₀₁ᴸ-def

  ch : CF {3} {k} CH
  ch = cf-loc′ CH CH₀₁ᴸ CH₀₁ᴸ-def

  cz : CF {3} {k} CZ
  cz = cf-loc′ CZ CZ₀₁ᴸ CZ₀₁ᴸ-def

  pp : CF {3} {k} PP
  pp = cf-loc′ PP PP₀₁ᴸ PP₀₁ᴸ-def

  hc : CF {3} {k} HC
  hc = cf-• ex (cf-• ch ex)

  box : CF {3} {k} (Λ□ (₂₊ k))
  box = cf-box 2 k

  b₁₀ : CF {3} {k} (B₁₀ k)
  b₁₀ = cf-• ex (cf-• box ex)

  hg₀₁ : CF {3} {k} (HG₀₁ k)
  hg₀₁ = cf-• pp (cf-• b₁₀ pp)

  hg′ : CF {3} {k} (HG′ k)
  hg′ = cf-• pp (cf-• box pp)

  -- The multi-controlled ZX and XZ on two fewer wires, with the payload
  -- on the wires 0 1, one wire up.
  private
    ex₂ : CF {2} {k} Ex
    ex₂ = cf-loc Ex
    ch₂ : CF {2} {k} CH
    ch₂ = cf-loc CH
    el₂ : CF {2} {k} (Ex-conj (Λ□ (₁₊ k)))
    el₂ = cf-• ex₂ (cf-• (cf-box 1 k) ex₂)

  zx₁ : CF {3} {k} (ZX₁ k)
  zx₁ = cf-↑ (cf-• ch₂ (cf-• el₂ (cf-• ch₂ el₂)))

  xz₁ : CF {3} {k} (XZ₁ k)
  xz₁ = cf-↑ (cf-• el₂ (cf-• ch₂ (cf-• el₂ ch₂)))

  -- The multi-controlled ZX on wire 0, controlled by the wires 1 ….
  zx₀ : CF {3} {k} (ΛZX (₂₊ k))
  zx₀ = cf-• ch (cf-• b₁₀ (cf-• ch b₁₀))

  eps : CF {3} {k} ε
  eps = cf-loc ε

------------------------------------------------------------------------
-- The steps

module _ (k : ℕ) where
  open Forms k

  -- (278), the step (317) makes: ZX and XZ are inverse.
  sem-317 : ⟦ ZX₁ k • XZ₁ k ⟧ ~ ⟦ ε ⟧
  sem-317 = cf-~ (cf-• zx₁ xz₁) eps Eq.refl Eq.refl

  -- (278), the first step by Lemma 5.1: the CZ from the box's control
  -- onto its box wire is the box's control conjugated by ZX and XZ.
  sem-a : ⟦ CZ • B₁₀ k ⟧ ~ ⟦ ZX₁ k • CZ • XZ₁ k ⟧
  sem-a = cf-~ (cf-• cz b₁₀) (cf-• zx₁ (cf-• cz xz₁)) Eq.refl Eq.refl

  -- The second: XZ and ZX around the CH from their target make the CH
  -- and the H gate.
  sem-b : ⟦ XZ₁ k • CH • ZX₁ k ⟧ ~ ⟦ CH • HG₀₁ k ⟧
  sem-b = cf-~ (cf-• xz₁ (cf-• ch zx₁)) (cf-• ch hg₀₁) Eq.refl Eq.refl

  -- The third: XZ on the box wire of the H gate passes it.
  sem-c : ⟦ HG₀₁ k • XZ₁ k ⟧ ~ ⟦ XZ₁ k • HG₀₁ k ⟧
  sem-c = cf-~ (cf-• hg₀₁ xz₁) (cf-• xz₁ hg₀₁) Eq.refl Eq.refl

  -- The last: what is left is the ZX on wire 0.
  sem-d : ⟦ CH • CZ • ZX₁ k • CZ • CH • XZ₁ k • HG₀₁ k • B₁₀ k ⟧ ~ ⟦ ΛZX (₂₊ k) ⟧
  sem-d = cf-~ (cf-• ch (cf-• cz (cf-• zx₁ (cf-• cz (cf-• ch (cf-• xz₁ (cf-• hg₀₁ b₁₀)))))))
               zx₀ Eq.refl Eq.refl

  -- The step with wire 2 idle: the CH and CZ from wire 1 onto wire 0
  -- pass the H gate on wire 0 with its box and the box.
  sem-e : ⟦ (HC • CZ) • HG′ k • Λ□ (₂₊ k) ⟧ ~ ⟦ HG′ k • Λ□ (₂₊ k) • (HC • CZ) ⟧
  sem-e = cf-~ (cf-• (cf-• hc cz) (cf-• hg′ box)) (cf-• hg′ (cf-• box (cf-• hc cz))) Eq.refl Eq.refl

  -- (355) one width down: the box is the square of the ZX.
  sem-355 : ⟦ Λ□ (₂₊ k) ⟧ ~ ⟦ ΛZX (₂₊ k) • ΛZX (₂₊ k) ⟧
  sem-355 = cf-~ box (cf-• zx₀ zx₀) Eq.refl Eq.refl
