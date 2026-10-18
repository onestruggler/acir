------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural CCX+H rules with the swap gate and the schema are sound
-- at every width.
--
-- A circuit is read through τH, which writes the swap gate as
-- Natural's swap word Ex = CX XC CX, in the ordinary circuit matrices
-- (`interpretH`).  Each rule and each law of the swap is derived in the
-- complete translated calculus of CCX+H.Presentation on its own wires
-- (the two sides having the same matrix, one boolean by by-eq√) and on
-- more wires by idle wires on top (Structural.cong⇓); the structural
-- rules are Structural's.  A schema instance θ w is, read through τH,
-- the expansion of the CCX+HH circuit τ w (`τH-θ`: they differ only in
-- the order of the two H of HH), whose matrix is that of τ w, the
-- identity by CCX+HH.NaturalP.SchemaSound.
--
-- The rule lemmas are written by NaturalP/gen/gen_nhsound.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Soundness where

open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_^_ to _^ℕ_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Quantum.Synthesis.Matrix using (Matrix)
import Presentation.Base as PB

import Examples.Groups.CCX+H.Syntactics as C
import Examples.Groups.CCX+H.Natural.Syntactics as N
import Examples.Groups.CCX+H.NaturalP.Syntactics as NH
open import Examples.Groups.CCX+H.NaturalP.Schema
open import Examples.Groups.CCX+H.NaturalP.Theta using (θg ; θ)
import Examples.Groups.CCX+H.Presentation as T
import Examples.Groups.CCX+H.Structural as St
open import Examples.Groups.CCX+HH.Decide using (by-eq√)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Schema using (CtrlCCX)
import Examples.Groups.CCX+HH.NaturalP.Bridge as PBr
import Examples.Groups.CCX+HH.NaturalP.SchemaSound as PSS
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as Emb
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R using (D)

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- The reading

τHg : Gen n → C.Circuit n
τHg (gate₀ ())
τHg (gate₁ X-gate)   = C.X
τHg (gate₁ H-gate)   = C.H
τHg (gate₂ CX-gate)  = C.CX
τHg (gate₂ SW-gate)  = N.Ex
τHg (gate₃ CCX-gate) = C.CCX
τHg (g ↥)            = τHg g C.↑

τH : Circuit n → C.Circuit n
τH [ g ]ʷ  = τHg g
τH ε       = ε
τH (u • v) = τH u • τH v

τH-↑ : (w : Circuit n) → τH (w ↑) ≡ τH w C.↑
τH-↑ [ g ]ʷ  = Eq.refl
τH-↑ ε       = Eq.refl
τH-↑ (u • v) = Eq.cong₂ _•_ (τH-↑ u) (τH-↑ v)

interpretH : Circuit n → Matrix (2 ^ℕ n) (2 ^ℕ n) D
interpretH w = T.interpret (τH w)

------------------------------------------------------------------------
-- Each rule on its own wires, in the translated calculus

private
  opaque
    unfolding S.actV S.set₁ S.set₂ R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

    X²₀ : 1 T.⊢ τH (X • X) ≈ τH (ε)
    X²₀ = T.complete 1 (by-eq√ tt)

    H²₀ : 1 T.⊢ τH (H • H) ≈ τH (ε)
    H²₀ = T.complete 1 (by-eq√ tt)

    CX²₀ : 2 T.⊢ τH (CX • CX) ≈ τH (ε)
    CX²₀ = T.complete 2 (by-eq√ tt)

    CCX²₀ : 3 T.⊢ τH (CCX • CCX) ≈ τH (ε)
    CCX²₀ = T.complete 3 (by-eq√ tt)

    XH⁸₀ : 1 T.⊢ τH (X • H • X • H • X • H • X • H • X • H • X • H • X • H • X • H) ≈ τH (ε)
    XH⁸₀ = T.complete 1 (by-eq√ tt)

    sw-def₀ : 2 T.⊢ τH (σ) ≈ τH (CX • XC • CX)
    sw-def₀ = T.complete 2 (by-eq√ tt)

    X-control₀ : 2 T.⊢ τH (X ↑ • CX • X ↑) ≈ τH (CX • X)
    X-control₀ = T.complete 2 (by-eq√ tt)

    X-controlᵣ₀ : 2 T.⊢ τH (XC • X • XC) ≈ τH (X • X ↑)
    X-controlᵣ₀ = T.complete 2 (by-eq√ tt)

    CNOT-S3₀ : 2 T.⊢ τH (CX • XC • CX • XC • CX • XC) ≈ τH (ε)
    CNOT-S3₀ = T.complete 2 (by-eq√ tt)

    X-Z₀ : 2 T.⊢ τH (X • HHw • X ↑ • HHw) ≈ τH (HHw • X ↑ • HHw • X)
    X-Z₀ = T.complete 2 (by-eq√ tt)

    CZ-XC₀ : 2 T.⊢ τH (CZ • XC • CZ • XC) ≈ τH (Z)
    CZ-XC₀ = T.complete 2 (by-eq√ tt)

    CCX-sym₀ : 3 T.⊢ τH (σ ↑ • CCX • σ ↑) ≈ τH (CCX)
    CCX-sym₀ = T.complete 3 (by-eq√ tt)

    CCX-neg₀ : 3 T.⊢ τH (X ↑ • CCX • X ↑) ≈ τH (CCX • σ ↑ • CX • σ ↑)
    CCX-neg₀ = T.complete 3 (by-eq√ tt)

    CCX-XC₀ : 3 T.⊢ τH (CCX • XC • CCX • XC) ≈ τH (σ • CCX • σ • CCX)
    CCX-XC₀ = T.complete 3 (by-eq√ tt)

    HH-swap₀₀ : 3 T.⊢ τH (σ • HHw ↑ • σ) ≈ τH (HHw • HHw ↑)
    HH-swap₀₀ = T.complete 3 (by-eq√ tt)

    HH-swap₁₀ : 3 T.⊢ τH (σ ↑ • HHw • σ ↑) ≈ τH (HHw • HHw ↑)
    HH-swap₁₀ = T.complete 3 (by-eq√ tt)

    CCX-HH₀ : 3 T.⊢ τH (CCX • XC • HHw • XC) ≈ τH (XC • HHw • XC • CCX)
    CCX-HH₀ = T.complete 3 (by-eq√ tt)

    CCX-comm₀ : 4 T.⊢ τH (CCX ↑ • CX • CCX ↑ • CX) ≈ τH (σ • CCX ↑ • σ)
    CCX-comm₀ = T.complete 4 (by-eq√ tt)

    σ-inv₀ : 2 T.⊢ τH (σ • σ) ≈ τH (ε)
    σ-inv₀ = T.complete 2 (by-eq√ tt)

    σ-natX₀ : 2 T.⊢ τH ([ gate₁ X-gate ]ʷ • σ[ 1 ]) ≈ τH (σ[ 1 ] • [ gate₁ X-gate ]ʷ ↑)
    σ-natX₀ = T.complete 2 (by-eq√ tt)

    σ-natH₀ : 2 T.⊢ τH ([ gate₁ H-gate ]ʷ • σ[ 1 ]) ≈ τH (σ[ 1 ] • [ gate₁ H-gate ]ʷ ↑)
    σ-natH₀ = T.complete 2 (by-eq√ tt)

    σ-natCX₀ : 3 T.⊢ τH ([ gate₂ CX-gate ]ʷ • σ[ 2 ]) ≈ τH (σ[ 2 ] • [ gate₂ CX-gate ]ʷ ↑)
    σ-natCX₀ = T.complete 3 (by-eq√ tt)

    σ-natSW₀ : 3 T.⊢ τH ([ gate₂ SW-gate ]ʷ • σ[ 2 ]) ≈ τH (σ[ 2 ] • [ gate₂ SW-gate ]ʷ ↑)
    σ-natSW₀ = T.complete 3 (by-eq√ tt)

    σ-natCCX₀ : 4 T.⊢ τH ([ gate₃ CCX-gate ]ʷ • σ[ 3 ]) ≈ τH (σ[ 3 ] • [ gate₃ CCX-gate ]ʷ ↑)
    σ-natCCX₀ = T.complete 4 (by-eq√ tt)

------------------------------------------------------------------------
-- On the bottom wires of any wider circuit

private
  X²ₙ : ∀ n → (₁₊ n) T.⊢ τH (X • X) ≈ τH (ε)
  X²ₙ zero    = X²₀
  X²ₙ (suc n) = St.cong⇓ (X²ₙ n)

  H²ₙ : ∀ n → (₁₊ n) T.⊢ τH (H • H) ≈ τH (ε)
  H²ₙ zero    = H²₀
  H²ₙ (suc n) = St.cong⇓ (H²ₙ n)

  CX²ₙ : ∀ n → (₂₊ n) T.⊢ τH (CX • CX) ≈ τH (ε)
  CX²ₙ zero    = CX²₀
  CX²ₙ (suc n) = St.cong⇓ (CX²ₙ n)

  CCX²ₙ : ∀ n → (₃₊ n) T.⊢ τH (CCX • CCX) ≈ τH (ε)
  CCX²ₙ zero    = CCX²₀
  CCX²ₙ (suc n) = St.cong⇓ (CCX²ₙ n)

  XH⁸ₙ : ∀ n → (₁₊ n) T.⊢ τH (X • H • X • H • X • H • X • H • X • H • X • H • X • H • X • H) ≈ τH (ε)
  XH⁸ₙ zero    = XH⁸₀
  XH⁸ₙ (suc n) = St.cong⇓ (XH⁸ₙ n)

  sw-defₙ : ∀ n → (₂₊ n) T.⊢ τH (σ) ≈ τH (CX • XC • CX)
  sw-defₙ zero    = sw-def₀
  sw-defₙ (suc n) = St.cong⇓ (sw-defₙ n)

  X-controlₙ : ∀ n → (₂₊ n) T.⊢ τH (X ↑ • CX • X ↑) ≈ τH (CX • X)
  X-controlₙ zero    = X-control₀
  X-controlₙ (suc n) = St.cong⇓ (X-controlₙ n)

  X-controlᵣₙ : ∀ n → (₂₊ n) T.⊢ τH (XC • X • XC) ≈ τH (X • X ↑)
  X-controlᵣₙ zero    = X-controlᵣ₀
  X-controlᵣₙ (suc n) = St.cong⇓ (X-controlᵣₙ n)

  CNOT-S3ₙ : ∀ n → (₂₊ n) T.⊢ τH (CX • XC • CX • XC • CX • XC) ≈ τH (ε)
  CNOT-S3ₙ zero    = CNOT-S3₀
  CNOT-S3ₙ (suc n) = St.cong⇓ (CNOT-S3ₙ n)

  X-Zₙ : ∀ n → (₂₊ n) T.⊢ τH (X • HHw • X ↑ • HHw) ≈ τH (HHw • X ↑ • HHw • X)
  X-Zₙ zero    = X-Z₀
  X-Zₙ (suc n) = St.cong⇓ (X-Zₙ n)

  CZ-XCₙ : ∀ n → (₂₊ n) T.⊢ τH (CZ • XC • CZ • XC) ≈ τH (Z)
  CZ-XCₙ zero    = CZ-XC₀
  CZ-XCₙ (suc n) = St.cong⇓ (CZ-XCₙ n)

  CCX-symₙ : ∀ n → (₃₊ n) T.⊢ τH (σ ↑ • CCX • σ ↑) ≈ τH (CCX)
  CCX-symₙ zero    = CCX-sym₀
  CCX-symₙ (suc n) = St.cong⇓ (CCX-symₙ n)

  CCX-negₙ : ∀ n → (₃₊ n) T.⊢ τH (X ↑ • CCX • X ↑) ≈ τH (CCX • σ ↑ • CX • σ ↑)
  CCX-negₙ zero    = CCX-neg₀
  CCX-negₙ (suc n) = St.cong⇓ (CCX-negₙ n)

  CCX-XCₙ : ∀ n → (₃₊ n) T.⊢ τH (CCX • XC • CCX • XC) ≈ τH (σ • CCX • σ • CCX)
  CCX-XCₙ zero    = CCX-XC₀
  CCX-XCₙ (suc n) = St.cong⇓ (CCX-XCₙ n)

  HH-swap₀ₙ : ∀ n → (₃₊ n) T.⊢ τH (σ • HHw ↑ • σ) ≈ τH (HHw • HHw ↑)
  HH-swap₀ₙ zero    = HH-swap₀₀
  HH-swap₀ₙ (suc n) = St.cong⇓ (HH-swap₀ₙ n)

  HH-swap₁ₙ : ∀ n → (₃₊ n) T.⊢ τH (σ ↑ • HHw • σ ↑) ≈ τH (HHw • HHw ↑)
  HH-swap₁ₙ zero    = HH-swap₁₀
  HH-swap₁ₙ (suc n) = St.cong⇓ (HH-swap₁ₙ n)

  CCX-HHₙ : ∀ n → (₃₊ n) T.⊢ τH (CCX • XC • HHw • XC) ≈ τH (XC • HHw • XC • CCX)
  CCX-HHₙ zero    = CCX-HH₀
  CCX-HHₙ (suc n) = St.cong⇓ (CCX-HHₙ n)

  CCX-commₙ : ∀ n → (₄₊ n) T.⊢ τH (CCX ↑ • CX • CCX ↑ • CX) ≈ τH (σ • CCX ↑ • σ)
  CCX-commₙ zero    = CCX-comm₀
  CCX-commₙ (suc n) = St.cong⇓ (CCX-commₙ n)

  σ-invₙ : ∀ n → (₂₊ n) T.⊢ τH (σ • σ) ≈ τH (ε)
  σ-invₙ zero    = σ-inv₀
  σ-invₙ (suc n) = St.cong⇓ (σ-invₙ n)

  σ-natXₙ : ∀ n → (₂₊ n) T.⊢ τH ([ gate₁ X-gate ]ʷ • σ[ 1 ]) ≈ τH (σ[ 1 ] • [ gate₁ X-gate ]ʷ ↑)
  σ-natXₙ zero    = σ-natX₀
  σ-natXₙ (suc n) = St.cong⇓ (σ-natXₙ n)

  σ-natHₙ : ∀ n → (₂₊ n) T.⊢ τH ([ gate₁ H-gate ]ʷ • σ[ 1 ]) ≈ τH (σ[ 1 ] • [ gate₁ H-gate ]ʷ ↑)
  σ-natHₙ zero    = σ-natH₀
  σ-natHₙ (suc n) = St.cong⇓ (σ-natHₙ n)

  σ-natCXₙ : ∀ n → (₃₊ n) T.⊢ τH ([ gate₂ CX-gate ]ʷ • σ[ 2 ]) ≈ τH (σ[ 2 ] • [ gate₂ CX-gate ]ʷ ↑)
  σ-natCXₙ zero    = σ-natCX₀
  σ-natCXₙ (suc n) = St.cong⇓ (σ-natCXₙ n)

  σ-natSWₙ : ∀ n → (₃₊ n) T.⊢ τH ([ gate₂ SW-gate ]ʷ • σ[ 2 ]) ≈ τH (σ[ 2 ] • [ gate₂ SW-gate ]ʷ ↑)
  σ-natSWₙ zero    = σ-natSW₀
  σ-natSWₙ (suc n) = St.cong⇓ (σ-natSWₙ n)

  σ-natCCXₙ : ∀ n → (₄₊ n) T.⊢ τH ([ gate₃ CCX-gate ]ʷ • σ[ 3 ]) ≈ τH (σ[ 3 ] • [ gate₃ CCX-gate ]ʷ ↑)
  σ-natCCXₙ zero    = σ-natCCX₀
  σ-natCCXₙ (suc n) = St.cong⇓ (σ-natCCXₙ n)

------------------------------------------------------------------------
-- The swap word passes a circuit two wires up

private
  pass : ∀ {w a b : C.Circuit n} → n T.⊢ w • a ≈ a • w → n T.⊢ w • b ≈ b • w →
         n T.⊢ w • (a • b) ≈ (a • b) • w
  pass wa wb = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong wa PB.refl)
    (PB.trans PB.assoc (PB.trans (PB.cong PB.refl wb) (PB.sym PB.assoc))))

  pass-Ex : (w : C.Circuit n) → (₂₊ n) T.⊢ w C.↑ C.↑ • N.Ex ≈ N.Ex • w C.↑ C.↑
  pass-Ex w = pass cx (pass (pass h (pass h↑ (pass cx (pass h↑ h)))) cx)
    where
    cx = St.comm₂ w C.CX-gate
    h  = St.comm₁ (w C.↑) C.H-gate
    h↑ = St.cong↑ (St.comm₁ w C.H-gate)

------------------------------------------------------------------------
-- θ, read through τH, is the expansion of HH

private
  hh : (₂₊ n) T.⊢ C.H • C.H C.↑ ≈ C.H C.↑ • C.H
  hh = PB.sym (St.comm₁ C.H C.H-gate)

  τH-θg : (g : P.Gen n) → n T.⊢ τH (θg g) ≈ Emb.embed (PBr.τg g)
  τH-θg (P.gate₀ ())
  τH-θg (P.gate₁ P.X-gate)   = PB.refl
  τH-θg (P.gate₂ P.CX-gate)  = PB.refl
  τH-θg (P.gate₂ P.HH-gate)  = hh
  τH-θg (P.gate₂ P.SW-gate)  = PB.cong PB.refl (PB.cong
    (PB.trans (PB.sym PB.assoc) (PB.cong hh PB.refl)) PB.refl)
  τH-θg (P.gate₃ P.CCX-gate) = PB.refl
  τH-θg (g P.↥) = Eq.subst₂ (T._⊢_≈_ _) (Eq.sym (τH-↑ (θg g)))
    (Eq.sym (Emb.embed-shift (PBr.τg g))) (St.cong↑ (τH-θg g))

τH-θ : (w : P.Circuit n) → n T.⊢ τH (θ w) ≈ Emb.embed (PBr.τ w)
τH-θ [ g ]ʷ  = τH-θg g
τH-θ ε       = PB.refl
τH-θ (u • v) = PB.cong (τH-θ u) (τH-θ v)

private
  schema : ∀ {w} → CtrlCCX k w → (₄₊ k) T.⊢ τH (θ w) ≈ ε
  schema {k = k} {w = w} c = PB.trans (τH-θ w)
    (T.complete (₄₊ k) {u = Emb.embed (PBr.τ w)} {v = ε}
      (Emb.preserve {u = PBr.τ w} {v = ε} (PSS.sch-sem c)))

------------------------------------------------------------------------
-- Every derivation is one of the translated calculus

axiom-T : ∀ {w v : Circuit n} → n VRel, w === v → n T.⊢ τH w ≈ τH v
axiom-T (srel (srel (nh (NH.X² {n})))) = X²ₙ n
axiom-T (srel (srel (nh (NH.H² {n})))) = H²ₙ n
axiom-T (srel (srel (nh (NH.CX² {n})))) = CX²ₙ n
axiom-T (srel (srel (nh (NH.CCX² {n})))) = CCX²ₙ n
axiom-T (srel (srel (nh (NH.XH⁸ {n})))) = XH⁸ₙ n
axiom-T (srel (srel (nh (NH.sw-def {n})))) = sw-defₙ n
axiom-T (srel (srel (nh (NH.X-control {n})))) = X-controlₙ n
axiom-T (srel (srel (nh (NH.X-controlᵣ {n})))) = X-controlᵣₙ n
axiom-T (srel (srel (nh (NH.CNOT-S3 {n})))) = CNOT-S3ₙ n
axiom-T (srel (srel (nh (NH.X-Z {n})))) = X-Zₙ n
axiom-T (srel (srel (nh (NH.CZ-XC {n})))) = CZ-XCₙ n
axiom-T (srel (srel (nh (NH.CCX-sym {n})))) = CCX-symₙ n
axiom-T (srel (srel (nh (NH.CCX-neg {n})))) = CCX-negₙ n
axiom-T (srel (srel (nh (NH.CCX-XC {n})))) = CCX-XCₙ n
axiom-T (srel (srel (nh (NH.HH-swap₀ {n})))) = HH-swap₀ₙ n
axiom-T (srel (srel (nh (NH.HH-swap₁ {n})))) = HH-swap₁ₙ n
axiom-T (srel (srel (nh (NH.CCX-HH {n})))) = CCX-HHₙ n
axiom-T (srel (srel (nh (NH.CCX-comm {n})))) = CCX-commₙ n
axiom-T (srel (σrel (σ-inv {n}))) = σ-invₙ n
axiom-T (srel (σrel (σ-nat₁ {n} X-gate))) = σ-natXₙ n
axiom-T (srel (σrel (σ-nat₁ {n} H-gate))) = σ-natHₙ n
axiom-T (srel (σrel (σ-nat₂ {n} CX-gate))) = σ-natCXₙ n
axiom-T (srel (σrel (σ-nat₂ {n} SW-gate))) = σ-natSWₙ n
axiom-T (srel (σrel (σ-nat₃ {n} CCX-gate))) = σ-natCCXₙ n
axiom-T (srel (srel (sch c))) = schema c
axiom-T (cong↑ {w = w} {v = v} r) = Eq.subst₂ (T._⊢_≈_ _) (Eq.sym (τH-↑ w))
  (Eq.sym (τH-↑ v)) (St.cong↑ (axiom-T r))
axiom-T (comm₁ X-gate g)   = St.comm₁ (τHg g) C.X-gate
axiom-T (comm₁ H-gate g)   = St.comm₁ (τHg g) C.H-gate
axiom-T (comm₂ CX-gate g)  = St.comm₂ (τHg g) C.CX-gate
axiom-T (comm₂ SW-gate g)  = pass-Ex (τHg g)
axiom-T (comm₃ CCX-gate g) = St.comm₃ (τHg g) C.CCX-gate
axiom-T (ω↑=ω ())

derivation-T : ∀ {w v : Circuit n} → n ⊢ w ≈ v → n T.⊢ τH w ≈ τH v
derivation-T PB.refl        = PB.refl
derivation-T (PB.sym p)     = PB.sym (derivation-T p)
derivation-T (PB.trans p q) = PB.trans (derivation-T p) (derivation-T q)
derivation-T (PB.cong p q)  = PB.cong (derivation-T p) (derivation-T q)
derivation-T PB.assoc       = PB.assoc
derivation-T PB.left-unit   = PB.left-unit
derivation-T PB.right-unit  = PB.right-unit
derivation-T (PB.axiom a)   = axiom-T a

-- The rules with the schema are sound for the ordinary circuit matrices.
sound : ∀ {w v : Circuit n} → n ⊢ w ≈ v → interpretH w ≡ interpretH v
sound {n} p = T.sound n (derivation-T p)
