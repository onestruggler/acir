# Generates Examples/Groups/CCX+H/NaturalP/Soundness.agda
rules = [
 # (lemma name, constructor pattern (with {n}), base width, lhs, rhs)
 ("X²", "srel (srel (nh (NH.X² {n})))", 1, "X • X", "ε"),
 ("H²", "srel (srel (nh (NH.H² {n})))", 1, "H • H", "ε"),
 ("CX²", "srel (srel (nh (NH.CX² {n})))", 2, "CX • CX", "ε"),
 ("CCX²", "srel (srel (nh (NH.CCX² {n})))", 3, "CCX • CCX", "ε"),
 ("XH⁸", "srel (srel (nh (NH.XH⁸ {n})))", 1, " • ".join(["X • H"]*8), "ε"),
 ("sw-def", "srel (srel (nh (NH.sw-def {n})))", 2, "σ", "CX • XC • CX"),
 ("X-control", "srel (srel (nh (NH.X-control {n})))", 2, "X ↑ • CX • X ↑", "CX • X"),
 ("X-controlᵣ", "srel (srel (nh (NH.X-controlᵣ {n})))", 2, "XC • X • XC", "X • X ↑"),
 ("CNOT-S3", "srel (srel (nh (NH.CNOT-S3 {n})))", 2, "CX • XC • CX • XC • CX • XC", "ε"),
 ("X-Z", "srel (srel (nh (NH.X-Z {n})))", 2, "X • HHw • X ↑ • HHw", "HHw • X ↑ • HHw • X"),
 ("CZ-XC", "srel (srel (nh (NH.CZ-XC {n})))", 2, "CZ • XC • CZ • XC", "Z"),
 ("CCX-sym", "srel (srel (nh (NH.CCX-sym {n})))", 3, "σ ↑ • CCX • σ ↑", "CCX"),
 ("CCX-neg", "srel (srel (nh (NH.CCX-neg {n})))", 3, "X ↑ • CCX • X ↑", "CCX • σ ↑ • CX • σ ↑"),
 ("CCX-XC", "srel (srel (nh (NH.CCX-XC {n})))", 3, "CCX • XC • CCX • XC", "σ • CCX • σ • CCX"),
 ("HH-swap₀", "srel (srel (nh (NH.HH-swap₀ {n})))", 3, "σ • HHw ↑ • σ", "HHw • HHw ↑"),
 ("HH-swap₁", "srel (srel (nh (NH.HH-swap₁ {n})))", 3, "σ ↑ • HHw • σ ↑", "HHw • HHw ↑"),
 ("CCX-HH", "srel (srel (nh (NH.CCX-HH {n})))", 3, "CCX • XC • HHw • XC", "XC • HHw • XC • CCX"),
 ("CCXH⁴", "srel (srel (nh (NH.CCXH⁴ {n})))", 3, "CCX • H • CCX • H • CCX • H • CCX • H", "CZ ↑"),
 ("CCX-comm", "srel (srel (nh (NH.CCX-comm {n})))", 4, "CCX ↑ • CX • CCX ↑ • CX", "σ • CCX ↑ • σ"),
 ("σ-inv", "srel (σrel (σ-inv {n}))", 2, "σ • σ", "ε"),
 ("σ-natX", "srel (σrel (σ-nat₁ {n} X-gate))", 2, "[ gate₁ X-gate ]ʷ • σ[ 1 ]", "σ[ 1 ] • [ gate₁ X-gate ]ʷ ↑"),
 ("σ-natH", "srel (σrel (σ-nat₁ {n} H-gate))", 2, "[ gate₁ H-gate ]ʷ • σ[ 1 ]", "σ[ 1 ] • [ gate₁ H-gate ]ʷ ↑"),
 ("σ-natCX", "srel (σrel (σ-nat₂ {n} CX-gate))", 3, "[ gate₂ CX-gate ]ʷ • σ[ 2 ]", "σ[ 2 ] • [ gate₂ CX-gate ]ʷ ↑"),
 ("σ-natSW", "srel (σrel (σ-nat₂ {n} SW-gate))", 3, "[ gate₂ SW-gate ]ʷ • σ[ 2 ]", "σ[ 2 ] • [ gate₂ SW-gate ]ʷ ↑"),
 ("σ-natCCX", "srel (σrel (σ-nat₃ {n} CCX-gate))", 4, "[ gate₃ CCX-gate ]ʷ • σ[ 3 ]", "σ[ 3 ] • [ gate₃ CCX-gate ]ʷ ↑"),
]
plus = {1: "₁₊", 2: "₂₊", 3: "₃₊", 4: "₄₊"}

HEADER = '''------------------------------------------------------------------------
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
'''

MIDDLE = '''------------------------------------------------------------------------
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
'''

TAIL = '''axiom-T (srel (srel (sch c))) = schema c
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
'''

out = [HEADER]
for (nm, pat, k, l, r) in rules:
    out.append(f'''
    {nm}₀ : {k} T.⊢ τH ({l}) ≈ τH ({r})
    {nm}₀ = T.complete {k} (by-eq√ tt)
''')
out.append('''
------------------------------------------------------------------------
-- On the bottom wires of any wider circuit

private
''')
for (nm, pat, k, l, r) in rules:
    out.append(f'''  {nm}ₙ : ∀ n → ({plus[k]} n) T.⊢ τH ({l}) ≈ τH ({r})
  {nm}ₙ zero    = {nm}₀
  {nm}ₙ (suc n) = St.cong⇓ ({nm}ₙ n)

''')
out.append(MIDDLE)
for (nm, pat, k, l, r) in rules:
    out.append(f'axiom-T ({pat}) = {nm}ₙ n\n')
out.append(TAIL)
import sys
open(sys.argv[1], 'w', encoding='utf-8').write(''.join(out))
