------------------------------------------------------------------------
-- Presentations of groups
--
-- The CCX+H rules with the swap gate and CCX+H.Natural are complete at
-- the same small widths.
--
-- Natural's circuits are those of NaturalP without the swap gate (`ι`),
-- read back by τH, and each rule of Natural is derived here: the rules
-- they share are the same once Natural's XC = H H↑ CX H↑ H is
-- identified with NaturalP's HH CX HH (`xc`, the two H commute), and
-- H-swap is the swap's naturality at H once Natural's swap word is
-- identified with the swap gate (`ex`, the rule sw-def).  Every
-- NaturalP circuit equals ι of its reading (`back`), so completeness of
-- Natural at a width gives completeness here (`complete⇒`).  On no
-- wires every circuit is ε (`complete₀`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Bridge where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊)
import Presentation.Base as PB

import Examples.Groups.CCX+H.Syntactics as C
import Examples.Groups.CCX+H.Natural.Syntactics as N
import Examples.Groups.CCX+H.NaturalP.Syntactics as NH
open import Examples.Groups.CCX+H.NaturalP.Schema
open import Examples.Groups.CCX+H.NaturalP.Soundness using (τHg ; τH ; τH-↑ ; interpretH)
open import Examples.Groups.CCX+H.NaturalP.Complete using (Complete)
import Examples.Groups.CCX+H.Presentation as T

private
  variable
    n : ℕ

open PB using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

------------------------------------------------------------------------
-- Natural's circuits

ιg : C.Gen n → Gen n
ιg (C.gate₀ ())
ιg (C.gate₁ C.X-gate)   = gate₁ X-gate
ιg (C.gate₁ C.H-gate)   = gate₁ H-gate
ιg (C.gate₂ C.CX-gate)  = gate₂ CX-gate
ιg (C.gate₃ C.CCX-gate) = gate₃ CCX-gate
ιg (g C.↥)              = ιg g ↥

ι : C.Circuit n → Circuit n
ι [ g ]ʷ  = [ ιg g ]ʷ
ι ε       = ε
ι (u • v) = ι u • ι v

ι-↑ : (w : C.Circuit n) → ι (w C.↑) ≡ ι w ↑
ι-↑ [ g ]ʷ  = Eq.refl
ι-↑ ε       = Eq.refl
ι-↑ (u • v) = Eq.cong₂ _•_ (ι-↑ u) (ι-↑ v)

private
  τιg : (g : C.Gen n) → τH [ ιg g ]ʷ ≡ [ g ]ʷ
  τιg (C.gate₀ ())
  τιg (C.gate₁ C.X-gate)   = Eq.refl
  τιg (C.gate₁ C.H-gate)   = Eq.refl
  τιg (C.gate₂ C.CX-gate)  = Eq.refl
  τιg (C.gate₃ C.CCX-gate) = Eq.refl
  τιg (g C.↥)              = Eq.cong (C._↑) (τιg g)

τι : (w : C.Circuit n) → τH (ι w) ≡ w
τι [ g ]ʷ  = τιg g
τι ε       = Eq.refl
τι (u • v) = Eq.cong₂ _•_ (τι u) (τι v)

------------------------------------------------------------------------
-- Natural's rules, derived

private
  rule : ∀ {w v} → n NH, w === v → n ⊢ w ≈ v
  rule r = axiom (srel (srel (nh r)))

  H-H↑ : (₂₊ n) ⊢ H ↑ • H ≈ H • H ↑
  H-H↑ = axiom (comm₁ H-gate (gate₁ H-gate))

  σHσ : (₂₊ n) ⊢ σ • (H • σ) ≈ H ↑
  σHσ = trans (cong refl (sym-rule (σ-nat₁ H-gate))) (trans (sym assoc)
    (trans (cong σ-invol refl) left-unit))

-- Natural's XC and swap word.
xc : (₂₊ n) ⊢ ι N.XC ≈ NH.XC
xc = trans (sym assoc) (cong refl (cong refl H-H↑))

ex : (₂₊ n) ⊢ ι N.Ex ≈ σ
ex = trans (cong refl (cong xc refl)) (sym (rule NH.sw-def))

private
  rule-N : ∀ {w v : C.Circuit n} → n N.VRel, w === v → n ⊢ ι w ≈ ι v
  rule-N (N.srel N.X²)   = rule NH.X²
  rule-N (N.srel N.H²)   = rule NH.H²
  rule-N (N.srel N.CX²)  = rule NH.CX²
  rule-N (N.srel N.CCX²) = rule NH.CCX²
  rule-N (N.srel N.XH⁸)  = rule NH.XH⁸
  rule-N (N.srel N.X-controlᵣ) =
    trans (cong xc (cong refl xc)) (rule NH.X-controlᵣ)
  rule-N (N.srel N.H-swap) =
    trans (cong ex (cong refl ex)) σHσ
  rule-N (N.srel N.CZ-XC) =
    trans (cong refl (cong xc (cong refl xc))) (rule NH.CZ-XC)
  rule-N (N.cong↑ {w = w} {v = v} r) =
    Eq.subst₂ (_⊢_≈_ _) (Eq.sym (ι-↑ w)) (Eq.sym (ι-↑ v)) (lemma-cong↑ _ _ (rule-N r))
  rule-N (N.comm₁ C.X-gate g)   = axiom (comm₁ X-gate (ιg g))
  rule-N (N.comm₁ C.H-gate g)   = axiom (comm₁ H-gate (ιg g))
  rule-N (N.comm₂ C.CX-gate g)  = axiom (comm₂ CX-gate (ιg g))
  rule-N (N.comm₃ C.CCX-gate g) = axiom (comm₃ CCX-gate (ιg g))
  rule-N (N.LR-ω↑=ω ())

ι-cong : ∀ {w v : C.Circuit n} → n N.⊢ w ≈ v → n ⊢ ι w ≈ ι v
ι-cong PB.refl        = refl
ι-cong (PB.sym p)     = sym (ι-cong p)
ι-cong (PB.trans p q) = trans (ι-cong p) (ι-cong q)
ι-cong (PB.cong p q)  = cong (ι-cong p) (ι-cong q)
ι-cong PB.assoc       = assoc
ι-cong PB.left-unit   = left-unit
ι-cong PB.right-unit  = right-unit
ι-cong (PB.axiom a)   = rule-N a

------------------------------------------------------------------------
-- Every circuit is ι of its reading

private
  backg : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ι (τHg g)
  backg (gate₀ ())
  backg (gate₁ X-gate)   = refl
  backg (gate₁ H-gate)   = refl
  backg (gate₂ CX-gate)  = refl
  backg (gate₂ SW-gate)  = sym ex
  backg (gate₃ CCX-gate) = refl
  backg (g ↥) = Eq.subst (λ t → _ ⊢ [ g ↥ ]ʷ ≈ t) (Eq.sym (ι-↑ (τHg g)))
    (lemma-cong↑ _ _ (backg g))

back : (w : Circuit n) → n ⊢ w ≈ ι (τH w)
back [ g ]ʷ  = backg g
back ε       = refl
back (u • v) = cong (back u) (back v)

------------------------------------------------------------------------
-- Completeness transfers

complete⇒ : (∀ {u v : C.Circuit n} → T.interpret u ≡ T.interpret v → n N.⊢ u ≈ v) →
            Complete n
complete⇒ c {u} {v} e = trans (back u) (trans (ι-cong (c e)) (sym (back v)))

complete₀ : Complete 0
complete₀ {u} {v} _ = trans (zero u) (sym (zero v))
  where
  zero : (w : Circuit 0) → 0 ⊢ w ≈ ε
  zero [ gate₀ () ]ʷ
  zero ε       = refl
  zero (u • v) = trans (cong (zero u) (zero v)) left-unit
