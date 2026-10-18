------------------------------------------------------------------------
-- Presentations of groups
--
-- From Natural to NaturalP: completeness at a width carries over.
--
-- Every rule of Natural is derived in NaturalP (`ι-cong`): the rules
-- they share are the same once Natural's swap word Ex is identified
-- with the swap gate (`ex`, the rule sw-def), the braid is the
-- Yang–Baxter equation, and CX-up and CCX-up are the swap's naturality
-- at CX and CCX.  Every NaturalP circuit equals ι of its reading
-- (`back`), so completeness of Natural at a width gives completeness of
-- NaturalP there (`complete⇐`), and of NaturalP with the schema
-- (`complete⇐Σ`).  On no wires every circuit is ε (`completeΣ₀`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Converse where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

import Examples.Groups.CCX+HH.Natural.Syntactics as N
import Examples.Groups.CCX+HH.NaturalP.Syntactics as NP
open import Examples.Groups.CCX+HH.NaturalP.Syntactics
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τg ; τ ; τ-↑ ; ιg ; ι ; τι ; interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S
import Examples.Groups.CCX+HH.Semantics as Sem

private
  variable
    n : ℕ

open PB using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

ι-↑ : (w : N.Circuit n) → ι (w N.↑) ≡ ι w ↑
ι-↑ [ g ]ʷ  = Eq.refl
ι-↑ ε       = Eq.refl
ι-↑ (u • v) = Eq.cong₂ _•_ (ι-↑ u) (ι-↑ v)

------------------------------------------------------------------------
-- Natural's swap word is the swap

private
  rule : ∀ {w v} → n NP, w === v → n ⊢ w ≈ v
  rule r = axiom (srel (srel r))

ex : (₂₊ n) ⊢ ι N.Ex ≈ σ
ex = sym (rule sw-def)

private
  ex↑ : (₃₊ n) ⊢ ι N.Ex ↑ ≈ σ ↑
  ex↑ = lemma-cong↑ _ _ ex

  ex↑↑ : (₄₊ n) ⊢ ι N.Ex ↑ ↑ ≈ σ ↑ ↑
  ex↑↑ = lemma-cong↑ _ _ ex↑

  -- An involution cancels on the left.
  cancel : ∀ {x y : Circuit n} → n ⊢ x • x ≈ ε → n ⊢ x • (x • y) ≈ y
  cancel xx = trans (sym assoc) (trans (cong xx refl) left-unit)

  σσ↑ : (₃₊ n) ⊢ σ ↑ • σ ↑ ≈ ε
  σσ↑ = lemma-cong↑ _ _ σ-invol

  σσ↑↑ : (₄₊ n) ⊢ σ ↑ ↑ • σ ↑ ↑ ≈ ε
  σσ↑↑ = lemma-cong↑ _ _ σσ↑

  -- a • (b • ((b • a) • y)) is y, for involutions a and b.
  unwind₂ : ∀ {a b y : Circuit n} → n ⊢ a • a ≈ ε → n ⊢ b • b ≈ ε →
            n ⊢ a • (b • ((b • a) • y)) ≈ y
  unwind₂ aa bb = trans (cong refl (trans (cong refl assoc) (cancel bb))) (cancel aa)

  -- a • (b • (c • (((c • b) • a) • y))) is y, for involutions a, b, c.
  unwind₃ : ∀ {a b c y : Circuit n} → n ⊢ a • a ≈ ε → n ⊢ b • b ≈ ε → n ⊢ c • c ≈ ε →
            n ⊢ a • (b • (c • (((c • b) • a) • y))) ≈ y
  unwind₃ aa bb cc =
    trans (cong refl (cong refl (trans (cong refl (trans assoc assoc)) (cancel cc))))
    (trans (cong refl (cancel bb)) (cancel aa))

  cx-up : (₃₊ n) ⊢ σ • (σ ↑ • (CX • (σ ↑ • σ))) ≈ CX ↑
  cx-up = trans (cong refl (cong refl (sym-rule (σ-nat₂ CX-gate))))
    (unwind₂ σ-invol σσ↑)

  ccx-up : (₄₊ n) ⊢ σ • (σ ↑ • (σ ↑ ↑ • (CCX • (σ ↑ ↑ • (σ ↑ • σ))))) ≈ CCX ↑
  ccx-up = trans (cong refl (cong refl (cong refl
      (trans (cong refl (sym assoc)) (sym-rule (σ-nat₃ CCX-gate))))))
    (unwind₃ σ-invol σσ↑ σσ↑↑)

------------------------------------------------------------------------
-- Natural's rules, derived

private
  rule-N : ∀ {w v : N.Circuit n} → n N.VRel, w === v → n ⊢ ι w ≈ ι v
  rule-N (N.srel N.X²)   = rule X²
  rule-N (N.srel N.CX²)  = rule CX²
  rule-N (N.srel N.CCX²) = rule CCX²
  rule-N (N.srel N.HH²)  = rule HH²
  rule-N (N.srel N.X-control)  = rule X-control
  rule-N (N.srel N.X-controlᵣ) = rule X-controlᵣ
  rule-N (N.srel N.CNOT-S3)    = rule CNOT-S3
  rule-N (N.srel N.X-Z)        = rule X-Z
  rule-N (N.srel N.braid) =
    trans (cong ex (cong ex↑ ex)) (trans yang-baxter (sym (cong ex↑ (cong ex ex↑))))
  rule-N (N.srel N.CX-up) =
    trans (cong ex (cong ex↑ (cong refl (cong ex↑ ex)))) cx-up
  rule-N (N.srel N.CCX-sym) =
    trans (cong ex↑ (cong refl ex↑)) (rule CCX-sym)
  rule-N (N.srel N.CCX-neg) =
    trans (rule CCX-neg) (sym (cong refl (cong ex↑ (cong refl ex↑))))
  rule-N (N.srel N.CCX-XC) =
    trans (rule CCX-XC) (sym (cong ex (cong refl (cong ex refl))))
  rule-N (N.srel N.HH-swap₀) =
    trans (cong ex (cong refl ex)) (rule HH-swap₀)
  rule-N (N.srel N.HH-swap₁) =
    trans (cong ex↑ (cong refl ex↑)) (rule HH-swap₁)
  rule-N (N.srel N.CCX-HH) = rule CCX-HH
  rule-N (N.srel N.CCX-comm) =
    trans (rule CCX-comm) (sym (cong ex (cong refl ex)))
  rule-N (N.srel N.CCX-up) =
    trans (cong ex (cong ex↑ (cong ex↑↑ (cong refl (cong ex↑↑ (cong ex↑ ex)))))) ccx-up
  rule-N (N.cong↑ {w = w} {v = v} r) =
    Eq.subst₂ (_⊢_≈_ _) (Eq.sym (ι-↑ w)) (Eq.sym (ι-↑ v)) (lemma-cong↑ _ _ (rule-N r))
  rule-N (N.comm₁ N.X-gate g)   = axiom (comm₁ X-gate (ιg g))
  rule-N (N.comm₂ N.CX-gate g)  = axiom (comm₂ CX-gate (ιg g))
  rule-N (N.comm₂ N.HH-gate g)  = axiom (comm₂ HH-gate (ιg g))
  rule-N (N.comm₃ N.CCX-gate g) = axiom (comm₃ CCX-gate (ιg g))
  rule-N (N.LR-ω↑=ω ())

ι-cong : ∀ {w v : N.Circuit n} → n N.⊢ w ≈ v → n ⊢ ι w ≈ ι v
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
  backg : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ι (τg g)
  backg (gate₀ ())
  backg (gate₁ X-gate)   = refl
  backg (gate₂ CX-gate)  = refl
  backg (gate₂ HH-gate)  = refl
  backg (gate₂ SW-gate)  = sym ex
  backg (gate₃ CCX-gate) = refl
  backg (g ↥) = Eq.subst (λ t → _ ⊢ [ g ↥ ]ʷ ≈ t) (Eq.sym (ι-↑ (τg g)))
    (lemma-cong↑ _ _ (backg g))

back : (w : Circuit n) → n ⊢ w ≈ ι (τ w)
back [ g ]ʷ  = backg g
back ε       = refl
back (u • v) = cong (back u) (back v)

------------------------------------------------------------------------
-- Completeness transfers from Natural to NaturalP

complete⇐ : (∀ {u v : N.Circuit n} → Sem.interpret u ≡ Sem.interpret v → n N.⊢ u ≈ v) →
            ∀ {u v : Circuit n} → interpret u ≡ interpret v → n ⊢ u ≈ v
complete⇐ c {u} {v} e = trans (back u) (trans (ι-cong (c e)) (sym (back v)))

complete⇐Σ : (∀ {u v : N.Circuit n} → Sem.interpret u ≡ Sem.interpret v → n N.⊢ u ≈ v) →
             ∀ {u v : Circuit n} → interpret u ≡ interpret v → n S.⊢ u ≈ v
complete⇐Σ c e = S.emb (complete⇐ c e)

completeΣ₀ : ∀ {u v : Circuit 0} → interpret u ≡ interpret v → 0 S.⊢ u ≈ v
completeΣ₀ {u} {v} _ = PB.trans (zero u) (PB.sym (zero v))
  where
  zero : (w : Circuit 0) → 0 S.⊢ w ≈ ε
  zero [ gate₀ () ]ʷ
  zero ε       = PB.refl
  zero (u • v) = PB.trans (PB.cong (zero u) (zero v)) PB.left-unit
