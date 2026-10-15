------------------------------------------------------------------------
-- Presentations of groups
--
-- NaturalP and Natural are complete at the same widths.
--
-- τ reads the swap gate SW as Natural's swap word Ex = CX XC CX and
-- every other gate as itself.  It carries every axiom of NaturalP to a
-- derivation in Natural (`τ-≈`): the rules shared by both are the same
-- equations once σ is read as Ex, `sw-def` is the definition of Ex, and
-- the swap rules of Circuit.Prop are Natural's braid, CX-up, HH-swap and
-- CCX-up together with Ex Ex = ε and X Ex = Ex X ↑ (`ex-ex`, `x-ex`,
-- the latter found by Rules/derive.py).  NaturalP is read through τ,
-- so a completeness theorem for NaturalP gives one for Natural at the
-- same width (`complete⇒`), every Natural circuit being its own image.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Bridge where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.CCX+HH.Natural.Syntactics as N
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.Natural.Engine
  using (Eqn ; lhs ; rhs ; prf ; ⟪_⟫ ; derive ; rw ; perm ; sym⁼ ; lift⁼)
open import Examples.Groups.CCX+HH.Natural.Axioms
import Examples.Groups.CCX+HH.Semantics as Sem
import Circuit.Base as CB

private
  variable
    n : ℕ
  module NLR = CB.Lift-Relation N.Gate N._N,_===_

------------------------------------------------------------------------
-- The translation

τg : P.Gen n → N.Circuit n
τg (P.gate₀ ())
τg (P.gate₁ P.X-gate)   = N.X
τg (P.gate₂ P.CX-gate)  = N.CX
τg (P.gate₂ P.HH-gate)  = N.HH
τg (P.gate₂ P.SW-gate)  = N.Ex
τg (P.gate₃ P.CCX-gate) = N.CCX
τg (g P.↥)              = τg g N.↑

τ : P.Circuit n → N.Circuit n
τ [ g ]ʷ  = τg g
τ ε       = ε
τ (u • v) = τ u • τ v

τ-↑ : (w : P.Circuit n) → τ (w P.↑) ≡ τ w N.↑
τ-↑ [ g ]ʷ  = Eq.refl
τ-↑ ε       = Eq.refl
τ-↑ (u • v) = Eq.cong₂ _•_ (τ-↑ u) (τ-↑ v)

-- Every Natural circuit is a NaturalP circuit, read back by τ.
ιg : N.Gen n → P.Gen n
ιg (N.gate₀ ())
ιg (N.gate₁ N.X-gate)   = P.gate₁ P.X-gate
ιg (N.gate₂ N.CX-gate)  = P.gate₂ P.CX-gate
ιg (N.gate₂ N.HH-gate)  = P.gate₂ P.HH-gate
ιg (N.gate₃ N.CCX-gate) = P.gate₃ P.CCX-gate
ιg (g N.↥)              = ιg g P.↥

ι : N.Circuit n → P.Circuit n
ι [ g ]ʷ  = [ ιg g ]ʷ
ι ε       = ε
ι (u • v) = ι u • ι v

τι : (w : N.Circuit n) → τ (ι w) ≡ w
τι [ g ]ʷ  = τιg g
  where
  τιg : (g : N.Gen n) → τg (ιg g) ≡ [ g ]ʷ
  τιg (N.gate₀ ())
  τιg (N.gate₁ N.X-gate)   = Eq.refl
  τιg (N.gate₂ N.CX-gate)  = Eq.refl
  τιg (N.gate₂ N.HH-gate)  = Eq.refl
  τιg (N.gate₃ N.CCX-gate) = Eq.refl
  τιg (g N.↥)              = Eq.cong (Word.Base.wmap N._↥) (τιg g)
τι ε       = Eq.refl
τι (u • v) = Eq.cong₂ _•_ (τι u) (τι v)

-- NaturalP's semantics: through τ.
interpret : P.Circuit n → _
interpret w = Sem.interpret (τ w)

------------------------------------------------------------------------
-- The swap rules of Circuit.Prop, for the word Ex

private
  as : ∀ {m} {w v : N.Circuit m} →
       PP.to-list (m N.VRel,_===_) w Eq.≡ PP.to-list (m N.VRel,_===_) v → m N.⊢ w ≈ v
  as {m} = PP.by-assoc (m N.VRel,_===_)

  -- An engine equation, read between two circuits with its lists.
  use : ∀ {m} (e : Eqn m) {w v : N.Circuit m} →
        PP.to-list (m N.VRel,_===_) w Eq.≡ PP.to-list (m N.VRel,_===_) ⟪ lhs e ⟫ →
        PP.to-list (m N.VRel,_===_) ⟪ rhs e ⟫ Eq.≡ PP.to-list (m N.VRel,_===_) v →
        m N.⊢ w ≈ v
  use e p q = PB.trans (as p) (PB.trans (prf e) (as q))

  exlist : List (N.Gen (₂₊ n))
  exlist = cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ []

ex-exᵉ : Eqn (₂₊ n)
ex-exᵉ = derive (cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ []) []
  (rw 4 (inv⁼ cx₀) ∷ rw 3 (inv⁼ hh₀) ∷ rw 2 (inv⁼ cx₀) ∷ rw 1 (inv⁼ hh₀) ∷
   rw 0 (inv⁼ cx₀) ∷ []) Eq.refl

x-exᵉ : Eqn (₂₊ n)
x-exᵉ = derive (x₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ []) (cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ x₁ ∷ [])
  (rw 0 (sym⁼ (inv⁼ x₁)) ∷ perm (x₁ ∷ x₀ ∷ x₁ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ []) ∷
   rw 1 (sym⁼ (inv⁼ cx₀)) ∷ rw 2 (sym⁼ (X-controlᵉ)) ∷ rw 0 (X-controlᵉ) ∷
   rw 3 (inv⁼ x₁) ∷ rw 2 (inv⁼ cx₀) ∷ rw 1 (sym⁼ (inv⁼ hh₀)) ∷
   rw 2 (sym⁼ (inv⁼ cx₀)) ∷ rw 3 (sym⁼ (inv⁼ hh₀)) ∷ rw 4 (sym⁼ (inv⁼ cx₀)) ∷
   rw 6 (X-controlᵣᵉ) ∷ rw 5 (sym⁼ (X-controlᵉ)) ∷ rw 7 (inv⁼ x₁) ∷
   rw 6 (inv⁼ cx₀) ∷ []) Eq.refl

ex-ex : (₂₊ n) N.⊢ N.Ex • N.Ex ≈ ε
ex-ex = use ex-exᵉ Eq.refl Eq.refl

x-ex : (₂₊ n) N.⊢ N.X • N.Ex ≈ N.Ex • N.X N.↑
x-ex = use x-exᵉ Eq.refl Eq.refl

private
  exᵉ↑ exᵉ↑↑ : ∀ {n} → Eqn (₃₊ n)
  exᵉ↑ = lift⁼ ex-exᵉ
  exᵉ↑↑ = lift⁼ ex-exᵉ

-- σ-nat₂ at CX, from CX-up.
cx-natᵉ : Eqn (₃₊ n)
cx-natᵉ = derive (cx₀ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ [])
                 (cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ cx₁ ∷ [])
  (rw 0 (sym⁼ (lift⁼ ex-exᵉ)) ∷ rw 5 (sym⁼ ex-exᵉ) ∷ rw 10 CX-upᵉ ∷ []) Eq.refl

-- σ-nat₂ at HH, from HH-swap₁ and HH-swap₀.
hh-natᵉ : Eqn (₃₊ n)
hh-natᵉ = derive (hh₀ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ [])
                 (cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₁ ∷ [])
  (rw 0 (sym⁼ (lift⁼ ex-exᵉ)) ∷ rw 5 HH-swap₁ᵉ ∷ rw 5 (sym⁼ HH-swap₀ᵉ) ∷
   rw 11 ex-exᵉ ∷ []) Eq.refl

-- σ-nat₃ at CCX, from CCX-up.
ccx-natᵉ : Eqn (₄₊ n)
ccx-natᵉ = derive
  (ccx₀ ∷ cx₂ ∷ hh₂ ∷ cx₂ ∷ hh₂ ∷ cx₂ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷
   cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ [])
  (cx₂ ∷ hh₂ ∷ cx₂ ∷ hh₂ ∷ cx₂ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷
   cx₀ ∷ hh₀ ∷ cx₀ ∷ hh₀ ∷ cx₀ ∷ ccx₁ ∷ [])
  (rw 0 (sym⁼ (lift⁼ (lift⁼ ex-exᵉ))) ∷ rw 5 (sym⁼ (lift⁼ ex-exᵉ)) ∷
   rw 10 (sym⁼ ex-exᵉ) ∷ rw 15 CCX-upᵉ ∷ []) Eq.refl

cx-nat : (₃₊ n) N.⊢ N.CX • (N.Ex N.↑ • N.Ex) ≈ (N.Ex N.↑ • N.Ex) • N.CX N.↑
cx-nat = use cx-natᵉ Eq.refl Eq.refl

hh-nat : (₃₊ n) N.⊢ N.HH • (N.Ex N.↑ • N.Ex) ≈ (N.Ex N.↑ • N.Ex) • N.HH N.↑
hh-nat = use hh-natᵉ Eq.refl Eq.refl

ex-nat : (₃₊ n) N.⊢ N.Ex • (N.Ex N.↑ • N.Ex) ≈ (N.Ex N.↑ • N.Ex) • N.Ex N.↑
ex-nat = use braidᵉ Eq.refl Eq.refl

ccx-nat : (₄₊ n) N.⊢ N.CCX • ((N.Ex N.↑ N.↑ • N.Ex N.↑) • N.Ex)
                      ≈ ((N.Ex N.↑ N.↑ • N.Ex N.↑) • N.Ex) • N.CCX N.↑
ccx-nat = use ccx-natᵉ Eq.refl Eq.refl

------------------------------------------------------------------------
-- τ carries derivations

private
  -- A word commuting with each of two words commutes with their product.
  comm-• : ∀ {m} {x a b : N.Circuit m} →
           m N.⊢ x • a ≈ a • x → m N.⊢ x • b ≈ b • x → m N.⊢ x • (a • b) ≈ (a • b) • x
  comm-• p q = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong p PB.refl)
    (PB.trans PB.assoc (PB.trans (PB.cong PB.refl q) (PB.sym PB.assoc))))

  ex-comm : (w : N.Circuit n) → (₂₊ n) N.⊢ w N.↑ N.↑ • N.Ex ≈ N.Ex • w N.↑ N.↑
  ex-comm w = comm-• cx (comm-• (comm-• hh (comm-• cx hh)) cx)
    where
    cx = NLR.comm-gate₂-w↑↑ N.CX-gate w
    hh = NLR.comm-gate₂-w↑↑ N.HH-gate w

τ-axiom : ∀ {w v : P.Circuit n} → n P.VRel, w === v → n N.⊢ τ w ≈ τ v
τ-axiom (P.srel (P.σrel P.σ-inv))                 = ex-ex
τ-axiom (P.srel (P.σrel (P.σ-nat₁ P.X-gate)))     = x-ex
τ-axiom (P.srel (P.σrel (P.σ-nat₂ P.CX-gate)))    = cx-nat
τ-axiom (P.srel (P.σrel (P.σ-nat₂ P.HH-gate)))    = hh-nat
τ-axiom (P.srel (P.σrel (P.σ-nat₂ P.SW-gate)))    = ex-nat
τ-axiom (P.srel (P.σrel (P.σ-nat₃ P.CCX-gate)))   = ccx-nat
τ-axiom (P.srel (P.srel P.X²))         = PB.axiom (N.srel N.X²)
τ-axiom (P.srel (P.srel P.CX²))        = PB.axiom (N.srel N.CX²)
τ-axiom (P.srel (P.srel P.CCX²))       = PB.axiom (N.srel N.CCX²)
τ-axiom (P.srel (P.srel P.HH²))        = PB.axiom (N.srel N.HH²)
τ-axiom (P.srel (P.srel P.sw-def))     = PB.refl
τ-axiom (P.srel (P.srel P.X-control))  = PB.axiom (N.srel N.X-control)
τ-axiom (P.srel (P.srel P.X-controlᵣ)) = PB.axiom (N.srel N.X-controlᵣ)
τ-axiom (P.srel (P.srel P.CNOT-S3))    = PB.axiom (N.srel N.CNOT-S3)
τ-axiom (P.srel (P.srel P.X-Z))        = PB.axiom (N.srel N.X-Z)
τ-axiom (P.srel (P.srel P.CCX-sym))    = PB.axiom (N.srel N.CCX-sym)
τ-axiom (P.srel (P.srel P.CCX-neg))    = PB.axiom (N.srel N.CCX-neg)
τ-axiom (P.srel (P.srel P.CCX-XC))     = PB.axiom (N.srel N.CCX-XC)
τ-axiom (P.srel (P.srel P.HH-swap₀))   = PB.axiom (N.srel N.HH-swap₀)
τ-axiom (P.srel (P.srel P.HH-swap₁))   = PB.axiom (N.srel N.HH-swap₁)
τ-axiom (P.srel (P.srel P.CCX-HH))     = PB.axiom (N.srel N.CCX-HH)
τ-axiom (P.srel (P.srel P.CCX-comm))   = PB.axiom (N.srel N.CCX-comm)
τ-axiom (P.cong↑ {w = w} {v = v} x) =
  Eq.subst₂ (λ a b → _ N.⊢ a ≈ b) (Eq.sym (τ-↑ w)) (Eq.sym (τ-↑ v))
    (N.lemma-cong↑ (τ w) (τ v) (τ-axiom x))
τ-axiom (P.comm₁ P.X-gate g)   = NLR.comm-gate₁-w↑ N.X-gate (τg g)
τ-axiom (P.comm₂ P.CX-gate g)  = NLR.comm-gate₂-w↑↑ N.CX-gate (τg g)
τ-axiom (P.comm₂ P.HH-gate g)  = NLR.comm-gate₂-w↑↑ N.HH-gate (τg g)
τ-axiom (P.comm₂ P.SW-gate g)  = ex-comm (τg g)
τ-axiom (P.comm₃ P.CCX-gate g) = NLR.comm-gate₃-w↑↑↑ N.CCX-gate (τg g)
τ-axiom (P.ω↑=ω ())

τ-≈ : ∀ {w v : P.Circuit n} → n P.⊢ w ≈ v → n N.⊢ τ w ≈ τ v
τ-≈ PB.refl        = PB.refl
τ-≈ (PB.sym p)     = PB.sym (τ-≈ p)
τ-≈ (PB.trans p q) = PB.trans (τ-≈ p) (τ-≈ q)
τ-≈ (PB.cong p q)  = PB.cong (τ-≈ p) (τ-≈ q)
τ-≈ PB.assoc       = PB.assoc
τ-≈ PB.left-unit   = PB.left-unit
τ-≈ PB.right-unit  = PB.right-unit
τ-≈ (PB.axiom x)   = τ-axiom x

------------------------------------------------------------------------
-- Completeness transfers from NaturalP to Natural

complete⇒ : (∀ {u v : P.Circuit n} → interpret u ≡ interpret v → n P.⊢ u ≈ v) →
            ∀ {u v : N.Circuit n} → Sem.interpret u ≡ Sem.interpret v → n N.⊢ u ≈ v
complete⇒ cP {u} {v} e =
  Eq.subst₂ (λ a b → _ N.⊢ a ≈ b) (τι u) (τι v) (τ-≈ (cP {ι u} {ι v} e′))
  where
  e′ : interpret (ι u) ≡ interpret (ι v)
  e′ = Eq.trans (Eq.cong Sem.interpret (τι u)) (Eq.trans e (Eq.cong Sem.interpret (Eq.sym (τι v))))
