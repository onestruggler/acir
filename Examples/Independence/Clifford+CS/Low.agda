------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂ is complete on no wires and on one, from Cliff₂
--
-- On at most one wire CliffCS₂ and Cliff₂ have the same gates (ω, H, S)
-- and the same axioms (ω⁸, H², S⁴, E): every other axiom and symmetry
-- rule of either needs two wires.  So a derivation of Cliff₂'s between
-- circuits on at most one wire, which Cliff₂'s completeness supplies
-- (Clifford.Completeness), is one of CliffCS₂'s, letter for letter
-- (tr): its axiom instances are among those four, ω↑=ω, and cong↑ of
-- them, the others being refuted by their width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Low where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
import Examples.Independence.Clifford.Syntactics as C
import Examples.Independence.Clifford.Semantics as C-Sem
import Examples.Independence.Clifford.Completeness as C-Cpl
import Examples.Independence.Semantics.Qubit as O
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (lift)

private
  variable
    n : ℕ
    w v : C.Circuit n

------------------------------------------------------------------------
-- Cliff₂'s circuits, read in CliffCS₂

Φg : C.Gen n → Circuit n
Φg (C.gate₀ C.⌈ C.ω-gate ⌉)  = ω
Φg (C.gate₁ C.⌈ C.H-gate ⌉)  = H
Φg (C.gate₁ C.⌈ C.S-gate ⌉)  = S
Φg (C.gate₂ C.⌈ C.CX-gate ⌉) = CX
Φg (C.gate₂ C.swap)          = σ
Φg (g C.↥)                   = Φg g ↑

Φ : C.Circuit n → Circuit n
Φ [ g ]ʷ  = Φg g
Φ ε       = ε
Φ (w • v) = Φ w • Φ v

private
  Φ-↑ : (w : C.Circuit n) → Φ (w C.↑) ≡ Φ w ↑
  Φ-↑ [ g ]ʷ  = refl
  Φ-↑ ε       = refl
  Φ-↑ (w • v) = Eq.cong₂ _•_ (Φ-↑ w) (Φ-↑ v)

  -- A symmetry rule needs two wires.
  sym-wide : n ≤ 1 → {w v : C.Circuit n} → C._Sym,_===_ n w v → ⊥
  sym-wide (s≤s ()) C.σ-inv
  sym-wide (s≤s ()) (C.σ-nat₁ _)
  sym-wide (s≤s ()) (C.σ-nat₂ _)

-- The axiom instances on at most one wire.
tr-ax : n C.VRel, w === v → n ≤ 1 → n ⊢ Φ w ≈ Φ v
tr-ax (C.srel (C.sym s))           le        = ⊥-elim (sym-wide le s)
tr-ax (C.srel (C.ax C.ω⁸ k))       _         = PB.axiom (srel (ax ω⁸ k))
tr-ax (C.srel (C.ax C.H² zero))    _         = PB.axiom (srel (ax H² 0))
tr-ax (C.srel (C.ax C.H² (suc _))) (s≤s ())
tr-ax (C.srel (C.ax C.S⁴ zero))    _         = PB.axiom (srel (ax S⁴ 0))
tr-ax (C.srel (C.ax C.S⁴ (suc _))) (s≤s ())
tr-ax (C.srel (C.ax C.E zero))     _         = PB.axiom (srel (ax E 0))
tr-ax (C.srel (C.ax C.E (suc _)))  (s≤s ())
tr-ax (C.srel (C.ax C.CPh _))      (s≤s ())
tr-ax (C.srel (C.ax C.B _))        (s≤s ())
tr-ax (C.srel (C.ax C.CZ _))       (s≤s ())
tr-ax (C.srel (C.ax C.I _))        (s≤s ())
tr-ax (C.cong↑ {w = w} {v} a)      (s≤s z≤n) =
  Eq.subst₂ (_ ⊢_≈_) (Eq.sym (Φ-↑ w)) (Eq.sym (Φ-↑ v)) (lift (tr-ax a z≤n))
tr-ax (C.comm₁ C.⌈ C.H-gate ⌉ (C.gate₀ C.⌈ C.ω-gate ⌉)) _ = PB.axiom (comm₁ ⌈ H-gate ⌉ (gate₀ ⌈ ω-gate ⌉))
tr-ax (C.comm₁ C.⌈ C.S-gate ⌉ (C.gate₀ C.⌈ C.ω-gate ⌉)) _ = PB.axiom (comm₁ ⌈ S-gate ⌉ (gate₀ ⌈ ω-gate ⌉))
tr-ax (C.comm₁ _ (C.gate₁ _))      (s≤s ())
tr-ax (C.comm₁ _ (C.gate₂ _))      (s≤s ())
tr-ax (C.comm₁ _ (_ C.↥))         (s≤s ())
tr-ax (C.comm₂ _ _)                (s≤s ())
tr-ax (C.ω↑=ω C.⌈ C.ω-gate ⌉)      _         = PB.axiom (ω↑=ω ⌈ ω-gate ⌉)

-- So every derivation.
tr : n ≤ 1 → PB._≈_ (n C.VRel,_===_) w v → n ⊢ Φ w ≈ Φ v
tr le PB.refl        = PB.refl
tr le (PB.sym e)     = PB.sym (tr le e)
tr le (PB.trans e f) = PB.trans (tr le e) (tr le f)
tr le (PB.cong e f)  = PB.cong (tr le e) (tr le f)
tr le PB.assoc       = PB.assoc
tr le PB.left-unit   = PB.left-unit
tr le PB.right-unit  = PB.right-unit
tr le (PB.axiom a)   = tr-ax a le

------------------------------------------------------------------------
-- CliffCS₂'s circuits on at most one wire, read in Cliff₂

private
  Ψ₀ : Gen 0 → C.Gen 0
  Ψ₀ (gate₀ ⌈ ω-gate ⌉) = C.gate₀ C.⌈ C.ω-gate ⌉

  Ψ₁ : Gen 1 → C.Gen 1
  Ψ₁ (gate₀ ⌈ ω-gate ⌉) = C.gate₀ C.⌈ C.ω-gate ⌉
  Ψ₁ (gate₁ ⌈ H-gate ⌉) = C.gate₁ C.⌈ C.H-gate ⌉
  Ψ₁ (gate₁ ⌈ S-gate ⌉) = C.gate₁ C.⌈ C.S-gate ⌉
  Ψ₁ (g ↥)              = Ψ₀ g C.↥

  Ψʷ₀ : Circuit 0 → C.Circuit 0
  Ψʷ₀ [ g ]ʷ  = [ Ψ₀ g ]ʷ
  Ψʷ₀ ε       = ε
  Ψʷ₀ (w • v) = Ψʷ₀ w • Ψʷ₀ v

  Ψʷ₁ : Circuit 1 → C.Circuit 1
  Ψʷ₁ [ g ]ʷ  = [ Ψ₁ g ]ʷ
  Ψʷ₁ ε       = ε
  Ψʷ₁ (w • v) = Ψʷ₁ w • Ψʷ₁ v

  ΦΨ₀ : (w : Circuit 0) → Φ (Ψʷ₀ w) ≡ w
  ΦΨ₀ [ gate₀ ⌈ ω-gate ⌉ ]ʷ = refl
  ΦΨ₀ ε       = refl
  ΦΨ₀ (w • v) = Eq.cong₂ _•_ (ΦΨ₀ w) (ΦΨ₀ v)

  ΦΨ₁ : (w : Circuit 1) → Φ (Ψʷ₁ w) ≡ w
  ΦΨ₁ [ gate₀ ⌈ ω-gate ⌉ ]ʷ       = refl
  ΦΨ₁ [ gate₁ ⌈ H-gate ⌉ ]ʷ       = refl
  ΦΨ₁ [ gate₁ ⌈ S-gate ⌉ ]ʷ       = refl
  ΦΨ₁ [ gate₀ ⌈ ω-gate ⌉ ↥ ]ʷ     = refl
  ΦΨ₁ ε       = refl
  ΦΨ₁ (w • v) = Eq.cong₂ _•_ (ΦΨ₁ w) (ΦΨ₁ v)

  -- The two semantics agree on these gates.
  sem₀ : (w : Circuit 0) → C-Sem.⟦ Ψʷ₀ w ⟧ ≡ Sem.⟦ w ⟧
  sem₀ [ gate₀ ⌈ ω-gate ⌉ ]ʷ = refl
  sem₀ ε       = refl
  sem₀ (w • v) = Eq.cong₂ O._∙_ (sem₀ w) (sem₀ v)

  sem₁ : (w : Circuit 1) → C-Sem.⟦ Ψʷ₁ w ⟧ ≡ Sem.⟦ w ⟧
  sem₁ [ gate₀ ⌈ ω-gate ⌉ ]ʷ   = refl
  sem₁ [ gate₁ ⌈ H-gate ⌉ ]ʷ   = refl
  sem₁ [ gate₁ ⌈ S-gate ⌉ ]ʷ   = refl
  sem₁ [ gate₀ ⌈ ω-gate ⌉ ↥ ]ʷ = refl
  sem₁ ε       = refl
  sem₁ (w • v) = Eq.cong₂ O._∙_ (sem₁ w) (sem₁ v)

------------------------------------------------------------------------
-- Completeness on no wires and on one

open O.Circuits Sem.val using () renaming (module Exact to SE)
open O.Circuits C-Sem.val using () renaming (module Exact to CE)

private
  -- The exact equality of values, for either gate set.
  conv : {s t : O.Sc n} → s SE.≈ t → s CE.≈ t
  conv (SE.phased k pk e) = CE.phased k pk e

complete₀ : {w v : Circuit 0} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 0 ⊢ w ≈ v
complete₀ {w} {v} e =
  Eq.subst₂ (0 ⊢_≈_) (ΦΨ₀ w) (ΦΨ₀ v)
    (tr z≤n (C-Cpl.complete {w = Ψʷ₀ w} {Ψʷ₀ v}
      (Eq.subst₂ C-Sem._≈_ (Eq.sym (sem₀ w)) (Eq.sym (sem₀ v)) (conv e))))

complete₁ : {w v : Circuit 1} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → 1 ⊢ w ≈ v
complete₁ {w} {v} e =
  Eq.subst₂ (1 ⊢_≈_) (ΦΨ₁ w) (ΦΨ₁ v)
    (tr (s≤s z≤n) (C-Cpl.complete {w = Ψʷ₁ w} {Ψʷ₁ v}
      (Eq.subst₂ C-Sem._≈_ (Eq.sym (sem₁ w)) (Eq.sym (sem₁ v)) (conv e))))
