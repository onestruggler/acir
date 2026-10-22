------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂ derives Cliff₂, and so is complete for Clifford circuits
--
-- Read a Cliff₂ circuit in CliffCS₂ letter for letter, its CNOT as
-- H CS CS H (Φ).  Every axiom of Cliff₂ then becomes an equation that
-- CliffCS₂ derives: (ω⁸), (H²), (S⁴), (E), (B) and (I) are CliffCS₂'s
-- own, letter for letter, and (CPh) and (CZ), two-wire equations that
-- hold in the matrix semantics, follow from CliffCS₂'s completeness on
-- two wires (Clifford+CS.Completeness).  Of the swap rules, the one
-- for the CNOT follows from those for H and CS (Circuit.Prop.nat₂), and
-- the structural rules carry over, a CNOT passing a circuit two wires
-- up letter by letter.  So every derivation of Cliff₂ is one of
-- CliffCS₂ (tr), and with Cliff₂'s completeness (Clifford.Completeness)
-- every equation between Clifford circuits that holds is derivable in
-- CliffCS₂ at every width (clifford-complete), where CliffCS₂'s own
-- completeness is formalised up to three wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.CliffordCircuits where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

import Presentation.Base as PB

open import Notations using (₂₊)

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
open import Examples.Independence.Clifford+CS.Completeness using (complete₂)
open import Examples.Independence.Semantics.Qubit using (module Circuits)
import Examples.Independence.Clifford.Syntactics as C
import Examples.Independence.Clifford.Semantics as C-Sem
import Examples.Independence.Clifford.Completeness as C-Cpl

open Circuits Sem.val using (module Exact)
open Exact using (check)

private
  variable
    n : ℕ
    w v : C.Circuit n

------------------------------------------------------------------------
-- Cliff₂ read in CliffCS₂

Φg : C.Gen n → Circuit n
Φg (C.gate₀ C.⌈ C.ω-gate ⌉)  = ω
Φg (C.gate₁ C.⌈ C.H-gate ⌉)  = H
Φg (C.gate₁ C.⌈ C.S-gate ⌉)  = S
Φg (C.gate₂ C.⌈ C.CX-gate ⌉) = CX
Φg (C.gate₂ C.swap)          = σ
Φg (C.gate₃ C.⌈ () ⌉)
Φg (g C.↥)                   = Φg g ↑

Φ : C.Circuit n → Circuit n
Φ [ g ]ʷ  = Φg g
Φ ε       = ε
Φ (w • v) = Φ w • Φ v

Φ-↑ : (w : C.Circuit n) → Φ (w C.↑) ≡ Φ w ↑
Φ-↑ [ g ]ʷ  = refl
Φ-↑ ε       = refl
Φ-↑ (w • v) = Eq.cong₂ _•_ (Φ-↑ w) (Φ-↑ v)

------------------------------------------------------------------------
-- What Cliff₂'s axioms need besides CliffCS₂'s

private
  -- A circuit two wires up passes a word, letter by letter.
  pass : (x : Circuit n) {a b : Circuit (₂₊ n)} →
         ₂₊ n ⊢ x ↑ ↑ • a ≈ a • x ↑ ↑ → ₂₊ n ⊢ x ↑ ↑ • b ≈ b • x ↑ ↑ →
         ₂₊ n ⊢ x ↑ ↑ • (a • b) ≈ (a • b) • x ↑ ↑
  pass x pa pb =
    PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong pa PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl pb) (PB.sym PB.assoc))))

  passH : (x : Circuit n) → ₂₊ n ⊢ x ↑ ↑ • H ≈ H • x ↑ ↑
  passH x = comm-gate₁-w↑ ⌈ H-gate ⌉ (x ↑)

  passCS : (x : Circuit n) → ₂₊ n ⊢ x ↑ ↑ • CS ≈ CS • x ↑ ↑
  passCS x = comm-gate₂-w↑↑ ⌈ CS-gate ⌉ x

  -- CX = H CS CS H passes a circuit two wires up.
  passCX : (x : Circuit n) → ₂₊ n ⊢ x ↑ ↑ • CX ≈ CX • x ↑ ↑
  passCX x = pass x (passH x) (pass x (passCS x) (pass x (passCS x) (passH x)))

-- (CPh) and (CZ), read in CliffCS₂: the CNOT conjugating S on its
-- control, and H conjugating the CNOT.  Both hold in the semantics.
cph : 2 ⊢ CX • S ↑ • CX ≈ S ↑
cph = complete₂ {w = CX • S ↑ • CX} {v = S ↑} (check 0 refl _ _ _)

cz : 2 ⊢ H • CX • H ≈ S ↑ • S • CX • S ^ 3 • CX
cz = complete₂ {w = H • CX • H} {v = S ↑ • S • CX • S ^ 3 • CX} (check 0 refl _ _ _)

------------------------------------------------------------------------
-- Cliff₂'s axiom instances, derived

tr-ax : n C.VRel, w === v → n ⊢ Φ w ≈ Φ v
tr-ax (C.srel (C.σrel C.σ-inv))                      = PB.axiom (srel (σrel σ-inv))
tr-ax (C.srel (C.σrel (C.σ-nat₁ C.⌈ C.H-gate ⌉)))    = PB.axiom (srel (σrel (σ-nat₁ ⌈ H-gate ⌉)))
tr-ax (C.srel (C.σrel (C.σ-nat₁ C.⌈ C.S-gate ⌉)))    = PB.axiom (srel (σrel (σ-nat₁ ⌈ S-gate ⌉)))
tr-ax (C.srel (C.σrel (C.σ-nat₂ C.⌈ C.CX-gate ⌉)))   = nat₂ CX
tr-ax (C.srel (C.σrel (C.σ-nat₂ C.swap)))            = PB.axiom (srel (σrel (σ-nat₂ swap)))
tr-ax (C.srel (C.σrel (C.σ-nat₃ C.⌈ () ⌉)))
tr-ax (C.srel (C.srel C.ω⁸))                         = PB.axiom (srel (srel ω⁸))
tr-ax (C.srel (C.srel C.H²))                         = PB.axiom (srel (srel H²))
tr-ax (C.srel (C.srel C.S⁴))                         = PB.axiom (srel (srel S⁴))
tr-ax (C.srel (C.srel C.E))                          = PB.axiom (srel (srel E))
tr-ax (C.srel (C.srel C.CPh))                        = cph
tr-ax (C.srel (C.srel C.B))                          = PB.axiom (srel (srel B))
tr-ax (C.srel (C.srel C.CZ))                         = cz
tr-ax (C.srel (C.srel C.I))                          = PB.axiom (srel (srel I))
tr-ax (C.cong↑ {w = w} {v} a)                        =
  Eq.subst₂ (_ ⊢_≈_) (Eq.sym (Φ-↑ w)) (Eq.sym (Φ-↑ v)) (lemma-cong↑ (Φ w) (Φ v) (tr-ax a))
tr-ax (C.comm₁ C.⌈ C.H-gate ⌉ g)                     = comm-gate₁-w↑ ⌈ H-gate ⌉ (Φg g)
tr-ax (C.comm₁ C.⌈ C.S-gate ⌉ g)                     = comm-gate₁-w↑ ⌈ S-gate ⌉ (Φg g)
tr-ax (C.comm₂ C.⌈ C.CX-gate ⌉ g)                    = passCX (Φg g)
tr-ax (C.comm₂ C.swap g)                             = comm-gate₂-w↑↑ swap (Φg g)
tr-ax (C.comm₃ C.⌈ () ⌉ g)
tr-ax (C.ω↑=ω C.⌈ C.ω-gate ⌉)                        = PB.axiom (ω↑=ω ⌈ ω-gate ⌉)

-- So every derivation of Cliff₂ is one of CliffCS₂.
tr : n C.⊢ w ≈ v → n ⊢ Φ w ≈ Φ v
tr PB.refl        = PB.refl
tr (PB.sym e)     = PB.sym (tr e)
tr (PB.trans e f) = PB.trans (tr e) (tr f)
tr (PB.cong e f)  = PB.cong (tr e) (tr f)
tr PB.assoc       = PB.assoc
tr PB.left-unit   = PB.left-unit
tr PB.right-unit  = PB.right-unit
tr (PB.axiom a)   = tr-ax a

------------------------------------------------------------------------
-- Completeness for Clifford circuits

-- Clifford circuits with the same matrix are equal in CliffCS₂, at
-- every width.
clifford-complete : C-Sem.⟦ w ⟧ C-Sem.≈ C-Sem.⟦ v ⟧ → n ⊢ Φ w ≈ Φ v
clifford-complete {w = w} {v} e = tr (C-Cpl.complete {w = w} {v} e)
