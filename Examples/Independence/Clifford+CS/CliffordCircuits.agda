------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂ derives Cliff₂, and so is complete for Clifford circuits
--
-- Read a Cliff₂ circuit in CliffCS₂ letter for letter, its CNOT as
-- H CS CS H (Clifford+CS.Low's Φ).  Every axiom of Cliff₂ then becomes
-- an equation that CliffCS₂ derives, at every width: (ω⁸), (H²), (S⁴),
-- (E), (B) and (I) are CliffCS₂'s own; (CPh) is (E3); (CZ), read
-- backwards, is the CNOT conjugating S on its target, which comes from
-- (CE) through the calculus of Clifford+CS.TwoWire; and the swap rule
-- for the CNOT from those for H and CS (Clifford+CS.CliffordRules).
-- The structural rules carry over, a CNOT passing a circuit two wires
-- up letter by letter.  So every derivation of Cliff₂ is one of
-- CliffCS₂ (tr), and with Cliff₂'s completeness (Clifford.Completeness)
-- every equation between Clifford circuits that holds is derivable in
-- CliffCS₂, at every width (clifford-complete) — on two wires too,
-- where CliffCS₂'s completeness is open.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.CliffordCircuits where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford.Syntactics as C
import Examples.Independence.Clifford.Semantics as C-Sem
import Examples.Independence.Clifford.Completeness as C-Cpl
open import Examples.Independence.Clifford+CS.Low using (Φg ; Φ)
open import Examples.Independence.Clifford+CS.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf)
open import Examples.Independence.Clifford+CS.CliffordRules using (TCPh⁼ ; TCZ′⁼ ; TσCX⁼)
import Examples.Independence.Reasoning Gate as R
open R.Theory arity lhs rhs using (lift)

private
  variable
    n : ℕ
    w v : C.Circuit n

  -- An equation of letter lists, read between words.
  via : {w v : Circuit n} (e : Eqn n) →
        Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (n VRel,_===_) v →
        n ⊢ w ≈ v
  via {n} e p q =
    PB.trans (PP.by-assoc (n VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (n VRel,_===_) q))

  Φ-↑ : (w : C.Circuit n) → Φ (w C.↑) ≡ Φ w ↑
  Φ-↑ [ g ]ʷ  = refl
  Φ-↑ ε       = refl
  Φ-↑ (w • v) = Eq.cong₂ _•_ (Φ-↑ w) (Φ-↑ v)

  -- A circuit two wires up passes a word, letter by letter.
  pass : (x : Circuit n) {a b : Circuit (suc (suc n))} →
         suc (suc n) ⊢ x ↑ ↑ • a ≈ a • x ↑ ↑ → suc (suc n) ⊢ x ↑ ↑ • b ≈ b • x ↑ ↑ →
         suc (suc n) ⊢ x ↑ ↑ • (a • b) ≈ (a • b) • x ↑ ↑
  pass x pa pb =
    PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong pa PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl pb) (PB.sym PB.assoc))))

  passH : (x : Circuit n) → suc (suc n) ⊢ x ↑ ↑ • H ≈ H • x ↑ ↑
  passH x = comm-gate₁-w↑ ⌈ H-gate ⌉ (x ↑)

  passCS : (x : Circuit n) → suc (suc n) ⊢ x ↑ ↑ • CS ≈ CS • x ↑ ↑
  passCS x = comm-gate₂-w↑↑ ⌈ CS-gate ⌉ x

  -- CX = H CS CS H passes a circuit two wires up.
  passCX : (x : Circuit n) → suc (suc n) ⊢ x ↑ ↑ • CX ≈ CX • x ↑ ↑
  passCX x = pass x (passH x) (pass x (passCS x) (pass x (passCS x) (passH x)))

------------------------------------------------------------------------
-- Cliff₂'s axiom instances, derived

tr-ax : n C.VRel, w === v → n ⊢ Φ w ≈ Φ v
tr-ax (C.srel (C.sym C.σ-inv))                    = PB.axiom (srel (sym σ-inv))
tr-ax (C.srel (C.sym (C.σ-nat₁ C.H-gate)))        = PB.axiom (srel (sym (σ-nat₁ H-gate)))
tr-ax (C.srel (C.sym (C.σ-nat₁ C.S-gate)))        = PB.axiom (srel (sym (σ-nat₁ S-gate)))
tr-ax (C.srel (C.sym (C.σ-nat₂ C.⌈ C.CX-gate ⌉))) = via TσCX⁼ refl refl
tr-ax (C.srel (C.sym (C.σ-nat₂ C.swap)))          = PB.axiom (srel (sym (σ-nat₂ swap)))
tr-ax (C.srel (C.ax C.ω⁸ k))                      = PB.axiom (srel (ax ω⁸ k))
tr-ax (C.srel (C.ax C.H² k))                      = PB.axiom (srel (ax H² k))
tr-ax (C.srel (C.ax C.S⁴ k))                      = PB.axiom (srel (ax S⁴ k))
tr-ax (C.srel (C.ax C.E k))                       = PB.axiom (srel (ax E k))
tr-ax (C.srel (C.ax C.CPh k))                     = via TCPh⁼ refl refl
tr-ax (C.srel (C.ax C.B k))                       = PB.axiom (srel (ax B k))
tr-ax (C.srel (C.ax C.CZ k))                      = PB.sym (via TCZ′⁼ refl refl)
tr-ax (C.srel (C.ax C.I k))                       = PB.axiom (srel (ax I k))
tr-ax (C.cong↑ {w = w} {v} a)                     =
  Eq.subst₂ (_ ⊢_≈_) (Eq.sym (Φ-↑ w)) (Eq.sym (Φ-↑ v)) (lift (tr-ax a))
tr-ax (C.comm₁ C.⌈ C.H-gate ⌉ g)                  = comm-gate₁-w↑ ⌈ H-gate ⌉ (Φg g)
tr-ax (C.comm₁ C.⌈ C.S-gate ⌉ g)                  = comm-gate₁-w↑ ⌈ S-gate ⌉ (Φg g)
tr-ax (C.comm₂ C.⌈ C.CX-gate ⌉ g)                 = passCX (Φg g)
tr-ax (C.comm₂ C.swap g)                          = comm-gate₂-w↑↑ swap (Φg g)
tr-ax (C.ω↑=ω C.⌈ C.ω-gate ⌉)                     = PB.axiom (ω↑=ω ⌈ ω-gate ⌉)

-- So every derivation of Cliff₂ is one of CliffCS₂.
tr : PB._≈_ (n C.VRel,_===_) w v → n ⊢ Φ w ≈ Φ v
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
