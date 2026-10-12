------------------------------------------------------------------------
-- Presentations of groups
--
-- CNOTdihe₂ is complete for the matrix semantics (Theorem 22, by
-- transfer)
--
-- Section 4 of Blake's paper: a complete presentation transfers to
-- another over the same gates once each of its axioms is derivable in
-- the other.  Here the source is Amy, Chen and Ross's (Examples.Groups.
-- CNOT+Dihedral, complete at every width), the gates and the swap are
-- the same letter for letter (ι), and so are the axioms: (R1), (R6),
-- (R7), (R9), (R10), (R12) and (R13) are axioms of CNOTdihe₂ — (R9) and
-- (R13) up to re-bracketing — the swap rules are the symmetry rules,
-- and (R2), (R3), (R4), (R5), (R8) and (R11) are derived in
-- CNOT-Dihedral.Derived.  Their words are read in operator order and
-- ours in diagram order, which is harmless: every gate is a symmetric
-- matrix, so the two readings of a word are transposes (Bridge), and
-- an equation holds in one exactly when it holds in the other.  Two
-- circuits with the same matrix then have the same operator, hence are
-- equal by Amy, Chen and Ross's rules, hence by CNOTdihe₂.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Completeness where

open import Data.Nat using (ℕ)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₃₊ ; ₄₊)

import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.CNOT+Dihedral.Syntactics as ACR
import Examples.Groups.CNOT+Dihedral.Completeness as ACRC

open import Examples.Independence.CNOT-Dihedral.Syntactics
import Examples.Independence.CNOT-Dihedral.Semantics as Sem
import Examples.Independence.CNOT-Dihedral.Derived as Der
open import Examples.Independence.CNOT-Dihedral.Bridge using (ι⁻ ; same-operator)
open import Examples.Independence.Reasoning Gate
open Theory arity lhs rhs using (ax-at ; sym-rule ; lift)

private
  variable
    k n : ℕ
    w v : ACR.Circuit n

------------------------------------------------------------------------
-- Letters: theirs to ours

ιg : ACR.Gate k → PGate k
ιg ACR.ω-gate    = ⌈ ω-gate ⌉
ιg ACR.X-gate    = ⌈ X-gate ⌉
ιg ACR.T-gate    = ⌈ T-gate ⌉
ιg ACR.CNOT-gate = ⌈ CX-gate ⌉
ιg ACR.SWAP-gate = swap

ι : ACR.Gen n → Gen n
ι (ACR.gate₀ g) = gate₀ (ιg g)
ι (ACR.gate₁ g) = gate₁ (ιg g)
ι (ACR.gate₂ g) = gate₂ (ιg g)
ι (g ACR.↥)     = ι g ↥

-- The circuit of a word of theirs.
D : ACR.Circuit n → Circuit n
D = wmap ι

D-↑ : (w : ACR.Circuit n) → D (w ACR.↑) ≡ D w ↑
D-↑ [ g ]ʷ  = refl
D-↑ ε       = refl
D-↑ (w • v) = Eq.cong₂ _•_ (D-↑ w) (D-↑ v)

-- ι undoes ι⁻.
ι-ι⁻ : (g : Gen n) → ι (ι⁻ g) ≡ g
ι-ι⁻ (gate₀ ⌈ ω-gate ⌉)  = refl
ι-ι⁻ (gate₁ ⌈ X-gate ⌉)  = refl
ι-ι⁻ (gate₁ ⌈ T-gate ⌉)  = refl
ι-ι⁻ (gate₂ ⌈ CX-gate ⌉) = refl
ι-ι⁻ (gate₂ swap)        = refl
ι-ι⁻ (g ↥)               = Eq.cong _↥ (ι-ι⁻ g)

D-ι⁻ : (w : Circuit n) → D (wmap ι⁻ w) ≡ w
D-ι⁻ [ g ]ʷ  = Eq.cong [_]ʷ (ι-ι⁻ g)
D-ι⁻ ε       = refl
D-ι⁻ (w • v) = Eq.cong₂ _•_ (D-ι⁻ w) (D-ι⁻ v)

------------------------------------------------------------------------
-- Their axioms, derived in CNOTdihe₂

D-rel : n ACR.SRel, w === v → n ⊢ D w ≈ D v
D-rel (ACR.R₁ {n = m})  = ax-at X² m
D-rel ACR.R₂            = Der.R₂
D-rel ACR.R₃            = Der.R₃
D-rel ACR.R₄            = Der.R₄
D-rel ACR.R₅            = Der.R₅
D-rel (ACR.R₆ {n = m})  = ax-at I m
D-rel (ACR.R₇ {n = m})  = ax-at T⁸ m
D-rel ACR.R₈            = Der.R₈
D-rel (ACR.R₉ {n = m})  =
  PB.trans (ax-at C²T m) (PP.by-assoc ((₃₊ m) VRel,_===_) refl)
D-rel (ACR.R₁₀ {n = m}) = ax-at ω⁸ m
D-rel ACR.R₁₁           = Der.R₁₁
D-rel (ACR.R₁₂ {n = m}) = ax-at CPh m
D-rel (ACR.R₁₃ {n = m}) =
  PB.trans (ax-at C³T m) (PP.by-assoc ((₄₊ m) VRel,_===_) refl)
D-rel ACR.swap-order    = sym-rule σ-inv
D-rel ACR.swap-braid    = sym-rule (σ-nat₂ swap)
D-rel ACR.swap-X        = sym-rule (σ-nat₁ X-gate)
D-rel ACR.swap-T        = sym-rule (σ-nat₁ T-gate)
D-rel ACR.swap-CNOT     = sym-rule (σ-nat₂ ⌈ CX-gate ⌉)

-- With the structural rules.
D-ax : n ACR.VRel, w === v → n ⊢ D w ≈ D v
D-ax (ACR.srel r)              = D-rel r
D-ax (ACR.cong↑ {w = w} {v} r) =
  Eq.subst₂ (_ ⊢_≈_) (Eq.sym (D-↑ w)) (Eq.sym (D-↑ v)) (lift (D-ax r))
D-ax (ACR.comm₁ h g)           = PB.axiom (comm₁ (ιg h) (ι g))
D-ax (ACR.comm₂ h g)           = PB.axiom (comm₂ (ιg h) (ι g))
D-ax (ACR.ω↑=ω h)              = PB.axiom (ω↑=ω (ιg h))

-- So every derivation of theirs.
D-≈ : n ACR.⊢ w ≈ v → n ⊢ D w ≈ D v
D-≈ PB.refl        = PB.refl
D-≈ (PB.sym e)     = PB.sym (D-≈ e)
D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
D-≈ (PB.cong e f)  = PB.cong (D-≈ e) (D-≈ f)
D-≈ PB.assoc       = PB.assoc
D-≈ PB.left-unit   = PB.left-unit
D-≈ PB.right-unit  = PB.right-unit
D-≈ (PB.axiom a)   = D-ax a

------------------------------------------------------------------------
-- Completeness

-- Circuits with the same matrix are equal by CNOTdihe₂, at every
-- width.
complete : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
complete {n} {w} {v} e =
  Eq.subst₂ (n ⊢_≈_) (D-ι⁻ w) (D-ι⁻ v) (D-≈ (ACRC.complete (same-operator w v e)))

-- So the rule set presents the semantics: two circuits are equal by
-- CNOTdihe₂ exactly when their matrices are.
sound-complete : {w v : Circuit n} → (n ⊢ w ≈ v) ⇔ (Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧)
sound-complete = mk⇔ Sem.sound complete
