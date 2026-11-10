/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The rules (1)–(7) for circuits over X, CX and CCX, and the half of their equivalence with the translated relation that the semantics gives

Translation of `Theory.agda`.  These are the rules r1, …, r7 of Figure 1 of
*Block Normal Forms and Certified Equations for Four-Bit Reversible
Circuits*, word for word, with the swap `σ` of that figure the gate `Ex`
here: `Ex` is the designated swap of `CircuitProp`, so the relation
`VRel TRel n` consists of the seven rules, the laws of the symmetry and the
structural rules.

The second Reidemeister–Schreier step of this folder is between
`Syntactics`' relation (Lafont's relations read on the cycles `Ω i`, and the
six gate rules) and this one, over the same gates, the translations being
the identity.  This module has the half that needs no derivation: every
rule here holds for functions on states (`T_sound`), so on four wires it
follows from `Syntactics`' relation, which is complete (`t_to_s`, the Agda's
`t⇒s`).  The other half, each of the rules `order`, `near`, `far`, `apart`
and `gate_…` derived from r1, …, r7, is `Equivalence`.

Names.  The Agda's `_TRel,_===_` is `TRel`; its module `T` (the relation
lifted to a PROP) is `CircuitProp`'s lemmas at `TRel`, and `n T.⊢ w ≈ v` is
`n ⊢ᵀ w ≈ v`; `CX↓`, `CCX↓` are `CXd`, `CCXd`; `X↑≈`, `CX↑≈`, `CCX↑≈` are
`X_up`, `CX_up`, `CCX_up`.
-/
import QCert.Alt16RevCir.Presentation

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp

variable {n : ℕ}

/-! ## Gates in other positions -/

/-- `CX` with its control on wire 0 and its target on wire 1. -/
abbrev CXd : Circ (n + 2) := Ex * CX * Ex

/-- `CCX` with its controls on wires 2 and 0 and its target on wire 1. -/
abbrev CCXd : Circ (n + 3) := Ex * CCX * Ex

/-- `CCX` with its controls on wires 3 and 2 and its target on wire 0. -/
abbrev CCX₃₂₀ : Circ (n + 4) := Ex * shift CCX * Ex

/-! ## The rules -/

/-- The seven rules, each on the wires it is drawn on. -/
inductive TRel : CRel Gate
  | r1 : TRel 1 (X * X) 1
  | r2 : TRel 2 (CX * shift X * CX * shift X) X
  | r3 : TRel 2 (CX * CXd * CX) Ex
  | r4 : TRel 3 (CCX * shift (shift X) * CCX * shift (shift X)) CX
  | r5 : TRel 3 (shift Ex * CCX * shift Ex) CCX
  | r6 : TRel 3 (CXd * CCX * CXd) (CCXd * CCX * CCXd)
  | r7 : TRel 4 (shift CCX * CX * shift CCX) (CCX₃₂₀ * CX)

/-- The congruence the rules generate with the swap rules and the structural
rules, at width `n` (the Agda's `n T.⊢ w ≈ v`). -/
scoped notation:50 n:51 " ⊢ᵀ " w:51 " ≈ " v:51 => CircuitProp.Der TRel n w v

/-! ## A gate one wire up, between swaps

By the naturality of the swap, as `Lemmas` has it for `Syntactics`'
relation (with `Lemmas.conjugate`, which is stated over any relation). -/

theorem X_up : (n + 2) ⊢ᵀ shift X ≈ Ex * X * Ex :=
  conjugate σ_invol (sym_rule (Sym.σ_nat₁ Gate.X_gate))

theorem CX_up : (n + 3) ⊢ᵀ shift CX ≈ σcInv 2 * CX * σc 2 :=
  conjugate (σInvσ 2) (sym_rule (Sym.σ_nat₂ Gate.CX_gate))

theorem CCX_up : (n + 4) ⊢ᵀ shift CCX ≈ σcInv 3 * CCX * σc 3 :=
  conjugate (σInvσ 3) (sym_rule (Sym.σ_nat₃ Gate.CCX_gate))

/-! ## Soundness for functions on states -/

private theorem trel_sound : ∀ {n : ℕ} {w v : Circ n}, TRel n w v → sem w ≐ sem v
  | _, _, _, .r1 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r2 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r3 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r4 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r5 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r6 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r7 => same_sound _ _ (by decide +kernel)

/-- The swap rules and the structural rules are those of `Syntactics`'
relation, where `Semantics` has them. -/
theorem T_ax_sound {w v : Circ n} (a : VRel TRel n w v) : sem w ≐ sem v :=
  lift_sound (fun r => match r with
    | .srel r => trel_sound r
    | .σrel s => sym_sound s) a

theorem T_sound {w v : Circ n} (d : n ⊢ᵀ w ≈ v) : sem w ≐ sem v :=
  con_sound T_ax_sound d

/-! ## From the rules to the translated relations, on four wires -/

/-- Every consequence of r1, …, r7 on four wires follows from `Syntactics`'
relation: it is true of functions on states. -/
theorem t_to_s {w v : Circ 4} (e : 4 ⊢ᵀ w ≈ v) : 4 ⊢ w ≈ v :=
  complete (T_sound e)

end QCert.Alt16RevCir
