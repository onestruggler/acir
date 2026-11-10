/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Four-wire circuits as words of placed letters

Translation of `ToPlaced.agda`.  Every letter of a four-wire circuit is a
placed letter (`Placed.PG`): `X`, `CX` and `CCX` shifted up are the letters
on consecutive wires (`Placed.ιX₀` …), and the swap of the wires `k` and
`k + 1` is three CNOTs by rule (3), the middle one with its control and
target exchanged.  So every circuit is the circuit of its word of placed
letters (`pg_ok`), and a statement about words of placed letters is one
about circuits.

Names.  The Agda's `ι*-++` is `ιs_append'` here (`Placed.ιs_append` is the
same fact as an equation of words).  `pg u` is computed letter by letter
from the list of `u`'s letters (`pgL`), so that the kernel evaluates it on a
concrete circuit.
-/
import QCert.XCXCCX4bit.Placed

namespace QCert.XCXCCX4bit.ToPlaced

open QCert QCert.Circuit CircuitProp IndepProp
open Coxeter Coxeter.Circuits Placed

/-! ## The CNOTs pointing up -/

theorem ιCX₀₁ : 4 ⊢ ι (.CXₚ 0 1) ≈ CXd := ι_CX 0 1 (FreeMonoid.of s₀) (by decide) (by decide)

theorem ιCX₁₂ : 4 ⊢ ι (.CXₚ 1 2) ≈ shift CXd := by
  have e := ι_CX 1 2 (ok := by decide) (FreeMonoid.of s₁ * Fc) (by decide) (by decide)
  rw [← Fr_conj] at e
  exact e.trans (((Derivable.refl _).mul CX_up₁.symm).mul (Derivable.refl _))

theorem ιCX₂₃ : 4 ⊢ ι (.CXₚ 2 3) ≈ shift (shift CXd) := by
  have e := ι_CX 2 3 (ok := by decide) (FreeMonoid.of s₂ * (Fc * Fc)) (by decide) (by decide)
  rw [← Fr_conj] at e
  exact e.trans (((Derivable.refl _).mul CX_up₂.symm).mul (Derivable.refl _))

/-! ## Letters -/

/-- The placed letters of a letter; the swap of the wires `k + 1`, `k` is
three CNOTs (rule (3)). -/
def pgl : Gn 4 → List PG
  | .gate0 (.gate g) => nomatch g
  | .gate1 (.gate .X_gate) => [.Xₚ 0]
  | .gate2 (.gate .CX_gate) => [.CXₚ 1 0]
  | .gate2 .swap => [.CXₚ 1 0, .CXₚ 0 1, .CXₚ 1 0]
  | .gate3 (.gate .CCX_gate) => [.CCXₚ 1 2 0]
  | .up (.gate0 (.gate g)) => nomatch g
  | .up (.gate1 (.gate .X_gate)) => [.Xₚ 1]
  | .up (.gate2 (.gate .CX_gate)) => [.CXₚ 2 1]
  | .up (.gate2 .swap) => [.CXₚ 2 1, .CXₚ 1 2, .CXₚ 2 1]
  | .up (.gate3 (.gate .CCX_gate)) => [.CCXₚ 2 3 1]
  | .up (.up (.gate0 (.gate g))) => nomatch g
  | .up (.up (.gate1 (.gate .X_gate))) => [.Xₚ 2]
  | .up (.up (.gate2 (.gate .CX_gate))) => [.CXₚ 3 2]
  | .up (.up (.gate2 .swap)) => [.CXₚ 3 2, .CXₚ 2 3, .CXₚ 3 2]
  | .up (.up (.up (.gate0 (.gate g)))) => nomatch g
  | .up (.up (.up (.gate1 (.gate .X_gate)))) => [.Xₚ 3]
  | .up (.up (.up (.up (.gate0 (.gate g))))) => nomatch g

private theorem one (g : PG) {w : Circ 4} (e : 4 ⊢ ι g ≈ w) : 4 ⊢ w ≈ ιs [g] := by
  show 4 ⊢ w ≈ ι g * 1
  rw [mul_one]; exact e.symm

private theorem three (a b : PG) {u v : Circ 4} (ea : 4 ⊢ ι a ≈ u) (eb : 4 ⊢ ι b ≈ v) :
    4 ⊢ u * v * u ≈ ιs [a, b, a] := by
  show 4 ⊢ u * v * u ≈ ι a * (ι b * (ι a * 1))
  rw [mul_one, ← mul_assoc]
  exact (ea.symm.mul eb.symm).mul ea.symm

/-- Rule (3) on the bottom two wires, read as the swap. -/
private theorem r3₀ : 4 ⊢ σ ≈ CX * CXd * CX := (ax_at SRel.r3 2).symm

private theorem r3₁ : 4 ⊢ shift σ ≈ shift CX * shift CXd * shift CX := by
  have := lift (ax_at (Gate := PGate Gate) (SRel := SRel) SRel.r3 1)
  simp only [map_mul] at this
  exact this.symm

private theorem r3₂ : 4 ⊢ shift (shift σ) ≈ shift (shift CX) * shift (shift CXd) * shift (shift CX) := by
  have := lift (lift (ax_at (Gate := PGate Gate) (SRel := SRel) SRel.r3 0))
  simp only [map_mul] at this
  exact this.symm

theorem pgl_ok : ∀ g : Gn 4, 4 ⊢ FreeMonoid.of g ≈ ιs (pgl g)
  | .gate0 (.gate g) => nomatch g
  | .gate1 (.gate .X_gate) => one (.Xₚ 0) ιX₀
  | .gate2 (.gate .CX_gate) => one (.CXₚ 1 0) ιCX₁₀
  | .gate2 .swap => r3₀.trans (three (.CXₚ 1 0) (.CXₚ 0 1) ιCX₁₀ ιCX₀₁)
  | .gate3 (.gate .CCX_gate) => one (.CCXₚ 1 2 0) ιCCX₁₂₀
  | .up (.gate0 (.gate g)) => nomatch g
  | .up (.gate1 (.gate .X_gate)) => one (.Xₚ 1) ιX₁
  | .up (.gate2 (.gate .CX_gate)) => one (.CXₚ 2 1) ιCX₂₁
  | .up (.gate2 .swap) => r3₁.trans (three (.CXₚ 2 1) (.CXₚ 1 2) ιCX₂₁ ιCX₁₂)
  | .up (.gate3 (.gate .CCX_gate)) => one (.CCXₚ 2 3 1) ιCCX₂₃₁
  | .up (.up (.gate0 (.gate g))) => nomatch g
  | .up (.up (.gate1 (.gate .X_gate))) => one (.Xₚ 2) ιX₂
  | .up (.up (.gate2 (.gate .CX_gate))) => one (.CXₚ 3 2) ιCX₃₂
  | .up (.up (.gate2 .swap)) => r3₂.trans (three (.CXₚ 3 2) (.CXₚ 2 3) ιCX₃₂ ιCX₂₃)
  | .up (.up (.up (.gate0 (.gate g)))) => nomatch g
  | .up (.up (.up (.gate1 (.gate .X_gate)))) => one (.Xₚ 3) ιX₃
  | .up (.up (.up (.up (.gate0 (.gate g))))) => nomatch g

/-! ## Circuits -/

/-- The placed letters of a list of letters. -/
def pgL : List (Gn 4) → List PG
  | [] => []
  | g :: l => pgl g ++ pgL l

/-- The placed letters of a circuit. -/
def pg (u : Circ 4) : List PG := pgL (FreeMonoid.toList u)

theorem pgL_append (l l' : List (Gn 4)) : pgL (l ++ l') = pgL l ++ pgL l' := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.cons_append, pgL, pgL, ih, List.append_assoc]

theorem pg_mul (u v : Circ 4) : pg (u * v) = pg u ++ pg v := by
  simp only [pg, FreeMonoid.toList_mul, pgL_append]

theorem pg_of (g : Gn 4) : pg (FreeMonoid.of g) = pgl g := by
  simp only [pg, FreeMonoid.toList_of, pgL, List.append_nil]

/-- The Agda's `ι*-++`. -/
theorem ιs_append' (xs ys : List PG) : 4 ⊢ ιs (xs ++ ys) ≈ ιs xs * ιs ys := by
  rw [ιs_append]

/-- Every circuit is the circuit of its placed letters. -/
theorem pg_ok (u : Circ 4) : 4 ⊢ u ≈ ιs (pg u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of g u ih =>
    rw [pg_mul, pg_of, ιs_append]
    exact (pgl_ok g).mul ih

end QCert.XCXCCX4bit.ToPlaced
