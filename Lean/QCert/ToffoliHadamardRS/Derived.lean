/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the derived identities

Translation of `Derived.agda` (which the Agda's `gen/mk_derived.py` writes):
the identities that `Completeness` takes as the structure `Derived`, at
level 1: the Coxeter relations and the identities of `Toffoli.Lemmas`,
derived from Figure 4 at level 0 and lifted, and two about `CCZ`, derived
from Figure 7's (83).  Written by hand here: it is short, and its two
derivations are those of the Agda generator.
-/
import QCert.ToffoliHadamardRS.Completeness
import QCert.ToffoliHadamardRS.Toffoli.Coxeter

namespace QCert.ToffoliHadamardRS

open Gate Engine

namespace DerivedEqns

/-- The engine at level 1, for `R₁⁺`. -/
abbrev Eqn1 : Type := Eqn R1plus

abbrev d1 (l r : List G₁) (ss : List (Step R1plus)) (h : check ss l r = true) : Eqn1 :=
  derive l r ss h

noncomputable section

def sq0 : Eqn1 := ax (R1plus.fig4 R0.r21)
def sq1 : Eqn1 := ofDer (lift01 (Toffoli.x1sq.toDer (w := X1 * X1) (v := 1) rfl rfl))
def sq2 : Eqn1 := ofDer (lift01 (Toffoli.x2sq.toDer (w := X2 * X2) (v := 1) rfl rfl))
def e83 : Eqn1 := ax (R1plus.fig7 Fig7.r83)

/-- `CCZ`, from `(-1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀`. -/
def cczr' : Eqn1 := d1
  [X₂, X₁, X₀, X₀, X₁, X₂, CCZ, X₂, X₁, X₀, X₀, X₁, X₂]
  [CCZ]
  [rw 2 sq0, rw 1 sq1, rw 0 sq2, rw 3 sq0, rw 2 sq1, rw 1 sq2]
  (by decide +kernel)

def cczsq : Eqn1 := d1
  [CCZ, CCZ]
  []
  [rw 0 cczr'.symm, rw 13 cczr'.symm, rw 12 sq2, rw 11 sq1, rw 10 sq0, rw 3 e83, rw 2 sq0,
    rw 1 sq1, rw 0 sq2]
  (by decide +kernel)

end

end DerivedEqns

open DerivedEqns

/-- Every letter of `Σ₁` is an involution modulo `R₁⁺`. -/
theorem invol1 : ∀ g : G₁, Derivable R1plus (FreeMonoid.of g * FreeMonoid.of g) 1
  | .X₀ => lift01 (Toffoli.invol .X₀)
  | .X₁ => lift01 (Toffoli.invol .X₁)
  | .X₂ => lift01 (Toffoli.invol .X₂)
  | .Z₀ => lift01 (Toffoli.invol .Z₀)
  | .Z₁ => lift01 (Toffoli.invol .Z₁)
  | .Z₂ => lift01 (Toffoli.invol .Z₂)
  | .CX₀₁ => lift01 (Toffoli.invol .CX₀₁)
  | .CX₀₂ => lift01 (Toffoli.invol .CX₀₂)
  | .CX₁₀ => lift01 (Toffoli.invol .CX₁₀)
  | .CX₁₂ => lift01 (Toffoli.invol .CX₁₂)
  | .CX₂₀ => lift01 (Toffoli.invol .CX₂₀)
  | .CX₂₁ => lift01 (Toffoli.invol .CX₂₁)
  | .CZ₀₁ => lift01 (Toffoli.invol .CZ₀₁)
  | .CZ₀₂ => lift01 (Toffoli.invol .CZ₀₂)
  | .CZ₁₂ => lift01 (Toffoli.invol .CZ₁₂)
  | .CCX₀₁ => lift01 (Toffoli.invol .CCX₀₁)
  | .CCX₀₂ => lift01 (Toffoli.invol .CCX₀₂)
  | .CCX₁₂ => lift01 (Toffoli.invol .CCX₁₂)
  | .K₀₁ => lift01 (Toffoli.invol .K₀₁)
  | .K₁₂ => lift01 (Toffoli.invol .K₁₂)
  | .SW₀₁ => lift01 (Toffoli.invol .SW₀₁)
  | .SW₀₂ => lift01 (Toffoli.invol .SW₀₂)
  | .SW₁₂ => lift01 (Toffoli.invol .SW₁₂)
  | .NK => Derivable.of (R1plus.fig7 Fig7.r84)
  | .CCZ => cczsq.toDer rfl rfl

/-- A level-0 derivation, lifted, between the same words at level 1. -/
theorem lift01' {w v : Word GD} {w' v' : Word G₁} (h : Derivable (R0 (k := 0)) w v)
    (hw : upW w = w' := by simp [upW_T, Gate.up]) (hv : upW v = v' := by simp [upW_T, Gate.up]) :
    Derivable R1plus w' v' :=
  hw ▸ hv ▸ lift01 h

/-- The identities of `Completeness`. -/
theorem derived : Derived where
  coxeter := Toffoli.coxeter1
  invol := invol1
  cx12r := lift01' (Toffoli.cx12r.toDer (w := CX12) (v := T 2 * CCX01) rfl rfl)
  cx02r := lift01' (Toffoli.cx02r.toDer (w := CX02) (v := T 4 * CCX01) rfl rfl)
  x2r := lift01' (Toffoli.x2r.toDer (w := X2) (v := T 0 * CCX01 * CX12 * CX02) rfl rfl)
  ccx02r := lift01' (Toffoli.ccx02r.toDer (w := CCX02) (v := CX12 * T 5 * CX12) rfl rfl)
  cx21r := lift01' (Toffoli.cx21r.toDer (w := CX21) (v := CX12 * T 1 * CX12 * CCX02) rfl rfl)
  cx01r := lift01' (Toffoli.cx01r.toDer (w := CX01) (v := SW12 * CX02 * SW12) rfl rfl)
  ccx12r := lift01' (Toffoli.ccx12r.toDer (w := CCX12) (v := CX02 * CX01 * T 3 * CX02 * CX01)
    rfl rfl)
  cx10r := lift01' (Toffoli.cx10r.toDer (w := CX10) (v := CCX12 * CX12 * CCX12 * CX12) rfl rfl)
  cx20r := (lift01' (Toffoli.cx20def.toDer (w := SW01 * CX21 * SW01) (v := CX20) rfl rfl)).symm
  x0r := lift01' (Toffoli.x0r.toDer (w := X0) (v := SW02 * X2 * SW02) rfl rfl)
  cczr := (cczr'.toDer (w := X2 * X1 * X0 * m0 * X0 * X1 * X2) (v := CCZw) rfl rfl).symm

end QCert.ToffoliHadamardRS
