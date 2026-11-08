/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: completeness

Translation of `Completeness.agda`: `R₁⁺` presents `O(8, 𝔻)`, given the
Coxeter relations for the circuits `T d` and a few circuit identities
derived from Figure 4 (the structure `Derived`, which `Derived.lean` fills
in).

Completeness by the encoding and the decoding: a circuit `w` has the value
of its encoding, two circuits with the same value have encodings equal by
Table 1 (Li, Ross and Selinger), the decoding respects Table 1 (`Decode`),
and decoding an encoded circuit gives it back (`Good`): for the circuits
`T d`, `(-1)_[0]` and `NK` by the aliases of `Decode`, and for each gate
from those along Figure 4's definitions, `Good` being closed under products
and, by soundness, under `R₁⁺`.
-/
import QCert.ToffoliHadamardRS.Decode
import QCert.ToffoliHadamardRS.SoundnessH
import QCert.ToffoliHadamardRS.StdMatrices
import QCert.LiRossSelinger.Theorem

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen sem)

/-! ## What the search derives -/

/-- The identities that completeness needs (the Agda's record `Derived`). -/
structure Derived : Prop where
  coxeter : Coxeter R1plus
  invol : ∀ g : G₁, Derivable R1plus (FreeMonoid.of g * FreeMonoid.of g) 1
  cx12r : Derivable R1plus CX12 (T 2 * CCX01)
  cx02r : Derivable R1plus CX02 (T 4 * CCX01)
  x2r : Derivable R1plus X2 (T 0 * CCX01 * CX12 * CX02)
  ccx02r : Derivable R1plus CCX02 (CX12 * T 5 * CX12)
  cx21r : Derivable R1plus CX21 (CX12 * T 1 * CX12 * CCX02)
  cx01r : Derivable R1plus CX01 (SW12 * CX02 * SW12)
  ccx12r : Derivable R1plus CCX12 (CX02 * CX01 * T 3 * CX02 * CX01)
  cx10r : Derivable R1plus CX10 (CCX12 * CX12 * CCX12 * CX12)
  cx20r : Derivable R1plus CX20 (SW01 * CX21 * SW01)
  x0r : Derivable R1plus X0 (SW02 * X2 * SW02)
  cczr : Derivable R1plus CCZw (X2 * X1 * X0 * m0 * X0 * X1 * X2)

namespace Complete

variable (D : Derived)
include D

/-! ## Decoding an encoded circuit -/

/-- Two-level words with the same value decode to equivalent circuits. -/
theorem lrs {u v : Word (Gen 8)} (h : FreeMonoid.lift (sem 8) u = FreeMonoid.lift (sem 8) v) :
    Derivable R1plus (decW u) (decW v) :=
  dec_cong D.coxeter (LiRossSelinger.complete 8 h)

/-- Decoding the encoding gives the circuit back. -/
def Good (w : Word G₁) : Prop := Derivable R1plus (decW (encW w)) w

omit D in
theorem Good_mul {u v : Word G₁} (gu : Good u) (gv : Good v) : Good (u * v) := by
  unfold Good; rw [map_mul, map_mul]; exact gu.mul gv

theorem Good_der {w w' : Word G₁} (e : Derivable R1plus w w') (g : Good w') : Good w :=
  (lrs D (sound1plus_der e)).trans (g.trans e.symm)

omit D in
theorem ax {w v : Word G₁} (h : R1plus w v) : Derivable R1plus w v := Derivable.of h

theorem via_std (w : Word G₁) (s : Std)
    (h : semO w = FreeMonoid.lift (sem 8) (FreeMonoid.of (std s))) (e : al s = w) : Good w := by
  have := (lrs D h).trans (al_ok D.coxeter s)
  rw [e] at this
  exact this

theorem good_T : ∀ i : ℕ, Good (T i)
  | 0 => via_std D (T 0) .x01 mT0 rfl
  | 1 => via_std D (T 1) .x12 mT1 rfl
  | 2 => via_std D (T 2) .x23 mT2 rfl
  | 3 => via_std D (T 3) .x34 mT3 rfl
  | 4 => via_std D (T 4) .x45 mT4 rfl
  | 5 => via_std D (T 5) .x56 mT5 rfl
  | _ + 6 => via_std D (T 6) .x67 mT6 rfl

theorem good_m0 : Good m0 := via_std D m0 .m0s mm0 rfl

theorem good_NK : Good NKw := al_ok D.coxeter .k0123

/-! Along the definitions of Figure 4. -/

theorem g_CCX01 : Good CCX01 := good_T D 6

theorem g_CX12 : Good CX12 :=
  Good_der D (D.cx12r)
    (Good_mul (good_T D 2) (g_CCX01 D))

theorem g_CX02 : Good CX02 :=
  Good_der D (D.cx02r)
    (Good_mul (good_T D 4) (g_CCX01 D))

theorem g_X2 : Good X2 :=
  Good_der D (D.x2r)
    (Good_mul (Good_mul (Good_mul (good_T D 0) (g_CCX01 D)) (g_CX12 D)) (g_CX02 D))

theorem g_CCX02 : Good CCX02 :=
  Good_der D (D.ccx02r)
    (Good_mul (Good_mul (g_CX12 D) (good_T D 5)) (g_CX12 D))

theorem g_CX21 : Good CX21 :=
  Good_der D (D.cx21r)
    (Good_mul (Good_mul (Good_mul (g_CX12 D) (good_T D 1)) (g_CX12 D)) (g_CCX02 D))

theorem g_SW12 : Good SW12 :=
  Good_der D (ax (.fig4 .r8))
    (Good_mul (Good_mul (g_CX12 D) (g_CX21 D)) (g_CX12 D))

theorem g_CX01 : Good CX01 :=
  Good_der D (D.cx01r)
    (Good_mul (Good_mul (g_SW12 D) (g_CX02 D)) (g_SW12 D))

theorem g_CCX12 : Good CCX12 :=
  Good_der D (D.ccx12r)
    (Good_mul (Good_mul (Good_mul (Good_mul (g_CX02 D) (g_CX01 D)) (good_T D 3)) (g_CX02 D)) (g_CX01 D))

theorem g_CX10 : Good CX10 :=
  Good_der D (D.cx10r)
    (Good_mul (Good_mul (Good_mul (g_CCX12 D) (g_CX12 D)) (g_CCX12 D)) (g_CX12 D))

theorem g_SW01 : Good SW01 :=
  Good_der D (ax (.fig4 .r13))
    (Good_mul (Good_mul (g_CX01 D) (g_CX10 D)) (g_CX01 D))

theorem g_CX20 : Good CX20 :=
  Good_der D (D.cx20r)
    (Good_mul (Good_mul (g_SW01 D) (g_CX21 D)) (g_SW01 D))

theorem g_SW02 : Good SW02 :=
  Good_der D (ax (.fig4 .r10))
    (Good_mul (Good_mul (g_CX02 D) (g_CX20 D)) (g_CX02 D))

theorem g_X0 : Good X0 :=
  Good_der D (D.x0r)
    (Good_mul (Good_mul (g_SW02 D) (g_X2 D)) (g_SW02 D))

theorem g_X1 : Good X1 :=
  Good_der D (ax (.fig4 .r2))
    (Good_mul (Good_mul (Good_mul (g_CX01 D) (g_X0 D)) (g_CX01 D)) (g_X0 D))

theorem g_K12 : Good K12 :=
  Good_der D (ax (.rK .rK))
    (Good_mul (Good_mul (Good_mul (g_X0 D) (good_NK D)) (g_X0 D)) (good_NK D))

theorem g_CZ01 : Good CZ01 :=
  Good_der D (ax (.fig4 .r1))
    (Good_mul (Good_mul (g_K12 D) (g_CX01 D)) (g_K12 D))

theorem g_Z0 : Good Z0 :=
  Good_der D (ax (.fig4 .r3))
    (Good_mul (Good_mul (Good_mul (g_CZ01 D) (g_CX01 D)) (g_CZ01 D)) (g_CX01 D))

theorem g_Z1 : Good Z1 :=
  Good_der D (ax (.fig4 .r4))
    (Good_mul (Good_mul (g_K12 D) (g_X1 D)) (g_K12 D))

theorem g_K01 : Good K01 :=
  Good_der D (ax (.fig4 .r11))
    (Good_mul (Good_mul (g_SW02 D) (g_K12 D)) (g_SW02 D))

theorem g_Z2 : Good Z2 :=
  Good_der D (ax (.fig4 .r16))
    (Good_mul (Good_mul (g_SW02 D) (g_Z0 D)) (g_SW02 D))

theorem g_CZ02 : Good CZ02 :=
  Good_der D (ax (.fig4 .r18))
    (Good_mul (Good_mul (g_SW12 D) (g_CZ01 D)) (g_SW12 D))

theorem g_CZ12 : Good CZ12 :=
  Good_der D (ax (.fig4 .r19))
    (Good_mul (Good_mul (g_SW01 D) (g_CZ02 D)) (g_SW01 D))

theorem g_CCZ : Good CCZw :=
  Good_der D (D.cczr)
    (Good_mul (Good_mul (Good_mul (Good_mul (Good_mul (Good_mul (g_X2 D) (g_X1 D)) (g_X0 D)) (good_m0 D)) (g_X0 D)) (g_X1 D)) (g_X2 D))

theorem good_gate : ∀ g : G₁, Good (FreeMonoid.of g)
  | .X₀ => g_X0 D
  | .X₁ => g_X1 D
  | .X₂ => g_X2 D
  | .Z₀ => g_Z0 D
  | .Z₁ => g_Z1 D
  | .Z₂ => g_Z2 D
  | .CX₀₁ => g_CX01 D
  | .CX₀₂ => g_CX02 D
  | .CX₁₀ => g_CX10 D
  | .CX₁₂ => g_CX12 D
  | .CX₂₀ => g_CX20 D
  | .CX₂₁ => g_CX21 D
  | .CZ₀₁ => g_CZ01 D
  | .CZ₀₂ => g_CZ02 D
  | .CZ₁₂ => g_CZ12 D
  | .CCX₀₁ => g_CCX01 D
  | .CCX₀₂ => g_CCX02 D
  | .CCX₁₂ => g_CCX12 D
  | .K₀₁ => g_K01 D
  | .K₁₂ => g_K12 D
  | .SW₀₁ => g_SW01 D
  | .SW₀₂ => g_SW02 D
  | .SW₁₂ => g_SW12 D
  | .NK => good_NK D
  | .CCZ => g_CCZ D

theorem good (w : Word G₁) : Good w := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of g w ih => exact Good_mul (good_gate D g) ih

/-! ## Completeness -/

theorem complete {w v : Word G₁} (h : semO w = semO v) : Derivable R1plus w v :=
  (good D w).symm.trans ((lrs D h).trans (good D v))

end Complete

end QCert.ToffoliHadamardRS
