/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-qubit completeness from Theorem 4.4 (Section 7.2)

The back-and-forth argument of Section 7.2 between two-qubit circuits and
words over the generators `𝒢₄` of `O₄(ℤ[1/√2])` (Hadamard-Π's alphabet,
`QCert.HadamardPi.Gen 4`, indices `0, …, 3`):

* the encoding `E` of Definition 7.2 (`enc`, on the gates of a two-wire
  circuit), which preserves the semantics (`wordMat_encW`): the basis state
  `|x, y⟩` (`x` on the upper wire, wire `1`) is the index `2x + y`;
* the decoding `D` of Definition 7.3 (`dec`), on the generators with
  increasing indices;
* Lemma 7.4, `D (E C) = C` in the theory (`lemma_7_4`), proved;
* Lemma 7.6 (two-qubit completeness) from Theorem 4.4 (completeness of
  Figure 6 for `𝒢₄`) and Lemma 7.5 (`D` maps the equations of Figure 6 to
  derivable equations), both taken as hypotheses (`complete_two_of`).
-/
import QCert.RealCliffordCH.OneQubit
import QCert.HadamardPi.Semantics

namespace QCert.RealCliffordCH

open Circuit Matrix

namespace Two

/-- The generators `𝒢₄`. -/
abbrev G4 := QCert.HadamardPi.Gen 4

/-! ## Shortcuts on two wires (Figure 3) -/

/-- CNOT, control on wire 1, target wire 0. -/
def cnot : Circ 2 := drawn [h, cz, h]

/-- CNOT with a white control on wire 1. -/
def cnotw : Circ 2 := drawn [shift x, cnot, shift x]

/-- CNOT, control on wire 0, target wire 1. -/
def cnot10 : Circ 2 := drawn [swap, cnot, swap]

/-- CNOT with a white control on wire 0, target wire 1. -/
def cnot10w : Circ 2 := drawn [x, cnot10, x]

/-- `CH`, control on wire 0, `H` on wire 1. -/
def ch10 : Circ 2 := drawn [swap, ch, swap]

/-- `CH` with a white control on wire 0, `H` on wire 1. -/
def ch10w : Circ 2 := drawn [x, ch10, x]

/-- `CZ` with white controls on both wires. -/
def czww : Circ 2 := drawn [shift x, x, cz, shift x, x]

/-- `CZ` with a white control on wire 0. -/
def czw0 : Circ 2 := drawn [x, cz, x]

/-! ## Definition 7.3: the decoding -/

/-- Definition 7.3, on the generators with increasing indices. -/
def dec : G4 → Circ 2
  | .Z a => match a.val with
    | 0 => czww
    | 1 => czw
    | 2 => czw0
    | _ => cz
  | .X a b _ => match a.val, b.val with
    | 0, 1 => cnotw
    | 0, 2 => cnot10w
    | 0, 3 => drawn [swap, x, shift x]
    | 1, 2 => swap
    | 1, 3 => cnot10
    | _, _ => cnot
  | .H a b _ => match a.val, b.val with
    | 0, 1 => chw
    | 0, 2 => ch10w
    | 0, 3 => drawn [cnot10, chw, cnot10]
    | 1, 2 => drawn [cnot, ch10, cnot]
    | 1, 3 => ch10
    | _, _ => ch

/-- The decoding of words. -/
def decW : Word G4 →* Circ 2 := FreeMonoid.lift dec

/-! ## Definition 7.2: the encoding -/

/-- Definition 7.2 on the generators of two-wire circuits: `H` and `Z` on
wire 0 (`E₁,₀`) and on wire 1 (`E₀,₁`), `CZ` and `CH` (`E₀,₀`). -/
def enc : Gen Gate 2 → Word G4
  | .gate0 c => nomatch c
  | .gate1 .H => FreeMonoid.of (.H 0 1 (by decide)) * FreeMonoid.of (.H 2 3 (by decide))
  | .gate1 .Z => FreeMonoid.of (.Z 1) * FreeMonoid.of (.Z 3)
  | .gate2 .CZ => FreeMonoid.of (.Z 3)
  | .gate2 .CH => FreeMonoid.of (.H 2 3 (by decide))
  | .up (.gate1 .H) => FreeMonoid.of (.H 0 2 (by decide)) * FreeMonoid.of (.H 1 3 (by decide))
  | .up (.gate1 .Z) => FreeMonoid.of (.Z 2) * FreeMonoid.of (.Z 3)
  | .up (.gate0 c) => nomatch c

/-- The encoding of circuits. -/
def encW : Circ 2 →* Word G4 := FreeMonoid.lift enc

/-! ## The encoding preserves the semantics -/

/-- The index of a two-wire basis state, `2 · (wire 1) + (wire 0)`. -/
def e4 : State 2 2 ≃ Fin 4 := finFunctionFinEquiv (m := 2) (n := 2)

/-- A two-wire operator as a `4 × 4` matrix, `|x, y⟩` at index `2x + y`. -/
def ri {R : Type*} (M : Op R 2 2) : Matrix (Fin 4) (Fin 4) R :=
  M.submatrix e4.symm e4.symm

theorem ri_mul {R : Type*} [CommRing R] (M N : Op R 2 2) : ri (M * N) = ri M * ri N :=
  (submatrix_mul_equiv M N _ _ _).symm

theorem ri_one {R : Type*} [CommRing R] : ri (1 : Op R 2 2) = 1 := submatrix_one_equiv _

theorem levelMat_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ}
    (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R) :
    (levelMat f M).map φ = levelMat f (M.map φ) := by
  have he : (embedMat (R := R) f).map φ = embedMat f := by
    ext i k; simp only [embedMat, map_apply]; split_ifs <;> simp
  simp only [levelMat]
  rw [Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    transpose_map, he]

theorem genMat_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (s : R) (g : G4) :
    (QCert.HadamardPi.genMat s g).map φ = QCert.HadamardPi.genMat (φ s) g := by
  cases g with
  | Z a =>
    rw [QCert.HadamardPi.genMat, QCert.HadamardPi.genMat, levelMat_map]
    congr 1; ext i j; fin_cases i; fin_cases j; simp [QCert.HadamardPi.Zmat]
  | X a b _ =>
    rw [QCert.HadamardPi.genMat, QCert.HadamardPi.genMat, levelMat_map]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [QCert.HadamardPi.Xmat]
  | H a b _ =>
    rw [QCert.HadamardPi.genMat, QCert.HadamardPi.genMat, levelMat_map]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [QCert.HadamardPi.Hmat]

theorem wordMat_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (s : R)
    (u : Word G4) :
    (QCert.HadamardPi.wordMat s u).map φ = QCert.HadamardPi.wordMat (φ s) u := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp [Matrix.map_one _ (map_zero φ) (map_one φ)]
  | mul_of g u ih =>
    rw [map_mul, map_mul, Matrix.map_mul, ih]
    congr 1
    exact genMat_map φ s g

/-- The encoding of each gate has the gate's matrix (over ℚ(√2)). -/
theorem enc_gen (g : Gen Gate 2) :
    QCert.HadamardPi.wordMat QSqrt2.invSqrt2 (enc g) = ri (opsQ.gen g) := by
  match g with
  | .gate0 c => exact nomatch c
  | .gate1 .H => decide +kernel
  | .gate1 .Z => decide +kernel
  | .gate2 .CZ => decide +kernel
  | .gate2 .CH => decide +kernel
  | .up (.gate1 .H) => decide +kernel
  | .up (.gate1 .Z) => decide +kernel
  | .up (.gate0 c) => exact nomatch c

/-- The encoding preserves the semantics (over ℚ(√2)). -/
theorem wordMat_encW (w : Circ 2) :
    QCert.HadamardPi.wordMat QSqrt2.invSqrt2 (encW w) = ri (opsQ.eval 2 w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [ri_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih, ri_mul]
    congr 1
    show QCert.HadamardPi.wordMat _ (enc g) = ri (opsQ.gen g)
    exact enc_gen g

/-- Circuits with the same semantics have encodings with the same value in
`O₄(ℤ[1/√2])`. -/
theorem encW_sem {w v : Circ 2} (h : S.sem 2 w = S.sem 2 v) :
    FreeMonoid.lift (QCert.HadamardPi.sem 4) (encW w) =
      FreeMonoid.lift (QCert.HadamardPi.sem 4) (encW v) := by
  have hq := congrArg ri (eval_eq_of_sem h)
  rw [← wordMat_encW, ← wordMat_encW] at hq
  have hr := congrArg (Matrix.map · QSqrt2.toR) hq
  simp only [wordMat_map, QSqrt2.toR_invSqrt2] at hr
  apply Subtype.ext; apply Subtype.ext
  rw [QCert.HadamardPi.lift_sem_val, QCert.HadamardPi.lift_sem_val]
  exact hr

/-! ## Lemma 7.4 -/

section Quotient

/-- The quotient monoid of two-wire circuits by the theory. -/
abbrev Q2 := (conGen (theory 2)).Quotient

/-- The class of a circuit. -/
def cl : Circ 2 →* Q2 := (conGen (theory 2)).mk'

theorem cl_eq {w v : Circ 2} : cl w = cl v ↔ Derivable (theory 2) w v :=
  (conGen (theory 2)).eq

abbrev h0 : Q2 := cl h
abbrev z0 : Q2 := cl z
abbrev h1 : Q2 := cl (shift h)
abbrev z1 : Q2 := cl (shift z)
abbrev cq : Q2 := cl cz
abbrev kq : Q2 := cl ch
abbrev sw : Q2 := cl swap
abbrev x0 : Q2 := h0 * z0 * h0
abbrev x1 : Q2 := h1 * z1 * h1

theorem sw_sw : sw * sw = 1 := by
  rw [← map_mul, ← map_one cl, cl_eq]
  exact derivable_rule Rule.g 0

theorem sw_z1 : sw * z1 = z0 * sw := by
  rw [← map_mul, ← map_mul, cl_eq]
  exact derivable_rule Rule.f1 0

theorem sw_h1 : sw * h1 = h0 * sw := by
  rw [← map_mul, ← map_mul, cl_eq]
  exact derivable_rule Rule.f2 0

theorem sw_cq : sw * cq = cq * sw := by
  rw [← map_mul, ← map_mul, cl_eq]
  exact derivable_rule Rule.e9 0

/-- Equation (6) in the quotient, right-associated. -/
theorem e6q : h1 * (z1 * (h1 * (cq * (h1 * (z1 * (h1 * cq)))))) = z0 := by
  have := derivable_rule Rule.e6 0
  rw [← cl_eq] at this
  simpa [czw, x, drawn, mul_assoc] using this

/-- Equation (7) in the quotient, right-associated. -/
theorem e7q : h1 * (z1 * (h1 * (kq * (h1 * (z1 * (h1 * kq)))))) = h0 := by
  have := derivable_rule Rule.e7 0
  rw [← cl_eq] at this
  simpa [chw, x, drawn, mul_assoc] using this

/-- A letter conjugated by the swap. -/
theorem sw_conj {a b : Q2} (hab : sw * a = b * sw) : sw * a * sw = b := by
  rw [hab, mul_assoc, sw_sw, mul_one]

theorem sw_conj' {a b : Q2} (hab : sw * a = b * sw) : sw * b = a * sw := by
  calc sw * b = sw * (b * sw) * sw := by rw [mul_assoc, mul_assoc, sw_sw, mul_one]
    _ = sw * (sw * a) * sw := by rw [hab]
    _ = a * sw := by rw [← mul_assoc sw sw, sw_sw, one_mul]

theorem swc_h1 (t : Q2) : sw * (h1 * t) = h0 * (sw * t) := by
  rw [← mul_assoc, sw_h1, mul_assoc]
theorem swc_z1 (t : Q2) : sw * (z1 * t) = z0 * (sw * t) := by
  rw [← mul_assoc, sw_z1, mul_assoc]
theorem swc_h0 (t : Q2) : sw * (h0 * t) = h1 * (sw * t) := by
  rw [← mul_assoc, sw_conj' sw_h1, mul_assoc]
theorem swc_z0 (t : Q2) : sw * (z0 * t) = z1 * (sw * t) := by
  rw [← mul_assoc, sw_conj' sw_z1, mul_assoc]
theorem swc_cq (t : Q2) : sw * (cq * t) = cq * (sw * t) := by
  rw [← mul_assoc, sw_cq, mul_assoc]
theorem swc_sw (t : Q2) : sw * (sw * t) = t := by
  rw [← mul_assoc, sw_sw, one_mul]

/-- `D(E(H on wire 1)) = H on wire 1`. -/
theorem dec_enc_h1 : cl (ch10w * ch10) = h1 := by
  have e : h1 = sw * (h1 * (z1 * (h1 * (kq * (h1 * (z1 * (h1 * (kq * sw)))))))) := by
    conv_lhs => rw [← sw_conj (sw_conj' sw_h1), ← e7q]
    simp only [mul_assoc]
  rw [e]
  simp only [ch10w, ch10, x, drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, map_mul, mul_assoc]
  simp only [swc_h0, swc_z0, swc_h1, swc_z1, swc_cq, swc_sw, sw_sw, mul_one]

/-- `D(E(Z on wire 1)) = Z on wire 1`. -/
theorem dec_enc_z1 : cl (czw0 * cz) = z1 := by
  have e : z1 = sw * (h1 * (z1 * (h1 * (cq * (h1 * (z1 * (h1 * (cq * sw)))))))) := by
    conv_lhs => rw [← sw_conj (sw_conj' sw_z1), ← e6q]
    simp only [mul_assoc]
  rw [e]
  simp only [czw0, x, drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, map_mul, mul_assoc]
  simp only [swc_h0, swc_z0, swc_h1, swc_z1, swc_cq, swc_sw, sw_sw, mul_one]

end Quotient

/-- Lemma 7.4: decoding the encoding of a circuit gives back the circuit. -/
theorem lemma_7_4 (w : Circ 2) : Derivable (theory 2) (decW (encW w)) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of g w ih =>
    rw [map_mul, map_mul]
    refine Derivable.mul ?_ ih
    show Derivable (theory 2) (decW (enc g)) (FreeMonoid.of g)
    rw [← cl_eq]
    match g with
    | .gate0 c => exact nomatch c
    | .gate1 .H =>
      show cl (chw * ch * 1) = cl h
      rw [mul_one, cl_eq]; exact derivable_rule Rule.e7 0
    | .gate1 .Z =>
      show cl (czw * cz * 1) = cl z
      rw [mul_one, cl_eq]; exact derivable_rule Rule.e6 0
    | .gate2 .CZ => rfl
    | .gate2 .CH => rfl
    | .up (.gate1 .H) => show cl (ch10w * ch10 * 1) = h1; rw [mul_one]; exact dec_enc_h1
    | .up (.gate1 .Z) => show cl (czw0 * cz * 1) = z1; rw [mul_one]; exact dec_enc_z1
    | .up (.gate0 c) => exact nomatch c

/-- Lemma 7.6 (2-qubit completeness) from Theorem 4.4 for `𝒢₄` (`h44`) and
Lemma 7.5 (`h75`). -/
theorem complete_two_of
    (h44 : ∀ u v : Word G4, FreeMonoid.lift (QCert.HadamardPi.sem 4) u =
      FreeMonoid.lift (QCert.HadamardPi.sem 4) v → Derivable QCert.HadamardPi.Fig6 u v)
    (h75 : ∀ u v : Word G4, QCert.HadamardPi.Fig6 u v → Derivable (theory 2) (decW u) (decW v))
    {w v : Circ 2} (h : S.sem 2 w = S.sem 2 v) : Derivable (theory 2) w v := by
  have d4 := h44 _ _ (encW_sem h)
  -- the decoding respects the congruence of Figure 6
  let c : Con (Word G4) := (conGen (theory 2)).comap decW (map_mul decW)
  have hc : conGen QCert.HadamardPi.Fig6 ≤ c := Con.conGen_le fun a b hab => h75 a b hab
  have dd : Derivable (theory 2) (decW (encW w)) (decW (encW v)) := hc d4
  exact (lemma_7_4 w).symm.trans (dd.trans (lemma_7_4 v))

end Two

end QCert.RealCliffordCH
