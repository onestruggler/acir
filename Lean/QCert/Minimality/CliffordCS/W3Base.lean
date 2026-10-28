/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CliffCS₂ on three wires: the encoding, the decoding and the tools

Theorem 22 (5) on three wires transfers completeness from Bian and
Selinger's three-qubit Clifford+CS presentation (`QCert.CliffordCS3`),
refined by a new central scalar `w` with `w² = i` (Appendix I), as the
paper does (Appendices E, F.5, G.5).  Qubit `q` is wire `2 - q`, so the
source's basis index `4 q₀ + 2 q₁ + q₂` is the index `s₀ + 2 s₁ + 4 s₂` of the
circuits.

* The encoding: `ω₈ ↦ w`, `H ↦ w K_q`, `S ↦ S_q`, `CS ↦ CS₁₂` (wires `0, 1`)
  or `CS₀₁` (wires `1, 2`), the swap `↦` three CNOTs `K_t CS CS K_t i`.
* The decoding: `w ↦ ω₈`, `i ↦ ω₈²`, `K_q ↦ H ω₈⁷` (`K = ω† H`), `S_q ↦ S`,
  `CS ↦ CS`.  The paper draws the source's relations left to right, i.e.
  reversed (its words are in the order of matrix multiplication), so the
  decoding is read on reversed words (`complete_of_flat_rev`), which the
  semantics allows because every generator's matrix is symmetric.

Every source relation on at most two qubits decodes to an equation on two
wires, which completeness on two wires (`complete₂`, from `W2Complete`)
derives once it is decided in the semantics (`lo2`, `hi2`); the
three-qubit ones are derived in `W3Lemmas`.
-/
import QCert.Minimality.CliffordCS.W2Complete
import QCert.CliffordCS3.Theorem

namespace QCert.Minimality.CliffordCS

open Matrix QCert.Circuit OmegaParity

/-- Completeness of CliffCS₂ on two wires (Theorem 22 (5), from
`QCert.BianSelingerUn.presentation`). -/
theorem complete₂ (w v : Circuit Gate 2) (h : sem.sem 2 w = sem.sem 2 v) :
    Derivable (Lift Th 2) w v :=
  complete₂_of_source (fun _ _ h => (QCert.BianSelingerUn.presentation 4).complete h) w v h

namespace W3

instance : DecidableEq (Circuit Gate 3) := inferInstanceAs (DecidableEq (List (QCert.Gen Gate 3)))

instance : DecidableEq (Circuit Gate 2) := inferInstanceAs (DecidableEq (List (QCert.Gen Gate 2)))

/-- An equation decided over ℤ[ω] on row tries. -/
theorem semrow {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (scaled.ex v - scaled.ex w)) (evalRows ops n w) =
      (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (scaled.ex w - scaled.ex v)) (evalRows ops n v)) :
    sem.sem n w = sem.sem n v :=
  Qubit.sem_eq_of_rows sem scaled sem_toOps h

/-- A two-wire equation that holds in the semantics, as a derived equation. -/
def sem2D (l r : Circuit Gate 2) (h : sem.sem 2 l = sem.sem 2 r) : DEqn Th 2 :=
  ⟨l, r, complete₂ l r h⟩

/-- A semantic two-wire equation on the wires `0, 1` of three. -/
theorem lo2 {w v : Circuit Gate 3} {u u' : Circuit Gate 2} (hw : w = Circuit.pad 1 u)
    (hv : v = Circuit.pad 1 u') (h : sem.sem 2 u = sem.sem 2 u') : Derivable (Lift Th 3) w v := by
  rw [hw, hv]; exact derivable_pad 1 (complete₂ u u' h)

/-- A semantic two-wire equation on the wires `1, 2` of three. -/
theorem hi2 {w v : Circuit Gate 3} {u u' : Circuit Gate 2} (hw : w = shift u)
    (hv : v = shift u') (h : sem.sem 2 u = sem.sem 2 u') : Derivable (Lift Th 3) w v := by
  rw [hw, hv]; exact derivable_shift (complete₂ u u' h)

/-- A generator of two wires one wire up, a scalar staying a scalar. -/
def upS : QCert.Gen Gate 2 → QCert.Gen Gate 3
  | .gate0 c => .gate0 c
  | g => .up g

/-- A two-wire circuit on the wires `1, 2`, its scalars kept as they are. -/
def shiftS : Circuit Gate 2 →* Circuit Gate 3 := FreeMonoid.map upS

theorem shiftS_derivable (u : Circuit Gate 2) : Derivable (Lift Th 3) (shiftS u) (shift u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp only [map_one]; exact Derivable.refl _
  | mul_of g u ih =>
    rw [map_mul, map_mul]
    refine Derivable.mul ?_ ih
    cases g with
    | gate0 c => exact (Derivable.of (Lift.scalar c)).symm
    | _ => exact Derivable.refl _

/-- A semantic two-wire equation on the wires `1, 2` of three, scalars kept. -/
theorem hi2s {w v : Circuit Gate 3} {u u' : Circuit Gate 2} (hw : w = shiftS u)
    (hv : v = shiftS u') (h : sem.sem 2 u = sem.sem 2 u') : Derivable (Lift Th 3) w v := by
  rw [hw, hv]
  exact (shiftS_derivable u).trans ((derivable_shift (complete₂ u u' h)).trans
    (shiftS_derivable u').symm)

/-- Two circuits whose generators are pairwise apart commute. -/
theorem comm_words {n : ℕ} :
    ∀ (u v : List (QCert.Gen Gate n)), (u.all fun a => v.all fun b => Gen.apart a b) = true →
      Derivable (Lift Th n) (FreeMonoid.ofList u * FreeMonoid.ofList v)
        (FreeMonoid.ofList v * FreeMonoid.ofList u)
  | [], v, _ => by simp only [FreeMonoid.ofList_nil, one_mul, mul_one]; exact Derivable.refl _
  | a :: u, v, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := comm_words u v h.2
    have ha : Derivable (Lift Th n) (FreeMonoid.of a * FreeMonoid.ofList v)
        (FreeMonoid.ofList v * FreeMonoid.of a) := by
      have := slide_right (R := Th) hsc a v h.1
      simpa [FreeMonoid.ofList_cons, FreeMonoid.ofList_append] using this
    rw [FreeMonoid.ofList_cons, mul_assoc]
    refine ((Derivable.refl _).mul ih).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact ha.mul (Derivable.refl _)

theorem derivable_congr' {n : ℕ} {a a' b b' : Circuit Gate n} (ha : a = a') (hb : b = b')
    (h : Derivable (Lift Th n) a' b') : Derivable (Lift Th n) a b := ha ▸ hb ▸ h

/-! ### The source's generators over `ℚ(ω)` -/

/-- The source's matrices (written out entry by entry). -/
abbrev matS : QCert.CliffordCS3.Gen → Matrix (Fin 8) (Fin 8) QOmega := QCert.CliffordCS3.matLit

theorem matS_eq : QCert.CliffordCS3.matQ = matS := funext QCert.CliffordCS3.matQ_eq_matLit

theorem lift_sem (a : Word QCert.CliffordCS3.Gen) :
    ((FreeMonoid.lift QCert.CliffordCS3.sem a : unitaryGroup (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ) =
      (FreeMonoid.lift matS a).map QOmega.toC := by
  have h := lift_unitaryQ QCert.CliffordCS3.matQ QCert.CliffordCS3.matQ_unitary a
  have e2 : cmat (FreeMonoid.lift QCert.CliffordCS3.matQ a) =
      (FreeMonoid.lift matS a).map QOmega.toC := by rw [matS_eq]; rfl
  exact h.trans e2

/-- The source's completeness, for its matrices over `ℚ(ω)`. -/
theorem complete_S
    (hsrc : ∀ a b : Word QCert.CliffordCS3.Gen,
      FreeMonoid.lift QCert.CliffordCS3.sem a = FreeMonoid.lift QCert.CliffordCS3.sem b →
        Derivable QCert.CliffordCS3.Rel a b)
    (a b : Word QCert.CliffordCS3.Gen) (h : FreeMonoid.lift matS a = FreeMonoid.lift matS b) :
    Derivable QCert.CliffordCS3.Rel a b :=
  hsrc a b (Subtype.ext (by rw [lift_sem, lift_sem, h]))

/-- The source's soundness, for its matrices over `ℚ(ω)`. -/
theorem sound_S (a b : Word QCert.CliffordCS3.Gen) (h : QCert.CliffordCS3.Rel a b) :
    FreeMonoid.lift matS a = FreeMonoid.lift matS b := by
  apply UN.mapC_injective
  simp only
  rw [← lift_sem, ← lift_sem, QCert.CliffordCS3.sound h]

theorem lift_ne_zero (a : Word QCert.CliffordCS3.Gen) : FreeMonoid.lift matS a ≠ 0 := by
  intro h0
  have hu := (FreeMonoid.lift QCert.CliffordCS3.sem a : unitaryGroup (Fin 8) ℂ).2
  have hm : ((FreeMonoid.lift QCert.CliffordCS3.sem a : unitaryGroup (Fin 8) ℂ) :
      Matrix (Fin 8) (Fin 8) ℂ) = 0 := by
    rw [lift_sem, h0]; exact Matrix.map_zero _ (map_zero _)
  rw [Matrix.mem_unitaryGroup_iff, hm, zero_mul] at hu
  have := congrFun (congrFun hu 0) 0
  simp at this

theorem matS_even (x : QCert.CliffordCS3.Gen) : MEven (matS x) := by
  cases x <;> exact fun s t => by revert s t; decide +kernel

theorem matS_symm (y : Option QCert.CliffordCS3.Gen) : (matR matS y)ᵀ = matR matS y := by
  cases y with
  | none => simp [matR]
  | some x => cases x <;> decide +kernel

/-- The source's word for `i` times the identity. -/
def gi : Word QCert.CliffordCS3.Gen := FreeMonoid.of .i

theorem gi_eq : FreeMonoid.lift matS gi = QOmega.I • 1 := by decide +kernel

/-! ### The encoding and the decoding -/

open QCert.CliffordCS3 in
/-- The controlled not `K_t CS CS K_t i` (Section 2.1), letter by letter. -/
def cxw (cs : QCert.CliffordCS3.Gen) (t : QCert.CliffordCS3.Gen) :
    FreeMonoid (Option QCert.CliffordCS3.Gen) :=
  FreeMonoid.ofList [some t, some cs, some cs, some t, some .i]

/-- The encoding of the generators on three wires. -/
def e : QCert.Gen Gate 3 → FreeMonoid (Option QCert.CliffordCS3.Gen)
  | .gate0 .ω => wl
  | .gate1 .H => wl * FreeMonoid.of (some .K₂)
  | .gate1 .S => FreeMonoid.of (some .S₂)
  | .gate2 .CS => FreeMonoid.of (some .CS₁₂)
  | .gate2 .swap => cxw .CS₁₂ .K₂ * cxw .CS₁₂ .K₁ * cxw .CS₁₂ .K₂
  | .up (.gate0 .ω) => wl
  | .up (.gate1 .H) => wl * FreeMonoid.of (some .K₁)
  | .up (.gate1 .S) => FreeMonoid.of (some .S₁)
  | .up (.gate2 .CS) => FreeMonoid.of (some .CS₀₁)
  | .up (.gate2 .swap) => cxw .CS₀₁ .K₁ * cxw .CS₀₁ .K₀ * cxw .CS₀₁ .K₁
  | .up (.up (.gate0 .ω)) => wl
  | .up (.up (.gate1 .H)) => wl * FreeMonoid.of (some .K₀)
  | .up (.up (.gate1 .S)) => FreeMonoid.of (some .S₀)
  | .up (.up (.up (.gate0 .ω))) => wl

/-- The decoding of the refined letters (operator order; `tw` reads time order). -/
def d : Option QCert.CliffordCS3.Gen → Circuit Gate 3
  | none => tw 3 [(.w, 0)]
  | some .i => tw 3 [(.w, 0), (.w, 0)]
  | some .K₀ => tw 3 [(.H, 2), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0)]
  | some .K₁ => tw 3 [(.H, 1), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0)]
  | some .K₂ => tw 3 [(.H, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0), (.w, 0)]
  | some .S₀ => tw 3 [(.S, 2)]
  | some .S₁ => tw 3 [(.S, 1)]
  | some .S₂ => tw 3 [(.S, 0)]
  | some .CS₀₁ => tw 3 [(.CS, 1)]
  | some .CS₁₂ => tw 3 [(.CS, 0)]

/-- The decoding. -/
def D : FreeMonoid (Option QCert.CliffordCS3.Gen) →* Circuit Gate 3 := FreeMonoid.lift d

end W3

end QCert.Minimality.CliffordCS
