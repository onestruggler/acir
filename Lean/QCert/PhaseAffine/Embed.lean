/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The affine fragment inside the higher levels

The gates of `Aff_d` (level `0`) are gates of every level, and its rules are
rules of every level (Definition 14: each phase fragment is obtained from
`Aff_d` by adjoining generators and equations).  So a derivation in `Aff_d`
is a derivation at every level (`derivable_lift`), with the same pairs
`(g, q)` (`sem_lift`), and every linear circuit of a level comes from one of
`Aff_d` (`lin_lift_surj`).
-/
import QCert.PhaseAffine.Translation

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-- A gate of `Aff_d` as a gate of level `lv`. -/
def Gate.lift (lv : ℕ) : {k : ℕ} → Gate d 0 k → Gate d lv k
  | _, .omega h => absurd h (by omega)
  | _, .X => .X
  | _, .M a => .M a
  | _, .Z h => absurd h (by omega)
  | _, .S h => absurd h (by omega)
  | _, .T h => absurd h (by omega)
  | _, .CX => .CX
  | _, .SWAP => .SWAP

/-- A generator of `Aff_d` as a generator of level `lv`. -/
def Gen.lift (lv : ℕ) : {n : ℕ} → Gen (Gate d 0) n → Gen (Gate d lv) n
  | _, .gate0 g => .gate0 (Gate.lift lv g)
  | _, .gate1 g => .gate1 (Gate.lift lv g)
  | _, .gate2 g => .gate2 (Gate.lift lv g)
  | _, .gate3 g => .gate3 (Gate.lift lv g)
  | _, .up g => .up (Gen.lift lv g)

/-- A circuit of `Aff_d` as a circuit of level `lv`. -/
def cl (lv : ℕ) {n : ℕ} : C d 0 n →* C d lv n := FreeMonoid.map (Gen.lift lv)

theorem cl_shift {n : ℕ} (w : C d 0 n) : cl lv (shift w) = shift (cl lv w) := by
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of x => rfl
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem gen_lift_pad (m : ℕ) {k : ℕ} (g : Gen (Gate d 0) k) :
    Gen.lift lv (g.pad m) = (Gen.lift lv g).pad m := by
  induction g with
  | gate0 c => rfl
  | gate1 c => rfl
  | gate2 c => rfl
  | gate3 c => rfl
  | up g ih => simp only [Gen.pad, Gen.lift, ih]

theorem cl_pad (m : ℕ) {k : ℕ} (w : C d 0 k) : cl lv (pad m w) = pad m (cl lv w) := by
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of x => show FreeMonoid.of _ = FreeMonoid.of _; rw [gen_lift_pad]
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem cl_seq {n : ℕ} (l : List (C d 0 n)) : cl lv (seq l) = seq (l.map (cl lv)) := by
  induction l with
  | nil => simp
  | cons g l ih => simp [ih]

theorem cl_fpow {n : ℕ} (w : C d 0 n) (k : ZMod d) : cl lv (w ^ᶠ k) = cl lv w ^ᶠ k := by
  simp [fpow]

/-- The rules of `Aff_d` are rules of every level. -/
theorem rules_lift {k : ℕ} {w v : C d 0 k} (h : Rules d 0 k w v) :
    Rules d lv k (cl lv w) (cl lv v) := by
  cases h with
  | r1 => exact Rules.r1
  | r2 x y => simpa [cl_seq] using Rules.r2 (d := d) (lv := lv) x y
  | r3 x => simpa [cl_seq, cl_fpow] using Rules.r3 (d := d) (lv := lv) x
  | r4 x => simpa [cl_seq, cl_fpow, cl_shift] using Rules.r4 (d := d) (lv := lv) x
  | r5 x => simpa [cl_seq, cl_fpow, cl_pad] using Rules.r5 (d := d) (lv := lv) x
  | r6 => simpa [cl_seq, cl_shift, cl_pad] using Rules.r6 (d := d) (lv := lv)
  | r7 => simpa [cl_seq, cl_fpow, cl_shift, flip] using Rules.r7 (d := d) (lv := lv)
  | r8 => simpa [cl_seq, cl_shift, cl_pad, long] using Rules.r8 (d := d) (lv := lv)
  | swap_inv => simpa [cl_seq] using Rules.swap_inv (d := d) (lv := lv)
  | swap_nat1 g =>
    simpa [cl_seq, cl_shift, cl_pad] using Rules.swap_nat1 (d := d) (lv := lv) (Gate.lift lv g)
  | swap_nat2 g =>
    simpa [cl_seq, cl_shift, cl_pad, cyc] using
      Rules.swap_nat2 (d := d) (lv := lv) (Gate.lift lv g)
  | r19 h => omega
  | r20 h => omega
  | r21 h => omega
  | r22 h => omega
  | r23 h => omega
  | r24 h => omega
  | r25 h => omega
  | r26 h => omega
  | r27 h => omega
  | r28 h => omega
  | r29 h => omega
  | r30 h => omega
  | r31 h => omega
  | r32 h => omega
  | r33 h => omega
  | r34 h => omega
  | r35 h => omega
  | r36 h => omega
  | r37 h => omega
  | r38 h => omega
  | r39 h => omega
  | r40 h => omega
  | r41 h => omega
  | r42 h => omega

theorem lift_lift {n : ℕ} {w v : C d 0 n} (h : theory d 0 n w v) :
    theory d lv n (cl lv w) (cl lv v) := by
  induction h with
  | rule hr =>
    cases hr with
    | pad m hb => rw [cl_pad, cl_pad]; exact Lift.rule (Padded.pad m (rules_lift hb))
  | shift _ ih => rw [cl_shift, cl_shift]; exact Lift.shift ih
  | comm1 h g => exact Lift.comm1 (Gate.lift lv h) (Gen.lift lv g)
  | comm2 h g => exact Lift.comm2 (Gate.lift lv h) (Gen.lift lv g)
  | comm3 h g => exact Lift.comm3 (Gate.lift lv h) (Gen.lift lv g)
  | scalar c => exact Lift.scalar (Gate.lift lv c)

/-- A derivation of `Aff_d` is a derivation at every level. -/
theorem derivable_lift {n : ℕ} {w v : C d 0 n} (h : Derivable (theory d 0 n) w v) :
    Derivable (theory d lv n) (cl lv w) (cl lv v) := by
  have : conGen (theory d 0 n) ≤
      Con.comap (cl lv) (fun x y => map_mul (cl lv) x y) (conGen (theory d lv n)) :=
    Con.conGen_le fun x y hr => ConGen.Rel.of _ _ (lift_lift hr)
  exact this h

/-- The pairs of a circuit of `Aff_d` are the same at every level. -/
theorem sem_lift {n : ℕ} (w : C d 0 n) :
    (gateData d lv).sem n (cl lv w) = (gateData d 0).sem n w := by
  have hg : ∀ {m : ℕ} (x : Gen (Gate d 0) m),
      (gateData d lv).gen (Gen.lift lv x) = (gateData d 0).gen x := by
    intro m x
    induction x with
    | gate0 c => cases c; omega
    | gate1 c => cases c <;> first | rfl | omega
    | gate2 c => cases c <;> rfl
    | gate3 c => nomatch c
    | up g ih => show PA.onTop _ = PA.onTop _; rw [ih]
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of x => exact hg x
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- Every linear generator of level `lv` comes from `Aff_d`. -/
theorem gen_lin_lift {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) :
    ∃ x0 : Gen (Gate d 0) n, x0.IsLin ∧ Gen.lift lv x0 = x := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsLin])
  | gate3 c => exact absurd hx (by simp [Gen.IsLin])
  | gate1 c =>
    cases c with
    | M a => exact ⟨.gate1 (.M a), trivial, rfl⟩
    | _ => exact absurd hx (by simp [Gen.IsLin])
  | gate2 c =>
    cases c
    · exact ⟨.gate2 .CX, trivial, rfl⟩
    · exact ⟨.gate2 .SWAP, trivial, rfl⟩
  | up g ih =>
    obtain ⟨g0, hg0, rfl⟩ := ih hx
    exact ⟨.up g0, hg0, rfl⟩

/-- Every linear circuit of level `lv` comes from `Aff_d`. -/
theorem lin_lift_surj {n : ℕ} (w : C d lv n) (hw : IsLinW w) :
    ∃ w0 : C d 0 n, IsLinW w0 ∧ cl lv w0 = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, IsLinW.one, rfl⟩
  | mul_of x w ih =>
    have hx : x.IsLin := hw x (by simp)
    have hw' : IsLinW w := fun y hy => hw y (by rw [FreeMonoid.toList_of_mul]; simp [hy])
    obtain ⟨x0, hx0, rfl⟩ := gen_lin_lift x hx
    obtain ⟨w0, hw0, rfl⟩ := ih hw'
    exact ⟨FreeMonoid.of x0 * w0, IsLinW.mul (IsLinW.of hx0) hw0, by simp [cl]⟩

end QCert.PhaseAffine
