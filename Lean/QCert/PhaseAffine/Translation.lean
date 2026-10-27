/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Collecting translations

The first step of the proof of Lemma 3 of Blake (arXiv:2603.06466): an
affine circuit is equal in the theory to its translation column `NF_tr(b)`
(Definition 9, `xcol b`: `X^{b_i}` on wire `i`) after a linear circuit
(multipliers, controlled additions, crossings).  A linear gate moves through
the column by acting on its labels (`push_xcol`), using (6), Lemma 18,
Lemma 21 and the naturality of the crossing.
-/
import QCert.PhaseAffine.Affine

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-! ### Affine and linear generators -/

/-- Linear generators: multipliers, controlled additions, crossings. -/
def _root_.QCert.Gen.IsLin : {n : ℕ} → Gen (Gate d lv) n → Prop
  | _, .gate1 (.M _) => True
  | _, .gate2 _ => True
  | _, .up g => g.IsLin
  | _, _ => False

/-- Affine generators: the linear ones and translations. -/
def _root_.QCert.Gen.IsAff : {n : ℕ} → Gen (Gate d lv) n → Prop
  | _, .gate1 .X => True
  | _, .gate1 (.M _) => True
  | _, .gate2 _ => True
  | _, .up g => g.IsAff
  | _, _ => False

/-- A circuit of linear generators. -/
def IsLinW {n : ℕ} (w : C d lv n) : Prop := ∀ x ∈ FreeMonoid.toList w, Gen.IsLin x

/-- A circuit of affine generators. -/
def IsAffW {n : ℕ} (w : C d lv n) : Prop := ∀ x ∈ FreeMonoid.toList w, Gen.IsAff x

theorem IsLinW.one {n : ℕ} : IsLinW (1 : C d lv n) := by simp [IsLinW]
theorem IsLinW.mul {n : ℕ} {w v : C d lv n} (hw : IsLinW w) (hv : IsLinW v) :
    IsLinW (w * v) := by
  intro x hx; rw [FreeMonoid.toList_mul, List.mem_append] at hx
  exact hx.elim (hw x) (hv x)
theorem IsLinW.of {n : ℕ} {x : Gen (Gate d lv) n} (h : x.IsLin) : IsLinW (FreeMonoid.of x) := by
  intro y hy; simp only [FreeMonoid.toList_of, List.mem_singleton] at hy; exact hy ▸ h

theorem IsAffW.of_mul_left {n : ℕ} {x : Gen (Gate d lv) n} {w : C d lv n}
    (h : IsAffW (FreeMonoid.of x * w)) : x.IsAff ∧ IsAffW w := by
  refine ⟨h x (by simp), fun y hy => h y ?_⟩
  rw [FreeMonoid.toList_of_mul]; exact List.mem_cons_of_mem _ hy

/-! ### The translation column -/

/-- `NF_tr(b)`: `X^{b_i}` on every wire `i` (Definition 9). -/
def xcol : (n : ℕ) → Lab d n → C d lv n
  | 0, _ => 1
  | n + 1, b => shift (xcol n (Fin.tail b)) * g1 Gate.X ^ᶠ (b 0)

theorem xcol_zero (n : ℕ) : xcol (d := d) (lv := lv) n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xcol, fpow, Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
    rw [show (Fin.tail (0 : Lab d (n + 1))) = 0 from rfl, ih, map_one]

/-- The labels after a gate: the affine map of an affine generator. -/
def affMap : {n : ℕ} → Gen (Gate d lv) n → Lab d n → Lab d n
  | _, .gate1 .X, b => Fin.cons (b 0 + 1) (Fin.tail b)
  | _, .gate1 (.M a), b => Fin.cons ((a : ZMod d) * b 0) (Fin.tail b)
  | _, .gate2 .CX, b => Fin.cons (b 0 + b 1) (Fin.tail b)
  | _, .gate2 .SWAP, b => Fin.cons (b 1) (Fin.cons (b 0) (Fin.tail (Fin.tail b)))
  | _, .up g, b => Fin.cons (b 0) (affMap g (Fin.tail b))
  | _, _, b => b

/-- The linear part of an affine generator: the generator itself, or nothing
for a translation. -/
def linPart : {n : ℕ} → Gen (Gate d lv) n → C d lv n
  | _, .gate1 .X => 1
  | _, .up g => shift (linPart g)
  | _, x => FreeMonoid.of x

/-- The linear part of a circuit. -/
def lin {n : ℕ} : C d lv n →* C d lv n := FreeMonoid.lift linPart

theorem linPart_isLin {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) : IsLinW (linPart x) := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | gate1 g =>
    cases g <;> simp only [Gen.IsAff] at hx
    · exact IsLinW.one
    · exact IsLinW.of trivial
  | gate2 g => exact IsLinW.of trivial
  | gate3 g => exact absurd hx (by simp [Gen.IsAff])
  | up g ih =>
    intro y hy
    simp only [linPart, shift, FreeMonoid.toList_map, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ih hx z hz

theorem lin_isLin {n : ℕ} (w : C d lv n) (hw : IsAffW w) : IsLinW (lin w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa [lin] using IsLinW.one
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsAffW.of_mul_left hw
    rw [map_mul, lin, FreeMonoid.lift_eval_of]
    exact IsLinW.mul (linPart_isLin x hx) (ih hw)

section Push

variable [Fact d.Prime]

omit [Fact d.Prime] in
/-- A one-wire gate on the bottom wire commutes with a circuit shifted up. -/
theorem mk_comm1' {n : ℕ} (h : Gate d lv 1) (u : C d lv n) :
    Commute (mk (g1 h)) (mk (shift u)) := by
  show mk (g1 h) * mk (shift u) = mk (shift u) * mk (g1 h)
  rw [← map_mul, ← map_mul]; exact mk_comm1 h u

omit [Fact d.Prime] in
/-- A two-wire gate on the bottom wires commutes with a circuit moved up two
wires. -/
theorem mk_comm2' {n : ℕ} (h : Gate d lv 2) (u : C d lv n) :
    Commute (mk (g2 h)) (mk (shift (shift u))) := by
  show mk (g2 h) * mk (shift (shift u)) = mk (shift (shift u)) * mk (g2 h)
  rw [← map_mul, ← map_mul]; exact mk_comm2 h u

omit [Fact d.Prime] in
theorem mk_xcol_succ {n : ℕ} (b : Lab d (n + 1)) :
    mk (xcol (lv := lv) (n + 1) b) =
      mk (shift (xcol n (Fin.tail b))) * mk (g1 Gate.X) ^ (b 0).val := by
  rw [xcol, map_mul, fpow, map_pow]

omit [Fact d.Prime] in
theorem mk_xcol_succ_succ {m : ℕ} (c : Lab d (m + 2)) :
    mk (xcol (lv := lv) (m + 2) c) =
      mk (shift (shift (xcol m (Fin.tail (Fin.tail c))))) *
        mk (shift (g1 Gate.X)) ^ (c 1).val * mk (g1 Gate.X) ^ (c 0).val := by
  simp only [xcol, map_mul, fpow, map_pow]
  rfl

/-- `X` and `M` on the bottom wire move through the translation powers. -/
theorem relMXpow (m : ℕ) (a : (ZMod d)ˣ) (k : ℕ) :
    mk (g1 (n := m) (Gate.M (lv := lv) a)) * mk (g1 Gate.X) ^ k =
      (mk (g1 Gate.X) ^ (a : ZMod d).val) ^ k * mk (g1 (Gate.M a)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, relMX, ← mul_assoc, ← pow_succ]

theorem relCX_X1pow (m : ℕ) (k : ℕ) :
    mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) * mk (shift (g1 Gate.X)) ^ k =
      mk (g1 Gate.X) ^ k * mk (shift (g1 Gate.X)) ^ k * mk (g2 Gate.CX) := by
  set x0 := mk (g1 (n := m + 1) (Gate.X (d := d) (lv := lv)))
  set x1 := mk (shift (g1 (n := m) (Gate.X (d := d) (lv := lv))))
  set c := mk (g2 (n := m) (Gate.CX (d := d) (lv := lv)))
  have hc : Commute x0 x1 := mk_comm1' Gate.X _
  have h6 : c * x1 = x0 * x1 * c := rel6 m
  induction k with
  | zero => simp
  | succ k ih =>
    calc c * x1 ^ (k + 1) = (c * x1 ^ k) * x1 := by rw [pow_succ, mul_assoc]
      _ = x0 ^ k * x1 ^ k * (c * x1) := by rw [ih]; group
      _ = x0 ^ k * x1 ^ k * (x0 * x1 * c) := by rw [h6]
      _ = x0 ^ k * (x1 ^ k * x0) * x1 * c := by group
      _ = x0 ^ k * (x0 * x1 ^ k) * x1 * c := by rw [(hc.symm.pow_left k).eq]
      _ = x0 ^ (k + 1) * x1 ^ (k + 1) * c := by group

theorem relCX_X0pow (m : ℕ) (k : ℕ) :
    mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) * mk (g1 Gate.X) ^ k =
      mk (g1 Gate.X) ^ k * mk (g2 Gate.CX) :=
  (Commute.pow_right (rel21 m) k).eq

theorem relSW_pow (m : ℕ) (g : Gate d lv 1) (k : ℕ) :
    mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))) * mk (g1 g) ^ k =
      mk (shift (g1 g)) ^ k * mk (g2 Gate.SWAP) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, relSWnat, ← mul_assoc, ← pow_succ]

theorem relSW_pow' (m : ℕ) (g : Gate d lv 1) (k : ℕ) :
    mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))) * mk (shift (g1 g)) ^ k =
      mk (g1 g) ^ k * mk (g2 Gate.SWAP) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, relSWnat', ← mul_assoc, ← pow_succ]

/-- An affine generator moves through the translation column, acting on its
labels, and leaves its linear part. -/
theorem push_xcol {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) (b : Lab d n) :
    mk (FreeMonoid.of x * xcol n b) = mk (xcol n (affMap x b) * linPart x) := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | gate3 g => exact absurd hx (by simp [Gen.IsAff])
  | @gate1 m g =>
    cases g with
    | X =>
      set A := mk (shift (xcol (lv := lv) m (Fin.tail b)))
      set x := mk (g1 (n := m) (Gate.X (d := d) (lv := lv)))
      have hxA : x * A = A * x := (mk_comm1' Gate.X _).eq
      show x * mk (xcol (m + 1) b) = mk (xcol (m + 1) (Fin.cons (b 0 + 1) (Fin.tail b))) * mk 1
      rw [mk_xcol_succ, mk_xcol_succ, Fin.tail_cons, Fin.cons_zero, map_one, mul_one,
        pow_val_add (relXd m), pow_val_one one_lt_d, ← mul_assoc, hxA, mul_assoc,
        (Commute.self_pow x _).eq]
    | M a =>
      set A := mk (shift (xcol (lv := lv) m (Fin.tail b)))
      set x := mk (g1 (n := m) (Gate.M (d := d) (lv := lv) a))
      have hxA : x * A = A * x := (mk_comm1' (Gate.M a) _).eq
      show x * mk (xcol (m + 1) b) =
        mk (xcol (m + 1) (Fin.cons ((a : ZMod d) * b 0) (Fin.tail b))) * x
      rw [mk_xcol_succ, mk_xcol_succ, Fin.tail_cons, Fin.cons_zero, ← mul_assoc, hxA,
        mul_assoc, relMXpow, pow_val_mul (relXd m), mul_assoc]
    | Z h => exact absurd hx (by simp [Gen.IsAff])
    | S h => exact absurd hx (by simp [Gen.IsAff])
    | T h => exact absurd hx (by simp [Gen.IsAff])
  | @gate2 m g =>
    set A := mk (shift (shift (xcol (lv := lv) m (Fin.tail (Fin.tail b)))))
    set x0 := mk (g1 (n := m + 1) (Gate.X (d := d) (lv := lv)))
    set x1 := mk (shift (g1 (n := m) (Gate.X (d := d) (lv := lv))))
    have hc : Commute x0 x1 := mk_comm1' Gate.X _
    cases g with
    | CX =>
      show mk (g2 (Gate.CX (d := d) (lv := lv))) * mk (xcol (m + 2) b) =
        mk (xcol (m + 2) (Fin.cons (b 0 + b 1) (Fin.tail b))) * mk (g2 Gate.CX)
      rw [mk_xcol_succ_succ, mk_xcol_succ_succ]
      rw [show (Fin.cons (b 0 + b 1) (Fin.tail b) : Lab d (m + 2)) 1 = b 1 from rfl,
        show (Fin.tail (Fin.tail (Fin.cons (b 0 + b 1) (Fin.tail b) : Lab d (m + 2))) :
          Lab d m) = Fin.tail (Fin.tail b) from rfl, Fin.cons_zero,
        add_comm (b 0) (b 1), pow_val_add (relXd (m + 1))]
      set A := mk (shift (shift (xcol (lv := lv) m (Fin.tail (Fin.tail b)))))
      set x0 := mk (g1 (n := m + 1) (Gate.X (d := d) (lv := lv)))
      set x1 := mk (shift (g1 (n := m) (Gate.X (d := d) (lv := lv))))
      set c := mk (g2 (n := m) (Gate.CX (d := d) (lv := lv)))
      have hc : Commute x0 x1 := mk_comm1' Gate.X _
      have hcA : c * A = A * c := (mk_comm2' Gate.CX _).eq
      have h1 : c * x1 ^ (b 1).val = x0 ^ (b 1).val * x1 ^ (b 1).val * c := relCX_X1pow m _
      have h0 : c * x0 ^ (b 0).val = x0 ^ (b 0).val * c := relCX_X0pow m _
      calc c * (A * x1 ^ (b 1).val * x0 ^ (b 0).val)
          = A * (c * x1 ^ (b 1).val) * x0 ^ (b 0).val := by
            rw [← mul_assoc, ← mul_assoc, hcA]; group
        _ = A * (x0 ^ (b 1).val * x1 ^ (b 1).val) * (c * x0 ^ (b 0).val) := by
            rw [h1]; group
        _ = A * (x1 ^ (b 1).val * x0 ^ (b 1).val) * (x0 ^ (b 0).val * c) := by
            rw [h0, ((hc.pow_left _).pow_right _).eq]
        _ = _ := by group
    | SWAP =>
      show mk (g2 (Gate.SWAP (d := d) (lv := lv))) * mk (xcol (m + 2) b) =
        mk (xcol (m + 2) (Fin.cons (b 1) (Fin.cons (b 0) (Fin.tail (Fin.tail b))))) *
          mk (g2 Gate.SWAP)
      rw [mk_xcol_succ_succ, mk_xcol_succ_succ]
      rw [show (Fin.cons (b 1) (Fin.cons (b 0) (Fin.tail (Fin.tail b))) : Lab d (m + 2)) 1 =
          b 0 from rfl,
        show (Fin.tail (Fin.tail (Fin.cons (b 1) (Fin.cons (b 0) (Fin.tail (Fin.tail b))) :
          Lab d (m + 2))) : Lab d m) = Fin.tail (Fin.tail b) from rfl, Fin.cons_zero]
      set A := mk (shift (shift (xcol (lv := lv) m (Fin.tail (Fin.tail b)))))
      set x0 := mk (g1 (n := m + 1) (Gate.X (d := d) (lv := lv)))
      set x1 := mk (shift (g1 (n := m) (Gate.X (d := d) (lv := lv))))
      set c := mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))
      have hc : Commute x0 x1 := mk_comm1' Gate.X _
      have hcA : c * A = A * c := (mk_comm2' Gate.SWAP _).eq
      have h1 : c * x1 ^ (b 1).val = x0 ^ (b 1).val * c := relSW_pow' m _ _
      have h0 : c * x0 ^ (b 0).val = x1 ^ (b 0).val * c := relSW_pow m _ _
      calc c * (A * x1 ^ (b 1).val * x0 ^ (b 0).val)
          = A * (c * x1 ^ (b 1).val) * x0 ^ (b 0).val := by
            rw [← mul_assoc, ← mul_assoc, hcA]; group
        _ = A * x0 ^ (b 1).val * (c * x0 ^ (b 0).val) := by rw [h1]; group
        _ = A * (x0 ^ (b 1).val * x1 ^ (b 0).val) * c := by rw [h0]; group
        _ = A * (x1 ^ (b 0).val * x0 ^ (b 1).val) * c := by
            rw [((hc.pow_left _).pow_right _).eq]
        _ = _ := by group
  | @up m g ih =>
    have e := mk_shift (ih hx (Fin.tail b))
    simp only [map_mul] at e
    set x := mk (g1 (n := m) (Gate.X (d := d) (lv := lv)))
    have hcomm : Commute x (mk (shift (linPart g))) := mk_comm1' Gate.X _
    show mk (shift (FreeMonoid.of g)) * mk (xcol (m + 1) b) =
      mk (xcol (m + 1) (Fin.cons (b 0) (affMap g (Fin.tail b)))) * mk (shift (linPart g))
    rw [mk_xcol_succ, mk_xcol_succ, Fin.tail_cons, Fin.cons_zero, ← mul_assoc, e, mul_assoc,
      mul_assoc, (hcomm.pow_left _).eq]

/-- Every affine circuit is its translation column after its linear part. -/
theorem affine_collect {n : ℕ} (w : C d lv n) (hw : IsAffW w) :
    ∃ b, mk w = mk (xcol n b * lin w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨0, by simp [xcol_zero]⟩
  | mul_of x w ih =>
    obtain ⟨hx, hw⟩ := IsAffW.of_mul_left hw
    obtain ⟨b, hb⟩ := ih hw
    refine ⟨affMap x b, ?_⟩
    calc mk (FreeMonoid.of x * w) = mk (FreeMonoid.of x) * mk (xcol n b * lin w) := by
          rw [map_mul, hb]
      _ = mk (FreeMonoid.of x * xcol n b) * mk (lin w) := by simp only [map_mul, mul_assoc]
      _ = mk (xcol n (affMap x b) * linPart x) * mk (lin w) := by rw [push_xcol x hx b]
      _ = mk (xcol n (affMap x b) * lin (FreeMonoid.of x * w)) := by
          simp only [map_mul, lin, FreeMonoid.lift_eval_of, mul_assoc]

end Push

end QCert.PhaseAffine
