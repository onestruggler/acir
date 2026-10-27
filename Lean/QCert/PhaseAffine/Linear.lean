/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of the linear fragment

Linear circuits (multipliers, `CX`, crossings) with the same linear map are
equal in `Aff_d` (`linear_complete0`).  Blake (arXiv:2603.06466) obtains
this step of Lemma 3 from Lafont's normal form theorem for linear circuits
[17], with Lafont's rules derived in `Aff_d` (Lemma 16); here it is proved
from the normal form of `LinearNF`: every linear circuit is a stair `S(v)`,
a fan `F(c)` and a linear circuit `B` one wire up, and the map of
`S(v) F(c) ↑B` determines `v` (the image of `e₀`), `B` (the map on the upper
wires, equal in the theory by induction on the number of wires) and `c`
(the first row).

The relabellings are computed through the affine map of each generator
(`gen_f`, the map `affMap` of `Translation`).
-/
import QCert.PhaseAffine.LinearNF

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-! ### Pairs on some of the wires -/

namespace PA

theorem high_eq_tail {n : ℕ} (v : Lab d (n + 1)) : high v = Fin.tail v := by
  funext j; simp only [high, Fin.tail]; congr 1; ext; simp; omega

theorem onTop_f_zero' {n : ℕ} (p : PA d n) (v : Lab d (n + 1)) : (onTop p).f v 0 = v 0 :=
  onTop_f_zero p v 0 rfl

theorem onTop_f_succ {n : ℕ} (p : PA d n) (v : Lab d (n + 1)) (j : Fin n) :
    (onTop p).f v j.succ = p.f (Fin.tail v) j := by
  rw [onTop_f_pos p v j.succ (by simp), high_eq_tail]; congr 1

theorem onTop_q' {n : ℕ} (p : PA d n) (v : Lab d (n + 1)) : (onTop p).q v = p.q (Fin.tail v) := by
  rw [onTop_q, high_eq_tail]

theorem low_one {n : ℕ} (v : Lab d (n + 1)) : (low v : Lab d 1) = fun _ => v 0 := by
  funext i; simp only [low]; congr 1; ext; simp [Fin.fin_one_eq_zero i]

theorem onBottom1_f_zero {n : ℕ} (p : PA d 1) (v : Lab d (n + 1)) :
    (onBottom n p).f v 0 = p.f (fun _ => v 0) 0 := by
  rw [onBottom_f_lt _ _ _ _ (by simp), low_one]; rfl

theorem onBottom1_f_succ {n : ℕ} (p : PA d 1) (v : Lab d (n + 1)) (j : Fin n) :
    (onBottom n p).f v j.succ = v j.succ :=
  onBottom_f_ge _ _ _ _ (by simp)

theorem onBottom1_q {n : ℕ} (p : PA d 1) (v : Lab d (n + 1)) :
    (onBottom n p).q v = p.q (fun _ => v 0) := by
  rw [onBottom_q, low_one]

end PA

local notation "𝒢" => gateData d lv

/-! ### Linear circuits fix `0` and carry no phase -/

theorem gen_lin {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) :
    ((𝒢).gen x).f 0 = 0 ∧ ∀ v, ((𝒢).gen x).q v = 0 := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsLin])
  | gate3 g => exact absurd hx (by simp [Gen.IsLin])
  | @gate1 m g =>
    cases g <;> simp only [Gen.IsLin] at hx
    refine ⟨funext fun i => ?_, fun v => rfl⟩
    show (PA.onBottom m _).f 0 i = 0
    by_cases h : (i : ℕ) < 1
    · rw [PA.onBottom_f_lt _ _ _ _ h]; simp [gateData, PA.perm, PA.low]
    · rw [PA.onBottom_f_ge _ _ _ _ h]; rfl
  | @gate2 m g =>
    refine ⟨funext fun i => ?_, fun v => ?_⟩
    · show (PA.onBottom m _).f 0 i = 0
      by_cases h : (i : ℕ) < 2
      · rw [PA.onBottom_f_lt _ _ _ _ h]
        cases g <;> simp [gateData, PA.perm, PA.low] <;> (interval_cases (i : ℕ) <;> simp)
      · rw [PA.onBottom_f_ge _ _ _ _ h]; rfl
    · cases g <;> rfl
  | @up m g ih =>
    obtain ⟨h0, hq⟩ := ih hx
    refine ⟨funext fun i => ?_, fun v => ?_⟩
    · show (PA.onTop _).f 0 i = 0
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [PA.onTop_f_zero']; rfl
      · rw [PA.onTop_f_succ]; exact congrFun h0 j
    · show (PA.onTop _).q v = 0
      rw [PA.onTop_q']; exact hq _

theorem sem_lin {n : ℕ} (w : C d lv n) (hw : IsLinW w) :
    ((𝒢).sem n w).f 0 = 0 ∧ ∀ v, ((𝒢).sem n w).q v = 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨rfl, fun v => rfl⟩
  | mul_of x w ih =>
    have hx : x.IsLin := hw x (by simp)
    have hw' : IsLinW w := fun y hy => hw y (by rw [FreeMonoid.toList_of_mul]; simp [hy])
    obtain ⟨h0, hq⟩ := ih hw'
    obtain ⟨g0, gq⟩ := gen_lin x hx
    rw [map_mul, GateData.sem_of]
    exact ⟨by simp [h0, g0], fun v => by simp [hq, gq]⟩

/-! ### The relabelling of an affine generator -/

namespace PA

/-- An operator on the bottom two wires, on labels written with `Fin.cons`. -/
theorem onBottom2_f {m : ℕ} (p : PA d 2) (b : Lab d (m + 2)) :
    (onBottom m p).f b =
      Fin.cons (p.f ![b 0, b 1] 0) (Fin.cons (p.f ![b 0, b 1] 1) (Fin.tail (Fin.tail b))) := by
  have hl : (low b : Lab d 2) = ![b 0, b 1] := by
    funext i; fin_cases i <;> rfl
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [onBottom_f_lt _ _ _ _ (by simp), hl, Fin.cons_zero]; rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rw [onBottom_f_lt _ _ _ _ (by simp), hl]; rfl
    · rw [onBottom_f_ge _ _ _ _ (by simp only [Fin.val_succ]; omega)]; rfl

end PA

theorem cons_tail_tail {m : ℕ} (b : Lab d (m + 2)) :
    (Fin.cons (b 1) (Fin.tail (Fin.tail b)) : Lab d (m + 1)) = Fin.tail b := by
  funext i; refine Fin.cases rfl (fun k => rfl) i

/-- An affine generator relabels by its affine map. -/
theorem gen_f {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) (b : Lab d n) :
    ((𝒢).gen x).f b = affMap x b := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsAff])
  | gate3 g => exact absurd hx (by simp [Gen.IsAff])
  | @gate1 m g =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show (PA.onBottom m ((𝒢).gate1 g)).f b 0 = affMap (Gen.gate1 g) b 0
      rw [PA.onBottom1_f_zero]
      cases g with
      | X => simp [affMap, gateData, PA.perm]
      | M a => simp [affMap, gateData, PA.perm]
      | Z h => exact absurd hx (by simp [Gen.IsAff])
      | S h => exact absurd hx (by simp [Gen.IsAff])
      | T h => exact absurd hx (by simp [Gen.IsAff])
    · show (PA.onBottom m ((𝒢).gate1 g)).f b j.succ = affMap (Gen.gate1 g) b j.succ
      rw [PA.onBottom1_f_succ]
      cases g with
      | X => simp [affMap]; rfl
      | M a => simp [affMap]; rfl
      | Z h => exact absurd hx (by simp [Gen.IsAff])
      | S h => exact absurd hx (by simp [Gen.IsAff])
      | T h => exact absurd hx (by simp [Gen.IsAff])
  | @gate2 m g =>
    show (PA.onBottom m ((𝒢).gate2 g)).f b = affMap (Gen.gate2 g) b
    rw [PA.onBottom2_f]
    cases g with
    | CX =>
      simp only [affMap, gateData, PA.perm, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [cons_tail_tail]
    | SWAP => simp [affMap, gateData, PA.perm]
  | @up m g ih =>
    show (PA.onTop ((𝒢).gen g)).f b = affMap (Gen.up g) b
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [PA.onTop_f_zero']; simp [affMap]
    · rw [PA.onTop_f_succ, ih hx]; simp [affMap]

/-! ### The relabellings of the pieces of the normal form -/

theorem sem_f_mul {n : ℕ} (w v : C d lv n) (b : Lab d n) :
    ((𝒢).sem n (w * v)).f b = ((𝒢).sem n w).f (((𝒢).sem n v).f b) := by
  rw [map_mul]; rfl

theorem sem_f_shift {n : ℕ} (w : C d lv n) (y0 : ZMod d) (y : Lab d n) :
    ((𝒢).sem (n + 1) (shift w)).f (Fin.cons y0 y) = Fin.cons y0 (((𝒢).sem n w).f y) := by
  rw [GateData.sem_shift]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [PA.onTop_f_zero', Fin.cons_zero, Fin.cons_zero]
  · rw [PA.onTop_f_succ, Fin.tail_cons, Fin.cons_succ]

theorem sem_q_shift {n : ℕ} (w : C d lv n) (y0 : ZMod d) (y : Lab d n) :
    ((𝒢).sem (n + 1) (shift w)).q (Fin.cons y0 y) = ((𝒢).sem n w).q y := by
  rw [GateData.sem_shift, PA.onTop_q', Fin.tail_cons]

theorem sem_f_M {n : ℕ} (a : (ZMod d)ˣ) (y0 : ZMod d) (y : Lab d n) :
    ((𝒢).sem (n + 1) (g1 (Gate.M a))).f (Fin.cons y0 y) = Fin.cons ((a : ZMod d) * y0) y := by
  rw [GateData.sem_of, gen_f (Gen.gate1 (Gate.M a)) (by exact trivial)]
  simp [affMap]

theorem sem_f_SW {m : ℕ} (x0 x1 : ZMod d) (r : Lab d m) :
    ((𝒢).sem (m + 2) (g2 Gate.SWAP)).f (Fin.cons x0 (Fin.cons x1 r)) =
      Fin.cons x1 (Fin.cons x0 r) := by
  rw [GateData.sem_of, gen_f (Gen.gate2 Gate.SWAP) (by exact trivial)]
  simp [affMap]

theorem sem_f_CX_pow {m : ℕ} (k : ℕ) (x0 x1 : ZMod d) (r : Lab d m) :
    ((𝒢).sem (m + 2) (g2 Gate.CX ^ k)).f (Fin.cons x0 (Fin.cons x1 r)) =
      Fin.cons (x0 + k * x1) (Fin.cons x1 r) := by
  induction k generalizing x0 with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, sem_f_mul, GateData.sem_of, gen_f (Gen.gate2 Gate.CX) (by exact trivial)]
    simp only [affMap, Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
    rw [ih]
    congr 1; push_cast; ring

/-- The fan adds `c · (x₁, …, x_n)` to `x₀`. -/
theorem sem_fanW [NeZero d] : ∀ (n : ℕ) (c : Lab d n) (y0 : ZMod d) (y : Lab d n),
    ((𝒢).sem (n + 1) (fanW n c)).f (Fin.cons y0 y) = Fin.cons (y0 + ∑ j, c j * y j) y
  | 0, c, y0, y => by simp [fanW]
  | n + 1, c, y0, y => by
    rw [← Fin.cons_self_tail y]
    simp only [fanW, sem_f_mul, sem_f_CX_pow, sem_f_SW, sem_f_shift, sem_fanW n,
      ZMod.natCast_zmod_val]
    congr 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

theorem sem_q_fanW (n : ℕ) (c : Lab d n) (b : Lab d (n + 1)) :
    ((𝒢).sem (n + 1) (fanW n c)).q b = 0 :=
  (sem_lin _ (isLinW_fanW n c)).2 b

section Field

variable [Fact d.Prime]

theorem cons_one_zero (n : ℕ) :
    (Fin.cons 1 0 : Lab d (n + 2)) = Fin.cons 1 (Fin.cons 0 0) := by
  congr 1; funext i; refine Fin.cases rfl (fun k => rfl) i

/-- The stair of `v` sends `e₀` to `v`. -/
theorem sem_stairW : ∀ (n : ℕ) (v : Lab d (n + 1)), v ≠ 0 →
    ((𝒢).sem (n + 1) (stairW n v)).f (Fin.cons 1 0) = v
  | 0, v, hv => by
    have h0 : v 0 ≠ 0 := tail_ne_zero_of hv (Subsingleton.elim _ _)
    rw [stairW, sem_f_M, unitOf_val h0, mul_one]
    funext i; rw [Fin.fin_one_eq_zero i]; rfl
  | n + 1, v, hv => by
    by_cases ht : Fin.tail v = 0
    · have h0 := tail_ne_zero_of hv ht
      rw [stairW, if_pos ht, sem_f_M, unitOf_val h0, mul_one, ← ht, Fin.cons_self_tail]
    · rw [stairW, if_neg ht, sem_f_mul, sem_f_mul, cons_one_zero, sem_f_SW, sem_f_CX_pow,
        sem_f_shift, ZMod.natCast_zmod_val, mul_one, zero_add, sem_stairW n _ ht,
        Fin.cons_self_tail]

end Field

/-! ### Completeness -/

theorem isLinW_zero_width {w : C d lv 0} (hw : IsLinW w) : w = 1 := by
  have : FreeMonoid.toList w = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have h := hw x hx
    cases x with
    | gate0 c => simp [Gen.IsLin] at h
  rw [← FreeMonoid.ofList_toList w, this]
  rfl

section Complete

variable [Fact d.Prime]

/-- Linear circuits with the same linear map are equal in `Aff_d`: two
normal forms `S(v) F(c) ↑B` with the same map have the same `v` (the image
of `e₀`), the same `B` (the map on the upper wires, by induction) and the
same `c` (the first row). -/
theorem linear_mk : ∀ (n : ℕ) {w v : C d 0 n}, IsLinW w → IsLinW v →
    (gateData d 0).sem n w = (gateData d 0).sem n v → mk w = mk v
  | 0, w, v, hw, hv, _ => by rw [isLinW_zero_width hw, isLinW_zero_width hv]
  | n + 1, w, v, hw, hv, h => by
    obtain ⟨a, _, ha, ⟨c, u, hu, rfl⟩, ew⟩ := decompose n w hw
    obtain ⟨b, _, hb, ⟨c', u', hu', rfl⟩, ev⟩ := decompose n v hv
    have ew' : mk w = mk (stairW n a * (fanW n c * shift u)) := by
      rw [ew, map_mul, map_mul]; rfl
    have ev' : mk v = mk (stairW n b * (fanW n c' * shift u')) := by
      rw [ev, map_mul, map_mul]; rfl
    have sw := pa_sound admissible_zero (mk_eq_iff.1 ew')
    have sv := pa_sound admissible_zero (mk_eq_iff.1 ev')
    rw [map_mul] at sw sv
    have hPA := sw.symm.trans (h.trans sv)
    -- the action of the fan part
    have hA : ∀ (c : Lab d n) (u : C d 0 n) (y0 : ZMod d) (y : Lab d n),
        ((gateData d 0).sem (n + 1) (fanW n c * shift u)).f (Fin.cons y0 y) =
          Fin.cons (y0 + ∑ j, c j * ((gateData d 0).sem n u).f y j)
            (((gateData d 0).sem n u).f y) := by
      intro c u y0 y
      rw [sem_f_mul, sem_f_shift, sem_fanW]
    have hAq : ∀ (c : Lab d n) (u : C d 0 n) (y0 : ZMod d) (y : Lab d n),
        ((gateData d 0).sem (n + 1) (fanW n c * shift u)).q (Fin.cons y0 y) =
          ((gateData d 0).sem n u).q y := by
      intro c u y0 y
      rw [map_mul, PA.mul_q, sem_q_shift, sem_q_fanW, add_zero]
    -- the stairs agree: both send `e₀` to the image of `e₀`
    have e0 : ∀ (c : Lab d n) (u : C d 0 n), IsLinW u →
        ((gateData d 0).sem (n + 1) (fanW n c * shift u)).f (Fin.cons 1 0) = Fin.cons 1 0 := by
      intro c u hu
      rw [hA, (sem_lin u hu).1]
      congr 1; simp
    have hab : a = b := by
      have := congrArg (fun p => p.f (Fin.cons 1 0)) hPA
      simp only [PA.mul_f, Function.comp_apply, e0 c u hu, e0 c' u' hu'] at this
      rwa [sem_stairW n a ha, sem_stairW n b hb] at this
    subst hab
    -- cancel the stair
    obtain ⟨r, hr⟩ := mk_surjective ((stair (lv := 0) n a)⁻¹)
    have hr' : (gateData d 0).sem (n + 1) r * (gateData d 0).sem (n + 1) (stairW n a) = 1 := by
      rw [← map_mul]
      have : mk (r * stairW (lv := 0) n a) = mk 1 := by
        rw [map_mul, hr, map_one]; exact inv_mul_cancel _
      rw [pa_sound admissible_zero (mk_eq_iff.1 this), map_one]
    have hFF : (gateData d 0).sem (n + 1) (fanW n c * shift u) =
        (gateData d 0).sem (n + 1) (fanW n c' * shift u') := by
      calc _ = ((gateData d 0).sem (n + 1) r * (gateData d 0).sem (n + 1) (stairW n a)) *
            (gateData d 0).sem (n + 1) (fanW n c * shift u) := by rw [hr', one_mul]
        _ = _ := by rw [mul_assoc, hPA, ← mul_assoc, hr', one_mul]
    -- the upper wires
    have hf : ∀ y, ((gateData d 0).sem n u).f y = ((gateData d 0).sem n u').f y := by
      intro y
      have := congrArg (fun p => Fin.tail (p.f (Fin.cons 0 y))) hFF
      simpa only [hA, Fin.tail_cons] using this
    have hq : ∀ y, ((gateData d 0).sem n u).q y = ((gateData d 0).sem n u').q y := by
      intro y
      have := congrArg (fun p => p.q (Fin.cons 0 y)) hFF
      simpa only [hAq] using this
    have huu : (gateData d 0).sem n u = (gateData d 0).sem n u' :=
      PA.ext (funext hf) (funext hq)
    have hmu := linear_mk n hu hu' huu
    -- the fans
    have hsurj : Function.Surjective ((gateData d 0).sem n u).f := by
      obtain ⟨r', hr'⟩ := mk_surjective ((mk u : Q d 0 n)⁻¹)
      have : mk (u * r') = mk (1 : C d 0 n) := by
        rw [map_mul, hr', map_one]; exact mul_inv_cancel _
      have e := pa_sound admissible_zero (mk_eq_iff.1 this)
      rw [map_mul, map_one] at e
      intro z
      refine ⟨((gateData d 0).sem n r').f z, ?_⟩
      have := congrArg (fun p => p.f z) e
      simpa only [PA.mul_f, Function.comp_apply, PA.one_f, id] using this
    have hcc : c = c' := by
      have hs : ∀ z : Lab d n, ∑ j, c j * z j = ∑ j, c' j * z j := by
        intro z
        obtain ⟨y, rfl⟩ := hsurj z
        have := congrArg (fun p => p.f (Fin.cons 0 y) 0) hFF
        simp only [hA, Fin.cons_zero, zero_add] at this
        rwa [hf y] at this ⊢
      funext j
      have := hs (Pi.single j 1)
      simpa [Pi.single_apply] using this
    subst hcc
    rw [ew, ev, hmu]

end Complete

/-- Completeness of the linear fragment of `Aff_d`: linear circuits
(multipliers, controlled additions, crossings) with the same linear map are
equal in `Aff_d`.  The paper obtains this from Lafont's normal form theorem
for linear circuits [17] (whose rules (43)–(51) it derives in `Aff_d`,
Lemma 16); here it is the normal form of `LinearNF` and `linear_mk`. -/
theorem linear_complete0 [Fact d.Prime] {n : ℕ} {w v : C d 0 n} (hw : IsLinW w)
    (hv : IsLinW v) (h : (gateData d 0).sem n w = (gateData d 0).sem n v) :
    Derivable (theory d 0 n) w v :=
  mk_eq_iff.1 (linear_mk n hw hv h)

end QCert.PhaseAffine
