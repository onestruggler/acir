/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Projective Pauli points and the action of letter words

Toward Theorem 4.4.  The stabiliser chain of the completeness proof acts
on Pauli operators up to a phase.  Such a *point* on `n` wires is a list
of `n` exponent pairs `(a, b)` (the factor `X^a Z^b` on each wire, wire `0`
first), and a letter acts on it by conjugation (`ptAct`, Definition 2.6
with the phase forgotten): `H : (a, b) ↦ (2b, a)`, `S : (a, b) ↦ (a, b + 2a)`
and `CZ` adds each wire's `X` exponent to the other's `Z` exponent.  A word
acts letter by letter in time order (`ptRun`).

This is the action of the circuits on Pauli data (`toPt_run`), so words
equal up to a phase act alike (`ptRun_eq_of_E`) and a word acting trivially
on Pauli data fixes every point (`ptRun_triv`).
-/
import QCert.QutritClifford.Words
import QCert.QutritClifford.CosetCheck

namespace QCert.QutritClifford

/-- A Pauli operator up to a phase: the exponents `(a, b)` of `X^a Z^b` on
each wire, wire `0` first. -/
abbrev Pt := List (Fin 3 × Fin 3)

/-- `H` on one wire: `X^a Z^b ↦ X^{2b} Z^a`. -/
def h1 (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 := (2 * p.2, p.1)

/-- `S` on one wire: `X^a Z^b ↦ X^a Z^{b + 2a}`. -/
def s1 (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 := (p.1, p.2 + 2 * p.1)

/-- Conjugation by a letter. -/
def ptAct : Lt → Pt → Pt
  | .H 0, p :: y => h1 p :: y
  | .S 0, p :: y => s1 p :: y
  | .C 0, p :: q :: y => (p.1, p.2 + q.1) :: (q.1, q.2 + p.1) :: y
  | .H (j + 1), p :: y => p :: ptAct (.H j) y
  | .S (j + 1), p :: y => p :: ptAct (.S j) y
  | .C (j + 1), p :: y => p :: ptAct (.C j) y
  | _, y => y

/-- Conjugation by a word, its letters in time order. -/
def ptRun : List Lt → Pt → Pt
  | [], y => y
  | x :: l, y => ptRun l (ptAct x y)

/-- The point of the identity. -/
def isZ (y : Pt) : Bool := y.all (· == (0, 0))

theorem ptRun_append (a b : List Lt) (y : Pt) : ptRun (a ++ b) y = ptRun b (ptRun a y) := by
  induction a generalizing y with
  | nil => rfl
  | cons x a ih => exact ih _

@[simp] theorem ptRun_nil (y : Pt) : ptRun [] y = y := rfl

theorem ptRun_cons (x : Lt) (l : List Lt) (y : Pt) : ptRun (x :: l) y = ptRun l (ptAct x y) := rfl

theorem ptAct_up (x : Lt) (p : Fin 3 × Fin 3) (y : Pt) : ptAct x.up (p :: y) = p :: ptAct x y := by
  cases x <;> rfl

theorem ptRun_up : ∀ (l : List Lt) (p : Fin 3 × Fin 3) (y : Pt),
    ptRun (l.map Lt.up) (p :: y) = p :: ptRun l y
  | [], _, _ => rfl
  | x :: l, p, y => by
    simp only [List.map_cons, ptRun_cons, ptAct_up]; exact ptRun_up l p _

theorem length_ptAct : ∀ (x : Lt) (y : Pt), (ptAct x y).length = y.length
  | .H 0, [] => rfl
  | .H 0, _ :: _ => rfl
  | .S 0, [] => rfl
  | .S 0, _ :: _ => rfl
  | .C 0, [] => rfl
  | .C 0, [_] => rfl
  | .C 0, _ :: _ :: _ => rfl
  | .H (_ + 1), [] => rfl
  | .H (j + 1), _ :: y => by simp only [ptAct, List.length_cons, length_ptAct (.H j) y]
  | .S (_ + 1), [] => rfl
  | .S (j + 1), _ :: y => by simp only [ptAct, List.length_cons, length_ptAct (.S j) y]
  | .C (_ + 1), [] => rfl
  | .C (j + 1), _ :: y => by simp only [ptAct, List.length_cons, length_ptAct (.C j) y]

theorem length_ptRun : ∀ (l : List Lt) (y : Pt), (ptRun l y).length = y.length
  | [], _ => rfl
  | x :: l, y => by rw [ptRun_cons, length_ptRun l, length_ptAct]

theorem isZ_cons (p : Fin 3 × Fin 3) (y : Pt) : isZ (p :: y) = (p == (0, 0) && isZ y) := rfl

theorem h1_zero : ∀ p : Fin 3 × Fin 3, (h1 p == (0, 0)) = (p == (0, 0)) := by decide
theorem s1_zero : ∀ p : Fin 3 × Fin 3, (s1 p == (0, 0)) = (p == (0, 0)) := by decide
theorem cz_zero : ∀ p q : Fin 3 × Fin 3,
    (((p.1, p.2 + q.1) == (0, 0)) && ((q.1, q.2 + p.1) == (0, 0))) =
      ((p == (0, 0)) && (q == (0, 0))) := by decide

theorem isZ_ptAct : ∀ (x : Lt) (y : Pt), isZ (ptAct x y) = isZ y
  | .H 0, [] => rfl
  | .H 0, p :: y => by simp only [ptAct, isZ_cons, h1_zero]
  | .S 0, [] => rfl
  | .S 0, p :: y => by simp only [ptAct, isZ_cons, s1_zero]
  | .C 0, [] => rfl
  | .C 0, [_] => rfl
  | .C 0, p :: q :: y => by
    simp only [ptAct, isZ_cons, ← Bool.and_assoc, cz_zero]
  | .H (_ + 1), [] => rfl
  | .H (j + 1), p :: y => by simp only [ptAct, isZ_cons, isZ_ptAct (.H j) y]
  | .S (_ + 1), [] => rfl
  | .S (j + 1), p :: y => by simp only [ptAct, isZ_cons, isZ_ptAct (.S j) y]
  | .C (_ + 1), [] => rfl
  | .C (j + 1), p :: y => by simp only [ptAct, isZ_cons, isZ_ptAct (.C j) y]

theorem isZ_ptRun : ∀ (l : List Lt) (y : Pt), isZ (ptRun l y) = isZ y
  | [], _ => rfl
  | x :: l, y => by rw [ptRun_cons, isZ_ptRun l, isZ_ptAct]

/-! ### Letters on the bottom wires leave the others alone -/

/-- Letters on wire `0`. -/
def onW0 (x : Lt) : Bool := x.hi == 0

/-- Letters on wires `0, 1`. -/
def onW01 (x : Lt) : Bool := x.hi ≤ 1

theorem ptAct_w0 (x : Lt) (hx : onW0 x = true) (p : Fin 3 × Fin 3) (y : Pt) :
    ptAct x (p :: y) = ptAct x [p] ++ y := by
  rcases x with j | j | j <;> simp only [onW0, Lt.hi, beq_iff_eq] at hx
  · subst hx; rfl
  · subst hx; rfl
  · omega

theorem ptAct_w01 (x : Lt) (hx : onW01 x = true) (p q : Fin 3 × Fin 3) (y : Pt) :
    ptAct x (p :: q :: y) = ptAct x [p, q] ++ y := by
  rcases x with j | j | j <;> simp only [onW01, Lt.hi, decide_eq_true_eq] at hx
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  · obtain rfl : j = 0 := by omega
    rfl

theorem ptRun_w0 : ∀ (l : List Lt), l.all onW0 = true → ∀ (p : Fin 3 × Fin 3) (y : Pt),
    ∃ p', ptRun l [p] = [p'] ∧ ptRun l (p :: y) = p' :: y
  | [], _, p, _ => ⟨p, rfl, rfl⟩
  | x :: l, h, p, y => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hl : (ptAct x [p]).length = 1 := length_ptAct x [p]
    obtain ⟨p1, hp1⟩ : ∃ p1, ptAct x [p] = [p1] := by
      match e : ptAct x [p], hl with
      | [p1], _ => exact ⟨p1, rfl⟩
    obtain ⟨p', h1, h2⟩ := ptRun_w0 l h.2 p1 y
    refine ⟨p', by rw [ptRun_cons, hp1, h1], ?_⟩
    rw [ptRun_cons, ptAct_w0 x h.1, hp1, List.singleton_append, h2]

theorem ptRun_w01 : ∀ (l : List Lt), l.all onW01 = true → ∀ (p q : Fin 3 × Fin 3) (y : Pt),
    ∃ p' q', ptRun l [p, q] = [p', q'] ∧ ptRun l (p :: q :: y) = p' :: q' :: y
  | [], _, p, q, _ => ⟨p, q, rfl, rfl⟩
  | x :: l, h, p, q, y => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hl : (ptAct x [p, q]).length = 2 := length_ptAct x [p, q]
    obtain ⟨p1, q1, hp1⟩ : ∃ p1 q1, ptAct x [p, q] = [p1, q1] := by
      match e : ptAct x [p, q], hl with
      | [p1, q1], _ => exact ⟨p1, q1, rfl⟩
    obtain ⟨p', q', h1, h2⟩ := ptRun_w01 l h.2 p1 q1 y
    refine ⟨p', q', by rw [ptRun_cons, hp1, h1], ?_⟩
    rw [ptRun_cons, ptAct_w01 x h.1, hp1]
    exact h2

/-! ### The action of the circuits on Pauli data -/

/-- The point of Pauli data. -/
def toPt {n : ℕ} (P : PD n) : Pt := List.ofFn fun j => (P.a j, P.b j)

theorem toPt_cons {n : ℕ} (a0 b0 : Fin 3) (P : PD n) :
    toPt (P.cons a0 b0) = (a0, b0) :: toPt P := by
  simp only [toPt, PD.cons, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

theorem toPt_scale {n : ℕ} (c : Fin 3) (P : PD n) : toPt (PD.scale c P) = toPt P := rfl

theorem length_toPt {n : ℕ} (P : PD n) : (toPt P).length = n := List.length_ofFn

theorem toPt_surj {n : ℕ} (y : Pt) (h : y.length = n) : ∃ P : PD n, toPt P = y := by
  subst h
  refine ⟨⟨0, fun j => (y.get j).1, fun j => (y.get j).2⟩, ?_⟩
  simp only [toPt]
  exact List.ofFn_get y

theorem toPt_act : ∀ (n : ℕ) (x : Lt), x.hi < n → ∀ P : PD n,
    toPt (actC n (cw n [x]) P) = ptAct x (toPt P)
  | 0, x, h, _ => by cases x <;> simp [Lt.hi] at h
  | m + 1, x, h, P => by
    rw [← PD.cons_tl P, toPt_cons]
    by_cases hlo : 1 ≤ x.lo
    · have hw : cw (m + 1) [x] = top (cw m [x.down]) := cw_hi m [x] (by simpa [hi1] using hlo)
      rw [hw, actC_top, toPt_cons,
        toPt_act m x.down (by cases x <;> simp_all [Lt.hi, Lt.lo, Lt.down] <;> omega),
        ← ptAct_up, Lt.up_down x hlo]
    · rcases x with j | j | j <;> simp only [Lt.lo, Lt.hi] at hlo h
      · obtain rfl : j = 0 := by omega
        have hw : cw (m + 1) [.H 0] = bot (cw 1 [.H 0]) := cw_pad m [.H 0] (by decide)
        rw [hw, actC_bot (cw 1 [.H 0]) (P.a 0) (P.b 0) P.tl
          (r := (t1 (.H 0) ⟨0, P.a 0, P.b 0⟩).pd) (run1_ok [.H 0] rfl ⟨0, P.a 0, P.b 0⟩),
          toPt_scale, toPt_cons]
        rfl
      · obtain rfl : j = 0 := by omega
        have hw : cw (m + 1) [.S 0] = bot (cw 1 [.S 0]) := cw_pad m [.S 0] (by decide)
        rw [hw, actC_bot (cw 1 [.S 0]) (P.a 0) (P.b 0) P.tl
          (r := (t1 (.S 0) ⟨0, P.a 0, P.b 0⟩).pd) (run1_ok [.S 0] rfl ⟨0, P.a 0, P.b 0⟩),
          toPt_scale, toPt_cons]
        rfl
      · obtain rfl : j = 0 := by omega
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hw : cw (m' + 2) [.C 0] = bot2 (cw 2 [.C 0]) := cw_pad m' [.C 0] (by decide)
        rw [← PD.cons_tl P.tl, toPt_cons]
        show toPt (actC (m' + 2) (cw (m' + 2) [.C 0]) ((P.tl.tl.cons (P.tl.a 0) (P.tl.b 0)).cons
          (P.a 0) (P.b 0))) = _
        rw [hw, actC_bot2 (cw 2 [.C 0]) (P.a 0) (P.b 0) (P.tl.a 0) (P.tl.b 0) P.tl.tl
          (r := (t2 (.C 0) ⟨0, P.a 0, P.b 0, P.tl.a 0, P.tl.b 0⟩).pd)
          (run2_ok [.C 0] rfl ⟨0, P.a 0, P.b 0, P.tl.a 0, P.tl.b 0⟩), toPt_scale, toPt_cons,
          toPt_cons]
        rfl

theorem actC_cw_single {n : ℕ} (x : Lt) (l : List Lt) (P : PD n) :
    actC n (cw n (x :: l)) P = actC n (cw n l) (actC n (cw n [x]) P) := by
  simp only [cw, map_mul, one_mul]; rfl

/-- **Words act on points as circuits act on Pauli data.** -/
theorem toPt_run {n : ℕ} : ∀ (l : List Lt), Fits n l → ∀ P : PD n,
    toPt (actC n (cw n l) P) = ptRun l (toPt P)
  | [], _, P => by simp only [cw, actC_one, ptRun_nil]
  | x :: l, h, P => by
    rw [actC_cw_single, toPt_run l (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      toPt_act n x (h x List.mem_cons_self), ptRun_cons]

/-- Words equal up to a phase act alike on points. -/
theorem ptRun_eq_of_E {n : ℕ} {l r : List Lt} (h : E n l r) (hl : Fits n l) (hr : Fits n r)
    (y : Pt) (hy : y.length = n) : ptRun l y = ptRun r y := by
  obtain ⟨P, rfl⟩ := toPt_surj y hy
  rw [← toPt_run l hl, ← toPt_run r hr, actC_eq_of_E h]

/-- A word acting trivially on Pauli data fixes every point. -/
theorem ptRun_triv {n : ℕ} {l : List Lt} (h : actC n (cw n l) = 1) (hl : Fits n l)
    (y : Pt) (hy : y.length = n) : ptRun l y = y := by
  obtain ⟨P, rfl⟩ := toPt_surj y hy
  rw [← toPt_run l hl, h]; rfl

end QCert.QutritClifford
