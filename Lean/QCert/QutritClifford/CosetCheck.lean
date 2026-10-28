/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checking coset certificates, and completeness on one and two wires

Toward Theorem 4.4.  What the coset certificates of `Coset.lean` need
besides their data (`Cert1Data.lean`, `Cert2Data.lean`):

* the equations they are deduced from: (C2)-(C5) on one wire (`base1`);
  on two wires (C6)-(C14), (C2)-(C5) on each wire and the commutation of
  one-wire gates on different wires (`eq2A`), and the stabiliser facts of
  the two-wire library, each matched against an entry of a table
  (`Cert.eqsOk`, `Cert.eqs_valid_of`);
* how a word acting trivially on Pauli data comes out of a certificate:
  on one wire its coset is that of the empty word (`same1_rep`); on two
  wires, a representative acting like a local word is local
  (`isLoc2_rep`), and a local word acting trivially is derivably trivial
  given completeness on one wire (`local_trivial`).
-/
import QCert.QutritClifford.Words
import QCert.QutritClifford.Coset
import QCert.QutritClifford.Lib2

namespace QCert.QutritClifford

/-! ### The rules on one wire -/

/-- (C2)-(C5) on one wire, scalars dropped. -/
def base1 : Tbl :=
  [([.H 0, .H 0, .H 0, .H 0], []),
   ([.S 0, .S 0, .S 0], []),
   ([.S 0, .S 0, .H 0, .S 0, .S 0, .H 0, .S 0, .S 0, .H 0], []),
   ([.S 0, .H 0, .H 0, .S 0, .H 0, .H 0], [.H 0, .H 0, .S 0, .H 0, .H 0, .S 0])]

theorem base1_valid : Valid 1 base1 := by
  intro e he
  simp only [base1, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact E_of_rule Rule.C2 0 rfl rfl
  · exact E_of_rule Rule.C3 0 rfl rfl
  · exact E_of_rule Rule.C4 1 rfl rfl
  · exact E_of_rule Rule.C5 0 rfl rfl

/-! ### The equations of the two-wire certificate -/

/-- One-wire gates on different wires commute. -/
def comm2 : Tbl :=
  [([.H 0, .H 1], [.H 1, .H 0]), ([.H 0, .S 1], [.S 1, .H 0]),
   ([.S 0, .H 1], [.H 1, .S 0]), ([.S 0, .S 1], [.S 1, .S 0])]

/-- The equations at every coset of the two-wire certificate. -/
def eq2A : Tbl := base2 ++ base1 ++ base1.map (fun e => (e.1.map Lt.up, e.2.map Lt.up)) ++ comm2

theorem base1_fits : ∀ e ∈ base1, Fits 1 e.1 ∧ Fits 1 e.2 := by unfold Fits; decide

theorem eq2A_valid : Valid 2 eq2A := by
  intro e he
  simp only [eq2A, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · exact base2_valid e he
  · exact E.pad 1 (base1_valid e he) (base1_fits e he).1 (base1_fits e he).2
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact (base1_valid e' he').up
  · simp only [comm2, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact E.swap (by decide)

/-! ### Checking the equations of a certificate -/

/-- A table entry `rc ++ m = μ ++ rc` with `μ` local. -/
def stabMatch (loc rc m : List Lt) (e : List Lt × List Lt) : Bool :=
  e.1 == rc ++ m && e.2.drop (e.2.length - rc.length) == rc &&
    (e.2.take (e.2.length - rc.length)).all (fun x => loc.contains x)

namespace Cert

/-- Every equation of the certificate is an entry of `A` (at every coset),
or a stabiliser fact at its coset found in `S`. -/
def eqsOk (C : Cert) (A S : Tbl) : Bool :=
  C.eqs.all fun e =>
    (e.2.2 == 0 && A.contains (decW e.1, decW e.2.1)) ||
    (e.2.2 != 0 && decW e.2.1 == [] && S.any (stabMatch C.loc (C.repW (e.2.2 - 1)) (decW e.1)))

theorem eqs_valid_of {C : Cert} {A S : Tbl} (hA : Valid C.k A) (hS : Valid C.k S)
    (h : C.eqsOk A S = true) :
    ∀ e ∈ C.eqs, ∀ d, (e.2.2 = 0 ∨ e.2.2 = d + 1) → C.EqV (decW e.1) (decW e.2.1) d := by
  intro e he d hd
  have h1 := List.all_eq_true.1 h e he
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem, List.any_eq_true] at h1
  rcases h1 with ⟨-, hm⟩ | ⟨⟨hat, hr⟩, p, hp, hpm⟩
  · refine ⟨[], LocW.nil _, ?_⟩
    simpa using (E.refl (C.repW d)).append (hA _ hm)
  · have hd' : e.2.2 - 1 = d := by omega
    rw [hd'] at hpm
    simp only [stabMatch, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem]
      at hpm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hpm
    refine ⟨p.2.take (p.2.length - (C.repW d).length), h3, ?_⟩
    have hE := hS p hp
    have e2 : p.2 = p.2.take (p.2.length - (C.repW d).length) ++ C.repW d := by
      conv_lhs => rw [← List.take_append_drop (p.2.length - (C.repW d).length) p.2]
      rw [h2]
    rw [hr, List.append_nil, ← e2, ← h1]
    exact hE

theorem eqs_letters_of {C : Cert}
    (h : C.eqs.all (fun e => (decW e.1 ++ decW e.2.1).all (fun x => C.letters.contains x)) = true) :
    ∀ e ∈ C.eqs, ∀ x ∈ decW e.1 ++ decW e.2.1, x ∈ C.letters := by
  intro e he x hx
  have := List.all_eq_true.1 (List.all_eq_true.1 h e he) x hx
  simpa using this

theorem repW_of_le (C : Cert) {c : ℕ} (h : C.rep.length ≤ c) : C.repW c = [] := by
  simp only [repW, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
  rfl

end Cert

/-! ### Pauli tableaux of words acting trivially -/

theorem P1.pd_inj {p q : P1} (h : p.pd = q.pd) : p = q := by
  obtain ⟨c, a, b⟩ := p
  obtain ⟨c', a', b'⟩ := q
  have hc := congrArg PD.c h
  have ha := congrFun (congrArg PD.a h) 0
  have hb := congrFun (congrArg PD.b h) 0
  simp only [P1.pd] at hc ha hb
  simp only [Matrix.cons_val_zero] at ha hb
  rw [hc, ha, hb]

theorem P2.pd_inj {p q : P2} (h : p.pd = q.pd) : p = q := by
  obtain ⟨c, a0, b0, a1, b1⟩ := p
  obtain ⟨c', a0', b0', a1', b1'⟩ := q
  have hc := congrArg PD.c h
  have ha0 := congrFun (congrArg PD.a h) 0
  have hb0 := congrFun (congrArg PD.b h) 0
  have ha1 := congrFun (congrArg PD.a h) 1
  have hb1 := congrFun (congrArg PD.b h) 1
  simp only [P2.pd] at hc ha0 hb0 ha1 hb1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at ha0 hb0 ha1 hb1
  rw [hc, ha0, hb0, ha1, hb1]

theorem run1_triv {l : List Lt} (hl : l.all in1 = true) (h : actC 1 (cw 1 l) = 1) (p : P1) :
    run1 l p = p := by
  apply P1.pd_inj
  rw [← run1_ok l hl, h]; rfl

theorem run2_triv {l : List Lt} (hl : l.all in2 = true) (h : actC 2 (cw 2 l) = 1) (p : P2) :
    run2 l p = p := by
  apply P2.pd_inj
  rw [← run2_ok l hl, h]; rfl

theorem run1_append (a b : List Lt) (p : P1) : run1 (a ++ b) p = run1 b (run1 a p) := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih => exact ih _

theorem run2_append (a b : List Lt) (p : P2) : run2 (a ++ b) p = run2 b (run2 a p) := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih => exact ih _

theorem all_in1_of_fits {l : List Lt} (h : Fits 1 l) : l.all in1 = true := by
  simp only [List.all_eq_true, in1, beq_iff_eq]
  intro x hx; have := h x hx; omega

theorem all_in2_of_fits {l : List Lt} (h : Fits 2 l) : l.all in2 = true := by
  simp only [List.all_eq_true, in2, decide_eq_true_eq]
  intro x hx; have := h x hx; omega

/-- On one wire, a representative acting trivially is not a proper coset's. -/
theorem same1_rep {l : List Lt} (hl : Fits 1 l) (h : actC 1 (cw 1 l) = 1) : same1 l [] = true := by
  have := run1_triv (all_in1_of_fits hl) h
  simp only [same1, this, run1, beq_self_eq_true, Bool.and_self]

/-! ### Local words on two wires -/

/-- The local letters on two wires. -/
def loc2 : List Lt := [.H 0, .S 0, .H 1, .S 1]

def locLo (p : P2) : Bool := p.a1 == 0 && p.b1 == 0
def locHi (p : P2) : Bool := p.a0 == 0 && p.b0 == 0

/-- A word acting locally on the generators. -/
def isLoc2 (w : List Lt) : Bool :=
  locLo (run2 w ⟨0, 1, 0, 0, 0⟩) && locLo (run2 w ⟨0, 0, 1, 0, 0⟩) &&
  locHi (run2 w ⟨0, 0, 0, 1, 0⟩) && locHi (run2 w ⟨0, 0, 0, 0, 1⟩)

theorem t2_locLo : ∀ x ∈ loc2, ∀ c a0 b0 a1 b1 : Fin 3, locLo ⟨c, a0, b0, a1, b1⟩ = true →
    locLo (t2 x ⟨c, a0, b0, a1, b1⟩) = true := by decide

theorem t2_locHi : ∀ x ∈ loc2, ∀ c a0 b0 a1 b1 : Fin 3, locHi ⟨c, a0, b0, a1, b1⟩ = true →
    locHi (t2 x ⟨c, a0, b0, a1, b1⟩) = true := by decide

theorem run2_locLo : ∀ {μ : List Lt}, LocW loc2 μ → ∀ p, locLo p = true → locLo (run2 μ p) = true
  | [], _, _, h => h
  | x :: _, hμ, ⟨c, a0, b0, a1, b1⟩, h =>
    run2_locLo (fun y hy => hμ y (List.mem_cons_of_mem _ hy)) _
      (t2_locLo x (hμ x List.mem_cons_self) c a0 b0 a1 b1 h)

theorem run2_locHi : ∀ {μ : List Lt}, LocW loc2 μ → ∀ p, locHi p = true → locHi (run2 μ p) = true
  | [], _, _, h => h
  | x :: _, hμ, ⟨c, a0, b0, a1, b1⟩, h =>
    run2_locHi (fun y hy => hμ y (List.mem_cons_of_mem _ hy)) _
      (t2_locHi x (hμ x List.mem_cons_self) c a0 b0 a1 b1 h)

theorem fits_loc2 {μ : List Lt} (h : LocW loc2 μ) : Fits 2 μ := by
  intro x hx
  have := h x hx
  simp only [loc2, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> decide

/-- A representative acting like a local word acts locally. -/
theorem isLoc2_rep {μ r : List Lt} (hμ : LocW loc2 μ) (hr : Fits 2 r)
    (h : actC 2 (cw 2 (μ ++ r)) = 1) : isLoc2 r = true := by
  have hfμ := fits_loc2 hμ
  have hall := all_in2_of_fits (fits_append hfμ hr)
  have hinv : ∀ p, run2 μ (run2 (invW μ) p) = p := by
    intro p
    have hc : actC 2 (cw 2 (invW μ ++ μ)) = 1 := by
      rw [actC_eq_of_E (E_cancel' μ hfμ)]; exact map_one _
    rw [← run2_append]
    exact run2_triv (all_in2_of_fits (fits_append (fits_invW μ hfμ) hfμ)) hc p
  have key : ∀ p, run2 r p = run2 (invW μ) p := by
    intro p
    have := run2_triv hall h (run2 (invW μ) p)
    rw [run2_append, hinv] at this
    exact this
  simp only [isLoc2, key, Bool.and_eq_true]
  exact ⟨⟨⟨run2_locLo hμ.invW _ rfl, run2_locLo hμ.invW _ rfl⟩, run2_locHi hμ.invW _ rfl⟩,
    run2_locHi hμ.invW _ rfl⟩

/-! ### Local words acting trivially -/

theorem t2_lo : ∀ x : Lt, lo2 x = true → ∀ c a0 b0 a1 b1 : Fin 3,
    t2 x ⟨c, a0, b0, a1, b1⟩ =
      ⟨(t1 x ⟨c, a0, b0⟩).c, (t1 x ⟨c, a0, b0⟩).a, (t1 x ⟨c, a0, b0⟩).b, a1, b1⟩ := by
  intro x hx
  match x, hx with
  | .H 0, _ => decide
  | .S 0, _ => decide

theorem t2_hi : ∀ x : Lt, hi2 x = true → ∀ c a0 b0 a1 b1 : Fin 3,
    t2 x ⟨c, a0, b0, a1, b1⟩ =
      ⟨(t1 x.down ⟨c, a1, b1⟩).c, a0, b0, (t1 x.down ⟨c, a1, b1⟩).a, (t1 x.down ⟨c, a1, b1⟩).b⟩ := by
  intro x hx
  rcases x with j | j | j <;>
    simp only [hi2, Lt.lo, Lt.hi, Bool.and_eq_true, beq_iff_eq] at hx
  · obtain ⟨rfl, -⟩ := hx; decide
  · obtain ⟨rfl, -⟩ := hx; decide
  · omega

theorem run2_lo : ∀ l : List Lt, l.all lo2 = true → ∀ c a0 b0 a1 b1 : Fin 3,
    run2 l ⟨c, a0, b0, a1, b1⟩ =
      ⟨(run1 l ⟨c, a0, b0⟩).c, (run1 l ⟨c, a0, b0⟩).a, (run1 l ⟨c, a0, b0⟩).b, a1, b1⟩
  | [], _, _, _, _, _, _ => rfl
  | x :: l, h, c, a0, b0, a1, b1 => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [run2, run1, t2_lo x h.1]
    exact run2_lo l h.2 _ _ _ _ _

theorem run2_hi : ∀ l : List Lt, l.all hi2 = true → ∀ c a0 b0 a1 b1 : Fin 3,
    run2 l ⟨c, a0, b0, a1, b1⟩ =
      ⟨(run1 (l.map Lt.down) ⟨c, a1, b1⟩).c, a0, b0, (run1 (l.map Lt.down) ⟨c, a1, b1⟩).a,
        (run1 (l.map Lt.down) ⟨c, a1, b1⟩).b⟩
  | [], _, _, _, _, _, _ => rfl
  | x :: l, h, c, a0, b0, a1, b1 => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [run2, run1, List.map_cons, t2_hi x h.1]
    exact run2_hi l h.2 _ _ _ _ _

theorem loc2_split (x : Lt) (h : x ∈ loc2) : lo2 x = true ∨ hi2 x = true := by
  simp only [loc2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- A local word is its wire-0 letters followed by its wire-1 letters. -/
theorem E_sort_loc : ∀ {μ : List Lt}, LocW loc2 μ → E 2 μ (μ.filter lo2 ++ μ.filter hi2)
  | [], _ => E.refl _
  | x :: μ, hμ => by
    have ih := E_sort_loc (μ := μ) (fun y hy => hμ y (List.mem_cons_of_mem _ hy))
    have h1 : E 2 (x :: μ) (x :: (μ.filter lo2 ++ μ.filter hi2)) := (E.refl [x]).append ih
    refine h1.trans ?_
    rcases loc2_split x (hμ x List.mem_cons_self) with hx | hx
    · rw [List.filter_cons_of_pos hx, List.filter_cons_of_neg (by
        intro h; simp only [lo2, hi2, beq_iff_eq, Bool.and_eq_true] at hx h
        omega)]
      exact E.refl _
    · rw [List.filter_cons_of_neg (by
        intro h; simp only [lo2, hi2, beq_iff_eq, Bool.and_eq_true] at hx h
        omega), List.filter_cons_of_pos hx]
      have hd : ∀ y ∈ μ.filter lo2, Lt.disj y x = true := by
        intro y hy
        have hy' := (List.mem_filter.1 hy).2
        simp only [lo2, hi2, beq_iff_eq, Bool.and_eq_true, Lt.disj, Bool.or_eq_true,
          decide_eq_true_eq] at hx hy' ⊢
        omega
      have := (E.move_left (k := 2) x (μ.filter lo2) hd).symm.append (E.refl (μ.filter hi2))
      simpa [List.append_assoc] using this

theorem all_lo2_filter (μ : List Lt) : (μ.filter lo2).all lo2 = true := by
  simp only [List.all_eq_true, List.mem_filter]; exact fun x hx => hx.2

theorem all_hi2_filter (μ : List Lt) : (μ.filter hi2).all hi2 = true := by
  simp only [List.all_eq_true, List.mem_filter]; exact fun x hx => hx.2

theorem t1_zero : ∀ (x : Lt) (c : Fin 3), t1 x ⟨c, 0, 0⟩ = ⟨c, 0, 0⟩ := by
  intro x c
  match x with
  | .H 0 => revert c; decide
  | .S 0 => revert c; decide
  | .H (_ + 1) => rfl
  | .S (_ + 1) => rfl
  | .C _ => rfl

theorem run1_zero : ∀ (l : List Lt) (c : Fin 3), run1 l ⟨c, 0, 0⟩ = ⟨c, 0, 0⟩
  | [], _ => rfl
  | x :: l, c => by simp only [run1, t1_zero]; exact run1_zero l c

theorem lo2_in1 (x : Lt) (h : lo2 x = true) : in1 x = true := h

/-- **A local word acting trivially is derivably trivial**, given
completeness on one wire. -/
theorem local_trivial (hc : Complete 1) {μ : List Lt} (hμ : LocW loc2 μ)
    (h : actC 2 (cw 2 μ) = 1) : E 2 μ [] := by
  have hs := E_sort_loc hμ
  have h0 := all_lo2_filter μ
  have h1 := all_hi2_filter μ
  have hfit : Fits 2 (μ.filter lo2 ++ μ.filter hi2) :=
    fits_append (fun x hx => fits_loc2 hμ x (List.mem_of_mem_filter hx))
      (fun x hx => fits_loc2 hμ x (List.mem_of_mem_filter hx))
  have htr : actC 2 (cw 2 (μ.filter lo2 ++ μ.filter hi2)) = 1 := by
    rw [← actC_eq_of_E hs]; exact h
  have hrun := run2_triv (all_in2_of_fits hfit) htr
  have e0 : ∀ a b : Fin 3, run1 (μ.filter lo2) ⟨0, a, b⟩ = ⟨0, a, b⟩ := by
    intro a b
    have hx := hrun ⟨0, a, b, 0, 0⟩
    rw [run2_append, run2_lo _ h0, run2_hi _ h1, run1_zero] at hx
    simp only [P2.mk.injEq] at hx
    obtain ⟨hc', ha, hb, -, -⟩ := hx
    cases hq : run1 (μ.filter lo2) ⟨0, a, b⟩
    rw [hq] at hc' ha hb
    simp only at hc' ha hb
    rw [hc', ha, hb]
  have e1 : ∀ a b : Fin 3, run1 ((μ.filter hi2).map Lt.down) ⟨0, a, b⟩ = ⟨0, a, b⟩ := by
    intro a b
    have hx := hrun ⟨0, 0, 0, a, b⟩
    rw [run2_append, run2_lo _ h0, run1_zero, run2_hi _ h1] at hx
    simp only [P2.mk.injEq] at hx
    obtain ⟨hc', -, -, ha, hb⟩ := hx
    cases hq : run1 ((μ.filter hi2).map Lt.down) ⟨0, a, b⟩
    rw [hq] at hc' ha hb
    simp only at hc' ha hb
    rw [hc', ha, hb]
  have hin0 : (μ.filter lo2).all in1 = true := all_mono h0 lo2_in1
  have hin1 : ((μ.filter hi2).map Lt.down).all in1 = true := all_map_down h1 hi2_in1
  have p0 : E 1 (μ.filter lo2) [] :=
    pcomplete hc (same1_sound hin0 rfl (by simp only [same1, e0, run1, beq_self_eq_true,
      Bool.and_self]))
  have p1 : E 1 ((μ.filter hi2).map Lt.down) [] :=
    pcomplete hc (same1_sound hin1 rfl (by simp only [same1, e1, run1, beq_self_eq_true,
      Bool.and_self]))
  have q0 : E 2 (μ.filter lo2) [] := E.pad 1 p0 (fun x hx => by
    have := List.all_eq_true.1 h0 x hx
    simp only [lo2, beq_iff_eq] at this; omega) (fun _ h => nomatch h)
  have q1 : E 2 (μ.filter hi2) [] := by
    have := p1.up
    rwa [List.map_map, List.map_congr_left (l := μ.filter hi2) (g := id) (fun x hx => by
      have := List.all_eq_true.1 h1 x hx
      exact Lt.up_down x (by simpa [hi1] using hi2_hi1 x this)), List.map_id, List.map_nil] at this
  exact hs.trans (by simpa using q0.append q1)

end QCert.QutritClifford
