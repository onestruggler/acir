/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: swap networks

The paper works in a PROP, where a gate on wires that are not the bottom
ones is defined by conjugation with swaps, the network being irrelevant up
to the topological rules (Definition 2.4, Section 2.2).  Our circuits form
a PRO and the swap is the circuit of Equation (8); `placeG` fixes one
network (`netL`).  This file shows that the choice does not matter, at
every width.

* The Coxeter relations for the swaps `swAt N j` (`sw_inv`, `sw_far`,
  `sw_braid`): the involution is (g), the far commutation is structural,
  the braid relation follows from (f2), (f3) on three wires.
* Local derivations moved anywhere (`lift_word`): a derivation between
  words of letters (`Eng.L`) on `K` wires holds on any `K` consecutive wires
  of a wider circuit.

Derivations here use no semantic step, so nothing here needs completeness
on fewer wires.
-/
import QCert.RealCliffordCH.Sec8.EngineN

namespace QCert.RealCliffordCH.Sec8.Net

open Circuit Eng

/-! ## Runs of the engine without semantic steps -/

/-- A step that is not a semantic step. -/
def Step.pure : Step → Bool
  | .sem .. => false
  | _ => true

theorem applyStep_pure {N : ℕ} {T : Tbl} (hT : AllD (N + 1) T) {cur nxt : List L} {s : Step}
    (hs : Step.pure s = true) (h : applyStep N T cur s = some nxt) :
    Derivable (theory (N + 1)) (circW (N + 1) cur) (circW (N + 1) nxt) := by
  cases s with
  | rw i k dir =>
    simp only [applyStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i e he
      split_ifs at h with hm
      cases h
      have hmem : e ∈ T := List.mem_of_getElem? he
      have he' : Derivable (theory (N + 1)) (circW (N + 1) (orient dir e).1)
          (circW (N + 1) (orient dir e).2) := by
        unfold orient; split_ifs
        · exact (hT e hmem).symm
        · exact hT e hmem
      rw [beq_iff_eq] at hm
      conv_lhs => rw [split_at cur i (orient dir e).1.length, hm]
      exact replace _ _ _ _ he'
  | sw i =>
    simp only [applyStep] at h
    split at h
    · rename_i x y hxy
      split_ifs at h with hd
      cases h
      conv_lhs => rw [split_at cur i 2, hxy]
      refine replace _ _ _ _ ?_
      rw [circW_cons, circW_cons, circW_cons, circW_cons, circW_nil, one_mul, one_mul]
      exact comm_disj (N + 1) x y hd
    · exact absurd h (by simp)
  | sem i len r => exact absurd hs (by simp [Step.pure])

theorem runSteps_pure {N : ℕ} {T : Tbl} (hT : AllD (N + 1) T) :
    ∀ {cur u : List L} {ss : List Step}, ss.all Step.pure = true → runSteps N T cur ss = some u →
      Derivable (theory (N + 1)) (circW (N + 1) cur) (circW (N + 1) u) := by
  intro cur u ss hp h
  induction ss generalizing cur with
  | nil => simp only [runSteps, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | cons s ss ihs =>
    simp only [List.all_cons, Bool.and_eq_true] at hp
    simp only [runSteps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i nxt hn
      exact (applyStep_pure hT hp.1 hn).trans (ihs hp.2 h)

/-- A run without semantic steps that passes `check` is a derivation; it
needs no completeness hypothesis. -/
theorem check_pure {N : ℕ} {T : Tbl} (hT : AllD (N + 1) T) {w v : List L} {ss : List Step}
    (hp : ss.all Step.pure = true) (h : check N T w v ss = true) :
    Derivable (theory (N + 1)) (circW (N + 1) w) (circW (N + 1) v) := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · rename_i u hu
    rw [beq_iff_eq] at h
    subst h
    exact runSteps_pure hT hp hu

/-! ## Moving local derivations -/

/-- The letter one wire up. -/
def upL : L → L
  | .H j => .H (j + 1) | .Z j => .Z (j + 1) | .C j => .C (j + 1) | .K j => .K (j + 1)
  | .S j => .S (j + 1)

@[simp] theorem upL_lo (x : L) : (upL x).lo = x.lo + 1 := by cases x <;> rfl
@[simp] theorem upL_wd (x : L) : (upL x).wd = x.wd := by cases x <;> rfl
@[simp] theorem down_upL (x : L) : (upL x).down = x := by cases x <;> rfl

/-- The letter `j` wires up. -/
def upLBy : ℕ → L → L
  | 0, x => x
  | j + 1, x => upL (upLBy j x)

@[simp] theorem upLBy_lo (j : ℕ) (x : L) : (upLBy j x).lo = x.lo + j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, upL_lo, ih]; omega

@[simp] theorem upLBy_wd (j : ℕ) (x : L) : (upLBy j x).wd = x.wd := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, upL_wd, ih]

theorem circW_up (N : ℕ) (l : List L) : circW (N + 1) (l.map upL) = shift (circW N l) := by
  rw [circW_shift N _ (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; simp), List.map_map]
  congr 2
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left (fun x _ => down_upL x)

/-- A derivation between words that fit on `K` wires holds on every wider
circuit, on the bottom wires. -/
theorem lift_top {K : ℕ} {a b : List L} (hab : ∀ x ∈ a ++ b, x.lo + x.wd ≤ K)
    (d : Derivable (theory K) (circW K a) (circW K b)) :
    ∀ N, K ≤ N → Derivable (theory N) (circW N a) (circW N b) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact d
  | succ N hKN ih =>
    rw [circW_top N a (fun x hx => le_trans (hab x (List.mem_append_left _ hx)) hKN),
      circW_top N b (fun x hx => le_trans (hab x (List.mem_append_right _ hx)) hKN)]
    exact derivable_padTop ih

/-- A derivation between words that fit on `K` wires holds on any `K`
consecutive wires `j, …, j + K - 1` of a wider circuit. -/
theorem lift_word {K : ℕ} {a b : List L} (hab : ∀ x ∈ a ++ b, x.lo + x.wd ≤ K)
    (d : Derivable (theory K) (circW K a) (circW K b)) :
    ∀ j N, j + K ≤ N →
      Derivable (theory N) (circW N (a.map (upLBy j))) (circW N (b.map (upLBy j))) := by
  intro j
  induction j with
  | zero =>
    intro N hN
    have e0 : ∀ l : List L, l.map (upLBy 0) = l := fun l => by
      induction l with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons, ih]; rfl
    rw [e0, e0]
    exact lift_top hab d N (by omega)
  | succ j ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have e : ∀ l : List L, l.map (upLBy (j + 1)) = (l.map (upLBy j)).map upL := by
      intro l; rw [List.map_map]; exact List.map_congr_left (fun x _ => rfl)
    rw [e, e, circW_up, circW_up]
    exact derivable_shift (ih M (by omega))

/-! ## The Coxeter relations of the swaps -/

/-- The swap of wires `j`, `j + 1`, as a letter. -/
theorem swAt_eq (N j : ℕ) : swAt N j = (L.S j).circ N := rfl

theorem upBy_S (j i : ℕ) : upLBy j (L.S i) = L.S (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [upLBy, ih, upL]; rfl

/-- (g) on two wires, in letters. -/
theorem inv2 : Derivable (theory 2) (circW 2 [L.S 0, L.S 0]) (circW 2 []) := by
  have h := derivable_rule Rule.g 0
  simpa [circW, drawn, map_mul, L.circ, place2] using h

/-- The swap is an involution. -/
theorem sw_inv (N j : ℕ) (hj : j + 2 ≤ N) :
    Derivable (theory N) (drawn [swAt N j, swAt N j]) 1 := by
  have h := lift_word (K := 2) (by decide) inv2 j N hj
  simpa [upBy_S, circW, swAt_eq] using h

/-- Swaps on disjoint pairs of wires commute. -/
theorem sw_far (N i j : ℕ) (h : i + 2 ≤ j) :
    Derivable (theory N) (drawn [swAt N i, swAt N j]) (drawn [swAt N j, swAt N i]) := by
  have := comm_disj N (L.S i) (L.S j) (by simp [disj, below, L.lo, L.wd]; omega)
  simpa [drawn, swAt_eq] using this

/-- The table for the braid relation on three wires: the definition (8) of
the swap on wires 0, 1 and 1, 2, (f2) on wires 0, 1 and 1, 2, and (f3). -/
def braidT : Tbl :=
  [([.S 0], [.C 0, .H 1, .H 0, .C 0, .H 1, .H 0, .C 0, .H 1, .H 0]),
   ([.S 1], [.C 1, .H 2, .H 1, .C 1, .H 2, .H 1, .C 1, .H 2, .H 1]),
   ([.H 1, .S 0], [.S 0, .H 0]),
   ([.H 2, .S 1], [.S 1, .H 1]),
   ([.C 1, .S 0, .S 1], [.S 0, .S 1, .C 0])]

theorem braidT_ok : AllD 3 braidT := by
  intro e he
  simp only [braidT, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Derivable.refl _
  · exact Derivable.refl _
  · have h := derivable_rule Rule.f2 1
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h
  · have h := derivable_shift (derivable_rule Rule.f2 0)
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h
  · have h := derivable_rule Rule.f3 0
    simpa [circW, drawn, map_mul, L.circ, place2, place1] using h

/-- The braid relation on three wires. -/
theorem braid3 : Derivable (theory 3) (circW 3 [.S 1, .S 0, .S 1]) (circW 3 [.S 0, .S 1, .S 0]) :=
  check_pure (N := 2) braidT_ok (ss := [.rw 0 1 false,
      .rw 8 2 false, .sw 9, .sw 7, .rw 8 3 false, .rw 6 4 false,
      .rw 5 2 false, .sw 6, .sw 4, .rw 5 3 false, .rw 3 4 false,
      .rw 2 2 false, .sw 3, .sw 1, .rw 2 3 false, .rw 0 4 false,
      .rw 2 0 true]) (by decide) (by decide)

/-- The braid relation. -/
theorem sw_braid (N j : ℕ) (hj : j + 3 ≤ N) :
    Derivable (theory N) (drawn [swAt N (j + 1), swAt N j, swAt N (j + 1)])
      (drawn [swAt N j, swAt N (j + 1), swAt N j]) := by
  have h := lift_word (K := 3) (by decide) braid3 j N hj
  simpa [upBy_S, circW, swAt_eq, Nat.add_comm] using h

end QCert.RealCliffordCH.Sec8.Net
