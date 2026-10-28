/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-free derivations: two consecutive runs and one more letter

`two_runs`: with `R(D, m) = σ_D ⋯ σ_{m-1}`, the word
`R(D, m) R(D', m-1) σ_{m-1}` is, up to a word of signs in front, again of
the form `R(e, m) R(e', m-1)`: `e = D'`, `e' = D - 1` when `D' < D` (no
sign), and `e = D' + 1`, `e' = D` when `D ≤ D'` (where `σ_{m-1}` meets
itself, Equation (23)).
-/
import QCert.RealCliffordCH.Sec8.A.Runs

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- Signs with indices below `2ⁿ`. -/
def PairsBd (n : ℕ) (ps : List (ℕ × ℕ)) : Prop := ∀ p ∈ ps, p.1 < 2 ^ n ∧ p.2 < 2 ^ n

theorem run_mem_bd {a k : ℕ} (hk : a + k < 2 ^ n) : ∀ j ∈ List.range' a k, j + 1 < 2 ^ n := by
  intro j hj; rw [List.mem_range'] at hj; omega

/-- The new starts of the two runs. -/
def tr1 (D D' : ℕ) : ℕ := if D ≤ D' then D' + 1 else D'
def tr2 (D D' : ℕ) : ℕ := if D ≤ D' then D else D - 1

theorem two_runs (hN : 4 ≤ 2 ^ n) {m D D' : ℕ} (hm : m < 2 ^ n) (hD : D ≤ m) (hD' : D' + 1 ≤ m) :
    ∃ ps, PairsBd n ps ∧
      DH n (run n D (m - D) ++ run n D' (m - 1 - D') ++ [sg n (m - 1)])
        (zzs n ps ++ run n (tr1 D D') (m - tr1 D D') ++ run n (tr2 D D') (m - 1 - tr2 D D')) := by
  by_cases hle : D ≤ D'
  · simp only [tr1, tr2, if_pos hle]
    -- `R(D', m-1)` is shifted through `R(D, m)`
    have h1 := DR.right [sg n (m - 1)] (run_shift_run (n := n) (a := D) (k := m - D) (c := D')
      (m := m - 1 - D') hle (by omega) (by omega))
    -- `R(D, m) σ_{m-1} = R(D, m-1) σ_{m-1} σ_{m-1}`
    have e1 : run n D (m - D) = run n D (m - 1 - D) ++ [sg n (m - 1)] := by
      rw [show m - D = (m - 1 - D) + 1 by omega, run_snoc, show D + (m - 1 - D) = m - 1 by omega]
    have h23 := DR.left (run n D (m - 1 - D)) (e23 n (a := m - 1) (by omega)).symm
    rw [show m - 1 + 1 = m by omega] at h23
    have hz1 := zz_through hN (js := List.range' D (m - 1 - D)) (run_mem_bd (by omega))
      (c := m - 1) (d := m) (by omega) hm
    have hz2 := zz_through hN (js := List.range' (D' + 1) (m - 1 - D')) (run_mem_bd (by omega))
      (c := swL (List.range' D (m - 1 - D)) (m - 1)) (d := swL (List.range' D (m - 1 - D)) m)
      (swL_lt (run_mem_bd (by omega)) (by omega)) (swL_lt (run_mem_bd (by omega)) hm)
    refine ⟨[(swL (List.range' (D' + 1) (m - 1 - D')) (swL (List.range' D (m - 1 - D)) (m - 1)),
      swL (List.range' (D' + 1) (m - 1 - D')) (swL (List.range' D (m - 1 - D)) m))], ?_, ?_⟩
    · intro p hp; simp only [List.mem_singleton] at hp; subst hp
      exact ⟨swL_lt (run_mem_bd (by omega)) (swL_lt (run_mem_bd (by omega)) (by omega)),
        swL_lt (run_mem_bd (by omega)) (swL_lt (run_mem_bd (by omega)) hm)⟩
    rw [show m - (D' + 1) = m - 1 - D' by omega]
    refine h1.trans ?_
    rw [e1]
    have h2 := DR.left (run n (D' + 1) (m - 1 - D')) (h23.trans hz1)
    have h3 := DR.right (run n D (m - 1 - D)) hz2
    simp only [run, sgL, zzs, List.map_cons, List.map_nil] at h2 h3 ⊢
    exact (DR.rfl' (by simp)).trans (h2.trans ((DR.rfl' (by simp)).trans
      (h3.trans (DR.rfl' (by simp)))))
  · simp only [tr1, tr2, if_neg hle]
    refine ⟨[], fun p hp => by simp at hp, ?_⟩
    have f1 : run n D' (m - D') = run n D' (m - 1 - D') ++ [sg n (m - 1)] := by
      rw [show m - D' = (m - 1 - D') + 1 by omega, run_snoc,
        show D' + (m - 1 - D') = m - 1 by omega]
    have f2 : run n D' (m - D') = run n D' (D - 1 - D') ++ run n (D - 1) (m - D + 1) := by
      rw [show m - D' = (D - 1 - D') + (m - D + 1) by omega, run_add,
        show D' + (D - 1 - D') = D - 1 by omega]
    have e1 : run n D' (m - 1 - D') ++ [sg n (m - 1)] =
        run n D' (D - 1 - D') ++ run n (D - 1) (m - D + 1) := f1.symm.trans f2
    rw [List.append_assoc, e1, ← List.append_assoc]
    have h1 := DR.right (run n (D - 1) (m - D + 1)) (run_far (n := n) (a := D) (k := m - D)
      (c := D') (m := D - 1 - D') (by omega) (by omega))
    have h2 := DR.left (run n D' (D - 1 - D')) (run_shift_run (n := n) (a := D - 1)
      (k := m - D + 1) (c := D - 1) (m := m - D) le_rfl (by omega) (by omega)).symm
    rw [show D - 1 + 1 = D by omega] at h2
    have e2 : run n D' (D - 1 - D') ++ run n (D - 1) (m - D + 1) = run n D' (m - D') := f2.symm
    refine h1.trans ((DR.rfl' (by simp)).trans (h2.trans (DR.rfl' ?_)))
    rw [← List.append_assoc, e2, show m - 1 - (D - 1) = m - D by omega]; simp [zzs]

end QCert.RealCliffordCH.Sec8
