/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checked paths on a window are below the state

`pathOK P D A = true` (`SymForms.lean`) says that every state of the path `D`
from `A s` is integral at the exponent of `s` with fewer odd numerators on the
window: then the path is below `s` (`path_of_check`, by
`lev_lt_of_window_word`), and with a derivation it is a join
(`join_of_check`).
-/
import QCert.HadamardPi.SymForms
import QCert.HadamardPi.Join
import QCert.HadamardPi.Extend

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

/-- The check gives a path below `s`. -/
theorem path_of_check {n w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hfJ : ∀ j, (f j : ℕ) < piv s) {P : List ZL}
    {t : ℕ → ℤ} (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    {D A : List (Gen w)} (hc : pathOK P D A = true) :
    PathLt (lev s) (D.map (Gen.map f hf)) (run (A.map (Gen.map f hf)) s) := by
  classical
  apply pathLt_of_drop
  intro k hk'
  rw [List.length_map] at hk'
  have hck : stOK P (D.drop k ++ A) = true := by
    simp only [pathOK, List.all_eq_true, List.mem_range] at hc
    exact hc k (by omega)
  rw [← run_append, ← List.map_drop, ← List.map_append]
  set ws := D.drop k ++ A
  simp only [stOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck
  obtain ⟨hsome, hcnt⟩ := hck
  have hpv : (fun j : Fin w => num (col s (pj s (piv_pos hs))) (f j)) = pv P t := funext hP
  refine lev_lt_of_window_word hs hk f hf hfJ (fun j => zev ((divAt P ws j).getD dZ) t) ?_ ?_
  · intro j
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hsome j j.2)
    beta_reduce
    rw [hy, Option.getD_some, hpv, ← scwL_sound]
    exact zdivp_sound _ hy t
  · refine card_filter_lt (univ.filter fun j : Fin w => maybeOdd P ws j = true)
      (univ.filter fun j : Fin w => oddSure (P.getD j dZ) = true) ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_univ, true_and, maybeOdd] at hj
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hsome j j.2)
      beta_reduce
      rw [hy] at hj ⊢
      simp only [Bool.not_eq_true', Bool.not_eq_false'] at hj
      simp only [Option.getD_some]
      exact not_odd_of_allEven (by simpa using hj) t
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [hP j]; exact odd_of_oddSure hj t
    · rw [card_filter_univ_fin (maybeOdd P ws),
        card_filter_univ_fin (fun j => oddSure (P.getD j dZ))]
      exact hcnt

/-- A checked path with a derivation is a join. -/
theorem join_of_check {n w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hfJ : ∀ j, (f j : ℕ) < piv s) {P : List ZL}
    {t : ℕ → ℤ} (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    {D A B : List (Gen w)} (hd : Derivable Fig6 (ofList (D ++ A)) (ofList B))
    (hc : pathOK P D A = true) :
    Join s (A.map (Gen.map f hf)) (B.map (Gen.map f hf)) := by
  refine ⟨D.map (Gen.map f hf), ?_, path_of_check f hf hs hk hfJ hP hc⟩
  rw [← List.map_append]
  exact der_map f hf hd

end QCert.HadamardPi
