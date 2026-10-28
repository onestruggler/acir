/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-free derivations: the permutation part of the normal form

`PN n d m = R(d (m-1), m-1) ⋯ R(d 1, 1) R(d 0, 0)`, with `R(D, k) = σ_D ⋯ σ_{k-1}`
and `d k ≤ k` (a Lehmer code).  Appending a letter `σ_j`, `j + 1 < m`, gives
the same form again up to a word of signs in front (`push_sg`); a word of
signs passes it (`zzs_through`, `PN` being a word of `σ`s).
-/
import QCert.RealCliffordCH.Sec8.A.TwoRuns

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- The indices of the letters of the permutation part. -/
def pidx (d : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => List.range' (d m) (m - d m) ++ pidx d m

/-- The permutation part of the normal form, on the indices below `m`. -/
def PN (n : ℕ) (d : ℕ → ℕ) (m : ℕ) : List (PG (2 ^ n)) := sgL n (pidx d m)

theorem PN_zero (d : ℕ → ℕ) : PN n d 0 = [] := rfl

theorem PN_succ (d : ℕ → ℕ) (m : ℕ) : PN n d (m + 1) = run n (d m) (m - d m) ++ PN n d m := by
  simp [PN, pidx, sgL, run]

theorem pidx_congr {d d' : ℕ → ℕ} {m : ℕ} (h : ∀ k < m, d k = d' k) : pidx d m = pidx d' m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [pidx, h m (by omega), ih fun k hk => h k (by omega)]

theorem PN_congr {d d' : ℕ → ℕ} {m : ℕ} (h : ∀ k < m, d k = d' k) : PN n d m = PN n d' m := by
  rw [PN, PN, pidx_congr h]

theorem pidx_lt {d : ℕ → ℕ} {m : ℕ} (hd : ∀ k < m, d k ≤ k) : ∀ j ∈ pidx d m, j + 1 < m := by
  induction m with
  | zero => simp [pidx]
  | succ m ih =>
    intro j hj
    simp only [pidx, List.mem_append, List.mem_range'] at hj
    rcases hj with ⟨i, hi, rfl⟩ | hj
    · have := hd m (by omega); omega
    · have := ih (fun k hk => hd k (by omega)) j hj; omega

/-- `σ_j` passes the permutation part on the indices below `k ≤ j`. -/
theorem comm_PN {d : ℕ → ℕ} {j : ℕ} (hj : j + 1 < 2 ^ n) :
    ∀ k, k ≤ j → (∀ i < k, d i ≤ i) → DH n (PN n d k ++ [sg n j]) ([sg n j] ++ PN n d k)
  | 0, _, _ => DR.refl _
  | k + 1, hk, hd => by
    rw [PN_succ]
    have h1 := DR.left (run n (d k) (k - d k)) (comm_PN hj k (by omega) fun i hi => hd i (by omega))
    have h2 := DR.right (PN n d k) (comm_above (n := n) (a := d k) (k := k - d k) (j := j)
      (by have := hd k (by omega); omega) hj)
    exact (DR.rfl' (by simp)).trans (h1.trans ((DR.rfl' (by simp)).trans (h2.trans
      (DR.rfl' (by simp)))))

/-- A Lehmer code on the indices below `m`. -/
def Code (d : ℕ → ℕ) (m : ℕ) : Prop := ∀ k < m, d k ≤ k

/-- Appending `σ_j` to the permutation part. -/
theorem push_sg (hN : 4 ≤ 2 ^ n) : ∀ (m : ℕ) (d : ℕ → ℕ), m ≤ 2 ^ n → Code d m →
    ∀ j, j + 1 < m → ∃ ps d', PairsBd n ps ∧ Code d' m ∧
      DH n (PN n d m ++ [sg n j]) (zzs n ps ++ PN n d' m)
  | 0, _, _, _, j, hj => absurd hj (by omega)
  | m + 1, d, hm, hd, j, hj => by
    by_cases hjm : j + 1 < m
    · obtain ⟨ps, d', hps, hd', h⟩ := push_sg hN m d (by omega) (fun k hk => hd k (by omega)) j hjm
      have hz := zzs_through hN (js := List.range' (d m) (m - d m))
        (run_mem_bd (by have := hd m (by omega); omega)) hps
      refine ⟨ps.map fun p => (swL (List.range' (d m) (m - d m)) p.1,
        swL (List.range' (d m) (m - d m)) p.2), fun k => if k = m then d m else d' k, ?_, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact ⟨swL_lt (run_mem_bd (by have := hd m (by omega); omega)) (hps q hq).1,
          swL_lt (run_mem_bd (by have := hd m (by omega); omega)) (hps q hq).2⟩
      · intro k hk
        by_cases e : k = m
        · simp only [e, if_true]; exact hd m (by omega)
        · simp only [e, if_false]; exact hd' k (by omega)
      · rw [PN_succ, PN_succ, if_pos rfl,
          PN_congr (d := fun k => if k = m then d m else d' k) (d' := d') (m := m)
            (fun k hk => by simp [show k ≠ m by omega])]
        have h1 := DR.left (run n (d m) (m - d m)) h
        have h2 := DR.right (PN n d' m) hz
        exact (DR.rfl' (by simp)).trans (h1.trans ((DR.rfl' (by simp [run])).trans
          (h2.trans (DR.rfl' (by simp [run])))))
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain rfl : j = m' := by omega
      have hD := hd (j + 1) (by omega)
      have hD' := hd j (by omega)
      obtain ⟨ps, hps, h⟩ := two_runs hN (m := j + 1) (D := d (j + 1)) (D' := d j) (by omega)
        hD (by omega)
      refine ⟨ps, fun k => if k = j + 1 then tr1 (d (j + 1)) (d j)
        else if k = j then tr2 (d (j + 1)) (d j) else d k, hps, ?_, ?_⟩
      · intro k hk
        by_cases e1 : k = j + 1
        · simp only [e1, if_true, tr1]; split_ifs <;> omega
        · by_cases e2 : k = j
          · simp only [e1, e2, if_false, if_true, tr2]; split_ifs <;> omega
          · simp only [e1, e2, if_false]; exact hd k (by omega)
      · rw [PN_succ, PN_succ, PN_succ, PN_succ, if_pos rfl, if_neg (by omega), if_pos rfl,
          PN_congr (d := fun k => if k = j + 1 then tr1 (d (j + 1)) (d j)
            else if k = j then tr2 (d (j + 1)) (d j) else d k) (d' := d) (m := j)
            (fun k hk => by simp [show k ≠ j + 1 by omega, show k ≠ j by omega])]
        have hc := comm_PN (n := n) (d := d) (j := j) (by omega) j le_rfl
          (fun i hi => hd i (by omega))
        have h1 := DR.left (run n (d (j + 1)) (j + 1 - d (j + 1)) ++
          run n (d j) (j - d j)) hc
        have h2 := DR.right (PN n d j) h
        simp only [show j + 1 - 1 = j by omega] at h2
        exact (DR.rfl' (by simp)).trans (h1.trans ((DR.rfl' (by simp)).trans (h2.trans
          (DR.rfl' (by simp)))))

end QCert.RealCliffordCH.Sec8
