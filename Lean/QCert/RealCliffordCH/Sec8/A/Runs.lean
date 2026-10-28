/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-free derivations: words of `σ`s and runs

* `sgL js`, the word `σ_{j₁} ⋯ σ_{jₖ}`; a word of sign letters passes it
  from right to left, renamed by the transpositions (`zzs_through`);
* runs `run a k = σ_a σ_{a+1} ⋯ σ_{a+k-1}`: a `σ_j` far below or above a run
  commutes with it (`comm_below`, `comm_above`), one inside it is shifted up
  by one (`run_shift`), and so is a run inside it (`run_shift_run`).
-/
import QCert.RealCliffordCH.Sec8.A.Sigma

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- The word `σ_{j₁} ⋯ σ_{jₖ}`. -/
def sgL (n : ℕ) (js : List ℕ) : List (PG (2 ^ n)) := js.map (sg n)

/-- The renaming of a sign moved left past `σ_{j₁} ⋯ σ_{jₖ}`. -/
def swL (js : List ℕ) (x : ℕ) : ℕ := js.foldr (fun j y => swN j (j + 1) y) x

/-- A word of sign letters. -/
def zzs (n : ℕ) (ps : List (ℕ × ℕ)) : List (PG (2 ^ n)) := ps.map fun p => Zz n p.1 p.2

theorem swN_lt' {j x : ℕ} (hj : j + 1 < 2 ^ n) (hx : x < 2 ^ n) : swN j (j + 1) x < 2 ^ n := by
  unfold swN; split_ifs <;> omega

theorem swL_lt {js : List ℕ} (hjs : ∀ j ∈ js, j + 1 < 2 ^ n) {x : ℕ} (hx : x < 2 ^ n) :
    swL js x < 2 ^ n := by
  induction js with
  | nil => exact hx
  | cons j js ih =>
    exact swN_lt' (hjs j (by simp)) (ih fun i hi => hjs i (List.mem_cons_of_mem _ hi))

/-- A pivot away from `j, j+1`. -/
theorem sg_zz' (hN : 4 ≤ 2 ^ n) {j c d : ℕ} (hj : j + 1 < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) :
    DH n [sg n j, Zz n c d] [Zz n (swN j (j + 1) c) (swN j (j + 1) d), sg n j] := by
  by_cases h0 : j = 0
  · exact sg_zz hj (p := 2) (by omega) (by omega) (by omega) hc hd
  · exact sg_zz hj (p := 0) (by omega) (by omega) (by omega) hc hd

/-- A sign letter passes a word of `σ`s. -/
theorem zz_through (hN : 4 ≤ 2 ^ n) {js : List ℕ} (hjs : ∀ j ∈ js, j + 1 < 2 ^ n) {c d : ℕ}
    (hc : c < 2 ^ n) (hd : d < 2 ^ n) :
    DH n (sgL n js ++ [Zz n c d]) ([Zz n (swL js c) (swL js d)] ++ sgL n js) := by
  induction js with
  | nil => exact DR.refl _
  | cons j js ih =>
    have hjs' : ∀ i ∈ js, i + 1 < 2 ^ n := fun i hi => hjs i (List.mem_cons_of_mem _ hi)
    exact (DR.cons (sg n j) (ih hjs')).trans <|
      DR.right (sgL n js) (sg_zz' hN (hjs j (by simp)) (swL_lt hjs' hc) (swL_lt hjs' hd))

/-- A word of sign letters passes a word of `σ`s. -/
theorem zzs_through (hN : 4 ≤ 2 ^ n) {js : List ℕ} (hjs : ∀ j ∈ js, j + 1 < 2 ^ n)
    {ps : List (ℕ × ℕ)} (hps : ∀ p ∈ ps, p.1 < 2 ^ n ∧ p.2 < 2 ^ n) :
    DH n (sgL n js ++ zzs n ps)
      (zzs n (ps.map fun p => (swL js p.1, swL js p.2)) ++ sgL n js) := by
  induction ps with
  | nil => exact DR.rfl' (by simp [zzs])
  | cons p ps ih =>
    have h1 := hps p (by simp)
    have := (DR.right (zzs n ps) (zz_through hN hjs h1.1 h1.2)).trans
      (DR.left [Zz n (swL js p.1) (swL js p.2)] (ih fun q hq => hps q (List.mem_cons_of_mem _ hq)))
    simpa [zzs] using this

/-! ## Runs -/

/-- `σ_a σ_{a+1} ⋯ σ_{a+k-1}`. -/
def run (n a k : ℕ) : List (PG (2 ^ n)) := sgL n (List.range' a k)

theorem run_succ (a k : ℕ) : run n a (k + 1) = sg n a :: run n (a + 1) k := by
  simp [run, sgL, List.range'_succ]

theorem run_zero (a : ℕ) : run n a 0 = [] := rfl

theorem run_add (a p q : ℕ) : run n a (p + q) = run n a p ++ run n (a + p) q := by
  induction p generalizing a with
  | zero => simp [run_zero]
  | succ p ih =>
    rw [show p + 1 + q = (p + q) + 1 by omega, run_succ, run_succ, ih, show a + 1 + p = a + (p + 1) by
      omega]; rfl

theorem run_snoc (a k : ℕ) : run n a (k + 1) = run n a k ++ [sg n (a + k)] := by
  rw [run_add, show run n (a + k) 1 = [sg n (a + k)] from rfl]

theorem comm_below {j a k : ℕ} (hj : j + 1 < a) (hk : a + k < 2 ^ n) :
    DH n ([sg n j] ++ run n a k) (run n a k ++ [sg n j]) := by
  induction k generalizing a with
  | zero => exact DR.refl _
  | succ k ih =>
    rw [run_succ]
    exact (DR.ctx [] (run n (a + 1) k) (e32 n hj (by omega))).trans
      (DR.cons (sg n a) (ih (by omega) (by omega)))

theorem comm_above {j a k : ℕ} (hj : a + k + 1 ≤ j) (hj' : j + 1 < 2 ^ n) :
    DH n (run n a k ++ [sg n j]) ([sg n j] ++ run n a k) := by
  induction k generalizing a with
  | zero => exact DR.refl _
  | succ k ih =>
    rw [run_succ]
    exact (DR.cons (sg n a) (ih (by omega))).trans
      (DR.ctx [] (run n (a + 1) k) (e32 n (by omega) hj'))

/-- A `σ_j` inside a run is shifted by one: `R σ_j ≈ σ_{j+1} R`. -/
theorem run_shift {a k j : ℕ} (haj : a ≤ j) (hjk : j + 1 < a + k) (hk : a + k < 2 ^ n) :
    DH n (run n a k ++ [sg n j]) ([sg n (j + 1)] ++ run n a k) := by
  obtain ⟨r, hr⟩ : ∃ r, k = (j - a) + 2 + r := ⟨a + k - j - 2, by omega⟩
  subst hr
  have e : run n a (j - a + 2 + r) =
      run n a (j - a) ++ [sg n j, sg n (j + 1)] ++ run n (j + 2) r := by
    rw [run_add, run_add, show run n (a + (j - a)) 2 = [sg n j, sg n (j + 1)] by
      rw [show a + (j - a) = j by omega]; rfl, show a + (j - a + 2) = j + 2 by omega]
  rw [e]
  have h0 : DH n (run n a (j - a) ++ [sg n j, sg n (j + 1)] ++ run n (j + 2) r ++ [sg n j])
      (run n a (j - a) ++ [sg n j, sg n (j + 1)] ++ ([sg n j] ++ run n (j + 2) r)) := by
    rw [List.append_assoc _ (run n (j + 2) r)]
    exact DR.left _ (comm_below (by omega) (by omega)).symm
  have h1 := DR.ctx (run n a (j - a)) (run n (j + 2) r) (e24 n (a := j) (by omega))
  have h2 := DR.right ([sg n j, sg n (j + 1)] ++ run n (j + 2) r)
    (comm_above (a := a) (k := j - a) (j := j + 1) (by omega) (by omega))
  exact h0.trans ((DR.rfl' (by simp)).trans (h1.trans ((DR.rfl' (by simp)).trans
    (h2.trans (DR.rfl' (by simp))))))

/-- A run inside a run is shifted by one. -/
theorem run_shift_run {a k c m : ℕ} (hac : a ≤ c) (hcm : c + m < a + k) (hk : a + k < 2 ^ n) :
    DH n (run n a k ++ run n c m) (run n (c + 1) m ++ run n a k) := by
  induction m generalizing c with
  | zero => exact DR.rfl' (by simp [run_zero])
  | succ m ih =>
    rw [run_succ, run_succ]
    have h1 := DR.right (run n (c + 1) m) (run_shift (a := a) (k := k) (j := c) hac (by omega) hk)
    have h2 := DR.left [sg n (c + 1)] (ih (c := c + 1) (by omega) (by omega))
    exact (DR.rfl' (by simp)).trans (h1.trans ((DR.rfl' (by simp)).trans (h2.trans (DR.rfl' (by simp)))))

/-- A run far below a run commutes with it. -/
theorem run_far {a k c m : ℕ} (hcm : c + m < a) (hk : a + k < 2 ^ n) :
    DH n (run n a k ++ run n c m) (run n c m ++ run n a k) := by
  induction m generalizing c with
  | zero => exact DR.rfl' (by simp [run_zero])
  | succ m ih =>
    rw [run_succ]
    have h1 := DR.right (run n (c + 1) m) (comm_below (j := c) (a := a) (k := k) (by omega) hk).symm
    have h2 := DR.left [sg n c] (ih (c := c + 1) (by omega))
    exact (DR.rfl' (by simp)).trans (h1.trans ((DR.rfl' (by simp)).trans (h2.trans (DR.rfl' (by simp)))))

end QCert.RealCliffordCH.Sec8
