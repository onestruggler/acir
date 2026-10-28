/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Words of local letters at every width

A letter is *local* on `K` wires when it is well formed there and has no
control on the bulk: a small letter, or a multi-controlled letter with its
bulk flag off.  A word of local letters on `N ≥ K` wires is the word on `K`
wires at the bottom (`wc_atBot`), so a derivation on `K` wires carries over
(`der_loc`).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E336x

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- A local letter on `K` wires. -/
def isLoc (K : ℕ) : Lt → Bool
  | .s l => decide (l.lo + l.wd ≤ K)
  | .g Kd tg cs b => (Lt.g Kd tg cs false).ok K && !b

theorem isLoc_ok {K : ℕ} {x : Lt} (h : isLoc K x = true) : x.ok K = true := by
  cases x with
  | s l => simpa [isLoc, Lt.ok] using h
  | g Kd tg cs b =>
    simp only [isLoc, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, rfl⟩ := h
    exact h1

theorem atBot_loc {K : ℕ} (x : Lt) (hx : isLoc K x = true) :
    ∀ N, K ≤ N → atBot N (x.circ K K) = x.circ K N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact atBot_self _
  | succ M hM ih =>
    rw [atBot_succ M _ (by omega), ih]
    cases x with
    | s l =>
      simp only [isLoc, decide_eq_true_eq] at hx
      exact (circ_top M l (by omega)).symm
    | g Kd tg cs b =>
      simp only [isLoc, Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
        Bool.not_eq_true'] at hx
      obtain ⟨⟨⟨hnd, hlt⟩, ha⟩, rfl⟩ := hx
      exact (mc_top M Kd tg _ (by rw [← kindSp_eq]; exact ha) hnd
        (fun t ht => by have := hlt t ht; simp at this; omega)
        (by simp [ctl, show ¬ M < K by omega])).symm

theorem wc_atBot {K : ℕ} (L : List Lt) (hL : L.all (isLoc K) = true) (N : ℕ) (hN : K ≤ N) :
    atBot N (wc K K L) = wc K N L := by
  unfold wc
  rw [atBot_drawn, List.map_map]
  congr 1
  refine List.map_congr_left (fun x hx => ?_)
  exact atBot_loc x (List.all_eq_true.1 hL x hx) N hN

/-- A derivation between local words on `K` wires holds on every `N ≥ K`. -/
theorem der_loc {K : ℕ} {L R : List Lt} (hL : L.all (isLoc K) = true) (hR : R.all (isLoc K) = true)
    (d : Derivable (theory K) (wc K K L) (wc K K R)) (N : ℕ) (hN : K ≤ N) :
    Derivable (theory N) (wc K N L) (wc K N R) := by
  have h := der_atBot d N hN
  rwa [wc_atBot L hL N hN, wc_atBot R hR N hN] at h

end QCert.RealCliffordCH.Sec8.D.N13
