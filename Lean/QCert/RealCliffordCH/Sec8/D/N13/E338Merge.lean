/- Complete (338) by merging over every colouring. -/
import QCert.RealCliffordCH.Sec8.D.N13.HgBorrow

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net Eng SE
set_option maxHeartbeats 0

theorem fixed_conj {N : ℕ} {u a : Circ N} (h : Comm N u a)
    (hu : Derivable (theory N) (u * u) 1) :
    Derivable (theory N) (u * a * u) a := by
  unfold Comm at h
  rw [drawn_two, drawn_two] at h
  refine (dright u h.symm).trans ?_
  rw [mul_assoc]
  simpa only [mul_one] using dleft a hu

theorem black338_from_diff (N : ℕ) (hN : 3 ≤ N) (ih : IH N)
    (diff : ∀ x y : ℕ → Bool, DiffOn 2 N x y → ∀ c : Bool,
      Comm N (bA N x c) (mc N .hg [1, 0] (colOn 2 N y)))
    (boxes : ∀ x y : ℕ → Bool, Comm N (mc N .box [0] (colOn 1 N x))
      (mc N .box [0] (colOn 1 N y))) :
    Comm N (mc N .box [0] (blackOn 1 N)) (mc N .hg [1, 0] (colOn 2 N fun _ => true)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  refine MergeAll.isolate_black ih _ (small_box_hg_black _ (by omega) ih) ?_ boxes
  intro x hx
  have h := diff x (fun _ => true) hx (x 1)
  have e : bA (M + 3) x (x 1) = mc (M + 3) .box [0] (colOn 1 (M + 3) x) := by
    apply mc_congr
    intro i hi
    simp only [ctlOr, ctlAt, colOn]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  rwa [e] at h

theorem black338_front (N : ℕ) (hN : 3 ≤ N) (ih : IH N)
    (h : Comm N (mc N .box [0] (blackOn 1 N))
      (mc N .hg [1, 0] (colOn 2 N fun _ => true))) (c : Bool) :
    Comm N (bA N (fun _ => true) c) (mc N .hg [1, 0] (colOn 2 N fun _ => true)) := by
  have et : bA N (fun _ => true) true = mc N .box [0] (blackOn 1 N) := by
    apply mc_congr
    intro i hi
    simp only [ctlOr, ctlAt, colOn, blackOn]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  cases c
  · have hf := eq81 N .box [0] (blackOn 1 N) 1 true (by omega) (by decide)
      (by simp [blackOn]; omega)
    rw [show drawn [xAt N 1, mc N .box [0] (blackOn 1 N), xAt N 1] =
      xAt N 1 * mc N .box [0] (blackOn 1 N) * xAt N 1 by simp [drawn, mul_assoc]] at hf
    have he : mc N .box [0] (setCtl (blackOn 1 N) 1 (some (!true))) = bA N (fun _ => true) false := by
      apply mc_congr
      intro i hi
      simp only [setCtl, ctlOr, ctlAt, blackOn, colOn]
      split_ifs <;> first | rfl | (exfalso; omega) | simp_all
    rw [he] at hf
    exact comm_flip h (xAt_inv N 1 (by omega)) hf
      (fixed_conj (x_one_hg_black N hN ih) (xAt_inv N 1 (by omega)))
  · rwa [et]

def box338L (c : Bool) : Lt := .g .box [0] [(1, c)] true
def hg338L : Lt := .g .hg [1, 0] [] true

theorem box338_read (N : ℕ) (x : ℕ → Bool) (c : Bool) :
    cX 2 N x (box338L c) = bA N x c := by
  apply mc_congr
  ctl_tac

theorem hg338_read (N : ℕ) (x : ℕ → Bool) :
    cX 2 N x hg338L = mc N .hg [1, 0] (colOn 2 N x) := by
  apply mc_congr
  ctl_tac

theorem box338_black (N : ℕ) (c : Bool) :
    (box338L c).circ 2 N = bA N (fun _ => true) c := by
  apply mc_congr
  ctl_tac

theorem hg338_black (N : ℕ) :
    hg338L.circ 2 N = mc N .hg [1, 0] (colOn 2 N fun _ => true) := by
  apply mc_congr
  ctl_tac

theorem same338_from_black (N : ℕ) (hN : 3 ≤ N) (x : ℕ → Bool) (c : Bool)
    (h : Comm N (bA N (fun _ => true) c) (mc N .hg [1, 0] (colOn 2 N fun _ => true))) :
    Comm N (bA N x c) (mc N .hg [1, 0] (colOn 2 N x)) := by
  have hb : ∀ g ∈ [box338L c, hg338L], g.ok 2 = true := by
    intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl <;> cases c <;> decide
  have hh : ∀ g ∈ [hg338L, box338L c], g.ok 2 = true := by
    intro g hg; apply hb; simpa [List.mem_cons, or_comm] using hg
  have hc : Derivable (theory N) (wc 2 N [box338L c, hg338L]) (wc 2 N [hg338L, box338L c]) := by
    simpa only [wc, List.map_cons, List.map_nil, box338_black, hg338_black] using h
  have hc' := colour_wc (by omega : 2 ≤ N) x hb hh hc
  simpa only [wcX, List.map_cons, List.map_nil, box338_read, hg338_read] using hc'

theorem comm338_from_diff (N : ℕ) (hN : 3 ≤ N) (ih : IH N)
    (diff : ∀ x y : ℕ → Bool, DiffOn 2 N x y → ∀ c : Bool,
      Comm N (bA N x c) (mc N .hg [1, 0] (colOn 2 N y)))
    (boxes : ∀ x y : ℕ → Bool, Comm N (mc N .box [0] (colOn 1 N x))
      (mc N .box [0] (colOn 1 N y))) (x y : ℕ → Bool) (c : Bool) :
    Comm N (bA N x c) (mc N .hg [1, 0] (colOn 2 N y)) := by
  by_cases hd : DiffOn 2 N x y
  · exact diff x y hd c
  · have e : mc N .hg [1, 0] (colOn 2 N y) = mc N .hg [1, 0] (colOn 2 N x) := by
      apply mc_congr
      intro i hi
      simp only [colOn]
      split_ifs with h2
      · have he : x i = y i := by by_contra hne; exact hd ⟨i, h2.1, h2.2, hne⟩
        rw [he]
      · rfl
    rw [e]
    exact same338_from_black N hN x c
      (black338_front N hN ih (black338_from_diff N hN ih diff boxes) c)

end QCert.RealCliffordCH.Sec8.D.N13
