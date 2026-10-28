/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (318) and (319) on either box wire

(318) with its control on wire `0` of either colour (`X` on wire `0`
changes it and passes the box, idle on wire `3`, by semantic steps), and
(318), (319) carried by the swap of the wires `0, 1` to the box on wire `1`.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E319

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- The rotation of (318) with its control on wire `0` of colour `β'`. -/
def Rg0 (a α β' : Bool) : Lt := .g (Kind.sgnZX a) [1] [(0, β'), (2, true), (3, α)] false

theorem chkX0 : ∀ a α β : Bool,
    check 4 [] (xL 0 ++ [Rg a α] ++ xL 0) [Rg0 a α false] [.sem 0 7 [Rg0 a α false] 4] = true ∧
    check 4 [] (xL 0 ++ [Bq β] ++ xL 0) [Bq β] [.sem 0 7 [Bq β] 3] = true := by
  decide +kernel

theorem r318g (m : ℕ) (ih : IH (m + 5)) (a α β β' : Bool) :
    Comm (m + 5) ((Rg0 a α β').circ 5 (m + 5)) ((Bq β).circ 5 (m + 5)) := by
  cases β'
  · have h1 := check_sound (frame 4) ih (allD_nil 5 m) (chkX0 a α β).1
    have h2 := check_sound (frame 4) ih (allD_nil 5 m) (chkX0 a α β).2
    rw [wc_xconj, wc_one'] at h1 h2
    exact comm_flip (r318 m ih a α β) (xAt_inv (m + 5) 0 (by omega)) h1 h2
  · exact r318 m ih a α β

theorem Rg0_ok : ∀ a α β' : Bool, (Rg0 a α β').ok 4 = true := by decide

/-- (318), any colour of the control on wire `0`, from five wires on. -/
theorem eq318g_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (a α β β' : Bool) :
    Comm N (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 β') (ctlOr (ctlAt 2 true) (ctlAt 3 α))))
      (mc N .box [0] (ctlOr (ctlAt 1 β) (ctlOr (ctlAt 2 false) (colOn 4 N x)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  have h : Derivable (theory (m + 5)) (wc 4 (m + 5) [Rg0 a α β', Bq4 β])
      (wc 4 (m + 5) [Bq4 β, Rg0 a α β']) := by
    have := r318g m ih a α β β'
    unfold Comm at this
    rw [show (Rg0 a α β').circ 5 (m + 5) = (Rg0 a α β').circ 4 (m + 5) from
      mc_congr _ _ _ (by ctl_tac), Bq_rebase] at this
    exact this
  have h4 := colour_wc (K := 4) (N := m + 5) (by omega) x (l := [Rg0 a α β', Bq4 β])
    (r := [Bq4 β, Rg0 a α β']) (all_two (Rg0_ok a α β') (Bq4_ok β))
    (all_two (Bq4_ok β) (Rg0_ok a α β')) h
  have e1 : cX 4 (m + 5) x (Rg0 a α β') =
      mc (m + 5) (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 β') (ctlOr (ctlAt 2 true) (ctlAt 3 α))) :=
    mc_congr _ _ _ (by ctl_tac)
  have e2 : cX 4 (m + 5) x (Bq4 β) =
      mc (m + 5) .box [0] (ctlOr (ctlAt 1 β) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) x))) := by
    show mc _ _ _ _ = _
    exact mc_congr _ _ _ (by ctl_tac)
  have e3 : ∀ y z : Lt, wcX 4 (m + 5) x [y, z] = drawn [cX 4 (m + 5) x y, cX 4 (m + 5) x z] :=
    fun _ _ => rfl
  rw [e3, e3, e1, e2] at h4
  exact h4

/-! ## The swap of the wires `0, 1` -/

/-- A gate with no control on wire `0` or `1` other than one of them,
conjugated by the swap of the wires `0, 1`. -/
theorem mc_s0 (N : ℕ) (hN : 3 ≤ N) (K : Kind) (t : ℕ) (ht : t ≤ 1) (c c' : ℕ → Option Bool)
    (hK : K ≠ .hg) (hc : ∀ i < N, c (Net.tau 0 i) = c' i) :
    Derivable (theory N) (swAt N 0 * mc N K [t] c * swAt N 0) (mc N K [Net.tau 0 t] c') := by
  have htg : [t].length = kindSp K := by cases K <;> simp_all [kindSp]
  have h := mc_swap N 0 (by omega) K [t] c htg (by simp) (by simp; omega) (by
    intro ⟨h1, h2⟩
    rw [MS.mem_ctrlWires] at h1 h2
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · exact h1.2.2 (by simp)
    · exact h2.2.2 (by simp))
  have e : drawn [swAt N 0, mc N K [t] c, swAt N 0] = swAt N 0 * mc N K [t] c * swAt N 0 := by
    simp [drawn, mul_assoc]
  rw [e] at h
  exact h.trans (der_of_eq (mc_congr _ _ _ (fun i hi => by simpa using hc i hi)))

/-- Conjugating a commutation by the swap of the wires `0, 1`. -/
theorem comm_s0 {N : ℕ} (hN : 3 ≤ N) {A B A' B' : Circ N} (h : Comm N A B)
    (hA : Derivable (theory N) (swAt N 0 * A * swAt N 0) A')
    (hB : Derivable (theory N) (swAt N 0 * B * swAt N 0) B') : Comm N A' B' :=
  comm_flip h (swsw N 0 (by omega)) hA hB

/-- (318) on the box wire `1`. -/
theorem eq318s_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (a α β β' : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 β') (ctlOr (ctlAt 2 true) (ctlAt 3 α))))
      (mc N .box [1] (ctlOr (ctlAt 0 β) (ctlOr (ctlAt 2 false) (colOn 4 N x)))) :=
  comm_s0 (by omega) (eq318g_ge5 N hN ih x a α β β')
    (mc_s0 N (by omega) _ 1 le_rfl _ _ (by cases a <;> decide) (fun i hi => by
      simp only [ctlOr, ctlAt, Net.tau]; split_ifs <;> first | rfl | omega | simp_all))
    (mc_s0 N (by omega) _ 0 (by omega) _ _ (by decide) (fun i hi => by
      simp only [ctlOr, ctlAt, colOn, Net.tau]; split_ifs <;> first | rfl | omega | simp_all))

/-- (319) on the box wire `1`. -/
theorem eq319s_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (a α β γ : Bool) :
    Comm N (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 β) (ctlOr (ctlAt 2 true) (ctlAt 3 α))))
      (mc N .box [1] (ctlOr (ctlAt 0 γ) (ctlOr (ctlAt 2 false) (colOn 4 N x)))) :=
  comm_s0 (by omega) (eq319_ge5 N hN ih x a α β γ)
    (mc_s0 N (by omega) _ 0 (by omega) _ _ (by cases a <;> decide) (fun i hi => by
      simp only [ctlOr, ctlAt, Net.tau]; split_ifs <;> first | rfl | omega | simp_all))
    (mc_s0 N (by omega) _ 0 (by omega) _ _ (by decide) (fun i hi => by
      simp only [ctlOr, ctlAt, colOn, Net.tau]; split_ifs <;> first | rfl | omega | simp_all))

end QCert.RealCliffordCH.Sec8.D.N13
