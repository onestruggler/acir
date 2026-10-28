/-
Copyright (c) 2026 QCert contributors. All rights reserved.

Equations (322), (323) with arbitrary colours on the bulk controls.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E322

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Eng SE Net N8

theorem W322_rebase (N : ℕ) (one a α β : Bool) :
    wc 5 N (W322 one a α β) = wc 4 N (W322 one a α β) := by
  have h0 : (R0 a α β).circ 5 N = (R0 a α β).circ 4 N :=
    mc_congr _ _ _ (by ctl_tac)
  have h1 : (R1 a α β).circ 5 N = (R1 a α β).circ 4 N :=
    mc_congr _ _ _ (by ctl_tac)
  cases one <;> simp only [W322, Bool.false_eq_true, if_false, if_true, W0, W1,
    wc_append, wc_one'] <;> first | (rw [h0]; rfl) | (rw [h1]; rfl)

theorem W322_ok : ∀ one a α β : Bool, ∀ g ∈ W322 one a α β, g.ok 4 = true := by
  decide

theorem W322_colour (N : ℕ) (x : ℕ → Bool) (one a α β : Bool) :
    wcX 4 N x (W322 one a α β) = wc 4 N (W322 one a α β) := by
  cases one <;> rfl

theorem B322_rebase (N : ℕ) (γ : Bool) :
    (B322 γ).circ 5 N = (Bq4 γ).circ 4 N :=
  mc_congr _ _ _ (by ctl_tac)

theorem B322_colour (N : ℕ) (x : ℕ → Bool) (γ : Bool) :
    cX 4 N x (Bq4 γ) = boxN N x γ false :=
  mc_congr _ _ _ (by ctl_tac)

theorem eq322_word (m : ℕ) (ih : IH (m + 5)) (x : ℕ → Bool) (one a α β γ : Bool) :
    Comm (m + 5) (wc 4 (m + 5) (W322 one a α β)) (boxN (m + 5) x γ false) := by
  have h := r322 m ih one a α β γ
  simp only [wc_append, wc_one', W322_rebase, B322_rebase] at h
  have h4 : Derivable (theory (m + 5))
      (wc 4 (m + 5) (W322 one a α β ++ [Bq4 γ]))
      (wc 4 (m + 5) ([Bq4 γ] ++ W322 one a α β)) := by
    simpa only [wc_append, wc_one'] using h
  have hc := colour_wc (K := 4) (N := m + 5) (by omega) x
    (l := W322 one a α β ++ [Bq4 γ]) (r := [Bq4 γ] ++ W322 one a α β)
    (by intro g hg; rcases List.mem_append.1 hg with hg | hg
        · exact W322_ok one a α β g hg
        · obtain rfl := List.mem_singleton.1 hg; exact Bq4_ok γ)
    (by intro g hg; rcases List.mem_append.1 hg with hg | hg
        · obtain rfl := List.mem_singleton.1 hg; exact Bq4_ok γ
        · exact W322_ok one a α β g hg) h4
  simp only [wcX, List.map_append, drawn_append, List.map_singleton,
    drawn_one] at hc
  unfold Comm
  rw [drawn_two, drawn_two]
  change Derivable _ (cX 4 (m + 5) x (Bq4 γ) * wcX 4 (m + 5) x (W322 one a α β))
    (wcX 4 (m + 5) x (W322 one a α β) * cX 4 (m + 5) x (Bq4 γ)) at hc
  simpa only [W322_colour, B322_colour] using hc

end QCert.RealCliffordCH.Sec8.D.N13
