/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits below the box wire (Lemmas D.9 and D.11)

Discharge the generator cases of `G_letter` at widths three, four and
at least five, then extend them to arbitrary circuits by `G_circ`.
-/
import QCert.RealCliffordCH.Sec8.D.N8.Low

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option maxRecDepth 100000

private theorem pair_mul {K N : ℕ} {a b : Lt}
    (h : Derivable (theory N) (wc K N [a, b]) (wc K N [b, a])) :
    Derivable (theory N) (b.circ K N * a.circ K N) (a.circ K N * b.circ K N) := by
  simpa only [wc2, drawn2] using h

theorem box_base1 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (_ : 1 + 0 ≤ N)
    (x : L) (hx : x = .H 0 ∨ x = .Z 0) :
    Derivable (theory N) (BoxM N 1 * x.circ N) (x.circ N * BoxM N 1) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact pair_mul (SE.check_sound (frame 2) (m := 0) ih T3b_ok (runB1_3 x hx))
  · rcases hx with rfl | rfl
    · exact W4.t155 ih
    · exact W4.t154 ih
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    rcases hx with rfl | rfl
    · have h := s285 m ih
      rw [wc2, wc2, bx0_mc, drawn2, drawn2] at h
      exact h
    · have h := t19 m
      rw [wc2, wc2, bx0_mc, drawn2, drawn2] at h
      exact h

theorem box_base2 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (_ : 2 + 0 ≤ N)
    (x : L) (hx : x = .C 0 ∨ x = .K 0) :
    Derivable (theory N) (BoxM N 2 * x.circ N) (x.circ N * BoxM N 2) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact pair_mul (SE.check_sound (frame 2) (m := 0) ih T3b_ok (runB2_3 x hx))
  · exact pair_mul (SE.check_sound (frame 3) (m := 0) ih (T := []) (fun _ h => by simp at h)
      (w := [.s x, b1_4]) (v := [b1_4, .s x])
      (ss := [.sem 1 1 [.s (.C 2)] 0, .sw 0, .sem 0 1 [b1_4] 0])
      (by rcases hx with rfl | rfl <;> decide +kernel))
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    rcases hx with rfl | rfl
    · have h := sCB1 m ih
      rw [wc2, wc2, B1_mc', drawn2, drawn2] at h
      exact h
    · have h := sKB1 m ih
      rw [wc2, wc2, B1_mc', drawn2, drawn2] at h
      exact h

theorem eq308_all (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : m ≤ N) (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, BoxM N m])
      (drawn [BoxM N m, atBot N C]) := by
  apply G_circ BoxM hmN
  exact G_letter 0 BoxM boxM_shift box_base1 box_base2 base0_box N hN ih m hm hmN

private def hp4 : WE.Tk := .p 2
  [.K 0, .H 1, .Z 0, .K 0, .H 1, .Z 0, .K 0, .H 1, .Z 0, .S 0] [0, 1]
private def hb4 : WE.Tk := .g .box [0] [(3, true), (2, true), (1, true)]
private def hh4 : WE.Tk := .g .hg [0, 1] [(3, true), (2, true)]

theorem hg_base1_4 (ih : IH 4) (x : L) (hx : x = .H 0 ∨ x = .Z 0) :
    Derivable (theory 4) (HgM 4 1 * x.circ 4) (x.circ 4 * HgM 4 1) := by
  rcases hx with rfl | rfl
  · have ht : WE.AllD 4 [([hh4], [hp4, hb4, hp4]),
        ([.s (.Z 0), hb4], [hb4, .s (.Z 0)])] :=
      WE.AllD.cons (W4.tDhg ih) (WE.AllD.cons (W4.t154 ih) (WE.AllD.nil 4))
    exact WE.check_sound ih ht (w := [.s (.H 0), hh4]) (v := [hh4, .s (.H 0)])
      (ss := [.rw 1 0 false, .sem 0 2 [hp4, .s (.Z 0)] 2,
        .rw 1 1 false, .sem 2 2 [hp4, .s (.H 0)] 2, .rw 0 0 true]) (by decide +kernel)
  · have ht : WE.AllD 4 [([hh4], [hp4, hb4, hp4]),
        ([.s (.H 0), hb4], [hb4, .s (.H 0)])] :=
      WE.AllD.cons (W4.tDhg ih) (WE.AllD.cons (W4.t155 ih) (WE.AllD.nil 4))
    exact WE.check_sound ih ht (w := [.s (.Z 0), hh4]) (v := [hh4, .s (.Z 0)])
      (ss := [.rw 1 0 false, .sem 0 2 [hp4, .s (.H 0)] 2,
        .rw 1 1 false, .sem 2 2 [hp4, .s (.Z 0)] 2, .rw 0 0 true]) (by decide +kernel)

theorem hg_base1 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (_ : 1 + 1 ≤ N)
    (x : L) (hx : x = .H 0 ∨ x = .Z 0) :
    Derivable (theory N) (HgM N 1 * x.circ N) (x.circ N * HgM N 1) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact pair_mul (SE.check_sound (frame 2) (m := 0) ih T3b_ok (runH1_3 x hx))
  · exact hg_base1_4 ih x hx
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    rcases hx with rfl | rfl
    · have h := s303 m ih
      rw [wc2, wc2, hgF_mc, drawn2, drawn2] at h
      exact h
    · have h := sZhg m ih
      rw [wc2, wc2, hgF_mc, drawn2, drawn2] at h
      exact h

theorem hg_base2 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (_ : 2 + 1 ≤ N)
    (x : L) (hx : x = .C 0 ∨ x = .K 0) :
    Derivable (theory N) (HgM N 2 * x.circ N) (x.circ N * HgM N 2) := by
  rcases (by omega : N = 3 ∨ N = 4 ∨ 5 ≤ N) with rfl | rfl | h5
  · exact pair_mul (SE.check_sound (frame 2) (m := 0) ih T3b_ok (runH2_3 x hx))
  · exact pair_mul (SE.check_sound (frame 3) (m := 0) ih (T := []) (fun _ h => by simp at h)
      (w := [.s x, .g .hg [1, 2] [(3, true)] false])
      (v := [.g .hg [1, 2] [(3, true)] false, .s x])
      (ss := [.sem 1 1 [.s (.K 2)] 0, .sw 0,
        .sem 0 1 [.g .hg [1, 2] [(3, true)] false] 0])
      (by rcases hx with rfl | rfl <;> decide +kernel))
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
    rcases hx with rfl | rfl
    · have h := s282 m ih
      rw [wc2, wc2, hg12_circ_mc, drawn2, drawn2] at h
      exact h
    · have h := sKhg m ih
      rw [wc2, wc2, hg12_circ_mc, drawn2, drawn2] at h
      exact h

theorem eq314_all (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : m + 1 ≤ N) (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, HgM N m])
      (drawn [HgM N m, atBot N C]) := by
  apply G_circ HgM (by omega)
  exact G_letter 1 HgM hgM_shift hg_base1 hg_base2 base0_hg N hN ih m hm hmN

end QCert.RealCliffordCH.Sec8.D.N8
