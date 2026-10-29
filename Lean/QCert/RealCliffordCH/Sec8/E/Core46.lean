/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (46): the core from four wires on

The paper's chain (pages 269–277, `Core46Chain`): the decoded right-hand side
`W0` is rewritten to `g6 :: WIII`, `WIII` to `WIV` (from (III) to (IV)),
`g6 :: WIV` to `g6 :: WIV.reverse`, and `g6 :: WIII.reverse` to the decoded
left-hand side `WEnd`.  The missing link, `WIV.reverse` to `WIII.reverse`, is
the paper's "same steps as from (III) to (IV), mirrored, in reverse order":
every gate is an involution, so a word equation reverses (`rev_eq`).
-/
import QCert.RealCliffordCH.Sec8.E.Core46Chain
import QCert.RealCliffordCH.Sec8.E.Core46Three

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.E.C46

open Circuit Net

/-! ## Reversing an equation between words of involutions -/

section Rev

variable {N : ℕ}

theorem wI_cons (g : GD) (l : List GD) : wI N (g :: l) = wI N l * g.circ N := by
  simp [wI, drawn]

theorem wI_nil : wI N [] = 1 := rfl

theorem wI_append' (a b : List GD) : wI N (a ++ b) = wI N b * wI N a := by
  simp [wI, SE.drawn_append]

theorem wI_cons_ctx (g : GD) {a b : List GD} (h : Derivable (theory N) (wI N a) (wI N b)) :
    Derivable (theory N) (wI N (g :: a)) (wI N (g :: b)) := by
  rw [wI_cons, wI_cons]; exact dright _ h

/-- The gates of a list are involutions. -/
def Invs (N : ℕ) (l : List GD) : Prop :=
  l.Forall fun g => Derivable (theory N) (wI N [g, g]) (wI N [])

theorem inv_circ {g : GD} (h : Derivable (theory N) (wI N [g, g]) (wI N [])) :
    Derivable (theory N) (g.circ N * g.circ N) 1 := by
  simpa [wI, drawn] using h

theorem rev_mul : ∀ {l : List GD}, (∀ g ∈ l, Derivable (theory N) (wI N [g, g]) (wI N [])) →
    Derivable (theory N) (wI N l.reverse * wI N l) 1
  | [], _ => by simp [wI, drawn]; exact Derivable.refl _
  | g :: l, h => by
    have hg := h g (by simp)
    have hl : ∀ g' ∈ l, Derivable (theory N) (wI N [g', g']) (wI N []) :=
      fun g' hg' => h g' (by simp [hg'])
    rw [List.reverse_cons, wI_append', wI_cons g l]
    have e : wI N [g] * wI N l.reverse * (wI N l * g.circ N) =
        g.circ N * (wI N l.reverse * wI N l) * g.circ N := by
      simp only [wI, List.map_cons, List.map_nil, drawn, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [e]
    have k := dright (g.circ N) (dleft (g.circ N) (rev_mul hl))
    rw [mul_one] at k
    exact k.trans (inv_circ hg)

theorem mul_rev {l : List GD} (h : ∀ g ∈ l, Derivable (theory N) (wI N [g, g]) (wI N [])) :
    Derivable (theory N) (wI N l * wI N l.reverse) 1 := by
  have := rev_mul (l := l.reverse) (fun g hg => h g (List.mem_reverse.1 hg))
  rwa [List.reverse_reverse] at this

/-- A word equation between involutions reverses. -/
theorem rev_eq {l r : List GD} (hl : Invs N l) (hr : Invs N r)
    (h : Derivable (theory N) (wI N l) (wI N r)) :
    Derivable (theory N) (wI N l.reverse) (wI N r.reverse) := by
  -- `l⁻ = l⁻ (r r⁻) = l⁻ (l r⁻) = (l⁻ l) r⁻ = r⁻`
  have hl := List.forall_iff_forall_mem.1 hl
  have hr := List.forall_iff_forall_mem.1 hr
  have k1 : Derivable (theory N) (wI N l.reverse) (wI N l.reverse * (wI N r * wI N r.reverse)) := by
    have := dleft (wI N l.reverse) (mul_rev hr)
    rw [mul_one] at this; exact this.symm
  have k2 := dleft (wI N l.reverse) (dright (wI N r.reverse) h.symm)
  have k3 : Derivable (theory N) (wI N l.reverse * (wI N l * wI N r.reverse)) (wI N r.reverse) := by
    rw [← mul_assoc]
    have := dright (wI N r.reverse) (rev_mul hl)
    rwa [one_mul] at this
  exact k1.trans (k2.trans k3)

end Rev

/-! ## The core -/

section Core

variable {n : ℕ} (ih : IH (n + 4))
include ih

theorem run1a : Derivable (theory (n + 4)) (wI (n + 4) W0) (wI (n + 4) (g6 :: WIII)) :=
  run_sound (allT46 ih) (ss := ss1a) (by decide +kernel)

theorem run1b : Derivable (theory (n + 4)) (wI (n + 4) WIII) (wI (n + 4) WIV) :=
  run_sound (allT46 ih) (ss := ss1b) (by decide +kernel)

theorem run2 : Derivable (theory (n + 4)) (wI (n + 4) (g6 :: WIV)) (wI (n + 4) (g6 :: WIV.reverse)) :=
  run_sound (allT46 ih) (ss := ss2) (by decide +kernel)

theorem run3 : Derivable (theory (n + 4)) (wI (n + 4) (g6 :: WIII.reverse)) (wI (n + 4) WEnd) :=
  run_sound (allT46 ih) (ss := ss3) (by decide +kernel)

/-- The decoded rule (46) from four wires on, as words. -/
theorem core46_words : Derivable (theory (n + 4)) (wI (n + 4) W0) (wI (n + 4) WEnd) :=
  (run1a ih).trans ((wI_cons_ctx g6 (run1b ih)).trans ((run2 ih).trans
    ((wI_cons_ctx g6 (rev_eq (invIII ih) (invIV ih) (run1b ih)).symm).trans (run3 ih))))

end Core

/-! ## The decoded letters as gate descriptions -/

section Letters

variable (m : ℕ)

theorem bit_hi (s j : ℕ) (hs : s < 16) (hj : 4 ≤ j) : bitOf s j = 0 :=
  bitOf_small (lt_of_lt_of_le hs (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

/-- The controls of the decoded letters are `c4` of their colours. -/
macro "c46eq" : tactic => `(tactic| (intro j hj; rcases j with _ | _ | _ | _ | j <;>
  first
  | (simp [c4, ctl2Of, ctlOf, bitOf]; done)
  | (have hb : ∀ s, s < 16 → bitOf s (j + 4) = 0 := fun s hs => bit_hi s (j + 4) hs (by omega)
     simp [c4, ctl2Of, ctlOf, hb])))

theorem eA46 : A46 (m + 1) = GD.circ (m + 4) (.g .hg [2, 0] [none, some false, none, some false]) :=
  Net.mc_congr _ _ _ (by c46eq)

theorem eB46 : B46 (m + 1) = GD.circ (m + 4) (.g .hg [0, 1] [none, none, some false, some false]) :=
  Net.mc_congr _ _ _ (by c46eq)

theorem eC46 : C46 (m + 1) = GD.circ (m + 4) (.g .hg [0, 2] [none, some true, none, some false]) :=
  Net.mc_congr _ _ _ (by c46eq)

theorem eD46 : D46 (m + 1) = GD.circ (m + 4) (.g .hg [2, 0] [none, some true, none, some false]) :=
  Net.mc_congr _ _ _ (by c46eq)

theorem eF46 : F46 (m + 1) = GD.circ (m + 4) (.g .hg [1, 0] [none, none, some true, some false]) :=
  Net.mc_congr _ _ _ (by c46eq)

theorem eZ46 : Z46 (m + 1) = GD.circ (m + 4) (.g .box [0] [none, some true, some false, some false]) :=
  Net.mc_congr _ _ _ (by c46eq)

end Letters

/-- The decoded rule (46), (147) with white controls above the wire `2`, at every width. -/
theorem core46 {M : ℕ} (ih : IH (M + 3)) : Core46 M := by
  rcases M with _ | m
  · exact core46_three ih
  · have h := core46_words (n := m) ih
    unfold Core46
    rw [eA46 m, eB46 m, eC46 m, eD46 m, eF46 m, eZ46 m]
    simpa only [wI, W0, WEnd, List.map_cons, List.map_nil, drawn, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc, List.prod_append] using h

end QCert.RealCliffordCH.Sec8.E.C46
