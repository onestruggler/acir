/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (346): the box and a rotation on the same wire

The box on wire `0` (controls coloured by `x`) commutes with the
multi-controlled `(-1)^a ZX` on wire `0` (controls coloured by `y`), at
every width from three.  By (81) on both gates (`MergeAll.colour_ind`), the
colouring `y` may be taken black.  Then (333), resp. (334), writes the
rotation as the multi-controlled `H` with its box on wire `2`, its `H` on
wire `0`, and the box on wire `1` (`HG333`, `B333`), and the box passes
both: the first by (338) relabelled by the swap of the wires `1, 2`, the
second by (336).  This is the paper's six-step chain (page 234), which it
writes for `x = y` black; it holds for every `x` and `y`.

(333), (334), (336) and (338) are hypotheses, supplied by `N13.lean`.

No window is decided here.  Memory (2026-10-29): about 20 s, peak 0.35 GB
anonymous.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E333

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- `x` with the colours of the wires `1, 2` exchanged on wire `2`. -/
def sw12 (x : ℕ → Bool) : ℕ → Bool := fun i => if i = 2 then x 1 else x i

/-- Pointwise equality of control functions on the wires `0, …, 3` and above. -/
macro "ctl_case46" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ 4 ≤ i) with h | h | h | h | h4 <;> (try subst h) <;>
  simp only [colOn, ctlOr, ctlAt, blackOn, setCtl, sw12, Net.tau, Function.comp] <;>
  (try split_ifs) <;> first | rfl | (exfalso; omega) | omega))

section
variable {N : ℕ} (hN : 3 ≤ N) (ih : IH N)
include hN ih

/-- The box passes the multi-controlled `H` of (333): (338) under the swap
of the wires `1, 2`. -/
theorem box_HG333 (x : ℕ → Bool)
    (h338 : ∀ x y : ℕ → Bool, ∀ c₁ : Bool,
      Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y))) :
    Comm N (mc N .box [0] (colOn 1 N x))
      (mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N))) := by
  have h := h338 (sw12 x) (fun _ => true) (x 2)
  have a1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 (x 2)) (colOn 2 N (sw12 x))) (colOn 1 N x) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case46)
  have b1 := swBH ih 1 (by omega) .hg (Or.inr rfl) [1, 0] [2, 0]
    (colOn 2 N (fun _ => true)) (ctlOr (ctlAt 1 true) (blackOn 3 N)) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case46)
  exact Comm.congr a1 b1 (Comm.conj h (swsw N 1 (by omega)))

/-- The box passes the box of (333) on wire `1`: (336). -/
theorem box_B333 (x : ℕ → Bool)
    (h336 : ∀ x y : ℕ → Bool, ∀ c₁ c₂ : Bool,
      Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
        (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y)))) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))) := by
  have h := h336 x (fun _ => true) (x 1) true
  refine Comm.congr (der_of_eq (Net.mc_congr _ _ _ ?_)) (der_of_eq (Net.mc_congr _ _ _ ?_)) h
  · ctl_case46
  · ctl_case46

end

/-- (346), given (333), (334), (336) and (338) at the same width. -/
theorem comm346 {N : ℕ} (hN : 3 ≤ N) (ih : IH N)
    (h333 : Derivable (theory N) (mc N .zx [0] (blackOn 1 N))
      (drawn [mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))]))
    (h334 : Derivable (theory N) (mc N .xz [0] (blackOn 1 N))
      (drawn [mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N))]))
    (h336 : ∀ x y : ℕ → Bool, ∀ c₁ c₂ : Bool,
      Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
        (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))))
    (h338 : ∀ x y : ℕ → Bool, ∀ c₁ : Bool,
      Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y)))
    (x y : ℕ → Bool) (a : Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N (Kind.sgnZX a) [0] (colOn 1 N y)) := by
  -- the rotation with black controls
  have black : ∀ x : ℕ → Bool, Comm N (mc N .box [0] (colOn 1 N x))
      (mc N (Kind.sgnZX a) [0] (colOn 1 N (fun _ => true))) := by
    intro x
    have pH := box_HG333 hN ih x h338
    have pB := box_B333 hN ih x h336
    have eR : mc N (Kind.sgnZX a) [0] (colOn 1 N (fun _ => true)) =
        mc N (Kind.sgnZX a) [0] (blackOn 1 N) :=
      Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
    rw [eR]
    have all : ∀ l : List (Circ N), (∀ g ∈ l, g = mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)) ∨
        g = mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))) →
        Comm N (mc N .box [0] (colOn 1 N x)) (drawn l) := fun l hl =>
      Derivable.symm (comm_drawn_left l (fun g hg => by
        rcases hl g hg with rfl | rfl
        · exact Derivable.symm pH
        · exact Derivable.symm pB))
    cases a
    · exact Comm.congr (Derivable.refl _) h333.symm
        (all _ (by intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg; tauto))
    · exact Comm.congr (Derivable.refl _) h334.symm
        (all _ (by intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg; tauto))
  -- every colouring of the rotation, by (81) on both gates
  refine MergeAll.colour_ind (N := N) (w := 0)
    (fun y => ∀ x : ℕ → Bool, Comm N (mc N .box [0] (colOn 1 N x))
      (mc N (Kind.sgnZX a) [0] (colOn 1 N y))) ?_ ?_ black y x
  · intro y y' hyy q x
    have e : mc N (Kind.sgnZX a) [0] (colOn 1 N y) = mc N (Kind.sgnZX a) [0] (colOn 1 N y') :=
      Net.mc_congr _ _ _ (fun i hi => by
        simp only [colOn]; split_ifs with h1
        · rw [hyy i h1.1 h1.2 (by omega)]
        · rfl)
    rw [← e]; exact q x
  · intro y j hj1 hjN _ q x
    have k := q (MergeAll.flip1 x j)
    have hx := xAt_inv N j hjN
    have fl : ∀ (K : Kind) (z : ℕ → Bool), Derivable (theory N)
        (xAt N j * mc N K [0] (colOn 1 N (MergeAll.flip1 z j)) * xAt N j) (mc N K [0] (colOn 1 N z)) := by
      intro K z
      have e := eq81 N K [0] (colOn 1 N (MergeAll.flip1 z j)) j (MergeAll.flip1 z j j) hjN
        (by simp; omega) (by simp [colOn, hj1, hjN])
      rw [show drawn [xAt N j, mc N K [0] (colOn 1 N (MergeAll.flip1 z j)), xAt N j] =
        xAt N j * mc N K [0] (colOn 1 N (MergeAll.flip1 z j)) * xAt N j by
          simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      simp only [setCtl, colOn, MergeAll.flip1]
      by_cases hij : i = j
      · subst hij; simp [hj1, hjN]
      · simp [hij]
    have fl' : Derivable (theory N)
        (xAt N j * mc N (Kind.sgnZX a) [0] (colOn 1 N y) * xAt N j)
        (mc N (Kind.sgnZX a) [0] (colOn 1 N (MergeAll.flip1 y j))) := by
      have h := fl (Kind.sgnZX a) (MergeAll.flip1 y j)
      have e : MergeAll.flip1 (MergeAll.flip1 y j) j = y := by
        funext i; simp only [MergeAll.flip1]; split_ifs <;> simp
      rwa [e] at h
    exact comm_flip k hx (fl .box x) fl'

end QCert.RealCliffordCH.Sec8.D.N13
