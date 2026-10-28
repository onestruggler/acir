/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (319)

The multi-controlled `(-1)^a ZX` with target wire `0` and controls `1`
(colour `β`), `2` (black), `3` (colour `α`) commutes with the box on wire `0`
whose controls are `1` (colour `γ`), `2` (white) and the wires `4, …`
(colour `x`), wire `3` idle.

From five wires on.  The rotation `ZX` with all its controls black passes
four boxes idle on wire `3`, with controls `1, 2`, `1`, `2`, none (and the
bulk): by (291) carried to the wires `0, 1, 2` by the swap of the wires
`2, 3`, by (290), by (290) carried by the swap of the wires `1, 2`, and by
(308) (the box with its box wire moved to wire `3`, a semantic step).  The
box of (319) is a product of those, by a semantic step without wire `3`:
`(1γ, 2○) = (1γ) (1γ, 2●)`, and `(1○) = () (1●)` for the colour of wire
`1` other than the rotation's.  The other colours and signs of the rotation:
`X` on wire `1` exchanges `β` and `γ` (semantic steps), `X` on wire `3`
changes `α` and passes the box (`qcommE`), and `XZ` passes as the inverse of
`ZX` (Lemma B.5).
-/
import QCert.RealCliffordCH.Sec8.D.N13.E318

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## The four boxes the rotation passes -/

/-- The box of (291): box wire `0`, controls `1, 3, 4` and the bulk. -/
def E1' : Lt := .g .box [0] [(1, true), (3, true), (4, true)] true
/-- Controls `1, 2, 4` and the bulk. -/
def E1 : Lt := .g .box [0] [(1, true), (2, true), (4, true)] true
/-- Controls `2, 4` and the bulk. -/
def E3 : Lt := .g .box [0] [(2, true), (4, true)] true
/-- Controls `4` and the bulk. -/
def E4 : Lt := .g .box [0] [(4, true)] true
/-- The same, box wire `3`. -/
def E4' : Lt := .g .box [3] [(4, true)] true

theorem t291c (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [E1', Zc]) (wc 5 (m + 5) [Zc, E1']) := by
  have h := eq291 (m + 5) (by omega) ih
  have e1 : E1'.circ 5 (m + 5) = mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 5))) :=
    mc_congr _ _ _ (by ctl_tac)
  have e2 : Zc.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 4) := mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, wc_two, e1, e2]
  exact h

def T291s : SE.Tbl := [([E1', Zc], [Zc, E1']), ([.s (.S 2), E1', .s (.S 2)], [E1])]

theorem T291s_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T291s := by
  intro e he
  simp only [T291s, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact t291c m ih
  · exact swapE m 5 2 (by omega) .box [0] _ true (by decide) (by decide)

theorem run291s : check 4 T291s [E1, Zc] [Zc, E1]
    [.rw 0 1 true, .sem 2 2 [Zc, .s (.S 2)] 4, .rw 1 0 false, .sem 0 2 [Zc, .s (.S 2)] 4,
     .rw 1 1 false] = true := by
  decide +kernel

theorem t291s (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [E1, Zc]) (wc 5 (m + 5) [Zc, E1]) :=
  check_sound (frame 4) ih (T291s_ok m ih) run291s

def T290s1 : SE.Tbl := [([Bc, Zc], [Zc, Bc]), ([.s (.S 1), Bc, .s (.S 1)], [E3])]

theorem T290s1_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T290s1 := by
  intro e he
  simp only [T290s1, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact t290c m ih
  · exact swapE m 5 1 (by omega) .box [0] _ true (by decide) (by decide)

theorem run290s1 : check 4 T290s1 [E3, Zc] [Zc, E3]
    [.rw 0 1 true, .sem 2 2 [Zc, .s (.S 1)] 4, .rw 1 0 false, .sem 0 2 [Zc, .s (.S 1)] 4,
     .rw 1 1 false] = true := by
  decide +kernel

theorem t290s1 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [E3, Zc]) (wc 5 (m + 5) [Zc, E3]) :=
  check_sound (frame 4) ih (T290s1_ok m ih) run290s1

theorem t308c (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [Zc, E4']) (wc 5 (m + 5) [E4', Zc]) := by
  have h := eq308 (m + 5) (by omega) ih 4 (by omega) (by omega) (Zc.circ 5 4)
  have e1 : Zc.circ 5 (m + 5) = atBot (m + 5) (Zc.circ 5 4) :=
    mc_atBot (k := 4) .zx [0] _ rfl (by decide) (by decide) (fun j hj => by
      rcases j with _ | _ | _ | _ | _ | j <;> simp [ctl] <;> omega) (m + 5) (by omega)
  have e2 : E4'.circ 5 (m + 5) = mc (m + 5) .box [4 - 1] (blackOn 4 (m + 5)) :=
    mc_congr _ _ _ (by ctl_tac)
  rw [wc_two, wc_two, e1, e2]
  exact h

def T308s : SE.Tbl := [([Zc, E4'], [E4', Zc])]

theorem run308s : check 4 T308s [E4, Zc] [Zc, E4]
    [.sem 0 1 [E4'] 1, .rw 0 0 true, .sem 1 1 [E4] 1] = true := by
  decide +kernel

theorem t308s (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [E4, Zc]) (wc 5 (m + 5) [Zc, E4]) :=
  check_sound (frame 4) ih (by
    intro e he
    simp only [T308s, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; exact t308c m ih) run308s

/-! ## The rotation with black controls -/

def T319 : SE.Tbl := [([Bc, Zc], [Zc, Bc]), ([E1, Zc], [Zc, E1]), ([E3, Zc], [Zc, E3]),
  ([E4, Zc], [Zc, E4])]

theorem T319_ok (m : ℕ) (ih : IH (m + 5)) : AllD 5 m T319 := by
  intro e he
  simp only [T319, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact t290c m ih
  · exact t291s m ih
  · exact t290s1 m ih
  · exact t308s m ih

def run319 : Bool → List St
  | true => [.sem 1 1 [Bc, E1] 3, .rw 0 0 true, .rw 1 1 true, .sem 0 2 [Bq true] 3]
  | false => [.sem 1 1 [E4, Bc, E3, E1] 3, .rw 0 3 true, .rw 1 0 true, .rw 2 2 true,
      .rw 3 1 true, .sem 0 4 [Bq false] 3]

theorem chk319 : ∀ γ : Bool, check 4 T319 [Zc, Bq γ] [Bq γ, Zc] (run319 γ) = true := by
  decide +kernel

/-! ## Every colour and sign of the rotation -/

/-- The rotation of (319). -/
def Wl (a α β : Bool) : Lt := .g (Kind.sgnZX a) [0] [(1, β), (2, true), (3, α)] false

theorem chkInv : ∀ α β : Bool,
    check 4 [] [Wl false α β, Wl true α β] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [Wl true α β, Wl false α β] [] [.sem 0 2 [] 4] = true := by
  decide +kernel

theorem chkFlipW : ∀ a α β : Bool,
    check 4 [] (xL 3 ++ [Wl a true β] ++ xL 3) [Wl a false β] [.sem 0 7 [Wl a false β] 4] = true ∧
    check 4 [] (xL 1 ++ [Wl a α true] ++ xL 1) [Wl a α false] [.sem 0 7 [Wl a α false] 4] = true := by
  decide +kernel

theorem chkFlipB : ∀ γ : Bool,
    check 4 [] (xL 1 ++ [Bq γ] ++ xL 1) [Bq (!γ)] [.sem 0 7 [Bq (!γ)] 3] = true := by
  decide +kernel

def TX3 (γ : Bool) : SE.Tbl := [([Bq γ, .s (.H 3)], [.s (.H 3), Bq γ]), ([Bq γ, .s (.Z 3)], [.s (.Z 3), Bq γ])]

theorem chkX3 : ∀ γ : Bool, check 4 (TX3 γ) (xL 3 ++ [Bq γ] ++ xL 3) [Bq γ]
    [.rw 2 0 true, .rw 1 1 true, .rw 0 0 true, .sem 1 6 [] 0] = true := by
  decide +kernel

theorem TX3_ok (m : ℕ) (γ : Bool) : AllD 5 m (TX3 γ) := by
  intro e he
  simp only [TX3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact qcommE m 4 3 (by omega) (Bq γ) (by cases γ <;> decide) (by cases γ <;> decide) _ (Or.inl rfl)
  · exact qcommE m 4 3 (by omega) (Bq γ) (by cases γ <;> decide) (by cases γ <;> decide) _ (Or.inr rfl)

theorem allD_nil (K m : ℕ) : AllD K m [] := fun _ h => by simp at h

theorem r319 (m : ℕ) (ih : IH (m + 5)) (a α β γ : Bool) :
    Comm (m + 5) ((Wl a α β).circ 5 (m + 5)) ((Bq γ).circ 5 (m + 5)) := by
  have hx : ∀ q, q < m + 5 → Derivable (theory (m + 5)) (xAt (m + 5) q * xAt (m + 5) q) 1 :=
    fun q hq => xAt_inv (m + 5) q hq
  have base : ∀ γ, Comm (m + 5) ((Wl false true true).circ 5 (m + 5)) ((Bq γ).circ 5 (m + 5)) :=
    fun γ => check_sound (frame 4) ih (T319_ok m ih) (chk319 γ)
  have flipB : ∀ γ, Derivable (theory (m + 5)) (xAt (m + 5) 1 * (Bq γ).circ 5 (m + 5) * xAt (m + 5) 1)
      ((Bq (!γ)).circ 5 (m + 5)) := fun γ => by
    have h := check_sound (frame 4) ih (allD_nil 5 m) (chkFlipB γ)
    rwa [wc_xconj, wc_one'] at h
  have flipW1 : ∀ a α, Derivable (theory (m + 5))
      (xAt (m + 5) 1 * (Wl a α true).circ 5 (m + 5) * xAt (m + 5) 1) ((Wl a α false).circ 5 (m + 5)) :=
    fun a α => by
      have h := check_sound (frame 4) ih (allD_nil 5 m) ((chkFlipW a α true).2)
      rwa [wc_xconj, wc_one'] at h
  have flipW3 : ∀ a β, Derivable (theory (m + 5))
      (xAt (m + 5) 3 * (Wl a true β).circ 5 (m + 5) * xAt (m + 5) 3) ((Wl a false β).circ 5 (m + 5)) :=
    fun a β => by
      have h := check_sound (frame 4) ih (allD_nil 5 m) ((chkFlipW a true β).1)
      rwa [wc_xconj, wc_one'] at h
  have passX3 : ∀ γ, Derivable (theory (m + 5))
      (xAt (m + 5) 3 * (Bq γ).circ 5 (m + 5) * xAt (m + 5) 3) ((Bq γ).circ 5 (m + 5)) := fun γ => by
    have h := check_sound (frame 4) ih (TX3_ok m γ) (chkX3 γ)
    rwa [wc_xconj, wc_one'] at h
  -- `β`
  have hβ : ∀ β γ, Comm (m + 5) ((Wl false true β).circ 5 (m + 5)) ((Bq γ).circ 5 (m + 5)) := by
    intro β γ
    cases β
    · have := comm_flip (base (!γ)) (hx 1 (by omega)) (flipW1 false true) (flipB (!γ))
      rwa [Bool.not_not] at this
    · exact base γ
  -- `α`
  have hα : ∀ α β γ, Comm (m + 5) ((Wl false α β).circ 5 (m + 5)) ((Bq γ).circ 5 (m + 5)) := by
    intro α β γ
    cases α
    · exact comm_flip (hβ β γ) (hx 3 (by omega)) (flipW3 false β) (passX3 γ)
    · exact hβ β γ
  -- `a`
  cases a
  · exact hα α β γ
  · have hi := check_sound (frame 4) ih (allD_nil 5 m) (chkInv α β).1
    have hi' := check_sound (frame 4) ih (allD_nil 5 m) (chkInv α β).2
    rw [wc_two] at hi hi'
    simp only [drawn_two] at hi hi'
    have e : wc 5 (m + 5) [] = 1 := rfl
    rw [e] at hi hi'
    exact Comm.inv (hα α β γ) hi' hi

/-! ## In the conventions of the interface -/

theorem Wl_ok : ∀ a α β : Bool, (Wl a α β).ok 4 = true := by decide

theorem Wl_rebase (N : ℕ) (a α β : Bool) : (Wl a α β).circ 5 N = (Wl a α β).circ 4 N :=
  mc_congr _ _ _ (by ctl_tac)

/-- (319) from five wires on, every colour. -/
theorem eq319_ge5 (N : ℕ) (hN : 5 ≤ N) (ih : IH N) (x : ℕ → Bool) (a α β γ : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 β) (ctlOr (ctlAt 2 true) (ctlAt 3 α))))
      (mc N .box [0] (ctlOr (ctlAt 1 γ) (ctlOr (ctlAt 2 false) (colOn 4 N x)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 5 := ⟨N - 5, by omega⟩
  have h : Derivable (theory (m + 5)) (wc 4 (m + 5) [Wl a α β, Bq4 γ])
      (wc 4 (m + 5) [Bq4 γ, Wl a α β]) := by
    have := r319 m ih a α β γ
    unfold Comm at this
    rw [Wl_rebase, Bq_rebase] at this
    exact this
  have h4 := colour_wc (K := 4) (N := m + 5) (by omega) x (l := [Wl a α β, Bq4 γ])
    (r := [Bq4 γ, Wl a α β]) (all_two (Wl_ok a α β) (Bq4_ok γ)) (all_two (Bq4_ok γ) (Wl_ok a α β)) h
  have e1 : cX 4 (m + 5) x (Wl a α β) =
      mc (m + 5) (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 β) (ctlOr (ctlAt 2 true) (ctlAt 3 α))) :=
    mc_congr _ _ _ (by ctl_tac)
  have e2 : cX 4 (m + 5) x (Bq4 γ) =
      mc (m + 5) .box [0] (ctlOr (ctlAt 1 γ) (ctlOr (ctlAt 2 false) (colOn 4 (m + 5) x))) := by
    show mc _ _ _ _ = _
    exact mc_congr _ _ _ (by ctl_tac)
  have e3 : ∀ y z : Lt, wcX 4 (m + 5) x [y, z] = drawn [cX 4 (m + 5) x y, cX 4 (m + 5) x z] :=
    fun _ _ => rfl
  rw [e3, e3, e1, e2] at h4
  exact h4

end QCert.RealCliffordCH.Sec8.D.N13
