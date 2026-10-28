/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (356): the statement

See `E356.lean` for the argument.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E356

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

section Target

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- `Z` on wire `0`. -/
abbrev Z0 (M : ℕ) : Circ (M + 3) := atBot (M + 3) (z : Circ 1)
/-- The single-qubit `ZX` on wire `0`, every other wire idle. -/
abbrev W0 (M : ℕ) : Circ (M + 3) := mc (M + 3) .zx [0] (fun _ => none)

omit ih in
theorem W0_eq : W0 M = Z0 M * xAt (M + 3) 0 := by
  rw [W0, N13.mc_atBot (k := 1) .zx [0] _ rfl (by simp) (by simp) (fun j _ => rfl) (M + 3) (by omega)]
  have e : mc 1 .zx [0] (fun _ => none) = zx 0 := by
    rw [← mc_zx_canon 0]
    exact Net.mc_congr _ _ _ (fun j hj => by simp [blackOn]; omega)
  rw [e, show zx 0 = drawn [(x : Circ 1), z] from rfl, atBot_drawn]
  simp only [List.map_cons, List.map_nil, drawn_two']
  rw [show xAt (M + 3) 0 = atBot (M + 3) (x : Circ 1) from pad_atBot1 (M + 2) x]

theorem Z0_inv : Derivable (theory (M + 3)) (Z0 M * Z0 M) 1 := by
  have h := der_atBot (N8.rule_full Rule.e2) (M + 3) (by omega)
  rw [drawn_two', atBot_mul] at h
  refine h.trans (der_of_eq ?_)
  have := atBot_drawn (M + 3) ([] : List (Circ 1))
  simpa [drawn] using this

/-- The single-qubit `ZX` on the target passes the multi-controlled `ZX`
((354) over every colouring, (351)). -/
theorem comm_W0 : D.Comm (M + 3) (W0 M) (mc (M + 3) .zx [0] (blackOn 1 (M + 3))) := by
  set ws := (List.range (M + 2)).map (· + 1)
  have hnd : ws.Nodup := List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
  have hmem : ∀ j, j ∈ ws ↔ 1 ≤ j ∧ j < M + 3 := by
    intro j; simp only [ws, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro h; exact ⟨j - 1, by omega, by omega⟩
  have mZ := mergeListZ ih false ws (fun _ => none) hnd (by rw [hmem]; omega)
    (fun w hw => ((hmem w).1 hw).2) rfl
  have eI : mc (M + 3) (Kind.sgnZX false) [0] (idleOn ws fun _ => none) = W0 M :=
    Net.mc_congr _ _ _ (fun j hj => by rw [idleOn_apply]; split_ifs <;> rfl)
  rw [eI] at mZ
  refine N13.Comm.congr mZ (Derivable.refl _) (N13.comm_drawn_left _ (fun g hg => ?_))
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hg
  have e : mc (M + 3) (Kind.sgnZX false) [0] (bitsOn ws i fun _ => none) =
      mc (M + 3) (Kind.sgnZX false) [0]
        (colOn 1 (M + 3) fun j => (bitsOn ws i (fun _ => none) j).getD false) :=
    Net.mc_congr _ _ _ (fun j hj => by
      by_cases hjw : j ∈ ws
      · obtain ⟨b, hb⟩ := bitsOn_mem ws i (fun _ => none) j hjw
        have := (hmem j).1 hjw
        simp [hb, colOn, this.1, hj]
      · rw [bitsOn_apply_not_mem hjw]
        have : j = 0 := by rw [hmem] at hjw; omega
        simp [this, colOn])
  rw [e]
  have h := D.eq351 (M + 3) (by omega) ih (fun j => (bitsOn ws i (fun _ => none) j).getD false)
    (fun _ => true) false false
  have e2 : mc (M + 3) (Kind.sgnZX false) [0] (colOn 1 (M + 3) fun _ => true) =
      mc (M + 3) .zx [0] (blackOn 1 (M + 3)) :=
    Net.mc_congr _ _ _ (fun j hj => by simp [colOn, blackOn])
  rw [e2] at h
  exact h

/-- `Z` on wire `0` is the box on wire `1` controlled by wire `0`, conjugated by
the swap of the wires `0, 1`. -/
theorem z0_box : Derivable (theory (M + 3))
    (swAt (M + 3) 0 * mc (M + 3) .box [0] (ctlAt 1 true) * swAt (M + 3) 0) (Z0 M) := by
  have h2 : Derivable (theory 2) (swAt 2 0 * box 1 * swAt 2 0) (atBot 2 (z : Circ 1)) :=
    ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h2 (M + 3) (by omega)
  rw [atBot_mul, atBot_mul, atBot_swAt 0 (by omega) (M + 3) (by omega),
    atBot_atBot (z : Circ 1) (by norm_num) (M + 3) (by omega)] at h
  have eB : atBot (M + 3) (box 1) = mc (M + 3) .box [0] (ctlAt 1 true) := by
    rw [N13.mc_atBot (k := 2) .box [0] _ rfl (by simp) (by simp)
      (fun j hj => by simp [ctlAt]; omega) (M + 3) (by omega)]
    congr 1
  rwa [eB] at h

end Target

/-- (356): `X` on the target on both sides turns `ZX` into `XZ`. -/
theorem eq356 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, mc N .zx [0] (blackOn 1 N), xAt N 0])
      (mc N .xz [0] (blackOn 1 N)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have hS0 := swsw (M + 3) 0 (by omega)
  have hZ : Derivable (theory (M + 3)) (swAt (M + 3) 0 * Z1 M * swAt (M + 3) 0)
      (mc (M + 3) .zx [0] (blackOn 1 (M + 3))) := by
    refine sw0_mc' ih .zx rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have hX : Derivable (theory (M + 3)) (swAt (M + 3) 0 * X1 M * swAt (M + 3) 0)
      (mc (M + 3) .xz [0] (blackOn 1 (M + 3))) := by
    refine sw0_mc' ih .xz rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have hB := z0_box ih
  have k := via_conj hS0
    (l := [mc (M + 3) .box [0] (ctlAt 1 true), Z1 M, mc (M + 3) .box [0] (ctlAt 1 true)])
    (L := [Z0 M, mc (M + 3) .zx [0] (blackOn 1 (M + 3)), Z0 M]) (r := [X1 M])
    (R := [mc (M + 3) .xz [0] (blackOn 1 (M + 3))])
    (List.Forall₂.cons hB (List.Forall₂.cons hZ (List.Forall₂.cons hB List.Forall₂.nil)))
    (List.Forall₂.cons hX List.Forall₂.nil) (by rw [drawn_one']; exact canon356 ih)
  rw [drawn_one', drawn_three'] at k
  -- `X C X = (Z W) C (W' Z) = Z C Z`, `W = Z X`, `W' = X Z`
  set C := mc (M + 3) .zx [0] (blackOn 1 (M + 3))
  set Z := Z0 M
  set X := xAt (M + 3) 0
  have hZZ := Z0_inv ih
  have hXX := D.xAt_inv (M + 3) 0 (by omega)
  have hW := comm_W0 ih
  rw [W0_eq] at hW
  unfold D.Comm at hW
  rw [drawn_two', drawn_two'] at hW
  rw [drawn_three']
  have k1 : Derivable (theory (M + 3)) (X * C * X) ((Z * (Z * X)) * C * ((X * Z) * Z)) := by
    have a1 : Derivable (theory (M + 3)) (Z * (Z * X)) X := by
      rw [← mul_assoc]; have := dright X hZZ; rwa [one_mul] at this
    have a2 : Derivable (theory (M + 3)) ((X * Z) * Z) X := by
      rw [mul_assoc]; have := dleft X hZZ; rwa [mul_one] at this
    exact (dmul (dmul a1 (Derivable.refl C)) a2).symm
  have e2 : (Z * (Z * X)) * C * ((X * Z) * Z) = Z * ((Z * X) * C) * (X * Z) * Z := by
    simp only [mul_assoc]
  have k3 : Derivable (theory (M + 3)) (Z * ((Z * X) * C) * (X * Z) * Z)
      (Z * (C * (Z * X)) * (X * Z) * Z) := dright _ (dright _ (dleft _ hW.symm))
  have k5 : Derivable (theory (M + 3)) (Z * (C * (Z * X)) * (X * Z) * Z) (Z * C * Z) := by
    have e5 : Z * (C * (Z * X)) * (X * Z) * Z = Z * C * (Z * (X * X) * Z) * Z := by
      simp only [mul_assoc]
    rw [e5]
    have a : Derivable (theory (M + 3)) (Z * (X * X) * Z) 1 := by
      have := dright Z (dleft Z hXX); rw [mul_one] at this; exact this.trans hZZ
    have := dright Z (dleft (Z * C) a)
    rwa [mul_one] at this
  exact k1.trans ((der_of_eq e2).trans (k3.trans (k5.trans k)))

end QCert.RealCliffordCH.Sec8.D.N15
