/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (357): the chain and the statement

See `E357.lean` for the argument.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E357

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

section Chain

variable {M : ℕ}

/-- The wires `3, …, M + 2`. -/
abbrev S6 (M : ℕ) : List ℕ := (List.range M).map (· + 3)
/-- The controls on the wires `1, 2`. -/
abbrev base6 : ℕ → Option Bool := ctlOr (ctlAt 1 true) (ctlAt 2 true)

theorem S6_nodup : (S6 M).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem mem_S6 {j : ℕ} : j ∈ S6 M ↔ 3 ≤ j ∧ j < M + 3 := by
  simp only [S6, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨j - 3, by omega, by omega⟩

/-- The box on wire `0`, black on `1, 2`, the `i`-th colouring of `3, …`. -/
abbrev B6 (M i : ℕ) : Circ (M + 3) := mc (M + 3) .box [0] (bitsOn (S6 M) i base6)

def col6 (M i : ℕ) : ℕ → Bool := fun j => (bitsOn (S6 M) i base6 j).getD false

theorem bitsOn6 (i : ℕ) : ∀ j < M + 3, bitsOn (S6 M) i base6 j = colOn 1 (M + 3) (col6 M i) j := by
  intro j hj
  by_cases hjS : j ∈ S6 M
  · obtain ⟨b, hb⟩ := bitsOn_mem (S6 M) i base6 j hjS
    have h2 := (mem_S6.1 hjS)
    simp [col6, hb, colOn, show 1 ≤ j by omega, hj]
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 ∨ j = 2 := by rw [mem_S6] at hjS; omega
    rcases this with rfl | rfl | rfl
    · simp [colOn, ctlOr, ctlAt]
    · simp [col6, colOn, ctlOr, ctlAt, bitsOn_apply_not_mem hjS]
    · simp [col6, colOn, ctlOr, ctlAt, bitsOn_apply_not_mem hjS]

theorem B6_eq (i : ℕ) : B6 M i = mc (M + 3) .box [0] (colOn 1 (M + 3) (col6 M i)) :=
  Net.mc_congr _ _ _ (bitsOn6 i)

theorem col6_two (i : ℕ) : col6 M i 2 = true := by
  simp [col6, bitsOn_apply_not_mem (show 2 ∉ S6 M by rw [mem_S6]; omega), ctlOr, ctlAt]

theorem col6_white {i : ℕ} (hi : i + 1 < 2 ^ M) :
    ∃ j, 3 ≤ j ∧ j < M + 3 ∧ col6 M i j = false := by
  obtain ⟨j, hj, hb⟩ := bitsOn_white (S6 M) i base6 S6_nodup (by simpa using hi)
  exact ⟨j, (mem_S6.1 hj).1, (mem_S6.1 hj).2, by simp [col6, hb]⟩

theorem bitsOn6_last : ∀ j < M + 3, bitsOn (S6 M) (2 ^ M - 1) base6 j = blackOn 1 (M + 3) j := by
  intro j hj
  by_cases hjS : j ∈ S6 M
  · have := bitsOn_last (S6 M) base6 j hjS
    simp only [S6, List.length_map, List.length_range] at this
    rw [this]; have := mem_S6.1 hjS; simp [blackOn]; omega
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 ∨ j = 2 := by rw [mem_S6] at hjS; omega
    rcases this with rfl | rfl | rfl <;> simp [ctlOr, ctlAt, blackOn]

/-- The `ZX`, `XZ` on wire `1`, black on `0, 2, …`. -/
abbrev Z1 (M : ℕ) : Circ (M + 3) := mc (M + 3) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))
abbrev X1 (M : ℕ) : Circ (M + 3) := mc (M + 3) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))

variable (ih : IH (M + 3))
include ih

/-- The gates on wire `0` moved to wire `1` by the swap of the wires `0, 1`. -/
theorem sw0_mc (K : Kind) (hK : kindSp K = 1) (c d : ℕ → Option Bool)
    (hcd : ∀ j < M + 3, d j = c (Net.tau 0 j)) :
    Derivable (theory (M + 3)) (swAt (M + 3) 0 * mc (M + 3) K [0] c * swAt (M + 3) 0)
      (mc (M + 3) K [1] d) := by
  have h := mcSwapAll' ih 0 (by omega) K [0] c (by simp [hK]) (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
  exact Net.mc_congr _ _ _ (fun j hj => (hcd j hj).symm)

theorem sw0_mc' (K : Kind) (hK : kindSp K = 1) (c d : ℕ → Option Bool)
    (hcd : ∀ j < M + 3, d j = c (Net.tau 0 j)) :
    Derivable (theory (M + 3)) (swAt (M + 3) 0 * mc (M + 3) K [1] c * swAt (M + 3) 0)
      (mc (M + 3) K [0] d) := by
  have h := mcSwapAll' ih 0 (by omega) K [1] c (by simp [hK]) (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([1] : List ℕ).map (Net.tau 0) = [0] by simp [Net.tau]]
  exact Net.mc_congr _ _ _ (fun j hj => (hcd j hj).symm)

/-- The box with every control black conjugates `ZX` into `XZ` on wire `1`. -/
theorem bx_z1 : Derivable (theory (M + 3)) (D.Bx (M + 3) * Z1 M * D.Bx (M + 3)) (X1 M) := by
  have hS := swsw (M + 3) 0 (by omega)
  have h333 := D.eq333 (M + 3) (by omega) ih
  have h334 := D.eq334 (M + 3) (by omega) ih
  set Hg := mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3)))
  have hB : Derivable (theory (M + 3)) (swAt (M + 3) 0 * B5 M * swAt (M + 3) 0) (D.Bx (M + 3)) := by
    refine sw0_mc' ih .box rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have hZ : Derivable (theory (M + 3))
      (swAt (M + 3) 0 * mc (M + 3) .zx [0] (blackOn 1 (M + 3)) * swAt (M + 3) 0) (Z1 M) := by
    refine sw0_mc ih .zx rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have hX : Derivable (theory (M + 3))
      (swAt (M + 3) 0 * mc (M + 3) .xz [0] (blackOn 1 (M + 3)) * swAt (M + 3) 0) (X1 M) := by
    refine sw0_mc ih .xz rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  set H' := swAt (M + 3) 0 * Hg * swAt (M + 3) 0
  have kZ := via_conj hS (l := [mc (M + 3) .zx [0] (blackOn 1 (M + 3))]) (L := [Z1 M])
    (R := [H', D.Bx (M + 3), H', D.Bx (M + 3)]) (List.Forall₂.cons hZ List.Forall₂.nil)
    (List.Forall₂.cons (Derivable.refl _) (List.Forall₂.cons hB (List.Forall₂.cons
      (Derivable.refl _) (List.Forall₂.cons hB List.Forall₂.nil)))) (by rw [drawn_one']; exact h333)
  have kX := via_conj hS (l := [mc (M + 3) .xz [0] (blackOn 1 (M + 3))]) (L := [X1 M])
    (R := [D.Bx (M + 3), H', D.Bx (M + 3), H']) (List.Forall₂.cons hX List.Forall₂.nil)
    (List.Forall₂.cons hB (List.Forall₂.cons (Derivable.refl _) (List.Forall₂.cons
      hB (List.Forall₂.cons (Derivable.refl _) List.Forall₂.nil)))) (by rw [drawn_one']; exact h334)
  rw [drawn_one', drawn_four'] at kZ kX
  have h299 := D.eq299 (M + 3) (by omega) ih
  rw [drawn_two'] at h299
  set B := D.Bx (M + 3)
  refine (dright B (dleft B kZ)).trans ?_
  have e : B * (B * H' * B * H') * B = (B * B) * (H' * B * H' * B) := by simp only [mul_assoc]
  rw [e]
  refine (dright _ h299).trans ?_
  rw [one_mul]; exact kX.symm

/-- (357) in the frame where the `CZ` is the box on wire `0`. -/
theorem canon357 :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) .box [0] base6, Z1 M, mc (M + 3) .box [0] base6]) (X1 M) := by
  set L := 2 ^ M - 1
  have hL : 2 ^ M = L + 1 := by have := Nat.one_le_two_pow (n := M); omega
  have eBL : B6 M L = D.Bx (M + 3) := Net.mc_congr _ _ _ bitsOn6_last
  have mB := mergeListB0 ih (S6 M) base6 S6_nodup (by rw [mem_S6]; omega)
    (fun w hw => (mem_S6.1 hw).2) (by simp [ctlOr, ctlAt])
  simp only [S6, List.length_map, List.length_range] at mB
  rw [hL, List.range_succ, List.map_append, SE.drawn_append] at mB
  simp only [List.map_cons, List.map_nil, drawn_one'] at mB
  have eI : mc (M + 3) .box [0] (idleOn ((List.range M).map (· + 3)) base6) =
      mc (M + 3) .box [0] base6 := Net.mc_congr _ _ _ (fun j hj => by
    rw [idleOn_apply]
    by_cases hjS : j ∈ (List.range M).map (· + 3)
    · rw [if_pos hjS]
      have h3 : 3 ≤ j := (mem_S6 (M := M)).1 hjS |>.1
      simp only [ctlOr, ctlAt]
      rw [if_neg (by omega), if_neg (by omega)]; rfl
    · rw [if_neg hjS])
  rw [eI] at mB
  set PB := drawn ((List.range L).map fun i => B6 M i)
  have mB' : Derivable (theory (M + 3)) (B6 M L * PB) (mc (M + 3) .box [0] base6) := mB
  -- `PB` passes `Z1 · Bx`
  have cPB : D.Comm (M + 3) PB (Z1 M * D.Bx (M + 3)) := N13.comm_drawn_left _ (fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' : i < L := by simpa using hi
    obtain ⟨j, hj3, hjN, hxj⟩ := col6_white (M := M) (i := i) (by omega)
    have c1 : D.Comm (M + 3) (Z1 M) (B6 M i) := by
      have hd : DiffOn 2 (M + 3) (col6 M i) (fun _ => true) :=
        ⟨j, by omega, hjN, by simp [hxj]⟩
      have h := D.eq347 (M + 3) (by omega) ih (col6 M i) (fun _ => true) hd false true true
      have e1 : mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) (col6 M i))) = B6 M i := by
        rw [B6_eq]; exact Net.mc_congr _ _ _ (fun k hk => by
          rcases k with _ | _ | k
          · simp [ctlOr, ctlAt, colOn]
          · simp [ctlOr, ctlAt, colOn, col6,
              bitsOn_apply_not_mem (show 1 ∉ S6 M by rw [mem_S6]; omega)]
          · simp [ctlOr, ctlAt, colOn])
      have e2 : mc (M + 3) (Kind.sgnZX false) [1] (ctlOr (ctlAt 0 true) (colOn 2 (M + 3) fun _ => true)) =
          Z1 M := Net.mc_congr _ _ _ (fun k hk => by simp [ctlOr, ctlAt, colOn, blackOn])
      rw [e1, e2] at h
      exact h.symm
    have c2 : D.Comm (M + 3) (D.Bx (M + 3)) (B6 M i) := by
      have h := D.eq335 (M + 3) (by omega) ih (fun _ => true) (col6 M i)
      have e : mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => true) = D.Bx (M + 3) :=
        Net.mc_congr _ _ _ (fun k hk => by simp [colOn, blackOn])
      rw [e, ← B6_eq] at h
      exact h
    exact (N13.Comm.mul_left c1 c2).symm)
  unfold D.Comm at cPB
  rw [drawn_two', drawn_two'] at cPB
  have hPP : Derivable (theory (M + 3)) (PB * PB) 1 :=
    prod_cancel (fun i => B6 M i) (fun i => B6 M i) L
      (fun i _ j _ _ => by
        show D.Comm _ (B6 M i) (B6 M j)
        rw [B6_eq, B6_eq]; exact D.eq335 (M + 3) (by omega) ih _ _)
      (fun i _ => by
        have h := D.eq311 (M + 3) (by omega) ih (col6 M i)
        rw [drawn_two'] at h
        show Derivable _ (B6 M i * B6 M i) 1
        rw [B6_eq]; exact h)
  rw [drawn_three']
  set Bc := mc (M + 3) .box [0] base6
  set B := D.Bx (M + 3)
  rw [eBL] at mB'
  -- `Bc Z Bc = (B PB) Z (B PB) = B (PB (Z B)) PB = B (Z B PB) PB = B Z B`
  have s1 : Derivable (theory (M + 3)) (Bc * Z1 M * Bc) ((B * PB) * Z1 M * (B * PB)) :=
    dmul (dmul mB'.symm (Derivable.refl _)) mB'.symm
  have e2 : (B * PB) * Z1 M * (B * PB) = B * (PB * (Z1 M * B)) * PB := by simp only [mul_assoc]
  have s3 : Derivable (theory (M + 3)) (B * (PB * (Z1 M * B)) * PB) (B * ((Z1 M * B) * PB) * PB) :=
    dright _ (dleft _ cPB.symm)
  have e4 : B * ((Z1 M * B) * PB) * PB = B * Z1 M * B * (PB * PB) := by simp only [mul_assoc]
  have s5 : Derivable (theory (M + 3)) (B * Z1 M * B * (PB * PB)) (B * Z1 M * B) := by
    have := dleft (B * Z1 M * B) hPP; rwa [mul_one] at this
  exact s1.trans ((der_of_eq e2).trans (s3.trans ((der_of_eq e4).trans (s5.trans (bx_z1 ih)))))

end Chain

/-- (357): the `CZ` of the target and the control on wire `1`, on both sides,
turns `ZX` into `XZ`. -/
theorem eq357 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [czAt N 0 1, mc N .zx [0] (blackOn 1 N), czAt N 0 1])
      (mc N .xz [0] (blackOn 1 N)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have h := canon357 ih
  have hS0 := swsw (M + 3) 0 (by omega)
  have hS1 := swsw (M + 3) 1 (by omega)
  have hC := cz_box (N := M + 3) hN
  have hZ : Derivable (theory (M + 3)) (swAt (M + 3) 0 * Z1 M * swAt (M + 3) 0)
      (mc (M + 3) .zx [0] (blackOn 1 (M + 3))) := by
    refine sw0_mc' ih .zx rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have hX : Derivable (theory (M + 3)) (swAt (M + 3) 0 * X1 M * swAt (M + 3) 0)
      (mc (M + 3) .xz [0] (blackOn 1 (M + 3))) := by
    refine sw0_mc' ih .xz rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  set C := czAt (M + 3) 0 1
  set S1 := swAt (M + 3) 1
  have k1 := via_conj hS0 (l := [mc (M + 3) .box [0] base6, Z1 M, mc (M + 3) .box [0] base6])
    (L := [S1 * C * S1, mc (M + 3) .zx [0] (blackOn 1 (M + 3)), S1 * C * S1]) (r := [X1 M])
    (R := [mc (M + 3) .xz [0] (blackOn 1 (M + 3))])
    (List.Forall₂.cons hC (List.Forall₂.cons hZ (List.Forall₂.cons hC List.Forall₂.nil)))
    (List.Forall₂.cons hX List.Forall₂.nil) (by rw [drawn_one']; exact h)
  have c1 : Derivable (theory (M + 3)) (S1 * (S1 * C * S1) * S1) C := by
    have e : S1 * (S1 * C * S1) * S1 = (S1 * S1) * C * (S1 * S1) := by simp only [mul_assoc]
    rw [e]; have := dmul (dright C hS1) hS1; simpa using this
  have cZ := conj_of_comm hS1 (eq353 (M + 3) hN ih false 1 le_rfl (by omega))
  have cX := conj_of_comm hS1 (eq353 (M + 3) hN ih true 1 le_rfl (by omega))
  have k2 := via_conj hS1 (L := [C, mc (M + 3) .zx [0] (blackOn 1 (M + 3)), C])
    (R := [mc (M + 3) .xz [0] (blackOn 1 (M + 3))])
    (List.Forall₂.cons c1 (List.Forall₂.cons cZ (List.Forall₂.cons c1 List.Forall₂.nil)))
    (List.Forall₂.cons cX List.Forall₂.nil) k1
  rwa [drawn_one'] at k2

end QCert.RealCliffordCH.Sec8.D.N15
