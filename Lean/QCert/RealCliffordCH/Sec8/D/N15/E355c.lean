/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (355): the chain and the statement

See `E355.lean` for the argument.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E355b

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

section Chain

variable {M : ℕ}

/-- The `XZ` and `ZX` with wire `1` black and the `i`-th colouring of `2, …`. -/
abbrev X5 (M i : ℕ) : Circ (M + 3) := mc (M + 3) .xz [0] (bitsOn (S5 M) i (ctlAt 1 true))
abbrev Z5 (M i : ℕ) : Circ (M + 3) := mc (M + 3) .zx [0] (bitsOn (S5 M) i (ctlAt 1 true))

theorem X5_eq (i : ℕ) : X5 M i = mc (M + 3) (Kind.sgnZX true) [0] (colOn 1 (M + 3) (col5 M i)) :=
  Net.mc_congr _ _ _ (bitsOn5 i)

theorem Z5_eq (i : ℕ) : Z5 M i = mc (M + 3) (Kind.sgnZX false) [0] (colOn 1 (M + 3) (col5 M i)) :=
  Net.mc_congr _ _ _ (bitsOn5 i)

theorem col5_one (i : ℕ) : col5 M i 1 = true := by
  simp [col5, bitsOn_apply_not_mem (show 1 ∉ S5 M by rw [mem_S5]; omega), ctlAt]

theorem col5_white {i : ℕ} (hi : i + 1 < 2 ^ (M + 1)) :
    ∃ j, 2 ≤ j ∧ j < M + 3 ∧ col5 M i j = false := by
  obtain ⟨j, hj, hb⟩ := bitsOn_white (S5 M) i (ctlAt 1 true) S5_nodup (by simpa using hi)
  exact ⟨j, (mem_S5.1 hj).1, (mem_S5.1 hj).2, by simp [col5, hb]⟩

theorem bitsOn5_last : ∀ j < M + 3,
    bitsOn (S5 M) (2 ^ (M + 1) - 1) (ctlAt 1 true) j = blackOn 1 (M + 3) j := by
  intro j hj
  by_cases hjS : j ∈ S5 M
  · have := bitsOn_last (S5 M) (ctlAt 1 true) j hjS
    simp only [S5, List.length_map, List.length_range] at this
    rw [this]; have := mem_S5.1 hjS; simp [blackOn]; omega
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 := by rw [mem_S5] at hjS; omega
    rcases this with rfl | rfl <;> simp [ctlAt, blackOn]

variable (ih : IH (M + 3))
include ih

/-- (354) over every colouring of the wires `2, …`. -/
theorem merged5 (a : Bool) :
    Derivable (theory (M + 3))
      (drawn ((List.range (2 ^ (M + 1))).map fun i =>
        mc (M + 3) (Kind.sgnZX a) [0] (bitsOn (S5 M) i (ctlAt 1 true))))
      (mc (M + 3) (Kind.sgnZX a) [0] (ctlAt 1 true)) := by
  have h := mergeListZ ih a (S5 M) (ctlAt 1 true) S5_nodup (by rw [mem_S5]; omega)
    (fun w hw => (mem_S5.1 hw).2) (by simp [ctlAt])
  simp only [S5, List.length_map, List.length_range] at h
  refine h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => ?_)))
  rw [idleOn_apply]
  by_cases hjS : j ∈ S5 M
  · rw [if_pos hjS]; have := mem_S5.1 hjS; simp [ctlAt]; omega
  · rw [if_neg hjS]

/-- `XZ · XZ` is the box, every control black. -/
theorem xz_sq_black :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) .xz [0] (blackOn 1 (M + 3)), mc (M + 3) .xz [0] (blackOn 1 (M + 3))])
      (D.Bx (M + 3)) := by
  set L := 2 ^ (M + 1) - 1
  have hL : 2 ^ (M + 1) = L + 1 := by have := Nat.one_le_two_pow (n := M + 1); omega
  have eXL : X5 M L = mc (M + 3) .xz [0] (blackOn 1 (M + 3)) := Net.mc_congr _ _ _ bitsOn5_last
  have eZL : Z5 M L = mc (M + 3) .zx [0] (blackOn 1 (M + 3)) := Net.mc_congr _ _ _ bitsOn5_last
  have mX := merged5 ih true
  have mZ := merged5 ih false
  rw [hL, List.range_succ, List.map_append, SE.drawn_append] at mX mZ
  simp only [List.map_cons, List.map_nil, drawn_one'] at mX mZ
  set PX := drawn ((List.range L).map fun i => X5 M i)
  set PZ := drawn ((List.range L).map fun i => Z5 M i)
  have mX' : Derivable (theory (M + 3)) (X5 M L * PX) (mc (M + 3) .xz [0] (ctlAt 1 true)) := mX
  have mZ' : Derivable (theory (M + 3)) (Z5 M L * PZ) (mc (M + 3) .zx [0] (ctlAt 1 true)) := mZ
  have h305 := D.eq305 (M + 3) (by omega) ih
  rw [drawn_four'] at h305
  -- `PX` passes `B5 · X5 L`
  have cPX : D.Comm (M + 3) PX (B5 M * X5 M L) := N13.comm_drawn_left _ (fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' : i < L := by simpa using hi
    obtain ⟨j, hj2, hjN, hxj⟩ := col5_white (M := M) (i := i) (by omega)
    have c1 : D.Comm (M + 3) (B5 M) (X5 M i) := by
      rw [X5_eq]; exact (comm_B5 ih true _ (col5_one i) j hj2 hjN hxj).symm
    have c2 : D.Comm (M + 3) (X5 M L) (X5 M i) := by
      rw [X5_eq, X5_eq]; exact D.eq351 (M + 3) (by omega) ih _ _ true true
    exact (N13.Comm.mul_left c1 c2).symm)
  unfold D.Comm at cPX
  rw [drawn_two', drawn_two'] at cPX
  -- `PZ · PX = 1`
  have hPP : Derivable (theory (M + 3)) (PZ * PX) 1 :=
    prod_cancel (fun i => Z5 M i) (fun i => X5 M i) L
      (fun i _ j _ _ => by
        show D.Comm _ (Z5 M i) (X5 M j)
        rw [Z5_eq, X5_eq]; exact D.eq351 (M + 3) (by omega) ih _ _ false true)
      (fun i _ => by
        have h := (D.eq317 (M + 3) (by omega) ih (col5 M i)).2
        rw [drawn_two'] at h
        show Derivable _ (Z5 M i * X5 M i) 1
        rw [Z5_eq, X5_eq]; exact h)
  -- the box `B5` is an involution, and `B5 · ZX · B5 = XZ`
  have hB := B5_inv ih
  rw [drawn_two'] at hB
  have h333 := D.eq333 (M + 3) (by omega) ih
  have h334 := D.eq334 (M + 3) (by omega) ih
  rw [drawn_four'] at h333 h334
  set Hg := mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3)))
  have kBZB : Derivable (theory (M + 3)) (B5 M * Z5 M L * B5 M) (X5 M L) := by
    rw [eZL, eXL]
    refine (dright _ (dleft _ h333)).trans ?_
    have e : B5 M * (B5 M * Hg * B5 M * Hg) * B5 M = (B5 M * B5 M) * (Hg * B5 M * Hg * B5 M) := by
      simp only [mul_assoc]
    rw [e]
    refine (dright _ hB).trans ?_
    rw [one_mul]; exact h334.symm
  -- the chain
  have s1 : Derivable (theory (M + 3)) (D.Bx (M + 3))
      (B5 M * (Z5 M L * PZ) * B5 M * (X5 M L * PX)) := by
    refine h305.symm.trans (dmul (dmul (dmul (Derivable.refl _) mZ'.symm) (Derivable.refl _)) mX'.symm)
  have e2 : B5 M * (Z5 M L * PZ) * B5 M * (X5 M L * PX) =
      B5 M * Z5 M L * PZ * (B5 M * X5 M L * PX) := by simp only [mul_assoc]
  have s3 : Derivable (theory (M + 3)) (B5 M * Z5 M L * PZ * (B5 M * X5 M L * PX))
      (B5 M * Z5 M L * (PZ * PX) * (B5 M * X5 M L)) := by
    have := dleft (B5 M * Z5 M L * PZ) cPX
    simpa only [mul_assoc] using this
  have s4 : Derivable (theory (M + 3)) (B5 M * Z5 M L * (PZ * PX) * (B5 M * X5 M L))
      (B5 M * Z5 M L * B5 M * X5 M L) := by
    have := dright (B5 M * X5 M L) (dleft (B5 M * Z5 M L) hPP)
    simpa only [mul_one, mul_assoc] using this
  have s5 : Derivable (theory (M + 3)) (B5 M * Z5 M L * B5 M * X5 M L) (X5 M L * X5 M L) :=
    dright _ kBZB
  rw [drawn_two', ← eXL]
  exact (s1.trans ((der_of_eq e2).trans (s3.trans (s4.trans s5)))).symm

end Chain

/-- (355) with every control black. -/
theorem sq_black {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (a : Bool) :
    Derivable (theory N)
      (drawn [mc N (Kind.sgnZX a) [0] (blackOn 1 N), mc N (Kind.sgnZX a) [0] (blackOn 1 N)])
      (D.Bx N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have hX := xz_sq_black ih
  cases a
  · -- `ZX ZX = ZX ZX (XZ XZ Bx) = Bx`
    have h317 := (D.eq317 (M + 3) hN ih (fun _ => true)).2
    have e : ∀ K, mc (M + 3) K [0] (colOn 1 (M + 3) fun _ => true) = mc (M + 3) K [0] (blackOn 1 (M + 3)) :=
      fun K => Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
    rw [e, e, drawn_two'] at h317
    have h299 := D.eq299 (M + 3) hN ih
    rw [drawn_two'] at h299 hX
    set Z := mc (M + 3) .zx [0] (blackOn 1 (M + 3))
    set X := mc (M + 3) .xz [0] (blackOn 1 (M + 3))
    set B := D.Bx (M + 3)
    show Derivable (theory (M + 3)) (drawn [Z, Z]) B
    rw [drawn_two']
    have k1 : Derivable (theory (M + 3)) (X * X * B) 1 := (dright B hX).trans h299
    have k2 : Derivable (theory (M + 3)) (Z * Z) (Z * Z * (X * X * B)) := by
      have := dleft (Z * Z) k1; rw [mul_one] at this; exact this.symm
    have e3 : Z * Z * (X * X * B) = Z * (Z * X) * X * B := by simp only [mul_assoc]
    have k3 : Derivable (theory (M + 3)) (Z * (Z * X) * X * B) (Z * X * B) := by
      have := dright B (dright X (dleft Z h317)); simpa only [mul_one] using this
    have k4 : Derivable (theory (M + 3)) (Z * X * B) B := by
      have := dright B h317; simpa only [one_mul] using this
    exact k2.trans ((der_of_eq e3).trans (k3.trans k4))
  · exact hX

/-- (355): the square of a multi-controlled `(-1)ᵃ XZ` is the box with the
same controls. -/
theorem eq355 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (x : ℕ → Bool) :
    Derivable (theory N)
      (drawn [mc N (Kind.sgnZX a) [0] (colOn 1 N x), mc N (Kind.sgnZX a) [0] (colOn 1 N x)])
      (mc N .box [0] (colOn 1 N x)) := by
  revert x
  refine colour_ind (N := N) (w := 0) (fun x => Derivable (theory N)
      (drawn [mc N (Kind.sgnZX a) [0] (colOn 1 N x), mc N (Kind.sgnZX a) [0] (colOn 1 N x)])
      (mc N .box [0] (colOn 1 N x))) ?_ ?_ ?_
  · intro x y hxy h
    have e : ∀ K, mc N K [0] (colOn 1 N x) = mc N K [0] (colOn 1 N y) := fun K =>
      Net.mc_congr _ _ _ (fun i hi => by
        simp only [colOn]; split_ifs with h1
        · rw [hxy i h1.1 h1.2 (by omega)]
        · rfl)
    rwa [e, e] at h
  · intro x j hj1 hjN _ h
    have hX := D.xAt_inv N j hjN
    have fl : ∀ K, Derivable (theory N) (xAt N j * mc N K [0] (colOn 1 N x) * xAt N j)
        (mc N K [0] (colOn 1 N (flip1 x j))) := by
      intro K
      have := D.eq81 N K [0] (colOn 1 N x) j (x j) hjN (by simp; omega) (by simp [colOn, hj1, hjN])
      rw [conj3] at this
      refine this.trans (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      simp only [setCtl, colOn, flip1]
      by_cases hij : i = j
      · subst hij; simp [hj1, hjN]
      · simp [hij]
    have k := via_conj hX (l := [mc N (Kind.sgnZX a) [0] (colOn 1 N x),
        mc N (Kind.sgnZX a) [0] (colOn 1 N x)]) (r := [mc N .box [0] (colOn 1 N x)])
      (List.Forall₂.cons (fl _) (List.Forall₂.cons (fl _) List.Forall₂.nil))
      (List.Forall₂.cons (fl _) List.Forall₂.nil) (by rw [drawn_one']; exact h)
    rwa [drawn_one'] at k
  · have h := sq_black hN ih a
    have e : ∀ K, mc N K [0] (colOn 1 N fun _ => true) = mc N K [0] (blackOn 1 N) := fun K =>
      Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
    show Derivable (theory N) (drawn [mc N (Kind.sgnZX a) [0] (colOn 1 N fun _ => true),
      mc N (Kind.sgnZX a) [0] (colOn 1 N fun _ => true)]) (mc N .box [0] (colOn 1 N fun _ => true))
    simp only [e]
    exact h

end QCert.RealCliffordCH.Sec8.D.N15
