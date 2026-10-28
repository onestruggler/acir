/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (356): `X` on the target turns `ZX` into `XZ`

Not the paper's route.  `X = Z · (ZX)` on the target, and the single-qubit
`ZX` there passes the multi-controlled `ZX`: by (354) over every colouring of
the other wires (`mergeListZ`) it is a product of multi-controlled `ZX`s, each
passing by (351).  So it is enough that `Z` on the target turns `ZX` into `XZ`;
conjugated by the swap of the wires `0, 1`, `Z` is the box on wire `0`
controlled by wire `1`, and the argument of (357) applies (`canon356`): by
(309) over every colouring of the wires `2, …`, (347), (335), (311), the box
with every control black remains, which conjugates `ZX` into `XZ`.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E357b

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

section Chain

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- The box on wire `0` controlled by wire `1` conjugates `ZX` on wire `1` into
`XZ`. -/
theorem canon356 :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) .box [0] (ctlAt 1 true), Z1 M, mc (M + 3) .box [0] (ctlAt 1 true)]) (X1 M) := by
  set L := 2 ^ (M + 1) - 1
  have hL : 2 ^ (M + 1) = L + 1 := by have := Nat.one_le_two_pow (n := M + 1); omega
  have eBL : mc (M + 3) .box [0] (bitsOn (S5 M) L (ctlAt 1 true)) = D.Bx (M + 3) :=
    Net.mc_congr _ _ _ bitsOn5_last
  have mB := mergeListB0 ih (S5 M) (ctlAt 1 true) S5_nodup (by rw [mem_S5]; omega)
    (fun w hw => (mem_S5.1 hw).2) (by simp [ctlAt])
  simp only [S5, List.length_map, List.length_range] at mB
  rw [hL, show List.range (L + 1) = List.range L ++ [L] from List.range_succ, List.map_append,
    SE.drawn_append] at mB
  simp only [List.map_cons, List.map_nil, drawn_one'] at mB
  have eI : mc (M + 3) .box [0] (idleOn ((List.range (M + 1)).map (· + 2)) (ctlAt 1 true)) =
      mc (M + 3) .box [0] (ctlAt 1 true) := Net.mc_congr _ _ _ (fun j hj => by
    rw [idleOn_apply]
    by_cases hjS : j ∈ (List.range (M + 1)).map (· + 2)
    · rw [if_pos hjS]
      have h2 : 2 ≤ j := (mem_S5 (M := M)).1 hjS |>.1
      simp only [ctlAt]
      rw [if_neg (by omega)]
    · rw [if_neg hjS])
  rw [eI] at mB
  set B7 := fun i => mc (M + 3) .box [0] (bitsOn (S5 M) i (ctlAt 1 true))
  have B7_eq : ∀ i, B7 i = mc (M + 3) .box [0] (colOn 1 (M + 3) (col5 M i)) := fun i =>
    Net.mc_congr _ _ _ (bitsOn5 i)
  set PB := drawn ((List.range L).map fun i => B7 i)
  have mB' : Derivable (theory (M + 3)) (B7 L * PB) (mc (M + 3) .box [0] (ctlAt 1 true)) := mB
  have cPB : D.Comm (M + 3) PB (Z1 M * D.Bx (M + 3)) := N13.comm_drawn_left _ (fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' : i < L := by simpa using hi
    obtain ⟨j, hj2, hjN, hxj⟩ := col5_white (M := M) (i := i) (by omega)
    have c1 : D.Comm (M + 3) (Z1 M) (B7 i) := by
      have hd : DiffOn 2 (M + 3) (col5 M i) (fun _ => true) :=
        ⟨j, hj2, hjN, by simp [hxj]⟩
      have h := D.eq347 (M + 3) (by omega) ih (col5 M i) (fun _ => true) hd false true true
      have e1 : mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) (col5 M i))) = B7 i := by
        rw [B7_eq]; exact Net.mc_congr _ _ _ (fun k hk => by
          rcases k with _ | _ | k
          · simp [ctlOr, ctlAt, colOn]
          · simp [ctlOr, ctlAt, colOn, col5_one]
          · simp [ctlOr, ctlAt, colOn])
      have e2 : mc (M + 3) (Kind.sgnZX false) [1] (ctlOr (ctlAt 0 true) (colOn 2 (M + 3) fun _ => true)) =
          Z1 M := Net.mc_congr _ _ _ (fun k hk => by simp [ctlOr, ctlAt, colOn, blackOn])
      rw [e1, e2] at h
      exact h.symm
    have c2 : D.Comm (M + 3) (D.Bx (M + 3)) (B7 i) := by
      have h := D.eq335 (M + 3) (by omega) ih (fun _ => true) (col5 M i)
      have e : mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => true) = D.Bx (M + 3) :=
        Net.mc_congr _ _ _ (fun k hk => by simp [colOn, blackOn])
      rw [e, ← B7_eq] at h
      exact h
    exact (N13.Comm.mul_left c1 c2).symm)
  unfold D.Comm at cPB
  rw [drawn_two', drawn_two'] at cPB
  have hPP : Derivable (theory (M + 3)) (PB * PB) 1 :=
    prod_cancel (fun i => B7 i) (fun i => B7 i) L
      (fun i _ j _ _ => by
        show D.Comm _ (B7 i) (B7 j)
        rw [B7_eq, B7_eq]; exact D.eq335 (M + 3) (by omega) ih _ _)
      (fun i _ => by
        have h := D.eq311 (M + 3) (by omega) ih (col5 M i)
        rw [drawn_two'] at h
        show Derivable _ (B7 i * B7 i) 1
        rw [B7_eq]; exact h)
  rw [drawn_three']
  set Bc := mc (M + 3) .box [0] (ctlAt 1 true)
  set B := D.Bx (M + 3)
  have eBL' : B7 L = B := eBL
  rw [eBL'] at mB'
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

end QCert.RealCliffordCH.Sec8.D.N15
