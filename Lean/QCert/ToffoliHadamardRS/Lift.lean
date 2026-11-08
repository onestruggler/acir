/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: lifting

Translation of `Lift.agda`.  A relation of Figure 4 or 7, or `r_K`, at one
level is the same relation one level up, so derivations lift: from Figure 4
at level 0 to `R₁⁺`, and from `R₁⁺` to `R₂⁺`.
-/
import QCert.ToffoliHadamardRS.Syntactics
import QCert.LiRossSelinger.Units

namespace QCert.ToffoliHadamardRS

variable {k : ℕ}

theorem up0 : ∀ {w v : Word (Gate k)}, R0 w v → R0 (upW w) (upW v)
  | _, _, .r1 => .r1
  | _, _, .r2 => .r2
  | _, _, .r3 => .r3
  | _, _, .r4 => .r4
  | _, _, .r5 => .r5
  | _, _, .r6 => .r6
  | _, _, .r7 => .r7
  | _, _, .r8 => .r8
  | _, _, .r9 => .r9
  | _, _, .r10 => .r10
  | _, _, .r11 => .r11
  | _, _, .r12 => .r12
  | _, _, .r13 => .r13
  | _, _, .r14 => .r14
  | _, _, .r15 => .r15
  | _, _, .r16 => .r16
  | _, _, .r17 => .r17
  | _, _, .r18 => .r18
  | _, _, .r19 => .r19
  | _, _, .r20 => .r20
  | _, _, .r21 => .r21
  | _, _, .r22 => .r22
  | _, _, .r23 => .r23
  | _, _, .r24 => .r24
  | _, _, .r25 => .r25
  | _, _, .r26 => .r26
  | _, _, .r27 => .r27
  | _, _, .r28 => .r28
  | _, _, .r29 => .r29
  | _, _, .r30 => .r30
  | _, _, .r31 => .r31
  | _, _, .r32 => .r32
  | _, _, .r33 => .r33
  | _, _, .r34 => .r34
  | _, _, .r35 => .r35
  | _, _, .r36 => .r36
  | _, _, .r37 => .r37
  | _, _, .r38 => .r38
  | _, _, .r39 => .r39
  | _, _, .r40 => .r40
  | _, _, .r41 => .r41
  | _, _, .r42 => .r42
  | _, _, .r43 => .r43
  | _, _, .r44 => .r44
  | _, _, .r45 => .r45
  | _, _, .r46 => .r46

/-! The aliases of Figure 7 are the same words one level up. -/

theorem upW_T : ∀ i : ℕ, upW (T (k := k) i) = T i
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

theorem upW_TR (a d : ℕ) : upW (TR (k := k) a d) = TR a d := by
  induction d generalizing a with
  | zero => exact upW_T a
  | succ d ih => simp only [TR, map_mul, upW_T, ih]

theorem upW_Xab (a b : ℕ) : upW (Xab (k := k) a b) = Xab a b := by
  unfold Xab; split
  · exact map_one _
  · exact upW_TR _ _

theorem upW_NK : upW (NKw (k := k)) = NKw := rfl

theorem upW_m0 : upW (m0 (k := k)) = m0 := rfl

theorem upW_m (c : ℕ) : upW (m (k := k) c) = m c := by
  simp only [m, map_mul, upW_Xab, upW_m0]

theorem upW_Kq (a b c d : ℕ) : upW (Kq (k := k) a b c d) = Kq a b c d := by
  simp only [Kq, map_mul, upW_Xab, upW_NK]

theorem upW_Ω : upW (Ω (k := k)) = Ω := by
  simp only [Ω, map_mul, upW_Kq, upW_NK, upW_T]

set_option linter.unusedSimpArgs false in
theorem up7 : ∀ {w v : Word (Gate (k + 1))}, Fig7 w v → Fig7 (upW w) (upW v)
  | _, _, .r83 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r83
  | _, _, .r84 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r84
  | _, _, .r85 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r85
  | _, _, .r86 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r86
  | _, _, .r87 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r87
  | _, _, .r88 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r88
  | _, _, .r89 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r89
  | _, _, .r90 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r90
  | _, _, .r91 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r91
  | _, _, .r92 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r92
  | _, _, .r93 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r93
  | _, _, .r94 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r94
  | _, _, .r95 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r95
  | _, _, .r96 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r96
  | _, _, .r97 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r97
  | _, _, .r98 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r98
  | _, _, .r99 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r99
  | _, _, .r100 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r100
  | _, _, .r101 => by simp only [map_mul, map_one, upW_T, upW_m0, upW_m, upW_Xab, upW_Kq, upW_Ω, upW_NK]; exact .r101

theorem upK : ∀ {w v : Word (Gate (k + 1))}, RK w v → RK (upW w) (upW v)
  | _, _, .rK => .rK

/-- Figure 4 at level 0 into `R₁⁺`. -/
theorem lift01 {w v : Word GD} (h : Derivable (R0 (k := 0)) w v) :
    Derivable R1plus (upW w) (upW v) :=
  derivable_map upW (fun _ _ r => Derivable.of (R1plus.fig4 (up0 r))) h

/-- `R₁⁺` into `R₂⁺`. -/
theorem lift12 {w v : Word G₁} (h : Derivable R1plus w v) : Derivable R2plus (upW w) (upW v) :=
  derivable_map upW (fun _ _ r => match r with
    | .fig4 a => Derivable.of (R2plus.fig4 (up0 a))
    | .fig7 a => Derivable.of (R2plus.fig7 (up7 a))
    | .rK a => Derivable.of (R2plus.rK (upK a))) h

end QCert.ToffoliHadamardRS
