/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (148b) on three wires

The paper does not derive (148) on three wires: Corollary D.4 takes it from
Lemma D.3, completeness on three qubits.  Here it is derived from the
equations of D.2 and completeness on two wires (`IH 3`), in the labelling
where the doubly controlled `ZX` of D.2 sits natively (target `0`,
controls `1`, `2`), and then relabelled (`WS.rel_entry`, the wires
`0, 1, 2` carried to `1, 2, 0`):

`ΛX(0|1●) · CZ(2●,0●) · ΛX(0|1●)` = `CZ(2●,1●) · CZ(2●,0●)` (`t148r`).

With `W` the `ZX` of (117), `V` its inverse, `R = ΛZX(0|1●)`:
`ΛX(0|1●) = R · CZ(1, 0)` (Lemma 5.1), so the left side is
`R · CZ₂₀ · R⁻¹` by (148a); `R = W° W` by (136) and `R⁻¹ = V V°` by (138),
`W° = X₂ W X₂`; `W CZ₂₀ V = CZ₂₀ CZ₂₁` by (128), (15) (`W W = CZ₂₁`) and
(117); `CZ₂₁` passes `V°` by (143); and `W°` passes `CZ₂₀`: `X₂ CZ₂₀ X₂ =
CZ₂₀ Z₀` (Lemma 5.1), and `W` passes `CZ₂₀ Z₀` by (128), (123), (15).
`CZ₂₁` and `CZ₂₀` commute by (12) and (f3) (`t_czc`).  Every step was
checked numerically first (scratch `d148.py`, `d148w.py`, the models
`gen/sec8/eng3.py` and `gen/sec8/w4/tok.py`).
-/
import QCert.RealCliffordCH.Sec8.D.W3.Base
import QCert.RealCliffordCH.Sec8.D.W3.Sym

namespace QCert.RealCliffordCH.Sec8.D

open Circuit Eng

/-- `CZ(1, 2)` and `CZ(0, 2)` commute, by (12) and (f3). -/
theorem t_czc (ih : IH 3) :
    Derivable (theory 3) (circW 3 [L.C 1, L.S 0, L.C 1, L.S 0])
      (circW 3 [L.S 0, L.C 1, L.S 0, L.C 1]) :=
  Eng.check_sound ih (T := [([L.C 1, L.C 0], [L.C 0, L.C 1]),
      ([L.C 1, L.S 0, L.S 1], [L.S 0, L.S 1, L.C 0])])
    (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact t_e12
    · exact t_f3)
    (w := [L.C 1, L.S 0, L.C 1, L.S 0]) (v := [L.S 0, L.C 1, L.S 0, L.C 1])
    (ss := [.sem 0 0 [L.S 0, L.S 0], .sem 6 0 [L.S 1, L.S 1], .rw 4 1 false, .sem 3 2 [],
      .sem 2 2 [L.S 1, L.C 1], .rw 3 0 false, .rw 1 1 true, .sem 4 2 [L.S 1, L.C 1], .sem 3 2 []])
    (by decide +kernel)

set_option maxRecDepth 20000 in
/-- (148b) in the labelling of D.2: `ΛX(0|1●) · CZ(2●,0●) · ΛX(0|1●)` =
`CZ(2●,1●) · CZ(2●,0●)`. -/
theorem t148r (ih : IH 3) :
    Derivable (theory 3)
      (circW 3 [L.H 0, L.C 0, L.H 0, L.S 0, L.C 1, L.S 0, L.H 0, L.C 0, L.H 0])
      (circW 3 [L.C 1, L.S 0, L.C 1, L.S 0]) :=
  Eng.check_sound ih (T := [
      ([L.C 0, L.S 0, L.C 1, L.S 0], [L.S 0, L.C 1, L.S 0, L.C 0]),
      ([L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0],
        [L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.C 1, L.S 0, L.C 1, L.S 0]),
      ([L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.S 0, L.C 1, L.S 0, L.K 0,
        L.S 0, L.C 1, L.S 0, L.K 0], []),
      ([L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.K 0, L.S 0, L.C 1, L.S 0,
        L.K 0, L.S 0, L.C 1, L.S 0], []),
      ([L.H 2, L.Z 2, L.H 2, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.H 2,
        L.Z 2, L.H 2, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0],
        [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0]),
      ([L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.H 2, L.Z 2, L.H 2, L.S 0,
        L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.H 2, L.Z 2, L.H 2],
        [L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0]),
      ([L.C 1, L.H 2, L.Z 2, L.H 2, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0,
        L.H 2, L.Z 2, L.H 2],
        [L.H 2, L.Z 2, L.H 2, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.H 2,
        L.Z 2, L.H 2, L.C 1]),
      ([L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0,
        L.K 0, L.S 0, L.C 1, L.S 0], [L.C 1]),
      ([L.Z 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0],
        [L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.Z 0]),
      ([L.C 1, L.S 0, L.C 1, L.S 0], [L.S 0, L.C 1, L.S 0, L.C 1])])
    (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact d148a ih
    · exact d128 ih
    · exact d117 ih
    · exact d118 ih
    · exact d136 ih
    · exact d138 ih
    · exact d143 ih
    · exact t_e15
    · exact d123 ih
    · exact t_czc ih)
    (w := [L.H 0, L.C 0, L.H 0, L.S 0, L.C 1, L.S 0, L.H 0, L.C 0, L.H 0])
    (v := [L.C 1, L.S 0, L.C 1, L.S 0])
    (ss := [.sem 0 3 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0, L.C 0],
      .sem 12 3 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0, L.C 0], .rw 8 0 false,
      .sem 11 10 [L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0], .rw 0 4 true,
      .rw 25 5 true, .sem 22 0 [L.C 1, L.C 1], .rw 23 9 false, .rw 14 1 true, .rw 25 7 true,
      .rw 17 7 false, .rw 18 2 false, .rw 17 6 false, .sw 13, .sw 12, .sw 11, .sw 16, .sw 17,
      .sw 18, .sem 12 7 [L.C 1, L.Z 1], .sem 13 2 [L.S 0, L.Z 0], .rw 14 3 true,
      .sem 11 0 [L.C 1, L.C 1], .rw 12 9 false, .rw 3 1 true, .rw 14 7 true, .rw 6 7 false,
      .rw 7 2 false, .rw 15 8 false, .rw 7 7 false, .sem 6 2 [], .sw 2, .sw 1, .sw 0, .sw 6,
      .sw 7, .sw 8, .sw 5, .sw 6, .sw 7, .sem 1 7 [L.C 1, L.Z 1], .sem 2 3 [L.S 0],
      .rw 0 9 true])
    (by decide +kernel)

namespace W3B

private theorem havailNone : ∀ (K : Kind) (k : ℕ), false = true → Net.CanonSym K k := by
  intro K k h
  cases h

/-- `t148r` carried to the wires `1, 2, 0` (`WS.rel_entry`). -/
theorem t148p (ih : IH 3) :
    Derivable (theory 3)
      (WE.wcT 3 [.p 1 [L.H 0] [1], .p 2 [L.C 0] [1, 2], .p 1 [L.H 0] [1], .p 2 [L.S 0] [1, 2],
        .p 2 [L.C 0] [2, 0], .p 2 [L.S 0] [1, 2], .p 1 [L.H 0] [1], .p 2 [L.C 0] [1, 2],
        .p 1 [L.H 0] [1]])
      (WE.wcT 3 [.p 2 [L.C 0] [2, 0], .p 2 [L.S 0] [1, 2], .p 2 [L.C 0] [2, 0],
        .p 2 [L.S 0] [1, 2]]) := by
  have h := t148r ih
  rw [WE.circW_eq_wcT, WE.circW_eq_wcT] at h
  exact WS.rel_entry (avail := fun _ _ => false) havailNone [1, 0] (by decide +kernel) h

/-- (148b) on three wires. -/
theorem e148b (ih : IH 3) : Derivable (theory 3) l148b r148b := by
  unfold l148b r148b
  rw [WE.circW_eq_wcT, WE.circW_eq_wcT]
  exact WE.check_sound ih (WE.AllD.cons (t148p ih) (WE.AllD.nil 3))
    (w := [.s (L.S 0), .s (L.C 1), .s (L.S 0), .s (L.C 0)])
    (v := [.s (L.H 1), .s (L.C 1), .s (L.H 1), .s (L.C 0), .s (L.H 1), .s (L.C 1), .s (L.H 1)])
    (ss := [.sem 1 1 [.p 2 [L.C 0] [1, 2]] 0,
      .swp 0 0 (.p 2 [L.C 0] [1, 2]) (.p 2 [L.C 0] [0, 2]) false,
      .sem 0 1 [.p 2 [L.C 0] [2, 0]] 1, .sem 1 1 [.p 2 [L.C 0] [1, 0]] 2,
      .swp 1 1 (.p 2 [L.C 0] [2, 0]) (.p 2 [L.C 0] [1, 0]) true,
      .sem 1 1 [.p 2 [L.S 0] [1, 2]] 0, .sem 3 1 [.p 2 [L.S 0] [1, 2]] 0, .rw 0 0 true,
      .sem 0 1 [.s (L.H 1)] 0, .sem 1 1 [.s (L.C 1)] 0, .sem 2 1 [.s (L.H 1)] 0,
      .sem 3 1 [.s (L.S 1)] 0, .sem 5 1 [.s (L.S 1)] 0,
      .swp 3 1 (.p 2 [L.C 0] [2, 0]) (.p 2 [L.C 0] [1, 0]) false, .sem 3 1 [.s (L.C 0)] 2,
      .sem 4 1 [.s (L.H 1)] 0, .sem 5 1 [.s (L.C 1)] 0, .sem 6 1 [.s (L.H 1)] 0])
    (by decide +kernel)

end W3B

end QCert.RealCliffordCH.Sec8.D
