/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Five-wire semantic steps from six wires on

A derivation between two words of local letters on the five local wires
`0, …, 4` holds on every width from six on as soon as the two words have the
same semantics on five wires (decided by `SE.lcheck 5`): completeness on five
wires (the induction hypothesis, `5 < N`) gives the derivation on five wires
and `Loc.der_loc` carries it up.  This is the step the engine cannot take
inside a run, its windows having to avoid one of the five local wires.

Status: not yet built at the time of writing (the build queue was full); nothing imports it.
-/
import QCert.RealCliffordCH.Sec8.D.N13.Loc

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

theorem circL_loc (K : ℕ) (x : Lt) : SE.circL K true x = x.circ K K := by
  cases x <;> rfl

theorem circWL_loc (K : ℕ) (l : List Lt) : SE.circWL K true l = wc K K l := by
  unfold SE.circWL wc
  congr 1
  exact List.map_congr_left (fun x _ => circL_loc K x)

/-- Two local words with the same semantics on five wires are equal on
every width `N ≥ 6`. -/
theorem loc5 {L R : List Lt} (hL : L.all (isLoc 5) = true) (hR : R.all (isLoc 5) = true)
    (h : SE.lcheck 5 true L R = true) {N : ℕ} (hN : 6 ≤ N) (ih : IH N) :
    Derivable (theory N) (wc 5 N L) (wc 5 N R) := by
  have hL' : ∀ x ∈ L, x.ok 5 = true := fun x hx => isLoc_ok (List.all_eq_true.1 hL x hx)
  have hR' : ∀ x ∈ R, x.ok 5 = true := fun x hx => isLoc_ok (List.all_eq_true.1 hR x hx)
  have he := SE.lcheck_sound true hL' hR' h
  rw [circWL_loc, circWL_loc] at he
  have d5 : Derivable (theory 5) (wc 5 5 L) (wc 5 5 R) := ih 5 (by omega) _ _ (sem_of_eval he)
  exact der_loc hL hR d5 N (by omega)

end QCert.RealCliffordCH.Sec8.D.N13
