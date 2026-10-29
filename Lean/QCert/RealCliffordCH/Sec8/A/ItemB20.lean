/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): Clément's relation (20) from Equation (45)

Clément's relation (20), Figure 7's (d3*),
`H[a,b] H[a,c] H[b,d] H[a,b] (-1)[a] (-1)[b] H[a,c] H[b,d] ≈
 H[a,c] H[b,d] H[a,b] (-1)[a] (-1)[b] H[a,c] H[b,d] H[a,b]`,
is in the congruence of Claim B whenever its generators have increasing
indices (`gb20`).  Its frame image is Equation (45) at the indices
`0, 1, 3, 2, 7, 6 ↦ a, b, c, d, e, f` (`e45_ren`, the frame pair `7, 6`
becoming the tags `e, f`), once the two `H` of each pair are merged
(`contract`), the two signs too, and `(-1)_[a](-1)_[b]` is moved past
`H_[a,b]` by (d1).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBRen8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- Equation (45). -/
theorem e45 : D8 n [Hh n 0 1 7 6, Hh n 0 3 1 2, Hh n 0 1 7 6, Zz n 0 1, Hh n 0 3 1 2]
    [Hh n 0 3 1 2, Zz n 0 1, Hh n 0 1 7 6, Hh n 0 3 1 2, Hh n 0 1 7 6] :=
  DR.ax (Fig8.r45 (n := n))

/-- The two sides of (45) as lists of `CL` letters. -/
def L45c : List CL := [CL.hh 0 1 7 6, CL.hh 0 3 1 2, CL.hh 0 1 7 6, CL.zz 0 1, CL.hh 0 3 1 2]
/-- The right-hand side. -/
def R45c : List CL := [CL.hh 0 3 1 2, CL.zz 0 1, CL.hh 0 1 7 6, CL.hh 0 3 1 2, CL.hh 0 1 7 6]

/-- The plan sending `0, 1, 3, 2, 7, 6` to `a, b, c, d, e, f`. -/
def plan45 (a b c d e f : ℕ) : List (ℕ × ℕ) := [(a, 0), (b, 1), (c, 3), (d, 2), (e, 7), (f, 6)]

/-- Equation (45) at the indices `0, 1, 3, 2, 7, 6 ↦ a, b, c, d, e, f`. -/
theorem e45_ren (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {a b c d e f : ℕ} (ha : a < 2 ^ n)
    (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (he : e < 2 ^ n) (hf : f < 2 ^ n)
    (hnd : [a, b, c, d, e, f].Nodup) :
    D8 n [Hh n a b e f, Hh n a c b d, Hh n a b e f, Zz n a b, Hh n a c b d]
      [Hh n a c b d, Zz n a b, Hh n a b e f, Hh n a c b d, Hh n a b e f] := by
  set p := plan45 a b c d e f
  have hok : PlanOk p := ⟨by simpa [p, plan45] using hnd, by simp [p, plan45]⟩
  have hbdp : PlanBd (2 ^ n) p := by
    intro q hq
    simp only [p, plan45, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by assumption, by omega⟩
  have hs : 4 < 2 ^ n := by omega
  obtain ⟨b1, b2⟩ := telNL_bd hs p hbdp
  obtain ⟨r1, r2⟩ := telNL_pr 4 p
  have hinv := fun v (_ : v < 2 ^ n) => telNL_inv 4 p v
  have rho' : ∀ x k, (x, k) ∈ p → permL (telNL 4 p) k = x := fun x k hm => by
    rw [permL_telNL]; exact rho_mem p hok x k hm
  have neg0 : ∀ v, v ≠ 4 → negL (telNL 4 p) v = false := fun v hv => negL_telNL 4 p v hv
  have ok : ∀ x ∈ L45c ++ R45c, x.Ok n (telNL 4 p) := by
    intro x hx
    simp only [L45c, R45c, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
      simp only [CL.Ok] <;>
      first
      | exact ⟨by omega, by omega⟩
      | exact ⟨by omega, by omega, by omega, by omega, by decide, by simp [neg0], by simp [neg0]⟩
  have k := ren_eq h8 hE b1 b2 r1 r2 hinv (L := L45c) (R := R45c)
    (fun x hx => ok x (List.mem_append_left _ hx)) (fun x hx => ok x (List.mem_append_right _ hx))
    e45
  have p0 := rho' a 0 (by simp [p, plan45])
  have p1 := rho' b 1 (by simp [p, plan45])
  have p3 := rho' c 3 (by simp [p, plan45])
  have p2 := rho' d 2 (by simp [p, plan45])
  have p7 := rho' e 7 (by simp [p, plan45])
  have p6 := rho' f 6 (by simp [p, plan45])
  simpa only [L45c, R45c, List.map, CL.ren, CL.toPG, p0, p1, p2, p3, p6, p7] using k

/-- Clément's relation (20) at increasing pairs of indices is in `GB`. -/
theorem gb20 (hn : 3 ≤ n) {a b c d : Fin (2 ^ n)} (hab : a < b) (hac : a < c) (hbd : b < d)
    (hbc : b ≠ c) (hcd : c ≠ d) :
    GB n (FreeMonoid.ofList [HadamardPi.Gen.H a b hab, HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd, HadamardPi.Gen.H a b hab, HadamardPi.Gen.Z a,
        HadamardPi.Gen.Z b, HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd])
      (FreeMonoid.ofList [HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd, HadamardPi.Gen.H a b hab, HadamardPi.Gen.Z a, HadamardPi.Gen.Z b,
        HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd, HadamardPi.Gen.H a b hab]) := by
  have h8 := h8_of hn
  have hE := e65 n hn
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ)} Finset.card_le_four ?_ ?_ ?_ ?_
  · refine InS.ofList fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact InS.ofZ (by simp) | exact InS.ofH (by simp) (by simp)
  · refine InS.ofList fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact InS.ofZ (by simp) | exact InS.ofH (by simp) (by simp)
  · simp [parL, gbits, pxor]
  · intro e f g T he hf hg
    have Tg := T.tags
    have va : Av n e f g a := avS (by simp) he hf hg
    have vb : Av n e f g b := avS (by simp) he hf hg
    have vc : Av n e f g c := avS (by simp) he hf hg
    have vd : Av n e f g d := avS (by simp) he hf hg
    have nab := flt hab; have nac := flt hac; have nbd := flt hbd
    have nbc := fne hbc; have ncd := fne hcd
    have nad : (a : ℕ) ≠ d := Nat.ne_of_lt (lt_trans hab hbd)
    have cac : D8 n [Hh n a c e f, Hh n b d e f] [Hh n a c b d] :=
      contract h8 hE va.1 vc.1 vb.1 vd.1 T.he T.hf nac
        ⟨nbd, vb.2.1, vb.2.2.1, vd.2.1, vd.2.2.1, T.hef⟩
    have zab : D8 n [Zz n a g, Zz n b g] [Zz n a b] := by
      have := A5v (n := n) (m := 3) (by omega) [a, b, g] rfl (by simp [nab, va.2.2.2, vb.2.2.2])
        (by simp [va.1, vb.1, T.hg]) [NL.zz 0 2, NL.zz 1 2] [NL.zz 0 1] (by decide)
      simpa [rv, NL.ren, NL.toPG] using this
    have d1 := img_d1 h8 Tg hE va vb nab
    have hnd : [(a : ℕ), b, c, d, e, f].Nodup := by
      simp [nab, nac, nad, nbc, nbd, ncd, va.2.1, va.2.2.1, vb.2.1, vb.2.2.1, vc.2.1, vc.2.2.1,
        vd.2.1, vd.2.2.1, T.hef]
    have k := e45_ren h8 hE va.1 vb.1 vc.1 vd.1 T.he T.hf hnd
    have hL : D8 n [Hh n a b e f, Hh n a c e f, Hh n b d e f, Hh n a b e f, Zz n a g, Zz n b g,
        Hh n a c e f, Hh n b d e f]
        [Hh n a b e f, Hh n a c b d, Hh n a b e f, Zz n a b, Hh n a c b d] :=
      DR.append (DR.refl [Hh n a b e f]) (DR.append cac (DR.append (DR.refl [Hh n a b e f])
        (DR.append zab cac)))
    have hR : D8 n [Hh n a c e f, Hh n b d e f, Hh n a b e f, Zz n a g, Zz n b g, Hh n a c e f,
        Hh n b d e f, Hh n a b e f]
        [Hh n a c b d, Zz n a b, Hh n a b e f, Hh n a c b d, Hh n a b e f] :=
      DR.append cac (((DR.append d1.symm (DR.refl [Hh n a c e f, Hh n b d e f, Hh n a b e f])).trans
        (DR.append zab (DR.append (DR.refl [Hh n a b e f]) (DR.append cac
          (DR.refl [Hh n a b e f]))))))
    simp only [phiW, FreeMonoid.toList_ofList, List.flatMap_cons, List.flatMap_nil, phiG,
      List.singleton_append, List.cons_append, List.nil_append, List.append_nil]
    exact hL.trans (k.trans hR.symm)

end QCert.RealCliffordCH.Sec8
