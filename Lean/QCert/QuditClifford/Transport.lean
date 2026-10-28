/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Moving local facts onto the bottom wires

The local facts are proved on one, two and three wires and used on the
bottom wires of every wider circuit.  This file relates the objects of the
stabiliser chain on `n + k` wires to those on `k` wires placed by
`padh n k`: the generators (`S0h`, `CZh`), the subgroups (`J`, `Kst`), the
sections of vectors supported on the bottom wires (`s₁h`, `cP`), and the
action (linearity, `J` fixes `Z` on wire 0).
-/
import QCert.QuditClifford.Width1

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### Padding twice -/

theorem pad_pad1 (a b : ℕ) (w : Circ 1) :
    Circuit.pad a (Circuit.pad b w) = Circuit.pad (a + b) w := eq_of_heq (pad_pad_heq a b w)

theorem pad_pad2 (a b : ℕ) (w : Circ 2) :
    Circuit.pad a (Circuit.pad b w) = Circuit.pad (a + b) w := eq_of_heq (pad_pad_heq a b w)

theorem pad_pad3 (a b : ℕ) (w : Circ 3) :
    Circuit.pad a (Circuit.pad b w) = Circuit.pad (a + b) w := eq_of_heq (pad_pad_heq a b w)

theorem pad_zero2 (w : Circ 2) : Circuit.pad 0 w = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of y w ih =>
    rw [map_mul, ih]
    congr 1
    rcases y with c | c | c | _ | y
    · rfl
    · rfl
    · rfl
    · rcases y with c | c | _ | _ | y
      · rfl
      · rfl
      · rcases y with c | _ | _ | _ | _; rfl

theorem padh_ιh (n k : ℕ) (x : Gh p g k) : padh n (k + 1) (ιh k x) = ιh (n + k) (padh n k x) := by
  obtain ⟨w, rfl⟩ := qh_surjective k x
  rw [ιh_qh, padh_qh, padh_qh, ιh_qh, pad_shift]; rfl

theorem padh_padh1 (a b : ℕ) (x : Gh p g 1) : padh a (b + 1) (padh b 1 x) = padh (a + b) 1 x := by
  obtain ⟨w, rfl⟩ := qh_surjective 1 x
  rw [padh_qh, padh_qh, padh_qh, pad_pad1]; rfl

theorem padh_padh2 (a b : ℕ) (x : Gh p g 2) : padh a (b + 2) (padh b 2 x) = padh (a + b) 2 x := by
  obtain ⟨w, rfl⟩ := qh_surjective 2 x
  rw [padh_qh, padh_qh, padh_qh, pad_pad2]; rfl

theorem padh_zero1 (x : Gh p g 1) : padh 0 1 x = x := by
  obtain ⟨w, rfl⟩ := qh_surjective 1 x
  rw [padh_qh, pad_zero_one]

theorem padh_zero2 (x : Gh p g 2) : padh 0 2 x = x := by
  obtain ⟨w, rfl⟩ := qh_surjective 2 x
  rw [padh_qh, pad_zero2]

/-! ### The generators placed -/

theorem padh_S0h (m : ℕ) : padh m 1 (S0h p g 0) = S0h p g m := rfl

theorem padh_S0h1 (m : ℕ) : padh m 2 (S0h p g 1) = S0h p g (m + 1) := rfl

theorem padh_CZh (m : ℕ) : padh m 2 (CZh p g 0) = CZh p g m := rfl

theorem padh_CZh1 (m : ℕ) : padh m 3 (CZh p g 1) = CZh p g (m + 1) := rfl

theorem ιh_S0h (m : ℕ) : ιh (m + 1) (S0h p g m) = padh m 2 (ιh 1 (S0h p g 0)) := rfl

theorem ιh_CZh (m : ℕ) : ιh (m + 2) (CZh p g m) = padh m 3 (ιh 2 (CZh p g 0)) := rfl

/-! ### The subgroups placed -/

theorem J_one_mem_of {m : ℕ} {x : Gh p g (m + 1)} (hx : x ∈ Jgen p g m) : x ∈ J p g m :=
  Subgroup.subset_closure hx

theorem ιh_mem_J {m : ℕ} (z : Gh p g m) : ιh m z ∈ J p g m := by
  apply J_one_mem_of
  cases m with
  | zero => exact Set.mem_union_left _ ⟨z, rfl⟩
  | succ m => exact Set.mem_union_left _ ⟨z, rfl⟩

theorem S0h_mem_J (m : ℕ) : S0h p g m ∈ J p g m := by
  apply J_one_mem_of
  cases m with
  | zero => exact Set.mem_union_right _ rfl
  | succ m => exact Set.mem_union_right _ (Or.inl rfl)

theorem CZh_mem_J (m : ℕ) : CZh p g m ∈ J p g (m + 1) :=
  J_one_mem_of (Set.mem_union_right _ (Or.inr rfl))

theorem padh1_J {m : ℕ} {x : Gh p g 1} (hx : x ∈ J p g 0) : padh (m + 1) 1 x ∈ J p g (m + 1) := by
  refine (Subgroup.closure_le ((J p g (m + 1)).comap (padh (m + 1) 1))).2 ?_ hx
  rintro _ (⟨z, rfl⟩ | h)
  · rw [Gh_zero_trivial z, map_one, SetLike.mem_coe, Subgroup.mem_comap, map_one]
    exact Subgroup.one_mem _
  · rw [Set.mem_singleton_iff] at h; subst h
    exact S0h_mem_J (m + 1)

theorem padh2_J {m : ℕ} {x : Gh p g 2} (hx : x ∈ J p g 1) : padh m 2 x ∈ J p g (m + 1) := by
  refine (Subgroup.closure_le ((J p g (m + 1)).comap (padh m 2))).2 ?_ hx
  rintro _ (⟨z, rfl⟩ | h | h)
  · rw [SetLike.mem_coe, Subgroup.mem_comap, padh_ιh]
    exact ιh_mem_J _
  · subst h
    exact S0h_mem_J (m + 1)
  · rw [Set.mem_singleton_iff] at h; subst h
    exact CZh_mem_J m

theorem padh3_J {m : ℕ} {x : Gh p g 3} (hx : x ∈ J p g 2) : padh m 3 x ∈ J p g (m + 2) := by
  refine (Subgroup.closure_le ((J p g (m + 2)).comap (padh m 3))).2 ?_ hx
  rintro _ (⟨z, rfl⟩ | h | h)
  · rw [SetLike.mem_coe, Subgroup.mem_comap, padh_ιh]
    exact ιh_mem_J _
  · subst h
    exact S0h_mem_J (m + 2)
  · rw [Set.mem_singleton_iff] at h; subst h
    exact CZh_mem_J (m + 1)

theorem padh_Kst {n k : ℕ} {x : Gh p g (k + 1)} (hx : x ∈ Kst p g k) :
    padh n (k + 1) x ∈ Kst p g (n + k) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨padh n k z, (padh_ιh n k z).symm⟩

/-! ### The action is linear -/

theorem σGen_add : {n : ℕ} → (x : Gen Gate n) → (u v : V p n) →
    σGen p x (u + v) = σGen p x u + σGen p x v
  | _, .gate0 _, _, _ => rfl
  | _, .gate1 c, u, v => by
    funext i
    cases c <;> simp only [σGen, act1, Function.update_apply, Pi.add_apply] <;> split_ifs <;>
      simp <;> ring
  | _, .gate2 .CZ, u, v => by
    funext i
    simp only [σGen, Function.update_apply, Pi.add_apply]
    split_ifs <;> simp <;> ring
  | _, .gate3 c, _, _ => nomatch c
  | _, .up x, u, v => by
    funext i
    simp only [σGen]
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [Fin.cons_succ, Pi.add_apply]
      rw [show Fin.tail (u + v) = Fin.tail u + Fin.tail v from rfl, σGen_add x]
      rfl

theorem σGen_smul : {n : ℕ} → (x : Gen Gate n) → (c : ZMod p) → (u : V p n) →
    σGen p x (c • u) = c • σGen p x u
  | _, .gate0 _, _, _ => rfl
  | _, .gate1 a, c, u => by
    funext i
    cases a <;> simp only [σGen, act1, Function.update_apply, Pi.smul_apply] <;> split_ifs <;>
      simp <;> ring
  | _, .gate2 .CZ, c, u => by
    funext i
    simp only [σGen, Function.update_apply, Pi.smul_apply]
    split_ifs <;> simp <;> ring
  | _, .gate3 a, _, _ => nomatch a
  | _, .up x, c, u => by
    funext i
    simp only [σGen]
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [Fin.cons_succ, Pi.smul_apply]
      rw [show Fin.tail (c • u) = c • Fin.tail u from rfl, σGen_smul x]
      rfl

theorem σh_add {n : ℕ} (x : Gh p g n) (u v : V p n) : σh n x (u + v) = σh n x u + σh n x v := by
  refine Gh.induction_on (P := fun x => ∀ u v, σh n x (u + v) = σh n x u + σh n x v) x
    (fun _ _ => rfl) ?_ u v
  intro y x hx u v
  simp only [map_mul, Function.End.mul_def, Function.comp_apply, σh_qh, σC_of, hx, σGen_add]

theorem σh_smul {n : ℕ} (x : Gh p g n) (c : ZMod p) (u : V p n) : σh n x (c • u) = c • σh n x u := by
  refine Gh.induction_on (P := fun x => ∀ u, σh n x (c • u) = c • σh n x u) x (fun _ => rfl) ?_ u
  intro y x hx u
  simp only [map_mul, Function.End.mul_def, Function.comp_apply, σh_qh, σC_of, hx, σGen_smul]

/-! ### `J` fixes `Z` on wire 0 -/

theorem J_fix_eZ {m : ℕ} {h : Gh p g (m + 1)} (hh : h ∈ J p g m) : σh (m + 1) h (eZ p m) = eZ p m := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    have hS : σh (m + 1) (S0h p g m) (eZ p m) = eZ p m := by
      funext i
      simp only [S0h, σh_qh, σC_of, σGen, act1, Function.update_apply]
      split_ifs with h
      · subst h; simp [eZ]
      · rfl
    cases m with
    | zero =>
      rcases hx with ⟨z, rfl⟩ | hx
      · rw [Gh_zero_trivial z, map_one, map_one]; rfl
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hS
    | succ m =>
      rcases hx with ⟨z, rfl⟩ | hx | hx
      · rw [σh_ιh, show Fin.tail (eZ p (m + 1)) = 0 from rfl, σh_zero]; rfl
      · subst hx; exact hS
      · rw [Set.mem_singleton_iff] at hx; subst hx
        funext i
        simp only [CZh, σh_qh, σC_of, σGen, Function.update_apply]
        split_ifs with h1 h0 <;> simp_all [eZ]
  | one => rfl
  | mul x y _ _ hx hy => rw [map_mul, Function.End.mul_def, Function.comp_apply, hy, hx]
  | inv x _ hx => rw [← hx, σh_inv_apply, hx]

/-! ### The sections of vectors supported on the bottom wires -/

variable (p g) in
/-- The box `B_u` (inverse) as a class on two wires. -/
noncomputable def bh (u : ZMod p × ZMod p) : Gh p g 2 := qh p g 2 (bcirc p u)

theorem s₁h_succ (m : ℕ) (u : V p (m + 2)) (ht : Fin.tail u ≠ 0) :
    s₁h p g (m + 1) u = ιh (m + 1) (s₁h p g m (Fin.tail u)) * padh m 2 (bh p g (u 0)) := by
  simp only [s₁h, s₁circ, if_neg ht, map_mul]; rfl

theorem s₁h_tail0 : (m : ℕ) → (u : V p (m + 1)) → Fin.tail u = 0 →
    s₁h p g m u = padh m 1 (qh p g 1 (Acirc p (u 0)))
  | 0, u, _ => (padh_zero1 _).symm
  | m + 1, u, ht => by simp only [s₁h, s₁circ, if_pos ht]; rfl

theorem s₁h_one (u : V p 2) (ht : Fin.tail u ≠ 0) :
    s₁h p g 1 u = ιh 1 (qh p g 1 (Acirc p (u 1))) * bh p g (u 0) := by
  rw [s₁h_succ 0 u ht, padh_zero2]; rfl

omit hp in
theorem tail_low2 {m : ℕ} (u : V p (m + 2)) : Fin.tail (low p (n := m) (k := 2) u) = fun _ => u 1 := by
  funext i; rw [Subsingleton.elim i 0]; rfl

/-- A vector supported on wires 0, 1: its section is placed from two wires. -/
theorem s₁h_two (m : ℕ) (u : V p (m + 2)) (ht : Fin.tail (Fin.tail u) = 0) :
    s₁h p g (m + 1) u = padh m 2 (s₁h p g 1 (low p (n := m) (k := 2) u)) := by
  by_cases h1 : Fin.tail u = 0
  · have h1' : Fin.tail (low p (n := m) (k := 2) u) = 0 := by
      rw [tail_low2]; funext i; exact congrFun h1 0
    rw [s₁h_tail0 (m + 1) u h1, s₁h_tail0 1 _ h1', padh_padh1]; rfl
  · have h1' : Fin.tail (low p (n := m) (k := 2) u) ≠ 0 := by
      rw [tail_low2]; intro h; apply h1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact congrFun h 0
      · exact congrFun ht i
    rw [s₁h_succ m u h1, s₁h_tail0 m _ ht, s₁h_one _ h1', map_mul]
    erw [padh_ιh m 1]
    rfl

theorem padh_ιh_two (m : ℕ) (x : Gh p g 2) : padh m 3 (ιh 2 x) = ιh (m + 2) (padh m 2 x) :=
  padh_ιh m 2 x

theorem padh_padh_one_two (m : ℕ) (x : Gh p g 2) : padh m 3 (padh 1 2 x) = padh (m + 1) 2 x :=
  padh_padh2 m 1 x

/-- A vector with a nonzero component above wire 1: its section is the
section of that part moved up two wires, after a placed three-wire section. -/
theorem s₁h_three (m : ℕ) (u : V p (m + 3)) (ht : Fin.tail (Fin.tail u) ≠ 0) :
    s₁h p g (m + 2) u = ιh (m + 2) (ιh (m + 1) (s₁h p g m (Fin.tail (Fin.tail u)))) *
      padh m 3 (s₁h p g 2 (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0)))) := by
  have h1 : Fin.tail u ≠ 0 := fun h => ht (by rw [h]; rfl)
  have hz : Fin.tail (Fin.cons (u 1) (eZ p 0) : V p 2) ≠ 0 := by
    rw [Fin.tail_cons]; exact eZ_ne_zero 0
  have hz' : Fin.tail (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0)) : V p 3) ≠ 0 := by
    rw [Fin.tail_cons]; intro h; exact hz (by rw [h]; rfl)
  have e1 : s₁h p g 1 (Fin.cons (u 1) (eZ p 0)) = bh p g (u 1) := by
    rw [s₁h_one _ hz]
    have hA : qh p g 1 (Acirc p ((Fin.cons (u 1) (eZ p 0) : V p 2) 1)) = 1 := by
      show qh p g 1 (Acirc p (0, 1)) = 1
      rw [Acirc_eq]; simp [Mq_one]
    rw [hA, map_one, one_mul, Fin.cons_zero]
  have e2 : s₁h p g 2 (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0))) =
      ιh 2 (bh p g (u 1)) * padh 1 2 (bh p g (u 0)) := by
    rw [s₁h_succ 1 _ hz', Fin.tail_cons, e1]; rfl
  rw [s₁h_succ (m + 1) u h1, s₁h_succ m _ ht, e2]
  simp only [map_mul]
  rw [padh_ιh_two, padh_padh_one_two, mul_assoc]
  rfl

theorem σGen_CZ (n : ℕ) (u : V p (n + 2)) :
    σGen p (Gen.gate2 (n := n) Gate.CZ) u =
      Fin.cons ((u 0).1, (u 0).2 + (u 1).1) (Fin.cons ((u 1).1, (u 1).2 + (u 0).1)
        (Fin.tail (Fin.tail u))) := by
  funext i
  simp only [σGen, Function.update_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp
  · simp
  · have a1 : (i.succ.succ : Fin (n + 2)) ≠ 1 := fun h => by
      have := congrArg Fin.val h; simp at this
    rw [if_neg a1, if_neg (Fin.succ_ne_zero _)]
    rfl

end QCert.QuditClifford
