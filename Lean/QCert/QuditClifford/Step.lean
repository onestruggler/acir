/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The induction step

From the stabiliser of `Z` on `m + 1` wires (`ZStab m`) and the local facts
on two and three wires (`LF2`, `LF3`), the two stages on `m + 2` wires:

* stage 1 (`zstab_succ`): Schreier's lemma for the action on nonzero
  vectors, with the section `s₁h`.  A generator on the wires above wire 0
  is moved through the section by the induction hypothesis and `L2` (the
  stabiliser of `Z` on the wires above conjugates through `B` into `J`);
  `H`, `S` on wire 0 and `CZ` on wires 0, 1 act on the bottom one, two or
  three boxes only, which is `LF2` or `LF3`;
* stage 2 (`xstab_succ`): Schreier's lemma for `J` acting on the vectors
  `X ⊗ …` with `Z`-coefficient `β` on wire 0, with the section `S^β c(P)`.
  The circuits on the wires above conjugate `c(P)` to `c` of the image of
  `P` (`cP_equiv`, from the induction hypothesis and `L1`: the stabiliser
  of `Z` on the wires above commutes with `CZ`), and `CZ` composes with
  `c(P)` as the Heisenberg group law, reduced by that equivariance to `P`
  on wire 1 (`LF2`) or on wires 1, 2 (`LF3`).
-/
import QCert.QuditClifford.Transport

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

variable (p g) in
/-- The local facts on two wires. -/
structure LF2 : Prop where
  bS : ∀ u, (bh p g u)⁻¹ * ιh 1 (S0h p g 0) * bh p g u ∈ J p g 1
  bOne : ∀ (y : Gate 1) u,
    (bh p g (act1 p y u))⁻¹ * qh p g 2 (Circuit.g1 y) * bh p g u ∈ J p g 1
  cz : ∀ u : V p 2, u ≠ 0 →
    (s₁h p g 1 (σGen p (Gen.gate2 (n := 0) Gate.CZ) u))⁻¹ * CZh p g 0 * s₁h p g 1 u ∈ J p g 1
  czS0 : Commute (CZh p g 0) (S0h p g 1)
  heis : ∀ P : V p 1,
    (S0h p g 1 ^ (P 0).1.val * cP p g 0 (P + eZ p 0))⁻¹ * (CZh p g 0 * cP p g 0 P) ∈ Kst p g 1

variable (p g) in
/-- The local facts on three wires. -/
structure LF3 : Prop where
  bCZ : ∀ u, (padh 1 2 (bh p g u))⁻¹ * ιh 2 (CZh p g 0) * padh 1 2 (bh p g u) ∈ J p g 2
  cz : ∀ u0 u1 : ZMod p × ZMod p,
    (s₁h p g 2 (σGen p (Gen.gate2 (n := 1) Gate.CZ) (Fin.cons u0 (Fin.cons u1 (eZ p 0)))))⁻¹ *
      CZh p g 1 * s₁h p g 2 (Fin.cons u0 (Fin.cons u1 (eZ p 0))) ∈ J p g 2
  czcz : Commute (CZh p g 1) (ιh 2 (CZh p g 0))
  heis : ∀ β : ZMod p, (cP p g 1 (Fin.cons (0, β + 1) (eZ p 0)))⁻¹ *
    (CZh p g 1 * cP p g 1 (Fin.cons (0, β) (eZ p 0))) ∈ Kst p g 2

/-! ### Two conjugation lemmas -/

/-- (C8) on two wires. -/
theorem czS1 : Commute (CZh p g 0) (ιh 1 (S0h p g 0)) := by
  have := qh_rule (g := g) 0 Rule.C8
  simp only [seq_def, map_mul, pad_zero2] at this
  exact this

/-- `L1`: the stabiliser of `Z` on the wires above wire 0 commutes with `CZ`. -/
theorem L1 {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) {k : Gh p g (m + 1)} (hk : k ∈ J p g m) :
    Commute (CZh p g m) (ιh (m + 1) k) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    cases m with
    | zero =>
      rcases hx with ⟨z, rfl⟩ | hx
      · rw [Gh_zero_trivial z, map_one, map_one]; exact Commute.one_right _
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact czS1
    | succ m =>
      rcases hx with ⟨z, rfl⟩ | hx | hx
      · rw [← padh_CZh (m + 1)]; exact commute_padh2_ιh2 _ _
      · subst hx
        rw [ιh_S0h, ← padh_CZh]; exact czS1.map _
      · rw [Set.mem_singleton_iff] at hx; subst hx
        rw [ιh_CZh, ← padh_CZh1]; exact (lf3 (Nat.succ_ne_zero m)).czcz.map _
  | one => rw [map_one]; exact Commute.one_right _
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
  | inv x _ hx => rw [map_inv]; exact hx.inv_right

/-- `L2`: the stabiliser of `Z` on the wires above wire 0, conjugated by a box
`B` on wires 0, 1, stays in the stabiliser of `Z` on wire 0. -/
theorem L2 (bS : ∀ u, (bh p g u)⁻¹ * ιh 1 (S0h p g 0) * bh p g u ∈ J p g 1) {m : ℕ}
    (lf3 : m ≠ 0 → LF3 p g) (u : ZMod p × ZMod p) {k : Gh p g (m + 1)}
    (hk : k ∈ J p g m) : (padh m 2 (bh p g u))⁻¹ * ιh (m + 1) k * padh m 2 (bh p g u) ∈ J p g (m + 1) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    cases m with
    | zero =>
      rcases hx with ⟨z, rfl⟩ | hx
      · rw [Gh_zero_trivial z, map_one, map_one, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _
      · rw [Set.mem_singleton_iff] at hx; subst hx
        rw [padh_zero2]; exact bS u
    | succ m =>
      rcases hx with ⟨z, rfl⟩ | hx | hx
      · have hc := commute_padh2_ιh2 (bh p g u) z
        rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
        exact ιh_mem_J _
      · subst hx
        rw [ιh_S0h, ← map_inv, ← map_mul, ← map_mul]; exact padh2_J (bS u)
      · rw [Set.mem_singleton_iff] at hx; subst hx
        rw [ιh_CZh, show padh (m + 1) 2 (bh p g u) = padh m 3 (padh 1 2 (bh p g u)) from
          (padh_padh2 m 1 _).symm, ← map_inv, ← map_mul, ← map_mul]
        exact padh3_J ((lf3 (Nat.succ_ne_zero m)).bCZ u)
  | one => rw [map_one, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : (padh m 2 (bh p g u))⁻¹ * ιh (m + 1) (x * y) * padh m 2 (bh p g u) =
        ((padh m 2 (bh p g u))⁻¹ * ιh (m + 1) x * padh m 2 (bh p g u)) *
          ((padh m 2 (bh p g u))⁻¹ * ιh (m + 1) y * padh m 2 (bh p g u)) := by
      rw [map_mul]; group
    rw [e]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : (padh m 2 (bh p g u))⁻¹ * ιh (m + 1) x⁻¹ * padh m 2 (bh p g u) =
        ((padh m 2 (bh p g u))⁻¹ * ιh (m + 1) x * padh m 2 (bh p g u))⁻¹ := by
      rw [map_inv]; group
    rw [e]; exact Subgroup.inv_mem _ hx

/-! ### Stage 1 -/

omit hp in
theorem tail_update_zero {n : ℕ} (u : V p (n + 1)) (a : ZMod p × ZMod p) :
    Fin.tail (Function.update u 0 a) = Fin.tail u := by
  funext i; simp [Fin.tail, Function.update_apply, Fin.succ_ne_zero]

theorem eq_zero_of_tail {n : ℕ} {u : V p (n + 1)} (h0 : u 0 = 0) (ht : Fin.tail u = 0) : u = 0 := by
  rw [← Fin.cons_self_tail u, h0, ht]; exact funext fun i => Fin.cases rfl (fun _ => rfl) i

theorem low2_ne_zero {m : ℕ} {u : V p (m + 2)} (hu : u ≠ 0) (ht : Fin.tail (Fin.tail u) = 0) :
    low p (n := m) (k := 2) u ≠ 0 := by
  intro h
  apply hu
  refine eq_zero_of_tail (congrFun h 0) (eq_zero_of_tail (congrFun h 1) ht)

theorem low2_σGen_CZ (m : ℕ) (u : V p (m + 2)) :
    low p (n := m) (k := 2) (σGen p (Gen.gate2 (n := m) Gate.CZ) u) =
      σGen p (Gen.gate2 (n := 0) Gate.CZ) (low p (n := m) (k := 2) u) := by
  rw [σGen_CZ, σGen_CZ]
  apply V2_ext p <;> rfl

theorem tail_tail_σGen_CZ (m : ℕ) (u : V p (m + 2)) :
    Fin.tail (Fin.tail (σGen p (Gen.gate2 (n := m) Gate.CZ) u)) = Fin.tail (Fin.tail u) := by
  rw [σGen_CZ]; rfl

theorem step1 (lf2 : LF2 p g) {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) (hZ : ZStab p g m) (y : Gen Gate (m + 2))
    {u : V p (m + 2)} (hu : u ≠ 0) :
    (s₁h p g (m + 1) (σGen p y u))⁻¹ * (qh p g (m + 2) (FreeMonoid.of y) * s₁h p g (m + 1) u) ∈
      J p g (m + 1) := by
  rcases y with c | c | c | c | y
  · rw [qh_gate0, one_mul]
    simp only [σGen, id, inv_mul_cancel]
    exact Subgroup.one_mem _
  · -- a one-qudit gate on wire 0
    have hx : qh p g (m + 2) (FreeMonoid.of (Gen.gate1 c)) = padh (m + 1) 1 (qh p g 1 (Circuit.g1 c)) :=
      rfl
    simp only [σGen]
    by_cases ht : Fin.tail u = 0
    · have h0 : u 0 ≠ 0 := fun h0 => hu (eq_zero_of_tail h0 ht)
      rw [s₁h_tail0 (m + 1) _ (by rw [tail_update_zero]; exact ht), s₁h_tail0 (m + 1) u ht,
        Function.update_self, hx, ← map_inv, ← map_mul, ← map_mul, ← mul_assoc]
      exact padh1_J (lf1 c h0)
    · have hx' : qh p g (m + 2) (FreeMonoid.of (Gen.gate1 c)) = padh m 2 (qh p g 2 (Circuit.g1 c)) :=
        rfl
      rw [s₁h_succ m _ (by rw [tail_update_zero]; exact ht), s₁h_succ m u ht, tail_update_zero,
        Function.update_self]
      have hc := commute_padh_ιh (qh p g 1 (Circuit.g1 c)) (s₁h p g m (Fin.tail u))
      rw [← hx] at hc
      have e : (ιh (m + 1) (s₁h p g m (Fin.tail u)) * padh m 2 (bh p g (act1 p c (u 0))))⁻¹ *
          (qh p g (m + 2) (FreeMonoid.of (Gen.gate1 c)) * (ιh (m + 1) (s₁h p g m (Fin.tail u)) *
            padh m 2 (bh p g (u 0)))) = (padh m 2 (bh p g (act1 p c (u 0))))⁻¹ *
          ((ιh (m + 1) (s₁h p g m (Fin.tail u)))⁻¹ * (qh p g (m + 2) (FreeMonoid.of (Gen.gate1 c)) *
            ιh (m + 1) (s₁h p g m (Fin.tail u)))) * padh m 2 (bh p g (u 0)) := by group
      rw [e, hc.eq, inv_mul_cancel_left, hx', ← map_inv, ← map_mul, ← map_mul]
      exact padh2_J (lf2.bOne c (u 0))
  · -- `CZ` on wires 0, 1
    cases c
    have hx : qh p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)) = CZh p g m := rfl
    rw [hx]
    by_cases ht2 : Fin.tail (Fin.tail u) = 0
    · rw [s₁h_two m u ht2, s₁h_two m _ (by rw [tail_tail_σGen_CZ]; exact ht2), low2_σGen_CZ,
        ← padh_CZh, ← map_inv, ← map_mul, ← map_mul, ← mul_assoc]
      exact padh2_J (lf2.cz _ (low2_ne_zero hu ht2))
    · cases m with
      | zero => exact absurd (funext fun i => Fin.elim0 i) ht2
      | succ m =>
        have ht2' : Fin.tail (Fin.tail (σGen p (Gen.gate2 (n := m + 1) Gate.CZ) u)) ≠ 0 := by
          rw [tail_tail_σGen_CZ]; exact ht2
        rw [s₁h_three m u ht2, s₁h_three m _ ht2', tail_tail_σGen_CZ]
        have hσ : (Fin.cons ((σGen p (Gen.gate2 (n := m + 1) Gate.CZ) u) 0)
            (Fin.cons ((σGen p (Gen.gate2 (n := m + 1) Gate.CZ) u) 1) (eZ p 0)) : V p 3) =
            σGen p (Gen.gate2 (n := 1) Gate.CZ) (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0))) := by
          rw [σGen_CZ, σGen_CZ]; rfl
        rw [hσ]
        set T := ιh (m + 2) (ιh (m + 1) (s₁h p g m (Fin.tail (Fin.tail u))))
        have hc : Commute (CZh p g (m + 1)) T := commute_padh2_ιh2 (n := m + 1) (CZh p g 0) _
        have e : (T * padh m 3 (s₁h p g 2 (σGen p (Gen.gate2 (n := 1) Gate.CZ)
            (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0))))))⁻¹ * (CZh p g (m + 1) *
            (T * padh m 3 (s₁h p g 2 (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0)))))) =
            (padh m 3 (s₁h p g 2 (σGen p (Gen.gate2 (n := 1) Gate.CZ)
              (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0))))))⁻¹ * (T⁻¹ * (CZh p g (m + 1) * T)) *
              padh m 3 (s₁h p g 2 (Fin.cons (u 0) (Fin.cons (u 1) (eZ p 0)))) := by group
        rw [e, hc.eq, inv_mul_cancel_left, ← padh_CZh1, ← map_inv, ← map_mul, ← map_mul]
        exact padh3_J ((lf3 (Nat.succ_ne_zero m)).cz (u 0) (u 1))
  · cases c
  · -- a generator on the wires above wire 0
    rw [qh_up]
    simp only [σGen]
    set x := qh p g (m + 1) (FreeMonoid.of y)
    have hσx : σh (m + 1) x = σGen p y := σC_of p y
    by_cases ht : Fin.tail u = 0
    · have ht' : Fin.tail (Fin.cons (u 0) (σGen p y (Fin.tail u)) : V p (m + 2)) = 0 := by
        rw [Fin.tail_cons, ht, ← hσx, σh_zero]
      rw [s₁h_tail0 (m + 1) _ ht', s₁h_tail0 (m + 1) u ht, Fin.cons_zero]
      have hc := commute_padh_ιh (qh p g 1 (Acirc p (u 0))) x
      rw [← hc.eq, inv_mul_cancel_left]
      exact ιh_mem_J _
    · have hne : σGen p y (Fin.tail u) ≠ 0 := by rw [← hσx]; exact σh_ne_zero x ht
      have ht' : Fin.tail (Fin.cons (u 0) (σGen p y (Fin.tail u)) : V p (m + 2)) ≠ 0 := by
        rw [Fin.tail_cons]; exact hne
      rw [s₁h_succ m _ ht', s₁h_succ m u ht, Fin.tail_cons, Fin.cons_zero]
      set t := s₁h p g m (Fin.tail u)
      set t' := s₁h p g m (σGen p y (Fin.tail u))
      have htσ : σh (m + 1) t (eZ p m) = Fin.tail u := σh_s₁h m ht
      have ht'σ : σh (m + 1) t' (eZ p m) = σGen p y (Fin.tail u) := σh_s₁h m hne
      have hk : t'⁻¹ * x * t ∈ J p g m := by
        apply hZ
        simp only [map_mul, Function.End.mul_def, Function.comp_apply]
        rw [htσ, hσx, ← ht'σ, σh_inv_apply]
      have e : (ιh (m + 1) t' * padh m 2 (bh p g (u 0)))⁻¹ * (ιh (m + 1) x * (ιh (m + 1) t *
          padh m 2 (bh p g (u 0)))) = (padh m 2 (bh p g (u 0)))⁻¹ * ιh (m + 1) (t'⁻¹ * x * t) *
          padh m 2 (bh p g (u 0)) := by
        rw [map_mul, map_mul, map_inv]; group
      rw [e]
      exact L2 lf2.bS lf3 (u 0) hk

/-- Stage 1 on `m + 2` wires. -/
theorem zstab_succ (lf2 : LF2 p g) {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) (hZ : ZStab p g m) :
    ZStab p g (m + 1) := by
  intro x hx
  refine schreier (σh (m + 2)) (eZ p (m + 1)) (K := J p g (m + 1))
    (S := Set.range fun y : Gen Gate (m + 2) => qh p g (m + 2) (FreeMonoid.of y))
    (s₁h p g (m + 1)) ?_ ?_ x (by rw [closure_gens]; trivial) hx
  · rw [s₁h_tail0 (m + 1) _ rfl]
    show padh (m + 1) 1 (qh p g 1 (Acirc p (0, 1))) ∈ J p g (m + 1)
    rw [Acirc_eq]
    simp only [if_true, inv_one, Mq_one, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨y, rfl⟩ h _
    dsimp only
    have hu0 : σh (m + 2) h (eZ p (m + 1)) ≠ 0 := σh_ne_zero h (eZ_ne_zero _)
    rw [map_mul, Function.End.mul_def, Function.comp_apply, σh_qh, σC_of]
    exact step1 lf2 lf3 hZ y hu0

end QCert.QuditClifford
