/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The induction step, stage 2

Within `J`, the stabiliser of `X` on wire 0 is the circuits on the wires
above (`xstab_succ`), by Schreier's lemma with the section `S^β c(P)` for
`X Z^β ⊗ P`.  The two facts behind it:

* `cP_equiv`: a circuit `z` on the wires above conjugates `c(P)` to
  `c(z P)`;
* `heis`: `CZ c(P) = S^{a} c(P + Z₁)` modulo `Kst`, `a` the `X`-exponent of
  `P` on wire 1 (the Heisenberg group law of the `c`), reduced by
  `cP_equiv` to `P` on wire 1 (`LF2`) or on wires 1, 2 (`LF3`).
-/
import QCert.QuditClifford.Step

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### The action of the sections -/

theorem σh_S0h_pow (m k : ℕ) (v : V p (m + 1)) :
    σh (m + 1) (S0h p g m ^ k) v = Function.update v 0 ((v 0).1, (v 0).2 + k * (v 0).1) := by
  induction k generalizing v with
  | zero => simp only [pow_zero, map_one, Nat.cast_zero, zero_mul, add_zero]; simp; rfl
  | succ k ih =>
    rw [pow_succ, map_mul, Function.End.mul_def, Function.comp_apply, ih]
    simp only [S0h, σh_qh, σC_of, σGen, act1, Function.update_self, Function.update_idem]
    congr 1
    push_cast; ext <;> simp; ring

theorem σh_cP (m : ℕ) (P : V p (m + 1)) :
    σh (m + 2) (cP p g m P) (eX p (m + 1)) = Fin.cons (1, 0) P := by
  unfold cP
  split_ifs with hP
  · subst hP; rfl
  · simp only [map_mul, map_inv, Function.End.mul_def, Function.comp_apply]
    have h1 : σh (m + 2) (ιh (m + 1) (s₁h p g m P))⁻¹ (eX p (m + 1)) = eX p (m + 1) := by
      rw [← map_inv, σh_ιh, show Fin.tail (eX p (m + 1)) = 0 from rfl, σh_zero]; rfl
    rw [h1]
    have h2 : σh (m + 2) (CZh p g m) (eX p (m + 1)) = Fin.cons (1, 0) (eZ p m) := by
      simp only [CZh, σh_qh, σC_of]
      rw [σGen_CZ]
      simp [eX, eZ]
      try rfl
    rw [h2, σh_ιh, Fin.cons_zero, Fin.tail_cons, σh_s₁h m hP]

theorem s₂h_mem_J : (m : ℕ) → (w : V p (m + 1)) → s₂h p g m w ∈ J p g m
  | 0, w => Subgroup.pow_mem _ (S0h_mem_J 0) _
  | m + 1, w => by
    refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (S0h_mem_J _) _) ?_
    unfold cP
    split_ifs
    · exact Subgroup.one_mem _
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ιh_mem_J _) (CZh_mem_J m))
        (Subgroup.inv_mem _ (ιh_mem_J _))

theorem σh_s₂h : (m : ℕ) → {w : V p (m + 1)} → (w 0).1 = 1 →
    σh (m + 1) (s₂h p g m w) (eX p m) = w
  | 0, w, hw => by
    show σh 1 (S0h p g 0 ^ (w 0).2.val) (eX p 0) = w
    rw [σh_S0h_pow]
    apply V1_ext p
    simp [eX, hw, val_cast]
    ext <;> simp [hw]
  | m + 1, w, hw => by
    show σh (m + 2) (S0h p g (m + 1) ^ (w 0).2.val * cP p g m (Fin.tail w)) (eX p (m + 1)) = w
    rw [map_mul, Function.End.mul_def, Function.comp_apply, σh_cP, σh_S0h_pow]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Function.update_self, Fin.cons_zero, val_cast]
      ext <;> simp [hw]
    · rw [Function.update_of_ne (Fin.succ_ne_zero i), Fin.cons_succ]; rfl

/-! ### Equivariance of `c` -/

theorem cP_equiv {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) (hZ : ZStab p g m) (z : Gh p g (m + 1)) (P : V p (m + 1)) :
    cP p g m (σh (m + 1) z P) = ιh (m + 1) z * cP p g m P * (ιh (m + 1) z)⁻¹ := by
  by_cases hP : P = 0
  · subst hP; rw [σh_zero]; unfold cP; simp
  · have hP' : σh (m + 1) z P ≠ 0 := σh_ne_zero z hP
    unfold cP
    rw [if_neg hP, if_neg hP']
    set t := s₁h p g m P
    set t' := s₁h p g m (σh (m + 1) z P)
    have htσ : σh (m + 1) t (eZ p m) = P := σh_s₁h m hP
    have ht'σ : σh (m + 1) t' (eZ p m) = σh (m + 1) z P := σh_s₁h m hP'
    have hk : t'⁻¹ * z * t ∈ J p g m := by
      apply hZ
      simp only [map_mul, Function.End.mul_def, Function.comp_apply]
      rw [htσ, ← ht'σ, σh_inv_apply]
    have hc := L1 lf3 hk
    have e : z * t = t' * (t'⁻¹ * z * t) := by group
    have e2 : ιh (m + 1) z * (ιh (m + 1) t * CZh p g m * (ιh (m + 1) t)⁻¹) * (ιh (m + 1) z)⁻¹ =
        ιh (m + 1) t' * (ιh (m + 1) (t'⁻¹ * z * t) * CZh p g m * (ιh (m + 1) (t'⁻¹ * z * t))⁻¹) *
          (ιh (m + 1) t')⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e2, hc.eq.symm, mul_inv_cancel_right]

/-! ### The Heisenberg law -/

theorem cP_tail0 (m : ℕ) (Q : V p (m + 1)) (ht : Fin.tail Q = 0) :
    cP p g m Q = padh m 2 (cP p g 0 (fun _ => Q 0)) := by
  by_cases h0 : Q 0 = 0
  · have hQ : Q = 0 := eq_zero_of_tail h0 ht
    have hQ' : (fun _ => Q 0 : V p 1) = 0 := funext fun _ => h0
    unfold cP; rw [if_pos hQ, if_pos hQ', map_one]
  · have hQ : Q ≠ 0 := fun h => h0 (by rw [h]; rfl)
    have hQ' : (fun _ => Q 0 : V p 1) ≠ 0 := fun h => h0 (congrFun h 0)
    unfold cP
    rw [if_neg hQ, if_neg hQ', s₁h_tail0 m Q ht]
    simp only [map_mul, map_inv, padh_ιh, padh_CZh]
    rfl

theorem cP_two (m : ℕ) (Q : V p (m + 2)) (ht : Fin.tail (Fin.tail Q) = 0) :
    cP p g (m + 1) Q = padh m 3 (cP p g 1 (low p (n := m) (k := 2) Q)) := by
  by_cases hQ : Q = 0
  · have hQ' : low p (n := m) (k := 2) Q = 0 := by subst hQ; rfl
    unfold cP; rw [if_pos hQ, if_pos hQ', map_one]
  · have hQ' := low2_ne_zero hQ ht
    unfold cP
    rw [if_neg hQ, if_neg hQ', s₁h_two m Q ht]
    simp only [map_mul, map_inv, padh_ιh, padh_CZh1]

theorem conj_bracket {G : Type*} [Group G] {T s z c c' : G} (hs : Commute s T) (hz : Commute z T) :
    (s * (T * c' * T⁻¹))⁻¹ * (z * (T * c * T⁻¹)) = T * ((s * c')⁻¹ * (z * c)) * T⁻¹ := by
  have hs' : T * s * T⁻¹ = s := by rw [← hs.eq, mul_inv_cancel_right]
  have hz' : T * z * T⁻¹ = z := by rw [← hz.eq, mul_inv_cancel_right]
  conv_lhs => rw [← hs', ← hz']
  group

theorem S0h_pow_p (m : ℕ) : S0h p g m ^ p = 1 := by
  rw [← padh_S0h, ← map_pow, S0h_zero, Sq_one, S_pow_p, map_one]

theorem heis (lf2 : LF2 p g) {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) (hZ : ZStab p g m) (P : V p (m + 1)) :
    (S0h p g (m + 1) ^ (P 0).1.val * cP p g m (P + eZ p m))⁻¹ * (CZh p g m * cP p g m P) ∈
      Kst p g (m + 1) := by
  by_cases ht : Fin.tail P = 0
  · -- `P` on wire 1: the two-wire fact, placed
    have ht' : Fin.tail (P + eZ p m) = 0 := by
      rw [show Fin.tail (P + eZ p m) = Fin.tail P + Fin.tail (eZ p m) from rfl, ht, zero_add]; rfl
    rw [cP_tail0 m P ht, cP_tail0 m _ ht', ← padh_CZh, ← padh_S0h1, ← map_pow, ← map_mul,
      ← map_mul, ← map_inv, ← map_mul]
    have e : (fun _ => (P + eZ p m) 0 : V p 1) = (fun _ => P 0) + eZ p 0 := by
      funext i; rw [Subsingleton.elim i 0]; rfl
    rw [e]
    exact padh_Kst (lf2.heis (fun _ => P 0))
  · by_cases hα : (P 0).1 = 0
    · -- `X`-exponent 0 on wire 1: move the rest of `P` onto wire 2
      cases m with
      | zero => exact absurd (funext fun i => Fin.elim0 i) ht
      | succ m =>
        set s := s₁h p g m (Fin.tail P)
        have hs : σh (m + 1) s (eZ p m) = Fin.tail P := σh_s₁h m ht
        set β := (P 0).2
        have hP0 : P 0 = (0, β) := Prod.ext hα rfl
        have hQ₁ : σh (m + 2) (ιh (m + 1) s) (Fin.cons (0, β) (eZ p m)) = P := by
          rw [σh_ιh, Fin.cons_zero, Fin.tail_cons, hs, ← hP0, Fin.cons_self_tail]
        have hQ₂ : σh (m + 2) (ιh (m + 1) s) (Fin.cons (0, β + 1) (eZ p m)) = P + eZ p (m + 1) := by
          rw [σh_ιh, Fin.cons_zero, Fin.tail_cons, hs]
          funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · rw [Fin.cons_zero]; show (0, β + 1) = P 0 + (0, 1); rw [hP0, Prod.mk_add_mk, add_zero]
          · rw [Fin.cons_succ]; show Fin.tail P i = P i.succ + 0; rw [add_zero]; rfl
        rw [← hQ₂, ← hQ₁, cP_equiv lf3 hZ, cP_equiv lf3 hZ, hQ₁, hα, ZMod.val_zero, pow_zero]
        have hz : Commute (CZh p g (m + 1)) (ιh (m + 2) (ιh (m + 1) s)) :=
          commute_padh2_ιh2 (n := m + 1) (CZh p g 0) s
        rw [conj_bracket (Commute.one_left _) hz]
        refine (Kst p g (m + 2)).mul_mem ((Kst p g (m + 2)).mul_mem ⟨_, rfl⟩ ?_)
          ((Kst p g (m + 2)).inv_mem ⟨_, rfl⟩)
        rw [one_mul, cP_two m _ rfl, cP_two m _ rfl, ← padh_CZh1, ← map_mul, ← map_inv, ← map_mul]
        have e1 : low p (n := m) (k := 2) (Fin.cons (0, β) (eZ p m) : V p (m + 2)) =
            Fin.cons (0, β) (eZ p 0) := by apply V2_ext p <;> rfl
        have e2 : low p (n := m) (k := 2) (Fin.cons (0, β + 1) (eZ p m) : V p (m + 2)) =
            Fin.cons (0, β + 1) (eZ p 0) := by apply V2_ext p <;> rfl
        rw [e1, e2]
        exact padh_Kst ((lf3 (Nat.succ_ne_zero m)).heis β)
    · -- nonzero `X`-exponent on wire 1: move `P` to `X` on wire 1
      set α := (P 0).1 with hαdef
      set w : V p (m + 1) := α⁻¹ • P
      have hw : (w 0).1 = 1 := by
        show α⁻¹ * (P 0).1 = 1
        rw [← hαdef]; exact inv_mul_cancel₀ hα
      set t := s₂h p g m w
      have htJ : t ∈ J p g m := s₂h_mem_J m w
      have htX : σh (m + 1) t (eX p m) = w := σh_s₂h m hw
      have htZ : σh (m + 1) t (eZ p m) = eZ p m := J_fix_eZ htJ
      have hQ₁ : σh (m + 1) t (α • eX p m) = P := by
        rw [σh_smul, htX, smul_smul, mul_inv_cancel₀ hα, one_smul]
      have hQ₂ : σh (m + 1) t (α • eX p m + eZ p m) = P + eZ p m := by
        rw [σh_add, hQ₁, htZ]
      rw [← hQ₂, ← hQ₁, cP_equiv lf3 hZ, cP_equiv lf3 hZ]
      have hz : Commute (CZh p g m) (ιh (m + 1) t) := L1 lf3 htJ
      have hs : Commute (S0h p g (m + 1) ^ α.val) (ιh (m + 1) t) :=
        (commute_padh_ιh (S0h p g 0) t).pow_left _
      rw [conj_bracket hs hz]
      refine (Kst p g (m + 1)).mul_mem ((Kst p g (m + 1)).mul_mem ⟨_, rfl⟩ ?_)
        ((Kst p g (m + 1)).inv_mem ⟨_, rfl⟩)
      have hz1 : Fin.tail (α • eX p m) = 0 := by
        show α • Fin.tail (eX p m) = 0; rw [show Fin.tail (eX p m) = 0 from rfl, smul_zero]
      have hz2 : Fin.tail (α • eX p m + eZ p m) = 0 := by
        show Fin.tail (α • eX p m) + Fin.tail (eZ p m) = 0
        rw [hz1, show Fin.tail (eZ p m) = 0 from rfl, add_zero]
      rw [cP_tail0 m _ hz1, cP_tail0 m _ hz2, ← padh_CZh, ← padh_S0h1, ← map_pow, ← map_mul,
        ← map_mul, ← map_inv, ← map_mul]
      have e : (fun _ => (α • eX p m + eZ p m) 0 : V p 1) = (fun _ => (α • eX p m) 0) + eZ p 0 := by
        funext i; rw [Subsingleton.elim i 0]; rfl
      have e' : ((fun _ => (α • eX p m) 0 : V p 1) 0).1 = α := by
        show α * 1 = α; rw [mul_one]
      have h := lf2.heis (fun _ => (α • eX p m) 0)
      rw [e', ← e] at h
      exact padh_Kst h

/-! ### Stage 2 -/

theorem step2 (lf2 : LF2 p g) {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) (hZ : ZStab p g m)
    {y : Gh p g (m + 2)} (hy : y ∈ Jgen p g (m + 1)) {v : V p (m + 2)} (hv : (v 0).1 = 1) :
    (s₂h p g (m + 1) (σh (m + 2) y v))⁻¹ * (y * s₂h p g (m + 1) v) ∈ Kst p g (m + 1) := by
  show (S0h p g (m + 1) ^ (σh (m + 2) y v 0).2.val * cP p g m (Fin.tail (σh (m + 2) y v)))⁻¹ *
    (y * (S0h p g (m + 1) ^ (v 0).2.val * cP p g m (Fin.tail v))) ∈ Kst p g (m + 1)
  rcases hy with ⟨z, rfl⟩ | hy | hy
  · rw [σh_ιh, Fin.cons_zero, Fin.tail_cons, cP_equiv lf3 hZ]
    have hs : Commute (S0h p g (m + 1) ^ (v 0).2.val) (ιh (m + 1) z) :=
      (commute_padh_ιh (S0h p g 0) z).pow_left _
    have e : (S0h p g (m + 1) ^ (v 0).2.val * (ιh (m + 1) z * cP p g m (Fin.tail v) *
        (ιh (m + 1) z)⁻¹))⁻¹ * (ιh (m + 1) z * (S0h p g (m + 1) ^ (v 0).2.val *
          cP p g m (Fin.tail v))) = ιh (m + 1) z := by
      have hs' : ιh (m + 1) z * S0h p g (m + 1) ^ (v 0).2.val =
          S0h p g (m + 1) ^ (v 0).2.val * ιh (m + 1) z := hs.eq.symm
      calc _ = ιh (m + 1) z * (cP p g m (Fin.tail v))⁻¹ * (ιh (m + 1) z)⁻¹ *
            (S0h p g (m + 1) ^ (v 0).2.val)⁻¹ * (ιh (m + 1) z * S0h p g (m + 1) ^ (v 0).2.val) *
            cP p g m (Fin.tail v) := by group
        _ = ιh (m + 1) z := by rw [hs']; group
    rw [e]; exact ⟨z, rfl⟩
  · subst hy
    have hS : σh (m + 2) (S0h p g (m + 1)) v = Function.update v 0 ((v 0).1, (v 0).1 + (v 0).2) := by
      simp [S0h, σh_qh, σC_of, σGen, act1]
    rw [hS, Function.update_self, tail_update_zero, hv, pow_val_add (S0h_pow_p (m + 1)),
      pow_val_one (S0h_pow_p (m + 1))]
    rw [show (S0h p g (m + 1) * S0h p g (m + 1) ^ (v 0).2.val * cP p g m (Fin.tail v))⁻¹ *
      (S0h p g (m + 1) * (S0h p g (m + 1) ^ (v 0).2.val * cP p g m (Fin.tail v))) = 1 by group]
    exact Subgroup.one_mem _
  · rw [Set.mem_singleton_iff] at hy; subst hy
    have hC : σh (m + 2) (CZh p g m) v =
        Fin.cons (1, (v 0).2 + (v 1).1) (Fin.tail v + eZ p m) := by
      simp only [CZh, σh_qh, σC_of]
      rw [σGen_CZ, hv]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; show _ = v 1 + (0, 1); ext <;> simp
      · rw [Fin.cons_succ]; show _ = Fin.tail v i.succ + 0; rw [add_zero]; rfl
    rw [hC, Fin.cons_zero, Fin.tail_cons, pow_val_add (S0h_pow_p (m + 1))]
    have hcz : Commute (CZh p g m) (S0h p g (m + 1) ^ (v 0).2.val) := by
      rw [← padh_CZh, ← padh_S0h1, ← map_pow]; exact (lf2.czS0.pow_right _).map _
    have e : (S0h p g (m + 1) ^ (v 0).2.val * S0h p g (m + 1) ^ (v 1).1.val *
        cP p g m (Fin.tail v + eZ p m))⁻¹ * (CZh p g m * (S0h p g (m + 1) ^ (v 0).2.val *
          cP p g m (Fin.tail v))) = (S0h p g (m + 1) ^ (v 1).1.val *
          cP p g m (Fin.tail v + eZ p m))⁻¹ * (CZh p g m * cP p g m (Fin.tail v)) := by
      calc _ = (S0h p g (m + 1) ^ (v 1).1.val * cP p g m (Fin.tail v + eZ p m))⁻¹ *
            (S0h p g (m + 1) ^ (v 0).2.val)⁻¹ * (CZh p g m * S0h p g (m + 1) ^ (v 0).2.val) *
            cP p g m (Fin.tail v) := by group
        _ = _ := by rw [hcz.eq]; group
    rw [e]
    exact heis lf2 lf3 hZ (Fin.tail v)

/-- Stage 2 on `m + 2` wires. -/
theorem xstab_succ (lf2 : LF2 p g) {m : ℕ} (lf3 : m ≠ 0 → LF3 p g) (hZ : ZStab p g m) :
    XStab p g (m + 1) := by
  intro x hx hfix
  refine schreier (σh (m + 2)) (eX p (m + 1)) (K := Kst p g (m + 1)) (S := Jgen p g (m + 1))
    (s₂h p g (m + 1)) ?_ ?_ x hx hfix
  · show S0h p g (m + 1) ^ (0 : ZMod p).val * cP p g m (Fin.tail (eX p (m + 1))) ∈ Kst p g (m + 1)
    rw [pow_val_zero, one_mul, show Fin.tail (eX p (m + 1)) = 0 from rfl]
    unfold cP; rw [if_pos rfl]; exact Subgroup.one_mem _
  · intro y hy h hh
    have hv : (σh (m + 2) h (eX p (m + 1)) 0).1 = 1 := by rw [J_fst hh]; rfl
    rw [map_mul, Function.End.mul_def, Function.comp_apply]
    exact step2 lf2 lf3 hZ hy hv

/-! ### Symplectic completeness from the local facts -/

/-- Both stages and faithfulness at every width, from the local facts. -/
theorem stab_all (lf2 : LF2 p g) (lf3 : LF3 p g) :
    ∀ m, ZStab p g m ∧ XStab p g m ∧ Faith p g (m + 1)
  | 0 => ⟨zstab_zero, xstab_zero, faith_one⟩
  | m + 1 => by
    obtain ⟨hZ, hX, hF⟩ := stab_all lf2 lf3 m
    have hZ' := zstab_succ lf2 (fun _ => lf3) hZ
    have hX' := xstab_succ lf2 (fun _ => lf3) hZ
    exact ⟨hZ', hX', faith_succ hZ' hX' hF⟩

end QCert.QuditClifford
