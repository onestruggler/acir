/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Proposition 3.9: every Clifford operator has a unique normal form

Lemma 3.8 (`lemma_3_8`): two `ω`-anticommuting Paulis are carried to `Z`
and `X` on the bottom wire by a `Z`-normal circuit followed by an
`X`-normal one, read off them.  Proposition 3.9: every unitary normalising
the Pauli group acts on it as a normal circuit does (`exists_nf`), and the
normal circuit is determined by the action (`nf_unique`).  With the phases
of Corollary B.3 every element of `𝒞ₙ` is the operator of exactly one
normal form (`NF`), which gives Corollary 3.10.
-/
import QCert.QutritClifford.NormalForm

namespace QCert.QutritClifford

open Matrix

/-! ### Commutation of Pauli data -/

namespace PD

variable {n : ℕ}

/-- `P Q = ω^φ Q P` with `φ = Σⱼ (bⱼ e'ⱼ - b'ⱼ aⱼ)`. -/
theorem mul_comm_phase (P Q : PD n) :
    P.mul Q = scale (∑ j, (P.b j * Q.a j - Q.b j * P.a j)) (Q.mul P) := by
  simp only [mul, scale, PD.mk.injEq]
  refine ⟨?_, add_comm _ _, add_comm _ _⟩
  rw [Finset.sum_sub_distrib]
  abel

theorem scale_inj {d e : Fin 3} {P : PD n} (h : scale d P = scale e P) : d = e := by
  have := congrArg PD.c h
  simp only [scale] at this
  exact add_right_cancel this

theorem sum_cons (a0 b0 : Fin 3) (P : PD n) (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3)
    (Q : PD (n + 1)) :
    ∑ j, f ((P.cons a0 b0).a j) ((P.cons a0 b0).b j) (Q.a j) (Q.b j) =
      f a0 b0 (Q.a 0) (Q.b 0) + ∑ j, f (P.a j) (P.b j) (Q.a j.succ) (Q.b j.succ) := by
  rw [Fin.sum_univ_succ]
  rfl

end PD

theorem Ztop_a : ∀ k : ℕ, (Ztop k).a = 0
  | 0 => by funext j; fin_cases j; rfl
  | k + 1 => by
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    show (Ztop k).a i = 0
    rw [Ztop_a k]; rfl

theorem Ztop_b : ∀ (k : ℕ) (j : Fin (k + 1)), (Ztop k).b j = if j = Fin.last k then 1 else 0
  | 0, j => by fin_cases j; rfl
  | k + 1, j => by
    refine Fin.cases rfl (fun i => ?_) j
    show (Ztop k).b i = _
    rw [Ztop_b k i]
    exact if_congr (by rw [← Fin.succ_last, Fin.succ_inj]) rfl rfl

/-- `Z` on the top wire against `Q`: `Z Q = ω^{a} Q Z`, `a` the `X`
exponent of `Q` on the top wire. -/
theorem Ztop_mul (k : ℕ) (Q : PD (k + 1)) :
    (Ztop k).mul Q = PD.scale (Q.a (Fin.last k)) (Q.mul (Ztop k)) := by
  rw [PD.mul_comm_phase]
  congr 1
  simp only [Ztop_a, Ztop_b, Pi.zero_apply, mul_zero, sub_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem Zbot_mul (k : ℕ) (Q : PD (k + 1)) :
    (Zbot k).mul Q = PD.scale (Q.a 0) (Q.mul (Zbot k)) := by
  rw [PD.mul_comm_phase]
  congr 1
  rw [Fin.sum_univ_succ]
  simp [Zbot, PD.cons, PD.sc]

theorem Xbot_mul (k : ℕ) (Q : PD (k + 1)) :
    (Xbot k 0 0).mul Q = PD.scale (-Q.b 0) (Q.mul (Xbot k 0 0)) := by
  rw [PD.mul_comm_phase]
  congr 1
  rw [Fin.sum_univ_succ]
  simp [Xbot, PD.cons, PD.sc]

noncomputable section

/-! ### Conjugation on Pauli data -/

theorem PD.op_scale {n : ℕ} (d : Fin 3) (P : PD n) : (P.scale d).op = wp d • P.op := by
  ext s t
  rw [smul_apply, PD.op_apply, PD.op_apply, smul_eq_mul]
  simp only [PD.scale]
  split_ifs
  · rw [add_assoc, AddChar.map_add_eq_mul]
  · rw [mul_zero]

theorem sem_unitary {n : ℕ} (w : Circ n) :
    star (sem n w : Op ℂ 3 n) * (sem n w : Op ℂ 3 n) = 1 ∧
      (sem n w : Op ℂ 3 n) * star (sem n w : Op ℂ 3 n) = 1 :=
  Unitary.mem_iff.1 (sem n w).2

theorem actC_mulPD {n : ℕ} (w : Circ n) (P Q : PD n) :
    actC n w (P.mul Q) = (actC n w P).mul (actC n w Q) := by
  apply PD.op_inj
  rw [← PD.op_mul, ← sem_conj, ← sem_conj, ← sem_conj, ← PD.op_mul]
  obtain ⟨h1, -⟩ := sem_unitary w
  calc (sem n w : Op ℂ 3 n) * (P.op * Q.op) * star (sem n w : Op ℂ 3 n)
      = (sem n w : Op ℂ 3 n) * P.op * (star (sem n w : Op ℂ 3 n) * (sem n w : Op ℂ 3 n)) *
          Q.op * star (sem n w : Op ℂ 3 n) := by rw [h1, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem actC_scale {n : ℕ} (w : Circ n) (d : Fin 3) (P : PD n) :
    actC n w (P.scale d) = (actC n w P).scale d := by
  apply PD.op_inj
  rw [← sem_conj, PD.op_scale, PD.op_scale, ← sem_conj, mul_smul_comm, smul_mul_assoc]

theorem actC_injective {n : ℕ} (w : Circ n) : Function.Injective (actC n w) := by
  intro P Q h
  apply PD.op_inj
  apply conj_injective (sem n w)
  simp only
  rw [sem_conj, sem_conj, h]

theorem actC_bijective {n : ℕ} (w : Circ n) : Function.Bijective (actC n w) :=
  Finite.injective_iff_bijective.1 (actC_injective w)

/-! ### Lemma 3.8 -/

/-- **Lemma 3.8**: for `ω`-anticommuting Paulis `P`, `Q` there are a
`Z`-normal circuit `L` and an `X`-normal circuit `M` with
`ML • P = I ⊗ ⋯ ⊗ I ⊗ Z` and `ML • Q = I ⊗ ⋯ ⊗ I ⊗ X`. -/
theorem lemma_3_8 {k : ℕ} (p q : PD (k + 1)) (h : p.mul q = PD.scale 1 (q.mul p)) :
    ∃ (L : ZN (k + 1)) (M : XN k), actC (k + 1) (L.circ ⨾ M.circ) p = Zbot k ∧
      actC (k + 1) (L.circ ⨾ M.circ) q = Xbot k 0 0 := by
  have hp : ∃ j, p.a j ≠ 0 ∨ p.b j ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_or, ne_eq, not_not] at hc
    have h0 : p.mul q = PD.scale 0 (q.mul p) := by
      rw [PD.mul_comm_phase]
      congr 1
      simp [(hc _).1, (hc _).2]
    rw [h0] at h
    exact absurd (PD.scale_inj h) (by decide)
  obtain ⟨L, hL⟩ := ZN.exists_pre p hp
  have hLp : actC (k + 1) L.circ p = Ztop k := by rw [← hL]; exact ZN.act_pre L
  set q' := actC (k + 1) L.circ q with hq'
  have h' : (Ztop k).mul q' = PD.scale 1 (q'.mul (Ztop k)) := by
    rw [← hLp, hq', ← actC_mulPD, h, actC_scale, actC_mulPD]
  rw [Ztop_mul] at h'
  have ha := PD.scale_inj h'
  obtain ⟨M, hM⟩ := XN.exists_pre q' ha
  refine ⟨L, M, ?_, ?_⟩
  · rw [actC_seq, hLp, XN.act_Ztop]
  · rw [actC_seq, ← hq', ← hM, XN.act_pre]

/-! ### Unitaries normalising the Pauli group -/

/-- A unitary that normalises the Pauli group. -/
def Normal (n : ℕ) (U : Op ℂ 3 n) : Prop :=
  star U * U = 1 ∧ U * star U = 1 ∧ ∀ p : PD n, ∃ r : PD n, U * p.op * star U = r.op

theorem conj_cancel {n : ℕ} {U : Op ℂ 3 n} (hU : star U * U = 1) (A : Op ℂ 3 n) :
    star U * (U * A * star U) * U = A := by
  calc star U * (U * A * star U) * U = (star U * U) * A * (star U * U) := by
        simp only [mul_assoc]
    _ = A := by rw [hU, one_mul, mul_one]

theorem conj_inj {n : ℕ} {U : Op ℂ 3 n} (hU : star U * U = 1) {A B : Op ℂ 3 n}
    (h : U * A * star U = U * B * star U) : A = B := by
  rw [← conj_cancel hU A, h, conj_cancel hU B]

theorem conj_mul_op {n : ℕ} {U : Op ℂ 3 n} (hU : star U * U = 1) (A B : Op ℂ 3 n) :
    U * (A * B) * star U = (U * A * star U) * (U * B * star U) := by
  calc U * (A * B) * star U = U * A * (star U * U) * B * star U := by
        rw [hU, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem sem_normal {n : ℕ} (w : Circ n) : Normal n (sem n w : Op ℂ 3 n) :=
  ⟨(sem_unitary w).1, (sem_unitary w).2, fun p => ⟨actC n w p, sem_conj w p⟩⟩

theorem Normal.mul {n : ℕ} {U V : Op ℂ 3 n} (hU : Normal n U) (hV : Normal n V) :
    Normal n (U * V) := by
  refine ⟨?_, ?_, fun p => ?_⟩
  · rw [star_mul]
    calc star V * star U * (U * V) = star V * (star U * U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hV.1]
  · rw [star_mul]
    calc U * V * (star V * star U) = U * (V * star V) * star U := by simp only [mul_assoc]
      _ = 1 := by rw [hV.2.1, mul_one, hU.2.1]
  · obtain ⟨r, hr⟩ := hV.2.2 p
    obtain ⟨r', hr'⟩ := hU.2.2 r
    refine ⟨r', ?_⟩
    rw [star_mul, ← hr', ← hr]
    simp only [mul_assoc]

/-- Conjugation by a unitary normalising the Pauli group is onto. -/
theorem Normal.pre {n : ℕ} {U : Op ℂ 3 n} (hU : Normal n U) (q : PD n) :
    ∃ p : PD n, U * p.op * star U = q.op := by
  choose f hf using hU.2.2
  have hinj : Function.Injective f := by
    intro p p' h
    apply PD.op_inj
    exact conj_inj hU.1 (by rw [hf, hf, h])
  obtain ⟨p, hp⟩ := Finite.injective_iff_surjective.1 hinj q
  exact ⟨p, by rw [hf, hp]⟩

theorem Normal.star {n : ℕ} {U : Op ℂ 3 n} (hU : Normal n U) : Normal n (star U) := by
  refine ⟨by rw [star_star]; exact hU.2.1, by rw [star_star]; exact hU.1, fun q => ?_⟩
  obtain ⟨p, hp⟩ := hU.pre q
  refine ⟨p, ?_⟩
  rw [star_star, ← hp, conj_cancel hU.1]

/-! ### Fixing `Z` and `X` on the bottom wire -/

theorem cons_zero_zero {n : ℕ} : (Fin.cons 0 (0 : Fin n → Fin 3) : Fin (n + 1) → Fin 3) = 0 := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

theorem Zbot_op (n : ℕ) : (Zbot n).op = diagonal fun t : State 3 (n + 1) => wp (t 0) := by
  ext s t
  rw [PD.op_apply, diagonal_apply]
  simp only [Zbot, PD.cons, PD.sc, cons_zero_zero, add_zero, zero_add]
  split_ifs with h
  · rw [h, Fin.sum_univ_succ]
    simp
  · rfl

/-- `e₀`: the basis state `1` on the bottom wire. -/
def e0 (n : ℕ) : State 3 (n + 1) := Fin.cons 1 0

theorem Xbot_op_apply (n : ℕ) (s t : State 3 (n + 1)) :
    (Xbot n 0 0).op s t = if s = t + e0 n then 1 else 0 := by
  rw [PD.op_apply]
  simp only [Xbot, PD.cons, PD.sc, cons_zero_zero, e0]
  split_ifs <;> simp

theorem cons_add_e0 {n : ℕ} (x : Fin 3) (s : State 3 n) :
    (Fin.cons x s : State 3 (n + 1)) + e0 n = Fin.cons (x + 1) s := by
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  show s i + 0 = s i
  rw [add_zero]

theorem onTop1_apply_cons {n : ℕ} (V : Op ℂ 3 n) (x y : Fin 3) (s t : State 3 n) :
    onTop 1 V (Fin.cons x s) (Fin.cons y t) = if x = y then V s t else 0 := by
  rw [onTop_apply, split1_fst, split1_fst, split1_snd, split1_snd]
  by_cases h : x = y
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun h' => h (by simpa using congrFun h' 0)), if_neg h]

theorem onTop1_inj {n : ℕ} {A B : Op ℂ 3 n} (h : onTop 1 A = onTop 1 B) : A = B := by
  ext s t
  have := congrFun (congrFun h (Fin.cons 0 s)) (Fin.cons 0 t)
  rwa [onTop1_apply_cons, onTop1_apply_cons, if_pos rfl, if_pos rfl] at this

theorem op_cons00 {n : ℕ} (p : PD n) : (p.cons 0 0).op = onTop 1 p.op := by
  rw [PD.op, pauli_split (k := 1), PD.cons, split1_fst, split1_fst, split1_snd, split1_snd]
  have h1 : pauli 0 ![(0 : Fin 3)] ![0] = 1 := by
    have : (![(0 : Fin 3)] : Fin 1 → Fin 3) = 0 := by funext j; fin_cases j; rfl
    rw [this]
    exact PD.op_one
  rw [h1, onBottom_one, one_mul]
  rfl

/-- **An operator commuting with `Z` and `X` on the bottom wire acts on the
other wires only.** -/
theorem eq_onTop {n : ℕ} {W : Op ℂ 3 (n + 1)} (hZ : W * (Zbot n).op = (Zbot n).op * W)
    (hX : W * (Xbot n 0 0).op = (Xbot n 0 0).op * W) :
    W = onTop 1 (fun s t => W (Fin.cons 0 s) (Fin.cons 0 t)) := by
  have hoff : ∀ s t : State 3 (n + 1), s 0 ≠ t 0 → W s t = 0 := by
    intro s t hst
    have e := congrFun (congrFun hZ s) t
    rw [Zbot_op, mul_diagonal, diagonal_mul] at e
    have hne : wp (t 0) - wp (s 0) ≠ 0 :=
      sub_ne_zero.2 fun e' => hst (ωℂ_pow_inj _ _ e').symm
    have e2 : (wp (t 0) - wp (s 0)) * W s t = 0 := by linear_combination e
    exact (mul_eq_zero.1 e2).resolve_left hne
  have hshift : ∀ s t : State 3 (n + 1), W (s + e0 n) (t + e0 n) = W s t := by
    intro s t
    have e := congrFun (congrFun hX (s + e0 n)) t
    rw [mul_apply, mul_apply, Finset.sum_eq_single (t + e0 n), Finset.sum_eq_single s,
      Xbot_op_apply, Xbot_op_apply, if_pos rfl, if_pos rfl, mul_one, one_mul] at e
    · exact e
    · intro u _ hu
      rw [Xbot_op_apply, if_neg (fun h => hu (add_right_cancel h).symm), zero_mul]
    · simp
    · intro u _ hu
      rw [Xbot_op_apply, if_neg hu, mul_zero]
    · simp
  have hdiag : ∀ (y : Fin 3) (s t : State 3 n),
      W (Fin.cons y s) (Fin.cons y t) = W (Fin.cons 0 s) (Fin.cons 0 t) := by
    intro y s t
    have h1 : W (Fin.cons 1 s) (Fin.cons 1 t) = W (Fin.cons 0 s) (Fin.cons 0 t) := by
      have e := hshift (Fin.cons 0 s) (Fin.cons 0 t)
      rw [cons_add_e0, cons_add_e0, zero_add] at e
      exact e
    have h2 : W (Fin.cons 2 s) (Fin.cons 2 t) = W (Fin.cons 1 s) (Fin.cons 1 t) := by
      have e := hshift (Fin.cons 1 s) (Fin.cons 1 t)
      rw [cons_add_e0, cons_add_e0, show (1 : Fin 3) + 1 = 2 from rfl] at e
      exact e
    fin_cases y
    · rfl
    · exact h1
    · exact h2.trans h1
  ext s t
  rw [← Fin.cons_self_tail s, ← Fin.cons_self_tail t, onTop1_apply_cons]
  split_ifs with h
  · rw [h, hdiag]
  · exact hoff _ _ h

/-- The operator on the other wires is again a unitary normalising the
Pauli group. -/
theorem normal_of_onTop {n : ℕ} {V : Op ℂ 3 n} (hW : Normal (n + 1) (onTop 1 V))
    (hZ : onTop 1 V * (Zbot n).op * star (onTop 1 V) = (Zbot n).op)
    (hX : onTop 1 V * (Xbot n 0 0).op * star (onTop 1 V) = (Xbot n 0 0).op) : Normal n V := by
  refine ⟨?_, ?_, fun p => ?_⟩
  · apply onTop1_inj
    rw [onTop_mul, ← star_onTop, hW.1, onTop_one]
  · apply onTop1_inj
    rw [onTop_mul, ← star_onTop, hW.2.1, onTop_one]
  · obtain ⟨r, hr⟩ := hW.2.2 (p.cons 0 0)
    have hZr : (Zbot n).mul r = r.mul (Zbot n) := by
      apply PD.op_inj
      rw [← PD.op_mul, ← PD.op_mul, ← hr, ← hZ, ← conj_mul_op hW.1, ← conj_mul_op hW.1,
        PD.op_mul, PD.op_mul, Zbot_mul]
      simp [PD.cons, PD.scale_zero]
    have hXr : (Xbot n 0 0).mul r = r.mul (Xbot n 0 0) := by
      apply PD.op_inj
      rw [← PD.op_mul, ← PD.op_mul, ← hr, ← hX, ← conj_mul_op hW.1, ← conj_mul_op hW.1,
        PD.op_mul, PD.op_mul, Xbot_mul]
      simp [PD.cons, PD.scale_zero]
    rw [Zbot_mul] at hZr
    rw [Xbot_mul] at hXr
    have ha : r.a 0 = 0 := PD.scale_inj (hZr.trans (PD.scale_zero _).symm)
    have hb : r.b 0 = 0 := neg_eq_zero.1 (PD.scale_inj (hXr.trans (PD.scale_zero _).symm))
    have hr0 : r = r.tl.cons 0 0 := by
      conv_lhs => rw [← PD.cons_tl r]
      rw [ha, hb]
    refine ⟨r.tl, onTop1_inj ?_⟩
    rw [← op_cons00, ← hr0, ← hr, op_cons00, star_onTop, onTop_mul, onTop_mul]

/-! ### Normal forms without the phase -/

/-- The `Z`- and `X`-normal layers of a normal form (Figure 11), without the
global phase. -/
def NFX : ℕ → Type
  | 0 => Unit
  | n + 1 => ZN (n + 1) × XN n × NFX n

/-- The circuit of the layers: `L⁽ⁿ⁾ ⨾ M⁽ⁿ⁾` on all wires, then the rest on
the top `n - 1` wires. -/
def NFX.circ : (n : ℕ) → NFX n → Circ n
  | 0, _ => 1
  | n + 1, x => x.1.circ ⨾ x.2.1.circ ⨾ top (NFX.circ n x.2.2)

theorem actC_top_embed {n : ℕ} (w : Circ n) (P : PD (n + 1)) :
    actC (n + 1) (top w) P = embedHi (k := 1) (actC n w) P := by
  apply PD.op_inj
  rw [← sem_conj, show ((sem (n + 1) (top w) : unitaryGroup (State 3 (n + 1)) ℂ) :
      Op ℂ 3 (n + 1)) = onTop 1 (sem n w : Op ℂ 3 n) from
      congrArg Subtype.val (gateSem.sem_shift w), conj_onTop (sem_conj w)]

theorem op_nil (p : PD 0) : p.op = wp p.c • (1 : Op ℂ 3 0) := by
  ext s t
  have hs : s = t := Subsingleton.elim s t
  subst hs
  rw [PD.op_apply, if_pos (Subsingleton.elim _ _)]
  simp

/-- **Proposition 3.9**, existence: a unitary normalising the Pauli group
acts on it as the layers of a normal form do. -/
theorem exists_nf : ∀ (n : ℕ) (U : Op ℂ 3 n), Normal n U →
    ∃ x : NFX n, ∀ p : PD n, U * p.op * star U = (actC n (NFX.circ n x) p).op
  | 0, U, hU => ⟨(), fun p => by
      rw [NFX.circ, actC_one, op_nil, mul_smul_comm, mul_one, smul_mul_assoc, hU.2.1]⟩
  | n + 1, U, hU => by
    obtain ⟨p, hp⟩ := hU.pre (Zbot n)
    obtain ⟨q, hq⟩ := hU.pre (Xbot n 0 0)
    have e1 : U * (p.mul q).op * star U = ((Zbot n).mul (Xbot n 0 0)).op := by
      rw [← PD.op_mul, conj_mul_op hU.1, hp, hq, PD.op_mul]
    have e2 : U * (q.mul p).op * star U = ((Xbot n 0 0).mul (Zbot n)).op := by
      rw [← PD.op_mul, conj_mul_op hU.1, hq, hp, PD.op_mul]
    have hpq : p.mul q = PD.scale 1 (q.mul p) := by
      apply PD.op_inj
      apply conj_inj hU.1
      rw [e1, PD.op_scale, mul_smul_comm, smul_mul_assoc, e2, ← PD.op_scale, Zbot_mul]
      rfl
    obtain ⟨L, M, hLp, hLq⟩ := lemma_3_8 p q hpq
    set N : Op ℂ 3 (n + 1) := (sem (n + 1) (L.circ ⨾ M.circ) : Op ℂ 3 (n + 1)) with hNdef
    have hN : Normal (n + 1) N := sem_normal _
    have hNp : star N * (Zbot n).op * N = p.op := by
      rw [← hLp, ← sem_conj, ← hNdef, conj_cancel hN.1]
    have hNq : star N * (Xbot n 0 0).op * N = q.op := by
      rw [← hLq, ← sem_conj, ← hNdef, conj_cancel hN.1]
    have hW : Normal (n + 1) (U * star N) := hU.mul hN.star
    have hWZ : U * star N * (Zbot n).op * star (U * star N) = (Zbot n).op := by
      rw [star_mul, star_star]
      calc U * star N * (Zbot n).op * (N * star U) = U * (star N * (Zbot n).op * N) * star U := by
            simp only [mul_assoc]
        _ = (Zbot n).op := by rw [hNp, hp]
    have hWX : U * star N * (Xbot n 0 0).op * star (U * star N) = (Xbot n 0 0).op := by
      rw [star_mul, star_star]
      calc U * star N * (Xbot n 0 0).op * (N * star U) =
          U * (star N * (Xbot n 0 0).op * N) * star U := by simp only [mul_assoc]
        _ = (Xbot n 0 0).op := by rw [hNq, hq]
    have hcomm : ∀ {A : Op ℂ 3 (n + 1)}, U * star N * A * star (U * star N) = A →
        U * star N * A = A * (U * star N) := by
      intro A hA
      calc U * star N * A = U * star N * A * (star (U * star N) * (U * star N)) := by
            rw [hW.1, mul_one]
        _ = A * (U * star N) := by rw [← mul_assoc, hA]
    have hWeq := eq_onTop (hcomm hWZ) (hcomm hWX)
    set V : Op ℂ 3 n := fun s t => (U * star N) (Fin.cons 0 s) (Fin.cons 0 t) with hV
    rw [hWeq] at hW hWZ hWX
    obtain ⟨x', hx'⟩ := exists_nf n V (normal_of_onTop hW hWZ hWX)
    refine ⟨(L, M, x'), fun P => ?_⟩
    have hU' : U = (U * star N) * N := by rw [mul_assoc, hN.1, mul_one]
    rw [NFX.circ, actC_seq, actC_top_embed, ← conj_onTop hx', ← sem_conj, ← hNdef, ← hWeq]
    conv_lhs => rw [hU']
    rw [star_mul]
    simp only [mul_assoc]

/-! ### Uniqueness -/

theorem PD.op_sc {n : ℕ} (c : Fin 3) : (PD.sc c : PD n).op = wp c • (1 : Op ℂ 3 n) := by
  ext s t
  rw [PD.op_apply, smul_apply, one_apply, smul_eq_mul]
  simp only [PD.sc, add_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  split_ifs <;> simp

/-- Circuits fix the scalars. -/
theorem actC_sc {n : ℕ} (w : Circ n) (c : Fin 3) : actC n w (PD.sc c) = PD.sc c := by
  apply PD.op_inj
  rw [← sem_conj, PD.op_sc, mul_smul_comm, mul_one, smul_mul_assoc, (sem_unitary w).2]

theorem actC_top_Zbot {n : ℕ} (w : Circ n) : actC (n + 1) (top w) (Zbot n) = Zbot n := by
  rw [Zbot, actC_top, actC_sc]

theorem actC_top_Xbot {n : ℕ} (w : Circ n) : actC (n + 1) (top w) (Xbot n 0 0) = Xbot n 0 0 := by
  rw [Xbot, actC_top, actC_sc]

theorem NFX.actC_succ {n : ℕ} (x : NFX (n + 1)) (P : PD (n + 1)) :
    actC (n + 1) (NFX.circ (n + 1) x) P =
      actC (n + 1) (top (NFX.circ n x.2.2)) (actC (n + 1) x.2.1.circ (actC (n + 1) x.1.circ P)) := by
  rw [NFX.circ, actC_seq, actC_seq]

/-- **Proposition 3.9**, uniqueness: the layers of a normal form are
determined by its action on the Pauli group. -/
theorem nfx_unique : ∀ (n : ℕ) (x x' : NFX n),
    actC n (NFX.circ n x) = actC n (NFX.circ n x') → x = x'
  | 0, (), (), _ => rfl
  | n + 1, x, x', h => by
    obtain ⟨L, M, y⟩ := x
    obtain ⟨L', M', y'⟩ := x'
    have hP : ∀ P, actC (n + 1) (NFX.circ (n + 1) (L, M, y)) P =
        actC (n + 1) (NFX.circ (n + 1) (L', M', y')) P := fun P => by rw [h]
    simp only [NFX.actC_succ] at hP
    -- the `Z`-normal layers agree
    have hL : L = L' := by
      have e := hP L.pre
      rw [ZN.act_pre, show ZN.ztop (n + 1) = Ztop n from rfl, XN.act_Ztop, actC_top_Zbot,
        ← actC_top_Zbot (NFX.circ n y')] at e
      have e1 := actC_injective _ e
      rw [← XN.act_Ztop M'] at e1
      have e2 := actC_injective _ e1
      apply ZN.pre_injective
      apply actC_injective L'.circ
      rw [← e2, ZN.act_pre]
      rfl
    subst hL
    -- the `X`-normal layers agree
    have hM : M = M' := by
      obtain ⟨q, hq⟩ := (actC_bijective L.circ).2 M.pre
      have e := hP q
      rw [hq, XN.act_pre, actC_top_Xbot, ← actC_top_Xbot (NFX.circ n y')] at e
      have e1 := actC_injective _ e
      rw [← XN.act_pre M'] at e1
      exact XN.pre_injective (actC_injective _ e1).symm
    subst hM
    -- the rest agrees
    have hy : actC n (NFX.circ n y) = actC n (NFX.circ n y') := by
      funext p
      obtain ⟨P, hPp⟩ := (actC_bijective (L.circ ⨾ M.circ)).2 (p.cons 0 0)
      have e := hP P
      rw [show actC (n + 1) M.circ (actC (n + 1) L.circ P) = p.cons 0 0 by
        rw [← actC_seq]; exact hPp, actC_top, actC_top] at e
      exact (PD.cons_inj e).2.2
    rw [nfx_unique n y y' hy]

/-! ### Normal forms with their phase -/

/-- A normal form (Definition 3.3, Figure 11): the layers, and the global
phase `(-ω)^t`, `t ∈ ℤ₆`. -/
def NF (n : ℕ) := NFX n × Fin 6

/-- The circuit of a normal form. -/
def NF.circ {n : ℕ} (N : NF n) : Circ n := NFX.circ n N.1 * negω ^ (N.2 : ℕ)

theorem sem_negω_pow (n t : ℕ) :
    (sem n (negω ^ t) : Op ℂ 3 n) = (-ωℂ) ^ t • (1 : Op ℂ 3 n) := by
  rw [map_pow, SubmonoidClass.coe_pow]
  show ((-ωℂ) • (1 : Op ℂ 3 n)) ^ t = _
  rw [smul_pow, one_pow]

theorem actC_negω_pow (n t : ℕ) (P : PD n) : actC n (negω ^ t) P = P := by
  have h1 : star ((-ωℂ) ^ t) * (-ωℂ) ^ t = 1 := by
    rw [star_pow, ← mul_pow, star_neg, neg_mul_neg, star_ωℂ, ← pow_succ, ωℂ_pow_three, one_pow]
  apply PD.op_inj
  rw [← sem_conj, sem_negω_pow]
  simp only [star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul, h1,
    one_smul]

theorem negω_pow_ne_one : ∀ k : ℕ, 0 < k → k < 6 → (-ωℂ) ^ k ≠ 1 := by
  intro k h0 h6 h
  interval_cases k
  · exact ωℂ_sq_ne_one (by linear_combination (1 - ωℂ) * h)
  · exact ωℂ_sq_ne_one (by linear_combination h)
  · have h2 : (2 : ℂ) = 0 := by linear_combination -h - ωℂ_pow_three
    norm_num at h2
  · exact ωℂ_ne_one (by linear_combination h - ωℂ * ωℂ_pow_three)
  · have h2 : ωℂ ^ 2 + 1 = 0 := by linear_combination -h - ωℂ ^ 2 * ωℂ_pow_three
    have h0 : ωℂ = 0 := by linear_combination ωℂ_sum - h2
    have := ωℂ_pow_three
    rw [h0] at this
    norm_num at this

theorem negω_pow_inj {t t' : ℕ} (ht : t < 6) (ht' : t' < 6) (h : (-ωℂ) ^ t = (-ωℂ) ^ t') :
    t = t' := by
  have hne : ∀ k : ℕ, (-ωℂ) ^ k ≠ 0 := fun k =>
    pow_ne_zero _ (neg_ne_zero.2 fun h0 => by
      have := ωℂ_pow_three; rw [h0] at this; norm_num at this)
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exfalso
    apply negω_pow_ne_one (t' - t) (by omega) (by omega)
    apply mul_left_cancel₀ (hne t)
    rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, h]
  · exact heq
  · exfalso
    apply negω_pow_ne_one (t - t') (by omega) (by omega)
    apply mul_left_cancel₀ (hne t')
    rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one, h]

theorem actC_eq_of_sem_eq {n : ℕ} {w w' : Circ n} (h : sem n w = sem n w') :
    actC n w = actC n w' := by
  funext P
  apply PD.op_inj
  rw [← sem_conj, ← sem_conj, h]

/-- **Proposition 3.9**, uniqueness with the phase: a normal form is
determined by its operator. -/
theorem nf_unique {n : ℕ} {N N' : NF n} (h : sem n N.circ = sem n N'.circ) : N = N' := by
  obtain ⟨x, t⟩ := N
  obtain ⟨x', t'⟩ := N'
  have hact := actC_eq_of_sem_eq h
  have hx : x = x' := by
    apply nfx_unique
    funext P
    have e := congrFun hact P
    simp only [NF.circ, actC_mul, actC_negω_pow] at e
    exact e
  subst hx
  have e := congrArg Subtype.val h
  simp only [NF.circ, map_mul, Submonoid.coe_mul, sem_negω_pow] at e
  have e2 : (-ωℂ) ^ (t : ℕ) • (1 : Op ℂ 3 n) = (-ωℂ) ^ (t' : ℕ) • (1 : Op ℂ 3 n) := by
    have := congrArg (fun A => star (sem n (NFX.circ n x) : Op ℂ 3 n) * A) e
    simpa only [← mul_assoc, (sem_unitary _).1, one_mul] using this
  have e3 := congrFun (congrFun e2 0) 0
  simp only [smul_apply, one_apply_eq, smul_eq_mul, mul_one] at e3
  rw [Fin.ext (negω_pow_inj t.2 t'.2 e3)]

end

end QCert.QutritClifford
