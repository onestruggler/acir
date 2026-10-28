/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The matrix semantics is injective on the Pauli group

Lemma 3.11 and the end of Section 4.2: every element of the Pauli group of
circuits is `(-ω)^K` times a normal form `⊗ᵢ Xᵢ^{aᵢ} Zᵢ^{bᵢ}` (`Wc v`), and
the normal form implements the Weyl operator `W(v)` (`sem_Wc`).  So a Pauli
circuit implementing the identity has `(-ω)^K W(v) = 1`: distinct Weyl
operators are not proportional, so `v = 0`, and `(-ω)^K = 1` forces
`2p ∣ K`, whence the circuit is `(-ω)^{2p q} = 1` by (C0) (`pauli_inj`).

Modulo the scalars, the normal forms make a homomorphism from `V p n`
(`qs_Wc_add`), since `Z X = X Z` and `X^p = Z^p = 1` there
(`PauliOne.lean`) and circuits on disjoint wires commute; its range holds
every Pauli generator, hence the whole Pauli group (`qs_pauliSub_range`).
-/
import QCert.QuditClifford.PauliNormal

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Products of Weyl operators -/

theorem weylOp_mul {n : ℕ} (u v : V p n) :
    weylOp p u * weylOp p v = ψ p (∑ i, (u i).2 * (v i).1) • weylOp p (u + v) := by
  rw [weylOp_def, weylOp_def, weylOp_def, mono_mul, smul_mono]
  apply mono_ext p
  · intro t; funext i
    apply z_injective p
    simp only [Function.comp_apply, z_wtr, Pi.add_apply, Prod.fst_add]
    ring
  · intro t
    dsimp only
    rw [← ψ_add, ← ψ_add]
    congr 1
    simp only [z_wtr, Pi.add_apply, Prod.snd_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem weylOp_zero {n : ℕ} : weylOp p (0 : V p n) = 1 := by
  rw [weylOp_def, one_eq_mono]
  apply mono_ext p
  · intro t; funext i
    apply z_injective p
    simp [z_wtr]
  · intro t; simp [ψ_zero]

theorem sem_X_weyl (hp2 : p ≠ 2) :
    ((sem p 1 (X p) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      weylOp p (fun _ => ((1 : ZMod p), (0 : ZMod p))) := by
  rw [sem_X p hp2, weylOp_def]
  have hz1 : z p (1 : Fin p) = 1 := by rw [z, Fin.val_one', ZMod.natCast_mod, Nat.cast_one]
  apply mono_ext p
  · intro t; funext i
    rw [Subsingleton.elim i 0]
    apply z_injective p
    simp [z_wtr, z_add, hz1]
  · intro t; simp [ψ_zero]

theorem sem_Z_weyl (hp2 : p ≠ 2) :
    ((sem p 1 (Z p) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      weylOp p (fun _ => ((0 : ZMod p), (1 : ZMod p))) := by
  rw [sem_Z p hp2, weylOp_def]
  apply mono_ext p
  · intro t; funext i
    apply z_injective p
    simp [z_wtr]
  · intro t; simp

theorem weylOp_X_pow (k : ℕ) :
    weylOp p (fun _ : Fin 1 => ((1 : ZMod p), (0 : ZMod p))) ^ k =
      weylOp p (fun _ => ((k : ZMod p), (0 : ZMod p))) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero]
    exact (weylOp_zero p).symm
  | succ k ih =>
    rw [pow_succ, ih, weylOp_mul]
    dsimp only
    simp only [zero_mul, Finset.sum_const_zero, ψ_zero, one_smul]
    congr 1; funext i; ext <;> simp

theorem weylOp_Z_pow (k : ℕ) :
    weylOp p (fun _ : Fin 1 => ((0 : ZMod p), (1 : ZMod p))) ^ k =
      weylOp p (fun _ => ((0 : ZMod p), (k : ZMod p))) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero]
    exact (weylOp_zero p).symm
  | succ k ih =>
    rw [pow_succ, ih, weylOp_mul]
    dsimp only
    simp only [mul_zero, Finset.sum_const_zero, ψ_zero, one_smul]
    congr 1; funext i; ext <;> simp

/-! ### The normal forms -/

/-- `X^a Z^b` on one wire. -/
def xzc (u : ZMod p × ZMod p) : Circ 1 := X p ^ u.1.val * Z p ^ u.2.val

/-- The Pauli normal form `⊗ᵢ Xᵢ^{aᵢ} Zᵢ^{bᵢ}` (Definition 3.10), wire `0` last. -/
def Wc : (n : ℕ) → V p n → Circ n
  | 0, _ => 1
  | n + 1, v => Circuit.shift (Wc n (Fin.tail v)) * Circuit.pad n (xzc p (v 0))

theorem xzc_zero : xzc p 0 = 1 := by
  simp [xzc]

theorem Wc_zero : (n : ℕ) → Wc p n 0 = 1
  | 0 => rfl
  | n + 1 => by
    rw [Wc, show Fin.tail (0 : V p (n + 1)) = 0 from rfl, Wc_zero n,
      show (0 : V p (n + 1)) 0 = 0 from rfl, xzc_zero, map_one, map_one, one_mul]

theorem Wc_cons_zero (n : ℕ) (u : ZMod p × ZMod p) :
    Wc p (n + 1) (Fin.cons u 0) = Circuit.pad n (xzc p u) := by
  rw [Wc, Fin.tail_cons, Fin.cons_zero, Wc_zero, map_one, one_mul]

theorem Wc_zero_cons (n : ℕ) (v : V p n) :
    Wc p (n + 1) (Fin.cons 0 v) = Circuit.shift (Wc p n v) := by
  rw [Wc, Fin.tail_cons, Fin.cons_zero, xzc_zero, map_one, mul_one]

theorem onWire_xzc : (n : ℕ) → (i : Fin n) → (u : ZMod p × ZMod p) →
    ∃ v : V p n, onWire n i (xzc p u) = Wc p n v
  | n + 1, ⟨0, _⟩, u => ⟨Fin.cons u 0, (Wc_cons_zero p n u).symm⟩
  | n + 1, ⟨j + 1, h⟩, u => by
    obtain ⟨v, hv⟩ := onWire_xzc n ⟨j, by omega⟩ u
    refine ⟨Fin.cons 0 v, ?_⟩
    show Circuit.shift (onWire n ⟨j, by omega⟩ (xzc p u)) = _
    rw [Wc_zero_cons, hv]

/-! ### The semantics of the normal forms -/

theorem sem_xzc (hp2 : p ≠ 2) (u : ZMod p × ZMod p) :
    ((sem p 1 (xzc p u) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) = weylOp p (fun _ => u) := by
  simp only [xzc, map_mul, map_pow, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  rw [sem_X_weyl p hp2, sem_Z_weyl p hp2, weylOp_X_pow, weylOp_Z_pow, weylOp_mul]
  dsimp only
  simp only [mul_zero, Finset.sum_const_zero, ψ_zero, one_smul]
  congr 1; funext i; ext <;> simp

omit hp in
theorem weylLo_one {n : ℕ} (v : V p (n + 1)) : weylLo p (k := 1) v = fun _ => v 0 := by
  funext i; rw [Subsingleton.elim i 0]; rfl

omit hp in
theorem weylHi_one {n : ℕ} (v : V p (n + 1)) : weylHi p (k := 1) v = Fin.tail v := by
  funext j; simp only [weylHi, Fin.tail]; congr 1; ext; simp [Nat.add_comm]

theorem sem_Wc (hp2 : p ≠ 2) : (n : ℕ) → (v : V p n) →
    ((sem p n (Wc p n v) : unitaryGroup (State p n) ℂ) : Op ℂ p n) = weylOp p v
  | 0, v => by
    rw [show v = 0 from Subsingleton.elim _ _, weylOp_zero]
    simp [Wc]
  | n + 1, v => by
    rw [Wc, map_mul, Submonoid.coe_mul, (gateSem p).sem_shift, (gateSem p).sem_pad]
    show onTop 1 ((sem p n (Wc p n (Fin.tail v)) : unitaryGroup (State p n) ℂ) : Op ℂ p n) *
      onBottom ((sem p 1 (xzc p (v 0)) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) = _
    rw [sem_Wc hp2 n (Fin.tail v), sem_xzc p hp2, weylOp_split p (k := 1) v, weylLo_one, weylHi_one,
      onBottom_onTop_comm]

theorem sem_negω_smul {n : ℕ} :
    ((sem p n negω : unitaryGroup (State p n) ℂ) : Op ℂ p n) = (-ωℂ p) • (1 : Op ℂ p n) := rfl

/-- `(-ω)^K = 1` only when `2p ∣ K`. -/
theorem two_p_dvd (hp2 : p ≠ 2) {K : ℕ} (h : (-ωℂ p) ^ K = 1) : 2 * p ∣ K := by
  have hprim := ωℂ_primitive p
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  rcases Nat.even_or_odd K with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [Even.neg_pow ⟨m, rfl⟩] at h
    have h1 : p ∣ 2 * m := by rw [two_mul]; exact (hprim.pow_eq_one_iff_dvd _).1 h
    rcases (Nat.Prime.dvd_mul hp.out).1 h1 with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2) hp2
    · obtain ⟨q, rfl⟩ := h2
      exact ⟨q, by ring⟩
  · exfalso
    rw [Odd.neg_pow ⟨m, rfl⟩] at h
    have h1 : ωℂ p ^ (2 * m + 1) = -1 := neg_eq_iff_eq_neg.1 h
    have h2 : (ωℂ p ^ (2 * m + 1)) ^ p = 1 := by
      rw [← pow_mul, show (2 * m + 1) * p = p * (2 * m + 1) by ring, pow_mul, ωℂ_pow_p, one_pow]
    rw [h1, Odd.neg_one_pow hodd] at h2
    norm_num at h2

/-! ### Modulo the scalars -/

variable {p} {g : ZMod p} [OddGen p g]

local notation "𝐗" => qs p g 1 (X p)
local notation "𝐙" => qs p g 1 (Z p)

theorem qs_xzc_add (u v : ZMod p × ZMod p) :
    qs p g 1 (xzc p (u + v)) = qs p g 1 (xzc p u) * qs p g 1 (xzc p v) := by
  simp only [xzc, map_mul, map_pow, Prod.fst_add, Prod.snd_add]
  rw [pow_val_add qsX_pow_p, pow_val_add qsZ_pow_p]
  have hc : Commute (𝐙 ^ u.2.val) (𝐗 ^ v.1.val) :=
    (show Commute 𝐙 𝐗 from qs_ZX).pow_pow _ _
  calc 𝐗 ^ u.1.val * 𝐗 ^ v.1.val * (𝐙 ^ u.2.val * 𝐙 ^ v.2.val)
      = 𝐗 ^ u.1.val * (𝐗 ^ v.1.val * 𝐙 ^ u.2.val) * 𝐙 ^ v.2.val := by simp only [mul_assoc]
    _ = 𝐗 ^ u.1.val * (𝐙 ^ u.2.val * 𝐗 ^ v.1.val) * 𝐙 ^ v.2.val := by rw [hc.eq]
    _ = _ := by simp only [mul_assoc]

theorem qs_Wc_add : (n : ℕ) → (u v : V p n) →
    qs p g n (Wc p n (u + v)) = qs p g n (Wc p n u) * qs p g n (Wc p n v)
  | 0, u, v => by simp only [Wc, map_one, mul_one]
  | n + 1, u, v => by
    simp only [Wc, map_mul]
    show ιs p g n (qs p g n (Wc p n (Fin.tail (u + v)))) * pads p g n 1 (qs p g 1 (xzc p ((u + v) 0))) =
      ιs p g n (qs p g n (Wc p n (Fin.tail u))) * pads p g n 1 (qs p g 1 (xzc p (u 0))) *
        (ιs p g n (qs p g n (Wc p n (Fin.tail v))) * pads p g n 1 (qs p g 1 (xzc p (v 0))))
    rw [show Fin.tail (u + v) = Fin.tail u + Fin.tail v from rfl,
      show (u + v) 0 = u 0 + v 0 from rfl, qs_Wc_add n, qs_xzc_add, map_mul, map_mul]
    have hc := commute_pads_ιs (p := p) (g := g) (n := n) (qs p g 1 (xzc p (u 0)))
      (qs p g n (Wc p n (Fin.tail v)))
    calc ιs p g n (qs p g n (Wc p n (Fin.tail u))) * ιs p g n (qs p g n (Wc p n (Fin.tail v))) *
          (pads p g n 1 (qs p g 1 (xzc p (u 0))) * pads p g n 1 (qs p g 1 (xzc p (v 0))))
        = ιs p g n (qs p g n (Wc p n (Fin.tail u))) *
            (ιs p g n (qs p g n (Wc p n (Fin.tail v))) * pads p g n 1 (qs p g 1 (xzc p (u 0)))) *
            pads p g n 1 (qs p g 1 (xzc p (v 0))) := by simp only [mul_assoc]
      _ = ιs p g n (qs p g n (Wc p n (Fin.tail u))) *
            (pads p g n 1 (qs p g 1 (xzc p (u 0))) * ιs p g n (qs p g n (Wc p n (Fin.tail v)))) *
            pads p g n 1 (qs p g 1 (xzc p (v 0))) := by rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

theorem qs_Wc_neg (n : ℕ) (v : V p n) : qs p g n (Wc p n (-v)) = (qs p g n (Wc p n v))⁻¹ := by
  have h := qs_Wc_add (g := g) n v (-v)
  rw [add_neg_cancel, Wc_zero, map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem qs_onWire_congr : (n : ℕ) → (i : Fin n) → {c c' : Circ 1} → qs p g 1 c = qs p g 1 c' →
    qs p g n (onWire n i c) = qs p g n (onWire n i c')
  | n + 1, ⟨0, _⟩, c, c', h => by
    show pads p g n 1 (qs p g 1 c) = pads p g n 1 (qs p g 1 c'); rw [h]
  | n + 1, ⟨j + 1, hj⟩, c, c', h => by
    show ιs p g n (qs p g n (onWire n ⟨j, by omega⟩ c)) = ιs p g n (qs p g n (onWire n ⟨j, by omega⟩ c'))
    rw [qs_onWire_congr n ⟨j, by omega⟩ h]

theorem qs_X_xzc : qs p g 1 (X p) = qs p g 1 (xzc p (1, 0)) := by
  simp only [xzc, map_mul, map_pow]
  show qs p g 1 (X p) = 𝐗 ^ (1 : ZMod p).val * 𝐙 ^ (0 : ZMod p).val
  rw [pow_val_one qsX_pow_p, ZMod.val_zero, pow_zero, mul_one]

theorem qs_Z_xzc : qs p g 1 (Z p) = qs p g 1 (xzc p (0, 1)) := by
  simp only [xzc, map_mul, map_pow]
  show qs p g 1 (Z p) = 𝐗 ^ (0 : ZMod p).val * 𝐙 ^ (1 : ZMod p).val
  rw [pow_val_one qsZ_pow_p, ZMod.val_zero, pow_zero, one_mul]

/-- Modulo the scalars, every Pauli circuit is a normal form. -/
theorem qs_pauliSub_range {n : ℕ} {x : CG p g n} (hx : x ∈ PauliSub p g n) :
    ∃ v : V p n, QuotientGroup.mk' (Sc p g n) x = qs p g n (Wc p n v) := by
  have hx' : x ∈ Subgroup.closure (PauliSet p g n) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl | rfl⟩
    · exact ⟨0, by rw [Wc_zero, map_one]; exact qs_negω⟩
    · obtain ⟨v, hv⟩ := onWire_xzc p n i (1, 0)
      exact ⟨v, by rw [← hv]; exact qs_onWire_congr n i qs_X_xzc⟩
    · obtain ⟨v, hv⟩ := onWire_xzc p n i (0, 1)
      exact ⟨v, by rw [← hv]; exact qs_onWire_congr n i qs_Z_xzc⟩
  | one => exact ⟨0, by rw [Wc_zero, map_one, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_mul, hu, hv, qs_Wc_add]⟩
  | inv x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨-v, by rw [map_inv, hv, qs_Wc_neg]⟩

theorem νc_zpow_nat {n : ℕ} (k : ℤ) : ∃ K : ℕ, νc p g n ^ k = νc p g n ^ K := by
  have hpos : (0 : ℤ) < ((2 * p : ℕ) : ℤ) := by
    have := hp.out.pos; omega
  refine ⟨(k % ((2 * p : ℕ) : ℤ)).toNat, ?_⟩
  have h0 : 0 ≤ k % ((2 * p : ℕ) : ℤ) := Int.emod_nonneg _ hpos.ne'
  rw [← zpow_natCast, Int.toNat_of_nonneg h0]
  conv_lhs => rw [← Int.emod_add_mul_ediv k ((2 * p : ℕ) : ℤ)]
  rw [zpow_add, zpow_mul, zpow_natCast, νc_pow_two_p, one_zpow, mul_one]

variable (p g) in
/-- Lemma 3.11 and the end of Section 4.2: a Pauli circuit that implements
the identity is equal to the empty circuit by the rules. -/
theorem pauli_inj {n : ℕ} {x : CG p g n} (hx : x ∈ PauliSub p g n) (h : semG n x = 1) : x = 1 := by
  have hp2 := OddGen.hp2 (p := p) g
  obtain ⟨v, hv⟩ := qs_pauliSub_range hx
  have hv' : QuotientGroup.mk' (Sc p g n) (mk p g n (Wc p n v)) = QuotientGroup.mk' (Sc p g n) x :=
    hv.symm
  have hmem : (mk p g n (Wc p n v))⁻¹ * x ∈ Sc p g n := QuotientGroup.eq.1 hv'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  obtain ⟨K, hK⟩ := νc_zpow_nat (g := g) (n := n) k
  have hxe : x = mk p g n (Wc p n v) * νc p g n ^ K := by
    rw [← hK, hk, mul_inv_cancel_left]
  rw [hxe, map_mul, map_pow, semG_mk, semG_mk] at h
  have h' := congrArg (fun U : unitaryGroup (State p n) ℂ => (U : Op ℂ p n)) h
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, Submonoid.coe_one] at h'
  rw [sem_Wc p hp2 n v, sem_negω_smul, smul_pow, one_pow, mul_smul_comm, mul_one] at h'
  have hc : (-ωℂ p) ^ K ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.2 ((ωℂ_primitive p).ne_zero hp.out.ne_zero))
  have hw : weylOp p v = ((-ωℂ p) ^ K)⁻¹ • weylOp p 0 := by
    rw [weylOp_zero, ← h', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hv0 : v = 0 := weylOp_eq_smul p hw
  subst hv0
  rw [weylOp_zero] at h'
  have hK1 : (-ωℂ p) ^ K = 1 := by
    have e := congrFun (congrFun h' (fun _ => ⟨0, hp.out.pos⟩)) (fun _ => ⟨0, hp.out.pos⟩)
    simpa using e
  obtain ⟨q, rfl⟩ := two_p_dvd p hp2 hK1
  rw [hxe, Wc_zero, map_one, one_mul, pow_mul, νc_pow_two_p, one_pow]

end QCert.QuditClifford
