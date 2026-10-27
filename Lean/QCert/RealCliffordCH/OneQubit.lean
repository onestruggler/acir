/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness on zero and one qubit (Lemma 7.1)

On no wire there is only the empty circuit.  On one wire, Lemma 7.1: modulo
Equations (1), (2) and (3) every circuit is `(H Z)^k` or `(H Z)^k` after an
`H` (drawn `H, (H, Z)^k`), `k < 8`, and these sixteen normal forms have
distinct semantics.  In operator order, with `r = Z H`, the normal forms are
`r^k` and `r^k H`; the proof computes in the quotient monoid of the theory,
where `H r = r^7 H` and `Z = r H`.
-/
import QCert.RealCliffordCH.Soundness
import QCert.RealCliffordCH.Grouplike
import Mathlib.NumberTheory.Real.Irrational

namespace QCert.RealCliffordCH

open Circuit Sim Matrix

/-! ## From the real semantics to ℚ(√2) -/

theorem QSqrt2.toR_injective : Function.Injective QSqrt2.toR := by
  intro a b hab
  simp only [QSqrt2.toR, Quadratic.lift_apply] at hab
  by_cases h1 : a.a1 = b.a1
  · rw [h1] at hab
    have h0 : (a.a0 : ℝ) = b.a0 := by linarith
    exact Quadratic.ext (by exact_mod_cast h0) h1
  · exfalso
    have hne : ((a.a1 : ℝ) - b.a1) ≠ 0 := by
      intro h; apply h1; exact_mod_cast sub_eq_zero.1 h
    have : Real.sqrt 2 = ((b.a0 - a.a0) / (a.a1 - b.a1) : ℚ) := by
      push_cast
      field_simp
      linarith
    exact irrational_sqrt_two.ne_rat _ this

/-- Equal real semantics give equal operators over ℚ(√2). -/
theorem eval_eq_of_sem {n : ℕ} {w v : Circ n} (h : S.sem n w = S.sem n v) :
    opsQ.eval n w = opsQ.eval n v := by
  have h' := congrArg Subtype.val h
  rw [S.sem_val, S.sem_val, toOps_eq, GateOps.eval_map, GateOps.eval_map] at h'
  funext s t
  exact QSqrt2.toR_injective (congrFun (congrFun h' s) t)

/-- The columns of a circuit's operator, computed by simulation. -/
def fingerprint {n : ℕ} (w : Circ n) : List (List Q) :=
  (allStates n).map fun t => toList (actW w (basis t))

theorem ofFun_toFun : ∀ {n : ℕ} (u : Vec n), ofFun (toFun u) = u
  | 0, _ => rfl
  | _ + 1, u => by
    show (ofFun fun s => toFun u (Fin.cons 0 s), ofFun fun s => toFun u (Fin.cons 1 s)) = u
    simp only [toFun_cons, if_neg one_ne_zero_fin, if_true, ofFun_toFun, Prod.mk.eta]

theorem fingerprint_eq {n : ℕ} {w v : Circ n} (h : opsQ.eval n w = opsQ.eval n v) :
    fingerprint w = fingerprint v := by
  unfold fingerprint
  congr 1; funext t
  have : toFun (actW w (basis t)) = toFun (actW v (basis t)) := by
    funext s; rw [← eval_apply, ← eval_apply, h]
  rw [← ofFun_toFun (actW w (basis t)), this, ofFun_toFun]

/-! ## Normal forms -/

section Quotient

/-- The quotient monoid of one-wire circuits by the theory. -/
abbrev Q1 := (conGen (theory 1)).Quotient

/-- The class of a circuit. -/
def cls : Circ 1 →* Q1 := (conGen (theory 1)).mk'

theorem cls_eq {w v : Circ 1} : cls w = cls v ↔ Derivable (theory 1) w v :=
  (conGen (theory 1)).eq

/-- `r = Z H`, drawn `H, Z`. -/
abbrev rq : Q1 := cls (z * h)

abbrev hq : Q1 := cls h

abbrev zq : Q1 := cls z

theorem hq_hq : hq * hq = 1 := by
  rw [← map_mul, ← map_one cls, cls_eq]
  exact derivable_rule Rule.e1 0

theorem zq_zq : zq * zq = 1 := by
  rw [← map_mul, ← map_one cls, cls_eq]
  exact derivable_rule Rule.e2 0

theorem rq_pow_eight : rq ^ 8 = 1 := by
  rw [← map_pow, ← map_one cls, cls_eq]
  exact derivable_rule Rule.e3 0

theorem rq_eq : rq = zq * hq := map_mul _ _ _

theorem rq_pow_seven : rq ^ 7 = hq * zq := by
  calc rq ^ 7 = rq ^ 7 * (zq * (hq * hq) * zq) := by rw [hq_hq, mul_one, zq_zq, mul_one]
    _ = rq ^ 7 * (rq * (hq * zq)) := by rw [rq_eq]; simp only [mul_assoc]
    _ = rq ^ 8 * (hq * zq) := by rw [pow_succ rq 7, mul_assoc]
    _ = hq * zq := by rw [rq_pow_eight, one_mul]

theorem hq_rq : hq * rq = rq ^ 7 * hq := by
  rw [rq_pow_seven, rq_eq, mul_assoc]

theorem hq_rq_pow (k : ℕ) : hq * rq ^ k = rq ^ (7 * k) * hq := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, hq_rq, ← mul_assoc, ← pow_add]
    ring_nf

theorem zq_eq : zq = rq * hq := by
  rw [rq_eq, mul_assoc, hq_hq, mul_one]

theorem rq_pow_mod (a : ℕ) : rq ^ a = rq ^ (a % 8) := by
  conv_lhs => rw [← Nat.div_add_mod a 8, pow_add, pow_mul, rq_pow_eight, one_pow, one_mul]

/-- The normal forms `r^k` and `r^k H`. -/
def nfq (b : Bool) (k : ℕ) : Q1 := rq ^ k * (if b then hq else 1)

theorem hq_nfq (b : Bool) (k : ℕ) : hq * nfq b k = nfq (!b) ((7 * k) % 8) := by
  unfold nfq
  rw [← mul_assoc, hq_rq_pow, rq_pow_mod, mul_assoc]
  cases b
  · simp
  · simp [hq_hq]

theorem zq_nfq (b : Bool) (k : ℕ) : zq * nfq b k = nfq (!b) ((1 + 7 * k) % 8) := by
  unfold nfq
  rw [zq_eq, mul_assoc, ← mul_assoc hq, hq_rq_pow, ← mul_assoc, ← mul_assoc, ← pow_succ',
    rq_pow_mod (7 * k + 1), mul_assoc, show 7 * k + 1 = 1 + 7 * k by ring]
  cases b
  · simp
  · simp [hq_hq]

/-- Every one-wire circuit is equal to a normal form. -/
theorem exists_nf (w : Circ 1) : ∃ b : Bool, ∃ k : Fin 8, cls w = nfq b k := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨false, 0, by simp [nfq]⟩
  | mul_of x w ih =>
    obtain ⟨b, k, hk⟩ := ih
    rw [map_mul, hk]
    cases x with
    | gate0 c => exact nomatch c
    | gate1 g =>
      cases g
      · exact ⟨!b, ⟨(7 * k) % 8, Nat.mod_lt _ (by norm_num)⟩, hq_nfq b k⟩
      · exact ⟨!b, ⟨(1 + 7 * k) % 8, Nat.mod_lt _ (by norm_num)⟩, zq_nfq b k⟩
    | up g => cases g with | gate0 c => exact nomatch c

end Quotient

/-- The normal forms as circuits. -/
def nfw (b : Bool) (k : ℕ) : Circ 1 := (z * h) ^ k * (if b then h else 1)

theorem cls_nfw (b : Bool) (k : ℕ) : cls (nfw b k) = nfq b k := by
  unfold nfw nfq; rw [map_mul, map_pow]; cases b <;> simp

/-- The sixteen normal forms have distinct operators. -/
theorem nfw_distinct : ∀ b : Bool, ∀ k : Fin 8, ∀ b' : Bool, ∀ k' : Fin 8,
    fingerprint (nfw b k) = fingerprint (nfw b' k') → b = b' ∧ k = k' := by
  decide +kernel

/-- Lemma 7.1 (1-qubit completeness). -/
theorem complete_one {w v : Circ 1} (h : S.sem 1 w = S.sem 1 v) : Derivable (theory 1) w v := by
  obtain ⟨b, k, hw⟩ := exists_nf w
  obtain ⟨b', k', hv⟩ := exists_nf v
  rw [← cls_nfw] at hw hv
  have dw := cls_eq.1 hw
  have dv := cls_eq.1 hv
  have sw : S.sem 1 w = S.sem 1 (nfw b k) :=
    derivable_sound (sem := S.gen (n := 1)) (fun _ _ h => sound 1 h) dw
  have sv : S.sem 1 v = S.sem 1 (nfw b' k') :=
    derivable_sound (sem := S.gen (n := 1)) (fun _ _ h => sound 1 h) dv
  have := nfw_distinct b k b' k'
    (fingerprint_eq (eval_eq_of_sem (sw.symm.trans (h.trans sv))))
  obtain ⟨rfl, rfl⟩ := this
  exact dw.trans dv.symm

/-- Completeness on no wire: the empty circuit is the only one. -/
theorem complete_zero {w v : Circ 0} : Derivable (theory 0) w v := by
  have e : ∀ u : Circ 0, u = 1 := by
    intro u
    induction u using FreeMonoid.inductionOn' with
    | one => rfl
    | mul_of x _ _ => cases x with | gate0 c => exact nomatch c
  rw [e w, e v]

end QCert.RealCliffordCH
