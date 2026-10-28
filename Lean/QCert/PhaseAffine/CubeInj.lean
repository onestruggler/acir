/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The pair of a cubic diagonal element determines it

The third difference of the phase, `θ x a b c` (in the directions `a, b, c`
at `0`), vanishes on the quadratic diagonal group, so it is defined on the
classes (`thetaV`); on `T` placed on `u` it is `(u · a)(u · b)(u · c)`.  On
the normal form `↑x' + α T(e₀) + ℓ β + Σ Gⱼₖ B(eⱼ, eₖ)` it reads off `α`
(at `e₀, e₀, e₀`), `β` (at `e₀, e₀, eⱼ`) and `Gⱼₖ + Gₖⱼ` (at `e₀, eⱼ, eₖ`),
so a cubic diagonal element whose phase has no cubic part is quadratic
(`dg3_quad`), and one with the trivial pair is trivial (`dg3_inj`):
Proposition 1 of Blake (arXiv:2603.06466) for the cubic fragment.
-/
import QCert.PhaseAffine.CubeSpan

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

/-- The value of a form. -/
def fv {n : ℕ} (u a : Lab d n) : ZMod d := ∑ j, u j * a j

theorem fv_def {n : ℕ} (u a : Lab d n) : ∑ j, u j * a j = fv u a := rfl

theorem fv_single_right {n : ℕ} (u : Lab d n) (j : Fin n) : fv u (Pi.single j 1) = u j := by
  simp [fv, Pi.single_apply]

theorem fv_add {n : ℕ} (u v a : Lab d n) : fv (u + v) a = fv u a + fv v a := fsum_add u v a

theorem fv_sub {n : ℕ} (u v a : Lab d n) : fv (u - v) a = fv u a - fv v a := by
  simp only [fv, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem fv_add_right {n : ℕ} (u a b : Lab d n) : fv u (a + b) = fv u a + fv u b := by
  simp only [fv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem fv_zero_right {n : ℕ} (u : Lab d n) : fv u 0 = 0 := by simp [fv]

theorem fv_single {n : ℕ} (i : Fin n) (a : Lab d n) : fv (Pi.single i 1) a = a i := by
  rw [fv, fsum_single, one_mul]

theorem fv_cons {n : ℕ} (x y : ZMod d) (u a : Lab d n) :
    fv (Fin.cons x u : Lab d (n + 1)) (Fin.cons y a) = x * y + fv u a := fsum_cons x y u a

section Theta

variable (hA : Admissible d lv) (h3 : 3 ≤ lv)

/-- The third difference at `0` of the phase of `x`. -/
noncomputable def theta {n : ℕ} (x : Q d lv n) (a b c : Lab d n) : ZMod d :=
  (semQ hA n x).q (a + b + c) - (semQ hA n x).q (a + b) - (semQ hA n x).q (a + c) -
    (semQ hA n x).q (b + c) + (semQ hA n x).q a + (semQ hA n x).q b + (semQ hA n x).q c -
    (semQ hA n x).q 0

variable {hA h3}

theorem theta_mul {n : ℕ} {x y : Q d lv n} (hx : x ∈ Dg3 h3 n) (hy : y ∈ Dg3 h3 n) :
    theta hA (x * y) = theta hA x + theta hA y := by
  funext a b c
  have e : (semQ hA n (x * y)).q = (semQ hA n x).q + (semQ hA n y).q := by
    rw [map_mul, dg3_diag hA h3 hx, dg3_diag hA h3 hy, PA.diag_mul]
    rfl
  simp only [theta, e, Pi.add_apply]
  ring

theorem theta_one {n : ℕ} : theta hA (1 : Q d lv n) = 0 := by
  funext a b c
  simp [theta]

theorem theta_inv {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) :
    theta hA x⁻¹ = -theta hA x := by
  have := theta_mul (hA := hA) (inv_mem hx) hx
  rw [inv_mul_cancel, theta_one] at this
  exact (neg_eq_of_add_eq_zero_left this.symm).symm

theorem theta_dg {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg (two_le_of_three h3) n) :
    theta hA x = 0 := by
  have h2 := two_le_of_three h3
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    funext a b c
    simp only [Pi.zero_apply]
    cases n with
    | zero =>
      simp only [dgens, Set.mem_singleton_iff] at hx
      subst hx
      simp only [theta, semQ_omega, PA.diag_q]; ring
    | succ n =>
      simp only [dgens, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
      rcases hx with (rfl | ⟨u, rfl⟩) | ⟨u, rfl⟩
      · simp only [theta, semQ_omega, PA.diag_q]; ring
      · simp only [theta, semQ_atomL_S, PA.diag_q]
        simp only [fv_def, fv_add_right, fv_zero_right]
        unfold binom2; ring
      · simp only [theta, semQ_atomL_Z, PA.diag_q]
        simp only [fv_def, fv_add_right, fv_zero_right]
        ring
  | one => exact theta_one
  | mul x y hx hy ihx ihy =>
    rw [theta_mul (dg_mem3 h3 hx) (dg_mem3 h3 hy), ihx, ihy, add_zero]
  | inv x hx ih => rw [theta_inv (dg_mem3 h3 hx), ih, neg_zero]

theorem theta_tau {n : ℕ} (u : Lab d (n + 1)) (a b c : Lab d (n + 1)) :
    theta hA (atomL (Gate.T h3) u) a b c = fv u a * fv u b * fv u c := by
  have h6 : (6 : ZMod d) * 6⁻¹ = 1 := by
    apply mul_inv_cancel₀
    rw [show (6 : ZMod d) = 2 * 3 by norm_num]
    exact mul_ne_zero (hA.two (two_le_of_three h3)) (hA.three h3)
  simp only [theta, semQ_atomL_T, PA.diag_q]
  simp only [fv_def, fv_add_right, fv_zero_right]
  unfold binom3
  linear_combination (fv u a * fv u b * fv u c) * h6

theorem theta_shift {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) (a b c : Lab d (n + 1)) :
    theta hA (shiftQ x) a b c = theta hA x (Fin.tail a) (Fin.tail b) (Fin.tail c) := by
  have e : (semQ hA (n + 1) (shiftQ x)).q = fun y => (semQ hA n x).q (Fin.tail y) := by
    rw [semQ_shiftQ, dg3_diag hA h3 hx, PA.onTop_diag]; rfl
  simp only [theta, e]
  rfl

/-- The third difference on classes. -/
noncomputable def thetaHom (n : ℕ) :
    D3 hA h3 n →* Multiplicative (Lab d n → Lab d n → Lab d n → ZMod d) where
  toFun x := Multiplicative.ofAdd (theta hA x.val)
  map_one' := by rw [D3.val_one, theta_one]; rfl
  map_mul' x y := by
    rw [D3.val_mul, theta_mul (D3.val_mem hA h3 x) (D3.val_mem hA h3 y)]; rfl

variable (hA h3) in
/-- The third difference of a class. -/
noncomputable def thetaV {n : ℕ} (v : V hA h3 n) : Lab d n → Lab d n → Lab d n → ZMod d :=
  Multiplicative.toAdd (QuotientGroup.lift (H3 hA h3 n) (thetaHom n)
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd (theta hA x.val) = 1
      rw [theta_dg (h3 := h3) (x := x.val) hx]; rfl) (Additive.toMul v))

theorem thetaV_cl {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) :
    thetaV hA h3 (kl hA h3 x) = theta hA x := by
  rw [kl_of hx]; rfl

theorem thetaV_add {n : ℕ} (v w : V hA h3 n) :
    thetaV hA h3 (v + w) = thetaV hA h3 v + thetaV hA h3 w := by
  unfold thetaV
  rw [show Additive.toMul (v + w) = Additive.toMul v * Additive.toMul w from rfl, map_mul,
    toAdd_mul]

theorem thetaV_zero {n : ℕ} : thetaV hA h3 (0 : V hA h3 n) = 0 := by
  unfold thetaV
  rw [show Additive.toMul (0 : V hA h3 n) = 1 from rfl, map_one, toAdd_one]

theorem thetaV_nsmul {n : ℕ} (k : ℕ) (v : V hA h3 n) :
    thetaV hA h3 (k • v) = k • thetaV hA h3 v := by
  induction k with
  | zero => rw [zero_smul, zero_smul, thetaV_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, thetaV_add, ih]

theorem thetaV_smul {n : ℕ} (c : ZMod d) (v : V hA h3 n) :
    thetaV hA h3 (c • v) = c • thetaV hA h3 v := by
  rw [← V_val_smul, thetaV_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod d), ZMod.natCast_zmod_val]

theorem thetaV_sub {n : ℕ} (v w : V hA h3 n) :
    thetaV hA h3 (v - w) = thetaV hA h3 v - thetaV hA h3 w := by
  rw [eq_sub_iff_add_eq, ← thetaV_add, sub_add_cancel]

theorem thetaV_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → V hA h3 n) :
    thetaV hA h3 (∑ i ∈ s, f i) = ∑ i ∈ s, thetaV hA h3 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaV_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, thetaV_add, ih]

theorem thetaV_tau {n : ℕ} (u a b c : Lab d (n + 1)) :
    thetaV hA h3 (tau (hA := hA) (h3 := h3) u) a b c = fv u a * fv u b * fv u c := by
  rw [tau, thetaV_cl (atomL_T_mem3 h3 u), theta_tau]

theorem thetaV_cs {n : ℕ} (x y a b c : Lab d (n + 1)) :
    thetaV hA h3 (cs (hA := hA) (h3 := h3) x y) a b c =
      fv x a * fv y b * fv y c + fv y a * fv x b * fv y c + fv y a * fv y b * fv x c := by
  have h2 := two_ne_zero' hA h3
  rw [cs, thetaV_sub, thetaV_sub, thetaV_smul, thetaV_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, thetaV_tau, fv_add, fv_sub]
  linear_combination (fv x a * fv y b * fv y c + fv y a * fv x b * fv y c +
    fv y a * fv y b * fv x c + fv x a * fv x b * fv x c) * mul_inv_cancel₀ h2

end Theta

/-! ### Reading off the normal form -/

section Read

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

theorem fv_e0_e0 {n : ℕ} : fv (Pi.single 0 1 : Lab d (n + 1)) (Pi.single 0 1) = 1 := by
  rw [fv_single]; simp

theorem fv_e0_ej {n : ℕ} (j : Fin n) :
    fv (Pi.single 0 1 : Lab d (n + 1)) (Pi.single j.succ 1) = 0 := by
  rw [fv_single]; simp [(Fin.succ_ne_zero j)]

theorem fv_w_e0 {n : ℕ} (w : Lab d n) :
    fv (Fin.cons 0 w : Lab d (n + 1)) (Pi.single 0 1) = 0 := by
  rw [show (Pi.single 0 1 : Lab d (n + 1)) = Fin.cons 1 0 by
    funext i; refine Fin.cases (by simp) (fun k => by simp [Fin.succ_ne_zero]) i,
    fv_cons, zero_mul, zero_add]
  simp [fv]

theorem fv_w_ej {n : ℕ} (w : Lab d n) (j : Fin n) :
    fv (Fin.cons 0 w : Lab d (n + 1)) (Pi.single j.succ 1) = w j := by
  rw [← cons_single, fv_cons, zero_mul, zero_add, fv_single_right]

end Read

section Inj

variable {hA : Admissible d lv} {h3 : 3 ≤ lv}

theorem thetaV_neg {n : ℕ} (v : V hA h3 n) : thetaV hA h3 (-v) = -thetaV hA h3 v := by
  rw [eq_neg_iff_add_eq_zero, ← thetaV_add, neg_add_cancel, thetaV_zero]

theorem theta_zero_dir {n : ℕ} (x : Q d lv n) (b c : Lab d n) : theta hA x 0 b c = 0 := by
  simp only [theta, zero_add]; ring

theorem theta_zero_dir2 {n : ℕ} (x : Q d lv n) (a c : Lab d n) : theta hA x a 0 c = 0 := by
  simp only [theta, add_zero, zero_add]; ring

theorem tail_e0 {n : ℕ} : Fin.tail (Pi.single 0 1 : Lab d (n + 1)) = 0 := by
  funext j; simp [Fin.tail, Fin.succ_ne_zero]

theorem thetaV_phiV {n : ℕ} (w : Lab d n) (a b c : Lab d (n + 1)) :
    thetaV hA h3 (phiV hA h3 w) a b c =
      fv (Pi.single 0 1) a * fv (Fin.cons 0 w) b * fv (Fin.cons 0 w) c +
      fv (Fin.cons 0 w) a * fv (Pi.single 0 1) b * fv (Fin.cons 0 w) c +
      fv (Fin.cons 0 w) a * fv (Fin.cons 0 w) b * fv (Pi.single 0 1) c :=
  thetaV_cs _ _ a b c

theorem thetaV_Bpol {n : ℕ} (u v : Lab d n) (a b c : Lab d (n + 1)) :
    thetaV hA h3 (Bpol hA h3 u v) a b c =
      thetaV hA h3 (phiV hA h3 (u + v)) a b c - thetaV hA h3 (phiV hA h3 u) a b c -
        thetaV hA h3 (phiV hA h3 v) a b c := by
  rw [Bpol, polar, thetaV_add, thetaV_add, thetaV_neg, thetaV_neg]
  simp only [Pi.add_apply, Pi.neg_apply]; ring

theorem thetaV_Bpol_E {n : ℕ} (u v : Lab d n) (j k : Fin n) :
    thetaV hA h3 (Bpol hA h3 u v) (Pi.single 0 1) (Pi.single j.succ 1) (Pi.single k.succ 1) =
      u j * v k + v j * u k := by
  rw [thetaV_Bpol, thetaV_phiV, thetaV_phiV, thetaV_phiV]
  simp only [fv_e0_e0, fv_e0_ej, fv_w_e0, fv_w_ej, cons_zero_add, fv_add]
  ring

theorem sum_sum_single {n : ℕ} (G : Fin n → Fin n → ZMod d) (j k : Fin n) :
    ∑ j', ∑ k', G j' k' * ((Pi.single j' 1 : Lab d n) j * (Pi.single k' 1 : Lab d n) k) =
      G j k := by
  simp [Pi.single_apply]

theorem sum_sum_single' {n : ℕ} (G : Fin n → Fin n → ZMod d) (j k : Fin n) :
    ∑ j', ∑ k', G j' k' * ((Pi.single k' 1 : Lab d n) j * (Pi.single j' 1 : Lab d n) k) =
      G k j := by
  simp [Pi.single_apply]

/-- A cubic diagonal element whose phase has no cubic part is quadratic. -/
theorem dg3_quad : ∀ (n : ℕ) {x : Q d lv n}, x ∈ Dg3 h3 n → theta hA x = 0 →
    x ∈ Dg (two_le_of_three h3) n
  | 0, x, hx, _ => hx
  | n + 1, x, hx, hθ => by
    have h2 := two_ne_zero' hA h3
    obtain ⟨x', hx', α, β, G, e⟩ := dg3_nf (hA := hA) hx
    have hS3 := shiftQ_dg3 hA h3 hx'
    have hT := congrArg (thetaV hA h3) e
    rw [thetaV_cl hx, hθ, thetaV_add, thetaV_add, thetaV_add, thetaV_cl hS3, thetaV_smul,
      thetaV_sum] at hT
    simp only [thetaV_sum, thetaV_smul] at hT
    have ev : ∀ a b c : Lab d (n + 1), 0 = theta hA (shiftQ x') a b c +
        α * (fv (Pi.single 0 1 : Lab d (n + 1)) a * fv (Pi.single 0 1 : Lab d (n + 1)) b * fv (Pi.single 0 1 : Lab d (n + 1)) c) + thetaV hA h3 (ellV hA h3 β) a b c +
        ∑ j, ∑ k, G j k * thetaV hA h3 (Bpol hA h3 (Pi.single j 1) (Pi.single k 1)) a b c := by
      intro a b c
      have := congrFun (congrFun (congrFun hT a) b) c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply,
        thetaV_tau] at this
      exact this
    have hsh : ∀ a b c : Lab d (n + 1), theta hA (shiftQ x') a b c =
        theta hA x' (Fin.tail a) (Fin.tail b) (Fin.tail c) := theta_shift hx'
    -- `α`
    have hα : α = 0 := by
      have := ev (Pi.single 0 1 : Lab d (n + 1)) (Pi.single 0 1 : Lab d (n + 1)) (Pi.single 0 1 : Lab d (n + 1))
      simp only [hsh, tail_e0, theta_zero_dir, ellV, thetaV_cs, thetaV_Bpol, thetaV_phiV,
        fv_e0_e0, fv_w_e0] at this
      simpa using this.symm
    -- `β`
    have hβ : β = 0 := by
      funext j
      have := ev (Pi.single 0 1 : Lab d (n + 1)) (Pi.single 0 1 : Lab d (n + 1)) (Pi.single j.succ 1)
      simp only [hsh, tail_e0, theta_zero_dir, ellV, thetaV_cs, thetaV_Bpol, thetaV_phiV,
        fv_e0_e0, fv_w_e0, fv_e0_ej, fv_w_ej, hα] at this
      simpa using this.symm
    -- `G` is antisymmetric
    have hG : ∀ j k : Fin n, G j k + G k j = 0 := by
      intro j k
      have := ev (Pi.single 0 1 : Lab d (n + 1)) (Pi.single j.succ 1) (Pi.single k.succ 1)
      simp only [hsh, tail_e0, theta_zero_dir, hα, hβ, ellV_zero, thetaV_zero, Pi.zero_apply,
        zero_mul, add_zero, zero_add, thetaV_Bpol_E] at this
      simp only [mul_add, Finset.sum_add_distrib, sum_sum_single, sum_sum_single'] at this
      linear_combination -this
    -- so the quadratic part vanishes
    have hsum : ∑ j, ∑ k, G j k • Bpol hA h3 (Pi.single j 1 : Lab d n) (Pi.single k 1) = 0 := by
      set S := ∑ j, ∑ k, G j k • Bpol hA h3 (Pi.single j 1 : Lab d n) (Pi.single k 1)
      have hS : S = ∑ j, ∑ k, G k j • Bpol hA h3 (Pi.single j 1 : Lab d n) (Pi.single k 1) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [Bpol_comm]
      have h2S : (2 : ZMod d) • S = 0 := by
        rw [two_smul]
        conv_lhs => rw [show S + S = S + ∑ j, ∑ k, G k j • Bpol hA h3 (Pi.single j 1 : Lab d n)
          (Pi.single k 1) by rw [← hS]]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [← add_smul, hG, zero_smul]
      have := congrArg (fun z => (2 : ZMod d)⁻¹ • z) h2S
      simpa only [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_zero] using this
    rw [hα, hβ, hsum, zero_smul, ellV_zero, add_zero, add_zero, add_zero] at e
    -- the upper wires
    have hx'q : theta hA x' = 0 := by
      have h0 := congrArg (thetaV hA h3) e
      rw [thetaV_cl hx, thetaV_cl hS3, hθ] at h0
      funext a b c
      have := congrFun (congrFun (congrFun h0 (Fin.cons 0 a)) (Fin.cons 0 b)) (Fin.cons 0 c)
      rw [hsh, Fin.tail_cons, Fin.tail_cons, Fin.tail_cons] at this
      exact this.symm
    have hx'' := dg3_quad n hx' hx'q
    have hc : kl hA h3 x = 0 := by rw [e, kl_dg (shiftQ_dg _ hA hx'')]
    exact mem_dg_of_cl hx hc

/-- Proposition 1 for the cubic fragment: a cubic diagonal element with the
trivial pair is trivial. -/
theorem dg3_inj {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) (h : semQ hA n x = 1) : x = 1 := by
  have hθ : theta hA x = 0 := by
    funext a b c
    simp only [theta, h]
    show (0 : ZMod d) - 0 - 0 - 0 + 0 + 0 + 0 - 0 = 0
    ring
  exact dg_inj hA (two_le_of_three h3) n (dg3_quad n hx hθ) h

end Inj

end QCert.PhaseAffine
