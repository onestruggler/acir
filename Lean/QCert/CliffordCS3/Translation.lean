/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The translation into two-level generators

Section 3.1 of Bian–Selinger (arXiv:2306.08530): the three-qubit
Clifford+CS group is a subgroup of `U₈(ℤ[1/2, i])`, presented by the
one- and two-level matrices `i_[j]`, `X_[j,k]`, `K_[j,k]` (their
Theorem 2.1, `QCert.BianSelingerUn.presentation`).  Each generator of
Theorem 3.1 is a product of commuting one- or two-level matrices on the
basis states `|q₀ q₁ q₂⟩ = 4 q₀ + 2 q₁ + q₂`:

  i = i_[0] ⋯ i_[7],                 K₀ = K_[0,4] K_[1,5] K_[2,6] K_[3,7],
  K₁ = K_[0,2] K_[1,3] K_[4,6] K_[5,7],  K₂ = K_[0,1] K_[2,3] K_[4,5] K_[6,7],
  S₀ = i_[4] i_[5] i_[6] i_[7],      S₁ = i_[2] i_[3] i_[6] i_[7],
  S₂ = i_[1] i_[3] i_[5] i_[7],      CS₀₁ = i_[6] i_[7],  CS₁₂ = i_[3] i_[7],

which is the translation `f` of the Reidemeister–Schreier argument; it
respects the interpretation (`lift_f`), decided over ℚ(ω).
-/
import QCert.CliffordCS3.Eval
import QCert.BianSelingerUn.Semantics

namespace QCert.CliffordCS3

open Matrix

/-- `i_[j]`, on 8 indices. -/
abbrev bi (j : Fin 8) : Word (BianSelingerUn.Gen 8) := BianSelingerUn.i j
/-- `K_[j,k]`. -/
abbrev bK (j k : Fin 8) (h : j < k := by decide) : Word (BianSelingerUn.Gen 8) :=
  BianSelingerUn.K j k h

/-- The translation of the generators into one- and two-level matrices. -/
def fG : Gen → Word (BianSelingerUn.Gen 8)
  | .i => bi 0 * bi 1 * bi 2 * bi 3 * bi 4 * bi 5 * bi 6 * bi 7
  | .K₀ => bK 0 4 * bK 1 5 * bK 2 6 * bK 3 7
  | .K₁ => bK 0 2 * bK 1 3 * bK 4 6 * bK 5 7
  | .K₂ => bK 0 1 * bK 2 3 * bK 4 5 * bK 6 7
  | .S₀ => bi 4 * bi 5 * bi 6 * bi 7
  | .S₁ => bi 2 * bi 3 * bi 6 * bi 7
  | .S₂ => bi 1 * bi 3 * bi 5 * bi 7
  | .CS₀₁ => bi 6 * bi 7
  | .CS₁₂ => bi 3 * bi 7

/-- `X` over ℚ(ω). -/
def XQ : Matrix (Fin 2) (Fin 2) QOmega := !![0, 1; 1, 0]

/-- The matrices of the one- and two-level generators over ℚ(ω). -/
def gmatQ : BianSelingerUn.Gen 8 → Matrix (Fin 8) (Fin 8) QOmega
  | .X j k _ => twoLevel j k XQ
  | .K j k _ => twoLevel j k Km
  | .i j => oneLevel j iQ

theorem toC_κ : QOmega.toC κ = (1 + Complex.I)⁻¹ := by
  have h := congrArg QOmega.toC κ_mul
  rw [map_mul, map_add, map_one, QOmega.toC_I] at h
  exact (eq_inv_of_mul_eq_one_left h)

theorem cmat_XQ : XQ.map QOmega.toC = BianSelingerUn.Xmat := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [XQ, BianSelingerUn.Xmat, -Quartic.zero_def, -Quartic.one_def]

theorem cmat_Km : Km.map QOmega.toC = BianSelingerUn.Kmat := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [Km, BianSelingerUn.Kmat, toC_κ, -Quartic.neg_def]

theorem mat_eq_cmat (y : BianSelingerUn.Gen 8) : BianSelingerUn.mat y = cmat (gmatQ y) := by
  cases y with
  | X j k _ => simp only [BianSelingerUn.mat, gmatQ, cmat, twoLevel_map, cmat_XQ]
  | K j k _ => simp only [BianSelingerUn.mat, gmatQ, cmat, twoLevel_map, cmat_Km]
  | i j => simp only [BianSelingerUn.mat, gmatQ, cmat, oneLevel_map, iQ, QOmega.toC_I]

/-- The value of a word of two-level generators, as a matrix. -/
theorem coe_lift_sem (u : Word (BianSelingerUn.Gen 8)) :
    (((FreeMonoid.lift (BianSelingerUn.sem 8) u : U_ZHalfI 8) : unitaryGroup (Fin 8) ℂ) :
      Matrix (Fin 8) (Fin 8) ℂ) = cmat (FreeMonoid.lift gmatQ u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp [cmat_one]
  | mul_of y u ih =>
    rw [map_mul, map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, cmat_mul, BianSelingerUn.coe_sem, mat_eq_cmat]

namespace V8

open ZOmega

/-- The coordinates of a vector. -/
def get (v : V8) : Fin 8 → ZOmega
  | 0 => v.x0 | 1 => v.x1 | 2 => v.x2 | 3 => v.x3
  | 4 => v.x4 | 5 => v.x5 | 6 => v.x6 | 7 => v.x7

/-- A vector from its coordinates. -/
def ofFun (k : ℕ) (f : Fin 8 → ZOmega) : V8 := ⟨k, f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

theorem toVec_get (v : V8) (t : Fin 8) : toVec v t = QOmega.invSqrt2 ^ v.k * toQ (v.get t) := by
  fin_cases t <;> rfl

theorem get_ofFun (k : ℕ) (f : Fin 8 → ZOmega) (t : Fin 8) : (ofFun k f).get t = f t := by
  fin_cases t <;> rfl

@[simp] theorem ofFun_k (k : ℕ) (f : Fin 8 → ZOmega) : (ofFun k f).k = k := rfl

/-- The action of a one- or two-level generator: `K_[j,k]` scales the
whole vector by `1/√2` and multiplies the other coordinates by `√2`. -/
def bact : BianSelingerUn.Gen 8 → V8 → V8
  | .i j, v => ofFun v.k fun t => if t = j then i * v.get t else v.get t
  | .X j k _, v => ofFun v.k fun t => if t = k then v.get j else if t = j then v.get k else v.get t
  | .K j k _, v => ofFun (v.k + 1) fun t =>
      if t = k then m * (v.get j - v.get k) else if t = j then m * (v.get j + v.get k)
      else rt2 * v.get t

/-- The action of a word, the last letter first. -/
def brun : List (BianSelingerUn.Gen 8) → V8 → V8
  | [], v => v
  | y :: l, v => bact y (brun l v)

theorem toVec_bact (y : BianSelingerUn.Gen 8) (v : V8) :
    toVec (bact y v) = gmatQ y *ᵥ toVec v := by
  have hs : QOmega.invSqrt2 * toQ rt2 = 1 := by rw [mul_comm]; exact toQ_rt2_mul_invSqrt2
  have hκ : κ = toQ m * QOmega.invSqrt2 := toQ_m_mul_invSqrt2.symm
  funext t
  cases y with
  | i j =>
    rw [gmatQ, oneLevel_mulVec, toVec_get, bact, get_ofFun, ofFun_k]
    by_cases h : t = j
    · subst h
      simp only [Function.update_self, toVec_get, ↓reduceIte, toQ_mul, toQ_i, iQ]
      ring
    · simp only [Function.update_of_ne h, toVec_get, h, ↓reduceIte]
  | X j k hjk =>
    rw [gmatQ, twoLevel_mulVec hjk.ne, toVec_get, bact, get_ofFun, ofFun_k]
    have e00 : XQ 0 0 = 0 := rfl
    have e01 : XQ 0 1 = 1 := rfl
    have e10 : XQ 1 0 = 1 := rfl
    have e11 : XQ 1 1 = 0 := rfl
    by_cases h : t = k
    · subst h
      simp only [Function.update_self, toVec_get, ↓reduceIte, e10, e11]
      ring
    · by_cases h' : t = j
      · subst h'
        simp only [Function.update_self, Function.update_of_ne h, toVec_get, h, ↓reduceIte,
           e00, e01]
        ring
      · simp only [Function.update_of_ne h, Function.update_of_ne h', toVec_get, h, h', ↓reduceIte]
  | K j k hjk =>
    rw [gmatQ, twoLevel_mulVec hjk.ne, toVec_get, bact, get_ofFun, ofFun_k]
    have e00 : Km 0 0 = κ := rfl
    have e01 : Km 0 1 = κ := rfl
    have e10 : Km 1 0 = κ := rfl
    have e11 : Km 1 1 = -κ := rfl
    by_cases h : t = k
    · subst h
      simp only [Function.update_self, toVec_get, ↓reduceIte, e10, e11, hκ, toQ_mul, toQ_sub,
        pow_succ]
      ring
    · by_cases h' : t = j
      · subst h'
        simp only [Function.update_self, Function.update_of_ne h, toVec_get, h, ↓reduceIte,
          e00, e01, hκ, toQ_mul, toQ_add, pow_succ]
        ring
      · simp only [Function.update_of_ne h, Function.update_of_ne h', h, h', ↓reduceIte,
          toVec_get, toQ_mul, pow_succ]
        linear_combination (QOmega.invSqrt2 ^ v.k * toQ (v.get t)) * hs

theorem toVec_brun (l : List (BianSelingerUn.Gen 8)) (v : V8) :
    toVec (brun l v) = (l.map gmatQ).prod *ᵥ toVec v := by
  induction l with
  | nil => simp [brun]
  | cons y l ih => rw [brun, toVec_bact, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

end V8

/-- The translation of each generator acts on every basis vector as the
generator. -/
def checkF (x : Gen) : Bool :=
  (List.finRange 8).all fun j =>
    V8.eqv (V8.brun (FreeMonoid.toList (fG x)) (V8.basis j)) (V8.run [x] (V8.basis j))

theorem checkF_true : ∀ x : Gen, checkF x = true := by decide +kernel

theorem gmatQ_fG (x : Gen) : FreeMonoid.lift gmatQ (fG x) = matQ x := by
  have h := checkF_true x
  simp only [checkF, List.all_eq_true, List.mem_finRange, true_implies] at h
  refine Matrix.ext fun a j => ?_
  have hc : FreeMonoid.lift gmatQ (fG x) *ᵥ Pi.single j 1 = matQ x *ᵥ Pi.single j 1 := by
    have e1 := V8.toVec_brun (FreeMonoid.toList (fG x)) (V8.basis j)
    have e2 := V8.toVec_run [x] (V8.basis j)
    rw [V8.toVec_basis] at e1 e2
    rw [FreeMonoid.lift_apply, ← e1, V8.toVec_eq_of_eqv (h j), e2]
    simp
  have := congrFun hc a
  rw [mulVec_single_one, mulVec_single_one] at this
  exact this

/-- `f` respects the interpretation. -/
theorem lift_f (x : Gen) : FreeMonoid.lift (BianSelingerUn.sem 8) (fG x) = semU x := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift_sem, gmatQ_fG]
  rfl

theorem lift_lift_f (w : Word Gen) :
    FreeMonoid.lift (BianSelingerUn.sem 8) (FreeMonoid.lift fG w) = FreeMonoid.lift semU w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => rw [map_mul, map_mul, map_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, lift_f]

end QCert.CliffordCS3
