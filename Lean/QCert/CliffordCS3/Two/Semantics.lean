/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two qubits: the translation into `U₄(ℤ[1/2, i])` and a decision procedure

The generators on a pair `u, l` (basis index `2 u + l`) are products of
commuting one- and two-level matrices of Bian–Selinger's presentation of
`U₄(ℤ[1/2, i])` (`QCert.BianSelingerUn`):

  i = i_[0] i_[1] i_[2] i_[3],   K_u = K_[0,2] K_[1,3],   K_l = K_[0,1] K_[2,3],
  S_u = i_[2] i_[3],   S_l = i_[1] i_[3],   CS = i_[3],

the translation `f2`.  The semantics of a pair word is that of its
translation (`sem2`).  `check4 u v = true` (decided by `decide +kernel`, by
the action of each one- and two-level generator on column vectors over
`ℤ[ω]`, as in `Translation.lean`) implies that the words `u, v` of
two-level generators have the same value (`sem_eq_of_check4`).
-/
import QCert.CliffordCS3.Two.Syntax
import QCert.CliffordCS3.Translation

namespace QCert.CliffordCS3.Two

open Matrix

/-- `i_[j]` on 4 indices. -/
abbrev ci (j : Fin 4) : Word (BianSelingerUn.Gen 4) := BianSelingerUn.i j
/-- `K_[j,k]` on 4 indices. -/
abbrev cK (j k : Fin 4) (h : j < k := by decide) : Word (BianSelingerUn.Gen 4) :=
  BianSelingerUn.K j k h

/-- The translation of the pair generators. -/
def f2 : Gen2 → Word (BianSelingerUn.Gen 4)
  | .i => ci 0 * ci 1 * ci 2 * ci 3
  | .Ku => cK 0 2 * cK 1 3
  | .Kl => cK 0 1 * cK 2 3
  | .Su => ci 2 * ci 3
  | .Sl => ci 1 * ci 3
  | .CS => ci 3

/-- The semantics of a pair word: that of its translation. -/
noncomputable def sem2 (w : Word Gen2) : U_ZHalfI 4 :=
  FreeMonoid.lift (BianSelingerUn.sem 4) (FreeMonoid.lift f2 w)

/-- The matrices of the one- and two-level generators on `n` indices over ℚ(ω). -/
def gmat {n : ℕ} : BianSelingerUn.Gen n → Matrix (Fin n) (Fin n) QOmega
  | .X j k _ => twoLevel j k XQ
  | .K j k _ => twoLevel j k Km
  | .i j => oneLevel j iQ

theorem mat_eq_cmat_gmat {n : ℕ} (y : BianSelingerUn.Gen n) : BianSelingerUn.mat y = cmat (gmat y) := by
  cases y with
  | X j k _ => simp only [BianSelingerUn.mat, gmat, cmat, twoLevel_map, cmat_XQ]
  | K j k _ => simp only [BianSelingerUn.mat, gmat, cmat, twoLevel_map, cmat_Km]
  | i j => simp only [BianSelingerUn.mat, gmat, cmat, oneLevel_map, iQ, QOmega.toC_I]

theorem coe_lift_sem_gmat {n : ℕ} (u : Word (BianSelingerUn.Gen n)) :
    (((FreeMonoid.lift (BianSelingerUn.sem n) u : U_ZHalfI n) : unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = cmat (FreeMonoid.lift gmat u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp [cmat_one]
  | mul_of y u ih =>
    rw [map_mul, map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, cmat_mul, BianSelingerUn.coe_sem, mat_eq_cmat_gmat]

/-- Words with the same matrix over ℚ(ω) have the same value. -/
theorem lift_sem_eq_of_gmat {n : ℕ} {u v : Word (BianSelingerUn.Gen n)}
    (h : FreeMonoid.lift gmat u = FreeMonoid.lift gmat v) :
    FreeMonoid.lift (BianSelingerUn.sem n) u = FreeMonoid.lift (BianSelingerUn.sem n) v := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift_sem_gmat, coe_lift_sem_gmat, h]

/-- A vector `(1/√2)^k (x₀, …, x₃)` over ℤ[ω]. -/
structure V4 where
  k : ℕ
  x0 : ZOmega
  x1 : ZOmega
  x2 : ZOmega
  x3 : ZOmega
  deriving DecidableEq

namespace V4

open ZOmega

/-- The vector over ℚ(ω). -/
def toVec (v : V4) : Fin 4 → QOmega :=
  ![QOmega.invSqrt2 ^ v.k * toQ v.x0, QOmega.invSqrt2 ^ v.k * toQ v.x1,
    QOmega.invSqrt2 ^ v.k * toQ v.x2, QOmega.invSqrt2 ^ v.k * toQ v.x3]

/-- The coordinates of a vector. -/
def get (v : V4) : Fin 4 → ZOmega
  | 0 => v.x0 | 1 => v.x1 | 2 => v.x2 | 3 => v.x3

/-- A vector from its coordinates. -/
def ofFun (k : ℕ) (f : Fin 4 → ZOmega) : V4 := ⟨k, f 0, f 1, f 2, f 3⟩

theorem toVec_get (v : V4) (t : Fin 4) : toVec v t = QOmega.invSqrt2 ^ v.k * toQ (v.get t) := by
  fin_cases t <;> rfl

theorem get_ofFun (k : ℕ) (f : Fin 4 → ZOmega) (t : Fin 4) : (ofFun k f).get t = f t := by
  fin_cases t <;> rfl

@[simp] theorem ofFun_k (k : ℕ) (f : Fin 4 → ZOmega) : (ofFun k f).k = k := rfl

/-- The action of a one- or two-level generator. -/
def bact : BianSelingerUn.Gen 4 → V4 → V4
  | .i j, v => ofFun v.k fun t => if t = j then i * v.get t else v.get t
  | .X j k _, v => ofFun v.k fun t => if t = k then v.get j else if t = j then v.get k else v.get t
  | .K j k _, v => ofFun (v.k + 1) fun t =>
      if t = k then V8.m * (v.get j - v.get k) else if t = j then V8.m * (v.get j + v.get k)
      else rt2 * v.get t

/-- The action of a word, the last letter first. -/
def brun : List (BianSelingerUn.Gen 4) → V4 → V4
  | [], v => v
  | y :: l, v => bact y (brun l v)

theorem toVec_bact (y : BianSelingerUn.Gen 4) (v : V4) :
    toVec (bact y v) = gmat y *ᵥ toVec v := by
  have hs : QOmega.invSqrt2 * toQ rt2 = 1 := by rw [mul_comm]; exact toQ_rt2_mul_invSqrt2
  have hκ : κ = toQ V8.m * QOmega.invSqrt2 := V8.toQ_m_mul_invSqrt2.symm
  funext t
  cases y with
  | i j =>
    rw [gmat, oneLevel_mulVec, toVec_get, bact, get_ofFun, ofFun_k]
    by_cases h : t = j
    · subst h
      simp only [Function.update_self, toVec_get, ↓reduceIte, toQ_mul, toQ_i, iQ]
      ring
    · simp only [Function.update_of_ne h, toVec_get, h, ↓reduceIte]
  | X j k hjk =>
    rw [gmat, twoLevel_mulVec hjk.ne, toVec_get, bact, get_ofFun, ofFun_k]
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
    rw [gmat, twoLevel_mulVec hjk.ne, toVec_get, bact, get_ofFun, ofFun_k]
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

theorem toVec_brun (l : List (BianSelingerUn.Gen 4)) (v : V4) :
    toVec (brun l v) = (l.map gmat).prod *ᵥ toVec v := by
  induction l with
  | nil => simp [brun]
  | cons y l ih => rw [brun, toVec_bact, ih, List.map_cons, List.prod_cons, mulVec_mulVec]

/-- Equality of the values of two vectors. -/
def eqv (u v : V4) : Bool :=
  mulRt2 v.k u.x0 == mulRt2 u.k v.x0 && mulRt2 v.k u.x1 == mulRt2 u.k v.x1 &&
    mulRt2 v.k u.x2 == mulRt2 u.k v.x2 && mulRt2 v.k u.x3 == mulRt2 u.k v.x3

theorem toVec_eq_of_eqv {u v : V4} (h : eqv u v = true) : toVec u = toVec v := by
  simp only [eqv, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  funext j
  fin_cases j
  · exact scaled_eq h0
  · exact scaled_eq h1
  · exact scaled_eq h2
  · exact scaled_eq h3

/-- The basis vectors. -/
def basis (j : Fin 4) : V4 :=
  ⟨0, if j = 0 then 1 else 0, if j = 1 then 1 else 0, if j = 2 then 1 else 0,
    if j = 3 then 1 else 0⟩

theorem toVec_basis : ∀ j : Fin 4, toVec (basis j) = Pi.single j 1 := by decide +kernel

end V4

/-- The decision procedure on words of one- and two-level generators. -/
def check4 (u v : Word (BianSelingerUn.Gen 4)) : Bool :=
  (List.finRange 4).all fun j =>
    V4.eqv (V4.brun u.toList (V4.basis j)) (V4.brun v.toList (V4.basis j))

theorem lift_gmat_eq_of_check4 {u v : Word (BianSelingerUn.Gen 4)} (h : check4 u v = true) :
    FreeMonoid.lift gmat u = FreeMonoid.lift gmat v := by
  simp only [check4, List.all_eq_true, List.mem_finRange, true_implies] at h
  refine Matrix.ext fun a j => ?_
  have hc : FreeMonoid.lift gmat u *ᵥ Pi.single j 1 = FreeMonoid.lift gmat v *ᵥ Pi.single j 1 := by
    have e1 := V4.toVec_brun u.toList (V4.basis j)
    have e2 := V4.toVec_brun v.toList (V4.basis j)
    rw [V4.toVec_basis] at e1 e2
    rw [FreeMonoid.lift_apply, FreeMonoid.lift_apply, ← e1, ← e2, V4.toVec_eq_of_eqv (h j)]
  have := congrFun hc a
  rw [mulVec_single_one, mulVec_single_one] at this
  exact this

/-- `check4` decides equality of values. -/
theorem sem_eq_of_check4 {u v : Word (BianSelingerUn.Gen 4)} (h : check4 u v = true) :
    FreeMonoid.lift (BianSelingerUn.sem 4) u = FreeMonoid.lift (BianSelingerUn.sem 4) v :=
  lift_sem_eq_of_gmat (lift_gmat_eq_of_check4 h)

/-- Two pair words with the same value of their translations. -/
def check2 (w v : Word Gen2) : Bool := check4 (FreeMonoid.lift f2 w) (FreeMonoid.lift f2 v)

theorem sem2_eq_of_check2 {w v : Word Gen2} (h : check2 w v = true) : sem2 w = sem2 v :=
  sem_eq_of_check4 h

end QCert.CliffordCS3.Two
