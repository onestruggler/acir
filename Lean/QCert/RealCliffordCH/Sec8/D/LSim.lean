/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Simulating multi-controlled gates directly

`Fast.check` simulates a circuit gate by gate; for the multi-controlled gates
of `MC` that means first unfolding `mc` into its canonical gate and swap
networks, which the kernel cannot afford.  Here such a gate acts on vectors
directly: each wire has a *role* (idle, a control of either colour, or the
target), and the gate is a phase (the box) or a `2 × 2` matrix on its target
(`ZX`, `XZ`, `H`) on the blocks where the controls match, the identity
elsewhere.  The actions are proved to compute the operators of `MCSem.eval_mc`.
As in `Fast`, vectors are over `ℤ[√2]` with one power of `√2` per letter:
the multi-controlled `H` multiplies the blocks where it acts as the identity
by `√2`.
-/
import QCert.RealCliffordCH.Sec8.Fast
import QCert.RealCliffordCH.Sec8.MCSem

namespace QCert.RealCliffordCH.Sec8.LS

open Matrix Circuit Fast Sim

/-! ## Scalars -/

/-- Multiplication in `ℤ[√2]`. -/
def zmul (x y : Z2) : Z2 := ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩

theorem toQ_zmul (x y : Z2) : Z2.toQ (zmul x y) = Z2.toQ x * Z2.toQ y := by
  ext <;> simp [Z2.toQ, zmul] <;> push_cast <;> ring

/-- A vector times a scalar. -/
def vsm (c : Z2) : {n : ℕ} → V n → V n
  | 0, v => zmul c v
  | _ + 1, v => (vsm c v.1, vsm c v.2)

theorem tf_vsm (c : Z2) : ∀ {n : ℕ} (v : V n), toFun (toS (vsm c v)) = Z2.toQ c • toFun (toS v)
  | 0, _ => by funext s; simp [toFun, toS, vsm, toQ_zmul]
  | _ + 1, v => by
    funext s; simp only [toFun, toS, vsm, Pi.smul_apply]
    split_ifs <;> rw [tf_vsm] <;> rfl

theorem tf_pair' {n : ℕ} (a b : V n) (s : State 2 (n + 1)) :
    toFun (toS ((a, b) : V (n + 1))) s =
      if s 0 = 0 then toFun (toS a) (Fin.tail s) else toFun (toS b) (Fin.tail s) :=
  Sim.toFun_pair _ _ s

/-! ## Roles -/

/-- The role of a wire for a multi-controlled gate. -/
inductive Role
  | idle
  | c0
  | c1
  | tgt
  deriving DecidableEq, Repr

/-- The control condition of a role on the value of its wire. -/
def Role.ok : Role → Fin 2 → Bool
  | .c0, b => b == 0
  | .c1, b => b == 1
  | _, _ => true

/-- All the controls match, the roles of the wires `0, 1, …` being `f 0, f 1, …`. -/
def mt (f : ℕ → Role) : (n : ℕ) → State 2 n → Bool
  | 0, _ => true
  | n + 1, s => (f 0).ok (s 0) && mt (fun j => f (j + 1)) n (Fin.tail s)

/-- The value of the (first) target wire. -/
def tb (f : ℕ → Role) : (n : ℕ) → State 2 n → Fin 2
  | 0, _ => 0
  | n + 1, s => if f 0 = .tgt then s 0 else tb (fun j => f (j + 1)) n (Fin.tail s)

/-- The state with its (first) target wire set. -/
def setT (f : ℕ → Role) : (n : ℕ) → State 2 n → Fin 2 → State 2 n
  | 0, s, _ => s
  | n + 1, s, b =>
    if f 0 = .tgt then Fin.cons b (Fin.tail s)
    else Fin.cons (s 0) (setT (fun j => f (j + 1)) n (Fin.tail s) b)

theorem fin2 (b : Fin 2) : b = 0 ∨ b = 1 := Sim.fin2_cases b

/-! ## The phase: `-1` where the controls match -/

def phV (f : ℕ → Role) : (n : ℕ) → V n → V n
  | 0, v => Z2.neg v
  | n + 1, v =>
    match f 0 with
    | .c0 => (phV (fun j => f (j + 1)) n v.1, v.2)
    | .c1 => (v.1, phV (fun j => f (j + 1)) n v.2)
    | _ => (phV (fun j => f (j + 1)) n v.1, phV (fun j => f (j + 1)) n v.2)

theorem tf_phV : ∀ (f : ℕ → Role) (n : ℕ) (v : V n) (s : State 2 n),
    toFun (toS (phV f n v)) s = if mt f n s then -toFun (toS v) s else toFun (toS v) s
  | f, 0, v, s => by simp [phV, mt, toFun, toS, Z2.toQ_neg]
  | f, n + 1, v, s => by
    have hv : v = (v.1, v.2) := rfl
    simp only [phV, mt]
    split
    · next h =>
      conv_rhs => rw [hv]
      rw [tf_pair', tf_pair']
      rcases fin2 (s 0) with h0 | h0 <;> simp [h, h0, Role.ok, tf_phV]
    · next h =>
      conv_rhs => rw [hv]
      rw [tf_pair', tf_pair']
      rcases fin2 (s 0) with h0 | h0 <;> simp [h, h0, Role.ok, tf_phV]
    · next h1 h2 =>
      have hok : ∀ b, (f 0).ok b = true := by intro b; cases hh : f 0 <;> simp_all [Role.ok]
      conv_rhs => rw [hv]
      rw [tf_pair', tf_pair']
      rcases fin2 (s 0) with h0 | h0 <;> simp [h0, hok, tf_phV]

/-! ## A `2 × 2` matrix on the target where the controls match -/

/-- Below the target: the row `d` of `U` applied to the parts `x` (target `0`)
and `y` (target `1`) where the controls match, `sc` times the part `d`
elsewhere. -/
def mixV (U : Fin 2 → Fin 2 → Z2) (sc : Z2) (d : Fin 2) (f : ℕ → Role) :
    (n : ℕ) → V n → V n → V n
  | 0, x, y => Z2.add (zmul (U d 0) x) (zmul (U d 1) y)
  | n + 1, x, y =>
    match f 0 with
    | .c0 => (mixV U sc d (fun j => f (j + 1)) n x.1 y.1, vsm sc (if d = 0 then x.2 else y.2))
    | .c1 => (vsm sc (if d = 0 then x.1 else y.1), mixV U sc d (fun j => f (j + 1)) n x.2 y.2)
    | _ => (mixV U sc d (fun j => f (j + 1)) n x.1 y.1, mixV U sc d (fun j => f (j + 1)) n x.2 y.2)

theorem tf_mixV (U : Fin 2 → Fin 2 → Z2) (sc : Z2) (d : Fin 2) :
    ∀ (f : ℕ → Role) (n : ℕ) (x y : V n) (s : State 2 n),
      toFun (toS (mixV U sc d f n x y)) s =
        if mt f n s then Z2.toQ (U d 0) * toFun (toS x) s + Z2.toQ (U d 1) * toFun (toS y) s
        else Z2.toQ sc * (if d = 0 then toFun (toS x) s else toFun (toS y) s)
  | f, 0, x, y, s => by
    simp [mixV, mt, toFun, toS, Z2.toQ_add, toQ_zmul]
  | f, n + 1, x, y, s => by
    have hx : x = (x.1, x.2) := rfl
    have hy : y = (y.1, y.2) := rfl
    simp only [mixV, mt]
    split
    · next h =>
      conv_rhs => rw [hx, hy]
      rw [tf_pair', tf_pair', tf_pair']
      rcases fin2 (s 0) with h0 | h0 <;> rcases fin2 d with hd | hd <;>
        simp [h, h0, hd, Role.ok, tf_mixV, tf_vsm]
    · next h =>
      conv_rhs => rw [hx, hy]
      rw [tf_pair', tf_pair', tf_pair']
      rcases fin2 (s 0) with h0 | h0 <;> rcases fin2 d with hd | hd <;>
        simp [h, h0, hd, Role.ok, tf_mixV, tf_vsm]
    · next h1 h2 =>
      have hok : ∀ b, (f 0).ok b = true := by intro b; cases hh : f 0 <;> simp_all [Role.ok]
      conv_rhs => rw [hx, hy]
      rw [tf_pair', tf_pair', tf_pair']
      rcases fin2 (s 0) with h0 | h0 <;> rcases fin2 d with hd | hd <;>
        simp [h0, hd, hok, tf_mixV]

/-- The matrix `U` on the (first) target where the controls match, `sc`
times the identity elsewhere. -/
def tgV (U : Fin 2 → Fin 2 → Z2) (sc : Z2) (f : ℕ → Role) : (n : ℕ) → V n → V n
  | 0, v => v
  | n + 1, v =>
    match f 0 with
    | .tgt => (mixV U sc 0 (fun j => f (j + 1)) n v.1 v.2, mixV U sc 1 (fun j => f (j + 1)) n v.1 v.2)
    | .c0 => (tgV U sc (fun j => f (j + 1)) n v.1, vsm sc v.2)
    | .c1 => (vsm sc v.1, tgV U sc (fun j => f (j + 1)) n v.2)
    | .idle => (tgV U sc (fun j => f (j + 1)) n v.1, tgV U sc (fun j => f (j + 1)) n v.2)

/-- `f` has its first target at `w`. -/
def FirstT (f : ℕ → Role) (w : ℕ) : Prop := f w = .tgt ∧ ∀ j < w, f j ≠ .tgt

theorem FirstT.succ {f : ℕ → Role} {w : ℕ} (h : FirstT f (w + 1)) :
    FirstT (fun j => f (j + 1)) w := ⟨h.1, fun j hj => h.2 (j + 1) (by omega)⟩

theorem tf_tgV (U : Fin 2 → Fin 2 → Z2) (sc : Z2) :
    ∀ (f : ℕ → Role) (n w : ℕ), w < n → FirstT f w → ∀ (v : V n) (s : State 2 n),
      toFun (toS (tgV U sc f n v)) s =
        if mt f n s then
          Z2.toQ (U (tb f n s) 0) * toFun (toS v) (setT f n s 0) +
            Z2.toQ (U (tb f n s) 1) * toFun (toS v) (setT f n s 1)
        else Z2.toQ sc * toFun (toS v) s
  | f, 0, _, h, _, _, _ => absurd h (by omega)
  | f, n + 1, 0, _, hf, v, s => by
    have hv : v = (v.1, v.2) := rfl
    simp only [tgV, mt, tb, setT, hf.1, if_true, Role.ok, Bool.true_and]
    conv_rhs => rw [hv]
    rw [tf_pair', tf_pair', tf_pair', tf_pair']
    simp only [Fin.cons_zero, Fin.tail_cons, Fin.cons_self_tail]
    rcases fin2 (s 0) with h0 | h0
    · simp [h0, tf_mixV]
    · simp [h0, tf_mixV]
  | f, n + 1, w + 1, hw, hf, v, s => by
    have hv : v = (v.1, v.2) := rfl
    have h0 : f 0 ≠ .tgt := hf.2 0 (by omega)
    have ih := tf_tgV U sc (fun j => f (j + 1)) n w (by omega) hf.succ
    simp only [tgV, mt, tb, setT, if_neg h0]
    split
    · next h => exact absurd h h0
    · next h =>
      conv_rhs => rw [hv]
      rw [tf_pair', tf_pair', tf_pair', tf_pair']
      simp only [Fin.cons_zero, Fin.tail_cons]
      rcases fin2 (s 0) with h0 | h0 <;> simp [h, h0, Role.ok, ih, tf_vsm]
    · next h =>
      conv_rhs => rw [hv]
      rw [tf_pair', tf_pair', tf_pair', tf_pair']
      simp only [Fin.cons_zero, Fin.tail_cons]
      rcases fin2 (s 0) with h0 | h0 <;> simp [h, h0, Role.ok, ih, tf_vsm]
    · next h =>
      conv_rhs => rw [hv]
      rw [tf_pair', tf_pair', tf_pair', tf_pair']
      simp only [Fin.cons_zero, Fin.tail_cons]
      rcases fin2 (s 0) with h0 | h0 <;> simp [h, h0, Role.ok, ih]

/-! ## Roles and bits -/

theorem bit_tail {n : ℕ} (s : State 2 (n + 1)) (j : ℕ) :
    MS.bit (Fin.tail s) j = MS.bit s (j + 1) := by
  by_cases h : j < n
  · rw [MS.bit_lt _ h, MS.bit_lt _ (by omega)]; rfl
  · rw [MS.bit_ge _ (by omega), MS.bit_ge _ (by omega)]

theorem bit_zero {n : ℕ} (s : State 2 (n + 1)) : MS.bit s 0 = s 0 := MS.bit_lt _ (by omega)

theorem bit_cons_zero {n : ℕ} (b : Fin 2) (t : State 2 n) :
    MS.bit (Fin.cons b t : State 2 (n + 1)) 0 = b := by
  rw [bit_zero]; rfl

theorem bit_cons_succ {n : ℕ} (b : Fin 2) (t : State 2 n) (j : ℕ) :
    MS.bit (Fin.cons b t : State 2 (n + 1)) (j + 1) = MS.bit t j := by
  rw [← bit_tail, Fin.tail_cons]

theorem mt_iff (f : ℕ → Role) : ∀ (n : ℕ) (s : State 2 n),
    mt f n s = true ↔ ∀ j < n, (f j).ok (MS.bit s j) = true
  | 0, s => by simp [mt]
  | n + 1, s => by
    simp only [mt, Bool.and_eq_true, mt_iff (fun j => f (j + 1)) n (Fin.tail s), bit_tail]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · rwa [bit_zero]
      · exact h j (by omega)
    · intro h
      exact ⟨by have := h 0 (by omega); rwa [bit_zero] at this, fun j hj => h (j + 1) (by omega)⟩

theorem tb_eq (f : ℕ → Role) : ∀ (n w : ℕ), w < n → FirstT f w → ∀ (s : State 2 n),
    tb f n s = MS.bit s w
  | 0, _, h, _, _ => absurd h (by omega)
  | n + 1, 0, _, hf, s => by simp only [tb, hf.1, if_true, bit_zero]
  | n + 1, w + 1, h, hf, s => by
    simp only [tb, if_neg (hf.2 0 (by omega))]
    rw [tb_eq _ n w (by omega) hf.succ, bit_tail]

theorem setT_eq (f : ℕ → Role) : ∀ (n w : ℕ), w < n → FirstT f w →
    ∀ (s : State 2 n) (u : Fin 2) (j : ℕ),
      MS.bit (setT f n s u) j = if j = w then u else MS.bit s j
  | 0, _, h, _, _, _, _ => absurd h (by omega)
  | n + 1, 0, _, hf, s, u, j => by
    simp only [setT, hf.1, if_true]
    rcases j with _ | j
    · rw [if_pos rfl, bit_cons_zero]
    · rw [if_neg (by omega), bit_cons_succ, bit_tail]
  | n + 1, w + 1, h, hf, s, u, j => by
    simp only [setT, if_neg (hf.2 0 (by omega))]
    rcases j with _ | j
    · rw [if_neg (by omega), bit_cons_zero, bit_zero]
    · rw [bit_cons_succ, setT_eq _ n w (by omega) hf.succ, bit_tail]
      simp only [Nat.add_right_cancel_iff]

/-! ## The letters' operators, entry by entry -/

/-- `ZX` as an integer matrix. -/
def mZX : Fin 2 → Fin 2 → Z2 := fun u v =>
  if u = 0 then (if v = 1 then Z2.one else Z2.zero) else (if v = 0 then Z2.neg Z2.one else Z2.zero)

/-- `XZ` as an integer matrix. -/
def mXZ : Fin 2 → Fin 2 → Z2 := fun u v =>
  if u = 0 then (if v = 1 then Z2.neg Z2.one else Z2.zero) else (if v = 0 then Z2.one else Z2.zero)

/-- `√2 H` as an integer matrix. -/
def mH : Fin 2 → Fin 2 → Z2 := fun u v => if u = 1 ∧ v = 1 then Z2.neg Z2.one else Z2.one

/-- `√2`. -/
def r2 : Z2 := ⟨0, 1⟩

theorem eval_box0 : opsQ.eval 1 (box 0) = fun u v => if u = v then (-1 : Q) else 0 :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_zx0 : opsQ.eval 1 (zx 0) = fun u v => Z2.toQ (mZX (u 0) (v 0)) :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_xz0 : opsQ.eval 1 (xz 0) = fun u v => Z2.toQ (mXZ (u 0) (v 0)) :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_mch0 : opsQ.eval 2 (mch 0) = fun u v =>
    if u 0 = v 0 then QSqrt2.invSqrt2 * Z2.toQ (mH (u 1) (v 1)) else 0 :=
  eval_eq_of_checkM (by decide +kernel)


/-! ## `Λ_c(U)` applied to a vector -/

section Lam

open MS

variable {K : ℕ}

theorem upd_bit {f : ℕ → Role} {w : ℕ} (hw : w < K) (hf : FirstT f w) (s : State 2 K) (u : Fin 2)
    (j : ℕ) : bit (setT f K s u) j = if j = w then u else bit s j :=
  setT_eq f K w hw hf s u j

theorem upd_self {f : ℕ → Role} {w : ℕ} (hw : w < K) (hf : FirstT f w) (s : State 2 K) :
    setT f K s (bit s w) = s := by
  apply state_ext; intro j _
  rw [upd_bit hw hf]; split_ifs with h
  · rw [h]
  · rfl

theorem upd_ne {f : ℕ → Role} {w : ℕ} (hw : w < K) (hf : FirstT f w) (s : State 2 K) :
    setT f K s 0 ≠ setT f K s 1 := by
  intro e
  have := congrArg (fun t => bit t w) e
  simp only [upd_bit hw hf, if_true] at this
  exact absurd this (by decide)

/-- A state that agrees with `s` off wire `w` is `s` with wire `w` set. -/
theorem eq_upd {f : ℕ → Role} {w : ℕ} (hw : w < K) (hf : FirstT f w) (s t : State 2 K)
    (h : ∀ j < K, j ≠ w → bit s j = bit t j) : t = setT f K s (bit t w) := by
  apply state_ext; intro j hj
  rw [upd_bit hw hf]; split_ifs with e
  · rw [e]
  · exact (h j hj e).symm

theorem match_upd {f : ℕ → Role} {w : ℕ} (hw : w < K) (hf : FirstT f w) {tg : List ℕ}
    (hwt : w ∈ tg) (c : ℕ → Option Bool) (s : State 2 K) (u : Fin 2) :
    Match K tg c (setT f K s u) ↔ Match K tg c s := by
  unfold Match
  refine forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hj => ?_
  have hjw : j ≠ w := fun e => hj (e ▸ hwt)
  rw [upd_bit hw hf, if_neg hjw]

/-- The phase. -/
theorem lam_box_mulVec {w : ℕ} (c : ℕ → Option Bool) (F : State 2 K → Q) (s : State 2 K) :
    (lamOp K [w] c (fun u v : State 2 1 => if u = v then (-1 : Q) else 0) *ᵥ F) s =
      if Match K [w] c s then -F s else F s := by
  rw [mulVec, dotProduct, Finset.sum_eq_single s]
  · unfold lamOp
    rw [if_pos (fun _ _ _ => rfl)]
    split_ifs <;> simp
  · intro t _ hts
    unfold lamOp
    split_ifs with hA hM
    · have : (rd [w] s : State 2 1) ≠ rd [w] t := by
        intro e
        apply hts; symm; apply state_ext; intro j hj
        by_cases hjw : j = w
        · subst hjw; exact congrFun e 0
        · exact hA j hj (by simpa using hjw)
      simp [this]
    · have : (rd [w] s : State 2 1) ≠ rd [w] t := by
        intro e
        apply hts; symm; apply state_ext; intro j hj
        by_cases hjw : j = w
        · subst hjw; exact congrFun e 0
        · exact hA j hj (by simpa using hjw)
      simp [this]
    · simp
  · simp

/-- A `2 × 2` matrix on wire `w`, read through `Z2`. -/
theorem lam_one_mulVec {f : ℕ → Role} {w : ℕ} (hw : w < K) (hf : FirstT f w)
    (c : ℕ → Option Bool) (M : Fin 2 → Fin 2 → Z2) (F : State 2 K → Q) (s : State 2 K) :
    (lamOp K [w] c (fun u v : State 2 1 => Z2.toQ (M (u 0) (v 0))) *ᵥ F) s =
      if Match K [w] c s then
        Z2.toQ (M (bit s w) 0) * F (setT f K s 0) + Z2.toQ (M (bit s w) 1) * F (setT f K s 1)
      else F s := by
  have hA : ∀ u, ∀ j < K, j ∉ [w] → bit s j = bit (setT f K s u) j := by
    intro u j _ hj
    rw [upd_bit hw hf, if_neg (by simpa using hj)]
  have val : ∀ u, lamOp K [w] c (fun u v : State 2 1 => Z2.toQ (M (u 0) (v 0))) s (setT f K s u) =
      if Match K [w] c s then Z2.toQ (M (bit s w) u) else if bit s w = u then 1 else 0 := by
    intro u
    unfold lamOp
    rw [if_pos (hA u)]
    have e0 : (rd [w] (setT f K s u) : State 2 1) 0 = u := by
      show bit (setT f K s u) ([w].getD 0 0) = u
      rw [upd_bit hw hf]; simp
    by_cases hM : Match K [w] c s
    · rw [if_pos ((match_upd hw hf (List.mem_singleton_self w) c s u).2 hM), if_pos hM]
      show Z2.toQ (M ((rd [w] s : State 2 1) 0) ((rd [w] (setT f K s u) : State 2 1) 0)) = _
      rw [e0]; rfl
    · rw [if_neg (fun h => hM ((match_upd hw hf (List.mem_singleton_self w) c s u).1 h)),
        if_neg hM, one_apply]
      have : ((rd [w] s : State 2 1) = rd [w] (setT f K s u)) ↔ bit s w = u := by
        constructor
        · intro e; have := congrFun e 0; rw [e0] at this; exact this
        · intro e; funext i
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi; exact e.trans e0.symm
      simp only [this]
  rw [mulVec, dotProduct, Fintype.sum_eq_add (setT f K s 0) (setT f K s 1) (upd_ne hw hf s),
    val, val]
  · by_cases hM : Match K [w] c s
    · simp only [if_pos hM]
    · simp only [if_neg hM]
      rcases fin2 (bit s w) with e | e
      · rw [if_pos e, if_neg (by rw [e]; decide), ← e, upd_self hw hf]; simp
      · rw [if_neg (by rw [e]; decide), if_pos e, ← e, upd_self hw hf]; simp
  · intro t ⟨h0, h1⟩
    unfold lamOp
    rw [if_neg, zero_mul]
    intro hA'
    have e := eq_upd hw hf s t (fun j hj hjw => hA' j hj (by simpa using hjw))
    rcases fin2 (bit t w) with h | h
    · rw [h] at e; exact h0 e
    · rw [h] at e; exact h1 e

/-- The multi-controlled `H`: box wire `b`, `H` on wire `w`. -/
theorem lam_hg_mulVec {f : ℕ → Role} {b w : ℕ} (hw : w < K) (hf : FirstT f w) (hbw : b ≠ w)
    (c : ℕ → Option Bool) (F : State 2 K → Q) (s : State 2 K) :
    (lamOp K [b, w] c (fun u v : State 2 2 =>
        if u 0 = v 0 then QSqrt2.invSqrt2 * Z2.toQ (mH (u 1) (v 1)) else 0) *ᵥ F) s =
      if Match K [b, w] c s then
        QSqrt2.invSqrt2 * Z2.toQ (mH (bit s w) 0) * F (setT f K s 0) +
          QSqrt2.invSqrt2 * Z2.toQ (mH (bit s w) 1) * F (setT f K s 1)
      else F s := by
  have hbs : ∀ u, bit (setT f K s u) b = bit s b := fun u => by rw [upd_bit hw hf, if_neg hbw]
  have hA : ∀ u, ∀ j < K, j ∉ [b, w] → bit s j = bit (setT f K s u) j := by
    intro u j _ hj
    rw [upd_bit hw hf, if_neg (by simp at hj; exact hj.2)]
  have r0 : ∀ t : State 2 K, (rd [b, w] t : State 2 2) 0 = bit t b := fun t => rfl
  have r1 : ∀ t : State 2 K, (rd [b, w] t : State 2 2) 1 = bit t w := fun t => rfl
  have hrd : ∀ t t' : State 2 K, ((rd [b, w] t : State 2 2) = rd [b, w] t') ↔
      (bit t b = bit t' b ∧ bit t w = bit t' w) := by
    intro t t'
    constructor
    · intro e; exact ⟨congrFun e 0, congrFun e 1⟩
    · rintro ⟨e0, e1⟩; funext i; fin_cases i
      · exact e0
      · exact e1
  have hwu : ∀ u, bit (setT f K s u) w = u := fun u => by rw [upd_bit hw hf]; simp
  have val : ∀ u, lamOp K [b, w] c (fun u v : State 2 2 =>
        if u 0 = v 0 then QSqrt2.invSqrt2 * Z2.toQ (mH (u 1) (v 1)) else 0) s (setT f K s u) =
      if Match K [b, w] c s then QSqrt2.invSqrt2 * Z2.toQ (mH (bit s w) u)
      else if bit s w = u then 1 else 0 := by
    intro u
    unfold lamOp
    rw [if_pos (hA u)]
    by_cases hM : Match K [b, w] c s
    · rw [if_pos ((match_upd hw hf (by simp) c s u).2 hM), if_pos hM]
      show (if (rd [b, w] s : State 2 2) 0 = (rd [b, w] (setT f K s u) : State 2 2) 0 then
        QSqrt2.invSqrt2 * Z2.toQ (mH ((rd [b, w] s : State 2 2) 1)
          ((rd [b, w] (setT f K s u) : State 2 2) 1)) else 0) = _
      rw [r0, r0, r1, r1, hbs, if_pos rfl, hwu]
    · rw [if_neg (fun h => hM ((match_upd hw hf (by simp) c s u).1 h)), if_neg hM, one_apply]
      simp only [hrd, hbs, hwu, true_and]
  rw [mulVec, dotProduct, Fintype.sum_eq_add (setT f K s 0) (setT f K s 1) (upd_ne hw hf s),
    val, val]
  · by_cases hM : Match K [b, w] c s
    · simp only [if_pos hM]
    · simp only [if_neg hM]
      rcases fin2 (bit s w) with e | e
      · rw [if_pos e, if_neg (by rw [e]; decide), ← e, upd_self hw hf]; simp
      · rw [if_neg (by rw [e]; decide), if_pos e, ← e, upd_self hw hf]; simp
  · intro t ⟨h0, h1⟩
    unfold lamOp
    have key : (∀ j < K, j ∉ [b, w] → bit s j = bit t j) → bit s b = bit t b → False := by
      intro hA' eb
      have e := eq_upd hw hf s t (fun j hj hjw => by
        by_cases hjb : j = b
        · rw [hjb]; exact eb
        · exact hA' j hj (by simp [hjb, hjw]))
      rcases fin2 (bit t w) with h | h
      · rw [h] at e; exact h0 e
      · rw [h] at e; exact h1 e
    split_ifs with hA' hM
    · show (if (rd [b, w] s : State 2 2) 0 = (rd [b, w] t : State 2 2) 0 then _ else 0) * F t = 0
      rw [r0, r0, if_neg (fun eb => key hA' eb), zero_mul]
    · rw [one_apply, if_neg (fun e => key hA' ((hrd s t).1 e).1), zero_mul]
    · rw [zero_mul]

end Lam

end QCert.RealCliffordCH.Sec8.LS
