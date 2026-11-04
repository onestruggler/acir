/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symbolic numerators: patterns of a window, checked by evaluation

A *pattern* describes the numerators of a window of the pivot column as
`ℤ√2`-valued affine forms in integer parameters `t₀, t₁, …`: an affine form
is the list of its coefficients, the constant first (`evv l (c1 t)`), and an
entry of the window is a pair of forms (its rational and its `√2` part,
`zev`).  The scaled action of a word on numerators (`scw`, `Window.lean`) is
computed on patterns (`scwL`), and dividing by `√2 ^ h` is a divisibility check
on the coefficients (`zdivp`).

`pathOK P D A` checks, by evaluation, that every state of the path `D`
from `A s` is integral at the exponent of `s` and has fewer odd numerators
on the window than `s` has, for *every* value of the parameters: an entry
counts as possibly odd unless all its coefficients are even, and as odd in
`s` only if its constant is odd and its other coefficients even.  The window
after a word, at the old exponent (`divAll`) or `δ` below it (`divAllD`), is
computed the same way, with the tests `allSome`, `sameOdd`, `clsCount` on it.

Patterns are refined by substituting affine forms for the parameters
(`Psubst`, `pv_Psubst`): this is how a case split on the parity of a form
in the parameters, and the change from one parametrisation of a set of
windows to another, are carried out.

This module has the definitions and their algebraic lemmas only (so that
`GoodCheck.lean` can use them before `Switch.lean`); what they say about
states is in `Sym.lean` and `SymState.lean`.
-/
import QCert.HadamardPi.Window

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

noncomputable section

variable {n : ℕ}

/-! ### Affine forms -/

/-- `Σ cᵢ tᵢ` for the list `[c₀, c₁, …]`. -/
def evv : List ℤ → (ℕ → ℤ) → ℤ
  | [], _ => 0
  | c :: cs, t => c * t 0 + evv cs (fun i => t (i + 1))

/-- The parameters with a constant `1` in front. -/
def c1 (t : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | i + 1 => t i

@[simp] theorem evv_nil (t : ℕ → ℤ) : evv [] t = 0 := rfl

theorem evv_cons (c : ℤ) (cs : List ℤ) (t : ℕ → ℤ) :
    evv (c :: cs) t = c * t 0 + evv cs (fun i => t (i + 1)) := rfl

theorem evv_c1 (c : ℤ) (cs : List ℤ) (t : ℕ → ℤ) : evv (c :: cs) (c1 t) = c + evv cs t := by
  simp only [evv_cons, c1, mul_one]

/-! The list functions that the kernel runs in the checks of the case tree (`ladd`, `lsmul`,
`allEven`, `lhalf`, `ldiv`, `lquo`) are written with `List.rec`, hence `noncomputable`: by
pattern matching they are compiled through `brecOn`, which costs the kernel about twice the
unfoldings.  Their equations are `rfl` lemmas (`ladd_cons_cons`, …). -/

/-- Sum of forms. -/
noncomputable def ladd : List ℤ → List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun l => l) fun a as ih l =>
    List.casesOn (motive := fun _ => List ℤ) l (a :: as) fun b bs => (a + b) :: ih bs

theorem ladd_nil (l : List ℤ) : ladd [] l = l := rfl
theorem ladd_cons_nil (a : ℤ) (as : List ℤ) : ladd (a :: as) [] = a :: as := rfl
theorem ladd_cons_cons (a b : ℤ) (as bs : List ℤ) :
    ladd (a :: as) (b :: bs) = (a + b) :: ladd as bs := rfl

theorem evv_ladd : ∀ (a b : List ℤ) (t : ℕ → ℤ), evv (ladd a b) t = evv a t + evv b t
  | [], l, t => by simp [ladd_nil]
  | a :: as, [], t => by simp [ladd_cons_nil]
  | a :: as, b :: bs, t => by simp only [ladd_cons_cons, evv_cons, evv_ladd as bs]; ring

/-- A multiple of a form. -/
noncomputable def lsmul (c : ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] fun a _ ih => c * a :: ih

theorem lsmul_nil (c : ℤ) : lsmul c [] = [] := rfl
theorem lsmul_cons (c a : ℤ) (as : List ℤ) : lsmul c (a :: as) = c * a :: lsmul c as := rfl

theorem evv_lsmul (c : ℤ) : ∀ (l : List ℤ) (t : ℕ → ℤ), evv (lsmul c l) t = c * evv l t
  | [], t => by simp [lsmul_nil]
  | a :: as, t => by simp only [lsmul_cons, evv_cons, evv_lsmul c as]; ring

/-! The parity and divisibility tests below are written on `Int.natAbs` with `Nat.beq`:
the kernel evaluates `Nat` operations on literals natively, where an `Int` comparison through
its `DecidableEq` instance costs a few dozen unfoldings per coefficient. -/

theorem natAbs_mod_two_eq_zero {a : ℤ} : a.natAbs % 2 = 0 ↔ a % 2 = 0 := by
  rw [← Nat.even_iff, Int.natAbs_even, Int.even_iff]

theorem natAbs_mod_two_eq_one {a : ℤ} : a.natAbs % 2 = 1 ↔ a % 2 = 1 := by
  rw [← Nat.odd_iff, Int.natAbs_odd, Int.odd_iff]

/-- Every coefficient is even. -/
noncomputable def allEven : List ℤ → Bool :=
  List.rec (motive := fun _ => Bool) true fun a _ ih => Nat.beq (a.natAbs % 2) 0 && ih

theorem allEven_nil : allEven [] = true := rfl

theorem allEven_cons {a : ℤ} {as : List ℤ} :
    allEven (a :: as) = true ↔ a % 2 = 0 ∧ allEven as = true := by
  change (Nat.beq (a.natAbs % 2) 0 && allEven as) = true ↔ _
  simp only [Bool.and_eq_true, Nat.beq_eq, natAbs_mod_two_eq_zero]

/-- Half of every coefficient. -/
noncomputable def lhalf : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] fun a _ ih => a / 2 :: ih

theorem evv_lhalf : ∀ (l : List ℤ) (t : ℕ → ℤ), allEven l = true → 2 * evv (lhalf l) t = evv l t
  | [], t, _ => by simp [show lhalf [] = [] from rfl]
  | a :: as, t, h => by
    rw [allEven_cons] at h
    simp only [show lhalf (a :: as) = a / 2 :: lhalf as from rfl, evv_cons]
    rw [← evv_lhalf as _ h.2]
    have : 2 * (a / 2) = a := by omega
    linear_combination t 0 * this

theorem even_evv : ∀ (l : List ℤ) (t : ℕ → ℤ), allEven l = true → Even (evv l t)
  | [], t, _ => by simp
  | a :: as, t, h => by
    rw [allEven_cons] at h
    rw [evv_cons]
    obtain ⟨m, hm⟩ := even_evv as (fun i => t (i + 1)) h.2
    have ha : a = 2 * (a / 2) := by omega
    refine ⟨a / 2 * t 0 + m, ?_⟩
    rw [hm]
    linear_combination (t 0) * ha

/-! ### `ℤ√2`-valued forms -/

/-- A `ℤ√2`-valued affine form: the forms of its rational and `√2` parts. -/
abbrev ZL := List ℤ × List ℤ

/-- The default entry. -/
def dZ : ZL := ([], [])

/-- Evaluation at the parameters `t`. -/
def zev (x : ZL) (t : ℕ → ℤ) : ℤ√2 := ⟨evv x.1 (c1 t), evv x.2 (c1 t)⟩

def zadd (x y : ZL) : ZL := (ladd x.1 y.1, ladd x.2 y.2)
def zneg (x : ZL) : ZL := (lsmul (-1) x.1, lsmul (-1) x.2)
def zsub (x y : ZL) : ZL := zadd x (zneg y)
def zrt2 (x : ZL) : ZL := (lsmul 2 x.2, x.1)

theorem zev_zadd (x y : ZL) (t : ℕ → ℤ) : zev (zadd x y) t = zev x t + zev y t := by
  ext <;> simp [zev, zadd, evv_ladd]

theorem zev_zneg (x : ZL) (t : ℕ → ℤ) : zev (zneg x) t = -zev x t := by
  ext <;> simp [zev, zneg, evv_lsmul]

theorem zev_zsub (x y : ZL) (t : ℕ → ℤ) : zev (zsub x y) t = zev x t - zev y t := by
  rw [zsub, zev_zadd, zev_zneg, sub_eq_add_neg]

theorem zev_zrt2 (x : ZL) (t : ℕ → ℤ) : zev (zrt2 x) t = rt2 * zev x t := by
  rw [rt2_mul]; ext <;> simp [zev, zrt2, evv_lsmul]

/-- Division by `√2`, if the rational part has even coefficients. -/
def zdiv (x : ZL) : Option ZL := if allEven x.1 then some (x.2, lhalf x.1) else none

theorem zdiv_sound {x y : ZL} (h : zdiv x = some y) (t : ℕ → ℤ) : rt2 * zev y t = zev x t := by
  unfold zdiv at h
  split_ifs at h with he
  cases h
  rw [rt2_mul]
  ext
  · simp only [zev]; exact evv_lhalf _ _ he
  · simp [zev]

/-- Every coefficient divisible by `d`. -/
noncomputable def ldiv (d : ℕ) : List ℤ → Bool :=
  List.rec (motive := fun _ => Bool) true fun a _ ih => Nat.beq (a.natAbs % d) 0 && ih

/-- Every coefficient divided by `d`. -/
noncomputable def lquo (d : ℕ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] fun a _ ih => a / (d : ℤ) :: ih

theorem evv_lquo (d : ℕ) : ∀ (l : List ℤ) (t : ℕ → ℤ), ldiv d l = true →
    (d : ℤ) * evv (lquo d l) t = evv l t
  | [], t, _ => by simp [show lquo d [] = [] from rfl]
  | a :: as, t, h => by
    change (Nat.beq (a.natAbs % d) 0 && ldiv d as) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    have hd : (d : ℤ) ∣ a := Int.ofNat_dvd_left.2 (Nat.dvd_of_mod_eq_zero h.1)
    simp only [show lquo d (a :: as) = a / (d : ℤ) :: lquo d as from rfl, evv_cons]
    rw [mul_add, ← mul_assoc, Int.mul_ediv_cancel' hd, evv_lquo d as _ h.2]

/-- Division by `√2 ^ h`: both parts divided by `2 ^ (h / 2)`, and once more by `√2` when
`h` is odd (one pass over the coefficients instead of `h`). -/
def zdivp (h : ℕ) (x : ZL) : Option ZL :=
  if h % 2 = 0 then
    if ldiv (2 ^ (h / 2)) x.1 && ldiv (2 ^ (h / 2)) x.2 then
      some (lquo (2 ^ (h / 2)) x.1, lquo (2 ^ (h / 2)) x.2)
    else none
  else
    if ldiv (2 ^ (h / 2 + 1)) x.1 && ldiv (2 ^ (h / 2)) x.2 then
      some (lquo (2 ^ (h / 2)) x.2, lquo (2 ^ (h / 2 + 1)) x.1)
    else none

theorem mk_mul_mk (c A B : ℤ) : (⟨c, 0⟩ : ℤ√2) * ⟨A, B⟩ = ⟨c * A, c * B⟩ := by ext <;> simp

theorem rt2_mul_mk (A B : ℤ) : rt2 * ⟨A, B⟩ = ⟨2 * B, A⟩ := by ext <;> simp [rt2]

theorem zdivp_sound (h : ℕ) {x y : ZL} (e : zdivp h x = some y) (t : ℕ → ℤ) :
    rt2 ^ h * zev y t = zev x t := by
  unfold zdivp at e
  set m := h / 2 with hm
  split_ifs at e with h0 hd hd
  · cases e
    rw [Bool.and_eq_true] at hd
    have e1 := evv_lquo _ _ (c1 t) hd.1
    have e2 := evv_lquo _ _ (c1 t) hd.2
    push_cast at e1 e2
    rw [show h = 2 * m by omega, rt2_pow_even]
    simp only [zev, mk_mul_mk]
    rw [e1, e2]
  · cases e
    rw [Bool.and_eq_true] at hd
    have e1 := evv_lquo _ _ (c1 t) hd.1
    have e2 := evv_lquo _ _ (c1 t) hd.2
    push_cast at e1 e2
    rw [show h = 2 * m + 1 by omega, pow_succ, mul_assoc, rt2_pow_even]
    simp only [zev, rt2_mul_mk, mk_mul_mk]
    rw [← mul_assoc, ← pow_succ, e1, e2]

/-- The constant is odd and the other coefficients even. -/
def oddSure (x : ZL) : Bool :=
  match x.1 with
  | [] => false
  | c :: cs => Nat.beq (c.natAbs % 2) 1 && allEven cs

theorem odd_of_oddSure {x : ZL} (h : oddSure x = true) (t : ℕ → ℤ) : Odd (zev x t).re := by
  obtain ⟨x1, x2⟩ := x
  cases x1 with
  | nil => simp [oddSure] at h
  | cons c cs =>
    simp only [oddSure, Bool.and_eq_true, Nat.beq_eq, natAbs_mod_two_eq_one] at h
    simp only [zev, evv_c1]
    obtain ⟨m, hm⟩ := even_evv cs t h.2
    exact ⟨c / 2 + m, by rw [hm]; omega⟩

theorem not_odd_of_allEven {x : ZL} (h : allEven x.1 = true) (t : ℕ → ℤ) : ¬Odd (zev x t).re := by
  rw [Int.not_odd_iff_even]; exact even_evv _ _ h

/-! ### Patterns and the scaled action -/

/-- The window values of a pattern. -/
def pv {w : ℕ} (P : List ZL) (t : ℕ → ℤ) : Fin w → ℤ√2 := fun j => zev (P.getD j dZ) t

/-- One letter on a pattern, at the entry `j`. -/
def scgE {w : ℕ} (g : Gen w) (P : List ZL) (j : ℕ) : ZL :=
  match g with
  | .Z p => if j = p.1 then zneg (P.getD j dZ) else P.getD j dZ
  | .X p q _ => if j = p.1 then P.getD q.1 dZ else if j = q.1 then P.getD p.1 dZ else P.getD j dZ
  | .H p q _ => if j = p.1 then zadd (P.getD p.1 dZ) (P.getD q.1 dZ)
      else if j = q.1 then zsub (P.getD p.1 dZ) (P.getD q.1 dZ) else zrt2 (P.getD j dZ)

/-- One letter on a pattern. -/
def scgL {w : ℕ} (g : Gen w) (P : List ZL) : List ZL := (List.range w).map (scgE g P)

/-- A word (written order) on a pattern. -/
def scwL {w : ℕ} : List (Gen w) → List ZL → List ZL
  | [], P => P
  | g :: ws, P => scgL g (scwL ws P)

theorem scgL_getD {w : ℕ} (g : Gen w) (P : List ZL) (j : Fin w) :
    (scgL g P).getD j dZ = scgE g P j := by
  simp [scgL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2]

theorem scgE_sound {w : ℕ} (g : Gen w) (P : List ZL) (t : ℕ → ℤ) (j : Fin w) :
    zev (scgE g P j) t = scg g (pv P t) j := by
  cases g with
  | Z p =>
    simp only [scgE, scg, pv, Fin.ext_iff]
    split_ifs <;> simp_all [zev_zneg]
  | X p q _ =>
    simp only [scgE, scg, pv, Fin.ext_iff]
    split_ifs <;> simp_all
  | H p q _ =>
    simp only [scgE, scg, pv, Fin.ext_iff]
    split_ifs <;> simp_all [zev_zadd, zev_zsub, zev_zrt2]

theorem scwL_sound {w : ℕ} : ∀ (ws : List (Gen w)) (P : List ZL) (t : ℕ → ℤ) (j : Fin w),
    zev ((scwL ws P).getD j dZ) t = scw ws (pv P t) j
  | [], P, t, j => rfl
  | g :: ws, P, t, j => by
    rw [scwL, scgL_getD, scgE_sound, scw]
    congr 1
    funext i
    exact scwL_sound ws P t i

/-! ### The check -/

/-- The entry `j` of the state `ws (s)` at the exponent of `s` (`none` if it
is not integral for every value of the parameters). -/
def divAt {w : ℕ} (P : List ZL) (ws : List (Gen w)) (j : ℕ) : Option ZL :=
  zdivp (hcntw ws) ((scwL ws P).getD j dZ)

/-- The entry `j` is possibly odd. -/
def maybeOdd {w : ℕ} (P : List ZL) (ws : List (Gen w)) (j : ℕ) : Bool :=
  match divAt P ws j with
  | some y => !allEven y.1
  | none => true

/-- The state `ws (s)` is integral with fewer odd window entries than `s`. -/
def stOK {w : ℕ} (P : List ZL) (ws : List (Gen w)) : Bool :=
  (List.range w).all (fun j => (divAt P ws j).isSome) &&
    decide ((List.range w).countP (maybeOdd P ws) <
      (List.range w).countP (fun j => oddSure (P.getD j dZ)))

/-- Every state of the path `D` from `A s`. -/
def pathOK {w : ℕ} (P : List ZL) (D A : List (Gen w)) : Bool :=
  (List.range (D.length + 1)).all fun k => stOK P (D.drop k ++ A)

theorem card_filter_univ_fin {w : ℕ} (p : ℕ → Bool) :
    (univ.filter fun j : Fin w => p j = true).card = (List.range w).countP p := by
  rw [List.countP_eq_length_filter]
  have : (univ.filter fun j : Fin w => p j = true) =
      ((List.range w).filter p).toFinset.attachFin (fun m hm => by
        simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hm; exact hm.1) := by
    ext j; simp
  rw [this, Finset.card_attachFin, List.toFinset_card_of_nodup]
  exact (List.nodup_range).filter _

/-! ### Substitution -/

/-- `Σ cᵢ φᵢ` for the coefficients `c` and the forms `φ` (a zero coefficient is skipped: the
forms are sparse, and the kernel would otherwise multiply and add every coefficient of `φᵢ`). -/
def sumL : List ℤ → List (List ℤ) → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | c :: cs, f :: fs => if c.natAbs = 0 then sumL cs fs else ladd (lsmul c f) (sumL cs fs)

/-- Substitute the form `φᵢ` for the parameter `tᵢ`. -/
def substL (l : List ℤ) (φ : List (List ℤ)) : List ℤ :=
  match l with
  | [] => []
  | c :: cs => ladd [c] (sumL cs φ)

theorem evv_sumL : ∀ (cs : List ℤ) (φ : List (List ℤ)) (u : ℕ → ℤ),
    evv (sumL cs φ) u = evv cs (fun i => evv (φ.getD i []) u)
  | [], φ, u => by simp [sumL]
  | c :: cs, [], u => by
    simp only [sumL, evv_nil, evv_cons, List.getD_nil]
    have : ∀ (cs : List ℤ), evv cs (fun _ => 0) = 0 := by
      intro cs; induction cs with
      | nil => rfl
      | cons a as ih => simp [evv_cons, ih]
    simp [this]
  | c :: cs, f :: fs, u => by
    simp only [sumL]
    split_ifs with hc
    · rw [Int.natAbs_eq_zero] at hc
      subst hc
      simp [evv_cons, evv_sumL cs fs u]
    · simp only [evv_ladd, evv_lsmul, evv_cons, evv_sumL cs fs u]
      simp

theorem evv_substL (l : List ℤ) (φ : List (List ℤ)) (t : ℕ → ℤ) :
    evv (substL l φ) (c1 t) = evv l (c1 fun i => evv (φ.getD i []) (c1 t)) := by
  cases l with
  | nil => simp [substL]
  | cons c cs =>
    simp only [substL, evv_ladd, evv_c1, evv_nil, add_zero, evv_sumL]

def zsubst (x : ZL) (φ : List (List ℤ)) : ZL := (substL x.1 φ, substL x.2 φ)

/-- Substitute in every entry. -/
def Psubst (P : List ZL) (φ : List (List ℤ)) : List ZL := P.map (zsubst · φ)

theorem zev_Psubst (P : List ZL) (φ : List (List ℤ)) (t : ℕ → ℤ) (j : ℕ) :
    zev ((Psubst P φ).getD j dZ) t = zev (P.getD j dZ) fun i => evv (φ.getD i []) (c1 t) := by
  simp only [Psubst, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : P[j]? with
  | none => simp [dZ, zev, zsubst, substL]
  | some x => simp [zev, zsubst, evv_substL]

/-- A window of pattern `Psubst Q φ` has pattern `Q` (at the substituted
parameters). -/
theorem pat_conv {n w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P Q : List ZL}
    {φ : List (List ℤ)} (e : Psubst Q φ = P) {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    ∀ j : Fin w, num v (f j) = zev (Q.getD j dZ) fun i => evv (φ.getD i []) (c1 t) := by
  intro j; rw [hP, ← e, zev_Psubst]

theorem evv_congr : ∀ (l : List ℤ) {t t' : ℕ → ℤ}, (∀ i < l.length, t i = t' i) →
    evv l t = evv l t'
  | [], _, _, _ => rfl
  | c :: cs, t, t', h => by
    rw [evv_cons, evv_cons, h 0 (by simp), evv_congr cs fun i hi => h (i + 1) (by simp; omega)]

/-- Every form of the pattern has at most `nv` parameters. -/
def Pwidth (P : List ZL) (nv : ℕ) : Bool :=
  P.all fun x => decide (x.1.length ≤ nv + 1) && decide (x.2.length ≤ nv + 1)

theorem zev_congr {P : List ZL} {nv : ℕ} (hw : Pwidth P nv = true) {t t' : ℕ → ℤ}
    (h : ∀ i < nv, t i = t' i) (j : ℕ) : zev (P.getD j dZ) t = zev (P.getD j dZ) t' := by
  have hc : ∀ i < nv + 1, c1 t i = c1 t' i := by
    intro i hi; cases i with
    | zero => rfl
    | succ i => exact h i (by omega)
  simp only [List.getD_eq_getElem?_getD]
  cases hj : P[j]? with
  | none => rfl
  | some x =>
    have hx : x ∈ P := List.mem_of_getElem? hj
    simp only [Pwidth, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨h1, h2⟩ := hw x hx
    simp only [Option.getD_some, zev]
    rw [evv_congr x.1 fun i hi => hc i (by omega), evv_congr x.2 fun i hi => hc i (by omega)]

/-- A window of pattern `P` (in `nv` parameters) has pattern `Psubst P φ` at
parameters `t'` whose substituted values are `t`. -/
theorem pat_refine {n w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P : List ZL} {nv : ℕ}
    (hw : Pwidth P nv = true) (φ : List (List ℤ)) {t t' : ℕ → ℤ}
    (ht : ∀ i < nv, evv (φ.getD i []) (c1 t') = t i)
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    ∀ j : Fin w, num v (f j) = zev ((Psubst P φ).getD j dZ) t' := by
  intro j; rw [hP, zev_Psubst]; exact zev_congr hw (fun i hi => (ht i hi).symm) j

/-- The form of the parameter `tᵢ`. -/
def ivar (i : ℕ) : List ℤ := 0 :: (List.replicate i 0 ++ [1])

theorem evv_ivar (i : ℕ) (t : ℕ → ℤ) : evv (ivar i) (c1 t) = t i := by
  rw [ivar, evv_c1, zero_add]
  induction i generalizing t with
  | zero => simp [evv_cons]
  | succ i ih => rw [List.replicate_succ, List.cons_append, evv_cons, ih]; simp

/-- Substitute `L` for the parameter `v` and keep the others (of `nv`). -/
def splitφ (nv v : ℕ) (L : List ℤ) : List (List ℤ) :=
  (List.range nv).map fun i => if i = v then L else ivar i

/-- A case split: substitute for the parameter `v` a form `L` in which the new
value `x` of `v` gives back the old one. -/
theorem pat_split {n w : ℕ} {v : Fin n → ℝ} {f : Fin w → Fin n} {P : List ZL} {nv : ℕ}
    (hw : Pwidth P nv = true) (p : ℕ) (L : List ℤ) {t : ℕ → ℤ} (x : ℤ)
    (hx : evv L (c1 (Function.update t p x)) = t p)
    (hP : ∀ j : Fin w, num v (f j) = zev (P.getD j dZ) t) :
    ∀ j : Fin w, num v (f j) = zev ((Psubst P (splitφ nv p L)).getD j dZ)
      (Function.update t p x) := by
  refine pat_refine hw _ (fun i hi => ?_) hP
  simp only [splitφ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  split_ifs with h
  · subst h; exact hx
  · rw [evv_ivar, Function.update_of_ne h]

/-! ### The window after a word -/

/-- The window after a word, at the old exponent. -/
def divAll {w : ℕ} (P : List ZL) (K : List (Gen w)) : List ZL :=
  (List.range w).map fun j => (divAt P K j).getD dZ

/-- Every entry of the window after the word is integral. -/
def allSome {w : ℕ} (P : List ZL) (K : List (Gen w)) : Bool :=
  (List.range w).all fun j => (divAt P K j).isSome

theorem divAll_getD {w : ℕ} (P : List ZL) (K : List (Gen w)) (j : Fin w) :
    (divAll P K).getD j dZ = (divAt P K j).getD dZ := by
  simp [divAll, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2]

theorem divAll_sound {w : ℕ} {P : List ZL} {K : List (Gen w)} (hc : allSome P K = true)
    (t : ℕ → ℤ) (j : Fin w) :
    rt2 ^ hcntw K * zev ((divAll P K).getD j dZ) t = scw K (pv P t) j := by
  have : (divAt P K j).isSome = true := by
    simp only [allSome, List.all_eq_true, List.mem_range] at hc; exact hc j j.2
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
  rw [divAll_getD, hy, Option.getD_some, zdivp_sound _ hy t, scwL_sound]

/-- The window has the same odd entries before and after. -/
def sameOdd {w : ℕ} (P P' : List ZL) : Bool :=
  (List.range w).all fun j =>
    (oddSure (P.getD j dZ) && oddSure (P'.getD j dZ)) ||
      (allEven (P.getD j dZ).1 && allEven (P'.getD j dZ).1)

theorem sameOdd_iff {w : ℕ} {P P' : List ZL} (h : sameOdd (w := w) P P' = true) (t : ℕ → ℤ)
    (j : Fin w) : Odd (zev (P'.getD j dZ) t).re ↔ Odd (zev (P.getD j dZ) t).re := by
  simp only [sameOdd, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h j j.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact iff_of_true (odd_of_oddSure h2 t) (odd_of_oddSure h1 t)
  · exact iff_of_false (not_odd_of_allEven h2 t) (not_odd_of_allEven h1 t)

/-- The entry `j` of the window after `K`, `δ` below the old exponent. -/
def divAtD {w : ℕ} (P : List ZL) (K : List (Gen w)) (δ j : ℕ) : Option ZL :=
  zdivp (hcntw K + δ) ((scwL K P).getD j dZ)

def divAllD {w : ℕ} (P : List ZL) (K : List (Gen w)) (δ : ℕ) : List ZL :=
  (List.range w).map fun j => (divAtD P K δ j).getD dZ

def allSomeD {w : ℕ} (P : List ZL) (K : List (Gen w)) (δ : ℕ) : Bool :=
  (List.range w).all fun j => (divAtD P K δ j).isSome

theorem divAllD_sound {w : ℕ} {P : List ZL} {K : List (Gen w)} {δ : ℕ}
    (hc : allSomeD P K δ = true) (t : ℕ → ℤ) (j : Fin w) :
    rt2 ^ (hcntw K + δ) * zev ((divAllD P K δ).getD j dZ) t = scw K (pv P t) j := by
  have : (divAtD P K δ j).isSome = true := by
    simp only [allSomeD, List.all_eq_true, List.mem_range] at hc; exact hc j j.2
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
  have e : (divAllD P K δ).getD j dZ = (divAtD P K δ j).getD dZ := by
    simp [divAllD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [e, hy, Option.getD_some, zdivp_sound _ hy t, scwL_sound]

/-- Odd with a constant: the constant odd and the other coefficients even. -/
def oddSureL : List ℤ → Bool
  | [] => false
  | c :: cs => Nat.beq (c.natAbs % 2) 1 && allEven cs

theorem odd_of_oddSureL {l : List ℤ} (h : oddSureL l = true) (t : ℕ → ℤ) : Odd (evv l (c1 t)) := by
  cases l with
  | nil => simp [oddSureL] at h
  | cons c cs =>
    simp only [oddSureL, Bool.and_eq_true, Nat.beq_eq, natAbs_mod_two_eq_one] at h
    rw [evv_c1]
    obtain ⟨m, hm⟩ := even_evv cs t h.2
    exact ⟨c / 2 + m, by rw [hm]; omega⟩

/-- Surely odd of the class `γ` (the parity of the `√2` part). -/
def isCls (γ : Bool) (x : ZL) : Bool := oddSure x && (if γ then oddSureL x.2 else allEven x.2)

/-- Surely not odd of the class `γ`. -/
def notCls (γ : Bool) (x : ZL) : Bool :=
  allEven x.1 || (oddSure x && (if γ then allEven x.2 else oddSureL x.2))

theorem isCls_iff {γ : Bool} {x : ZL} (h : (isCls γ x || notCls γ x) = true) (t : ℕ → ℤ) :
    (Odd (zev x t).re ∧ (Odd (zev x t).im ↔ γ = true)) ↔ isCls γ x = true := by
  have hre := fun h => odd_of_oddSure (x := x) h t
  have hev := fun h => not_odd_of_allEven (x := x) h t
  have him1 : oddSureL x.2 = true → Odd (zev x t).im := fun h => odd_of_oddSureL h t
  have him0 : allEven x.2 = true → ¬Odd (zev x t).im := fun h => by
    rw [Int.not_odd_iff_even]; exact even_evv _ _ h
  by_cases hi : isCls γ x = true
  · rw [iff_true_right hi]
    simp only [isCls, Bool.and_eq_true] at hi
    refine ⟨hre hi.1, ?_⟩
    cases γ <;> simp only [Bool.false_eq_true, if_false, if_true] at hi
    · simp [him0 hi.2]
    · simp [him1 hi.2]
  · rw [iff_false_right hi]
    simp only [hi, Bool.false_or, notCls, Bool.or_eq_true, Bool.and_eq_true] at h
    rintro ⟨a, b⟩
    rcases h with h | ⟨-, h2⟩
    · exact hev h a
    · cases γ
      · simp only [Bool.false_eq_true, if_false, iff_false] at h2 b
        exact b (him1 h2)
      · simp only [if_true, iff_true] at h2 b
        exact him0 h2 b

/-- Every entry has a sure status, and the class `γ` has a count of parity
`par`. -/
def clsCount {w : ℕ} (V : List ZL) (γ : Bool) (par : ℕ) : Bool :=
  (List.range w).all (fun j => isCls γ (V.getD j dZ) || notCls γ (V.getD j dZ)) &&
    (List.range w).countP (fun j => isCls γ (V.getD j dZ)) % 2 == par

theorem card_cls {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {U : Fin n → ℤ√2}
    {V : List ZL} {t : ℕ → ℤ} (hU : ∀ j, U (f j) = zev (V.getD j dZ) t) {γ : Bool} {par : ℕ}
    (hc : clsCount (w := w) V γ par = true) :
    ((univ.map ⟨f, hf.injective⟩).filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)).card
      % 2 = par := by
  classical
  simp only [clsCount, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  obtain ⟨hall, hcnt⟩ := hc
  rw [Finset.filter_map, Finset.card_map]
  have : (univ.filter ((fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)) ∘
      (⟨f, hf.injective⟩ : Fin w ↪ Fin n))) =
      univ.filter fun j : Fin w => isCls γ (V.getD j dZ) = true := by
    ext j
    simp only [mem_filter, mem_univ, true_and, Function.comp, Function.Embedding.coeFn_mk, hU]
    exact isCls_iff (hall j j.2) t
  rw [this, card_filter_univ_fin (fun j => isCls γ (V.getD j dZ))]
  exact hcnt

end

end QCert.HadamardPi
