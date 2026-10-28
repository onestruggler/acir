/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symbolic numerators: patterns of a window, checked by evaluation

A *pattern* describes the numerators of a window of the pivot column as
`ℤ√2`-valued affine forms in integer parameters `t₀, t₁, …`: an affine form
is the list of its coefficients, the constant first (`evv l (c1 t)`), and an
entry of the window is a pair of forms (its rational and its `√2` part,
`zev`).  The scaled action of a word on numerators (`scw`, `Window.lean`) is
computed on patterns (`scwL`), and dividing by `√2` is a check that the
rational part has even coefficients (`zdiv`).

`pathOK P D A` checks, by evaluation, that every state of the path `D`
from `A s` is integral at the exponent of `s` and has fewer odd numerators
on the window than `s` has, for *every* value of the parameters: an entry
counts as possibly odd unless all its coefficients are even, and as odd in
`s` only if its constant is odd and its other coefficients even.  Then the
path is below `s` (`path_of_check`, by `lev_lt_of_window_word`), and with a
derivation it is a join (`join_of_check`).

Patterns are refined by substituting affine forms for the parameters
(`Psubst`, `pv_Psubst`): this is how a case split on the parity of a form
in the parameters, and the change from one parametrisation of a set of
windows to another, are carried out.
-/
import QCert.HadamardPi.Join
import QCert.HadamardPi.Extend

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

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

/-- Sum of forms. -/
def ladd : List ℤ → List ℤ → List ℤ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: ladd as bs

theorem evv_ladd : ∀ (a b : List ℤ) (t : ℕ → ℤ), evv (ladd a b) t = evv a t + evv b t
  | [], l, t => by simp [ladd]
  | a :: as, [], t => by simp [ladd]
  | a :: as, b :: bs, t => by simp only [ladd, evv_cons, evv_ladd as bs]; ring

/-- A multiple of a form. -/
def lsmul (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: as => c * a :: lsmul c as

theorem evv_lsmul (c : ℤ) : ∀ (l : List ℤ) (t : ℕ → ℤ), evv (lsmul c l) t = c * evv l t
  | [], t => by simp [lsmul]
  | a :: as, t => by simp only [lsmul, evv_cons, evv_lsmul c as]; ring

/-- Every coefficient is even. -/
def allEven : List ℤ → Bool
  | [] => true
  | a :: as => a % 2 == 0 && allEven as

/-- Half of every coefficient. -/
def lhalf : List ℤ → List ℤ
  | [] => []
  | a :: as => a / 2 :: lhalf as

theorem evv_lhalf : ∀ (l : List ℤ) (t : ℕ → ℤ), allEven l = true → 2 * evv (lhalf l) t = evv l t
  | [], t, _ => by simp [lhalf]
  | a :: as, t, h => by
    simp only [allEven, Bool.and_eq_true, beq_iff_eq] at h
    simp only [lhalf, evv_cons]
    rw [← evv_lhalf as _ h.2]
    have : 2 * (a / 2) = a := by omega
    linear_combination t 0 * this

theorem even_evv : ∀ (l : List ℤ) (t : ℕ → ℤ), allEven l = true → Even (evv l t)
  | [], t, _ => by simp
  | a :: as, t, h => by
    simp only [allEven, Bool.and_eq_true, beq_iff_eq] at h
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

/-- Division by `√2 ^ h`. -/
def zdivp : ℕ → ZL → Option ZL
  | 0, x => some x
  | h + 1, x => (zdiv x).bind (zdivp h)

theorem zdivp_sound : ∀ (h : ℕ) {x y : ZL}, zdivp h x = some y → ∀ t : ℕ → ℤ,
    rt2 ^ h * zev y t = zev x t
  | 0, x, y, e, t => by simp only [zdivp, Option.some.injEq] at e; subst e; simp
  | h + 1, x, y, e, t => by
    simp only [zdivp, Option.bind_eq_some_iff] at e
    obtain ⟨x', h1, h2⟩ := e
    rw [pow_succ, mul_comm (rt2 ^ h), mul_assoc, zdivp_sound h h2 t, zdiv_sound h1 t]

/-- The constant is odd and the other coefficients even. -/
def oddSure (x : ZL) : Bool :=
  match x.1 with
  | [] => false
  | c :: cs => c % 2 == 1 && allEven cs

theorem odd_of_oddSure {x : ZL} (h : oddSure x = true) (t : ℕ → ℤ) : Odd (zev x t).re := by
  obtain ⟨x1, x2⟩ := x
  cases x1 with
  | nil => simp [oddSure] at h
  | cons c cs =>
    simp only [oddSure, Bool.and_eq_true, beq_iff_eq] at h
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

/-- The check gives a path below `s`. -/
theorem path_of_check {n w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hfJ : ∀ j, (f j : ℕ) < piv s) {P : List ZL}
    {t : ℕ → ℤ} (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    {D A : List (Gen w)} (hc : pathOK P D A = true) :
    PathLt (lev s) (D.map (Gen.map f hf)) (run (A.map (Gen.map f hf)) s) := by
  classical
  apply pathLt_of_drop
  intro k hk'
  rw [List.length_map] at hk'
  have hck : stOK P (D.drop k ++ A) = true := by
    simp only [pathOK, List.all_eq_true, List.mem_range] at hc
    exact hc k (by omega)
  rw [← run_append, ← List.map_drop, ← List.map_append]
  set ws := D.drop k ++ A
  simp only [stOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck
  obtain ⟨hsome, hcnt⟩ := hck
  have hpv : (fun j : Fin w => num (col s (pj s (piv_pos hs))) (f j)) = pv P t := funext hP
  refine lev_lt_of_window_word hs hk f hf hfJ (fun j => zev ((divAt P ws j).getD dZ) t) ?_ ?_
  · intro j
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hsome j j.2)
    beta_reduce
    rw [hy, Option.getD_some, hpv, ← scwL_sound]
    exact zdivp_sound _ hy t
  · refine card_filter_lt (univ.filter fun j : Fin w => maybeOdd P ws j = true)
      (univ.filter fun j : Fin w => oddSure (P.getD j dZ) = true) ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_univ, true_and, maybeOdd] at hj
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hsome j j.2)
      beta_reduce
      rw [hy] at hj ⊢
      simp only [Bool.not_eq_true', Bool.not_eq_false'] at hj
      simp only [Option.getD_some]
      exact not_odd_of_allEven (by simpa using hj) t
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [hP j]; exact odd_of_oddSure hj t
    · rw [card_filter_univ_fin (maybeOdd P ws),
        card_filter_univ_fin (fun j => oddSure (P.getD j dZ))]
      exact hcnt

/-- A checked path with a derivation is a join. -/
theorem join_of_check {n w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hfJ : ∀ j, (f j : ℕ) < piv s) {P : List ZL}
    {t : ℕ → ℤ} (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    {D A B : List (Gen w)} (hd : Derivable Fig6 (ofList (D ++ A)) (ofList B))
    (hc : pathOK P D A = true) :
    Join s (A.map (Gen.map f hf)) (B.map (Gen.map f hf)) := by
  refine ⟨D.map (Gen.map f hf), ?_, path_of_check f hf hs hk hfJ hP hc⟩
  rw [← List.map_append]
  exact der_map f hf hd

/-! ### Substitution -/

/-- `Σ cᵢ φᵢ` for the coefficients `c` and the forms `φ`. -/
def sumL : List ℤ → List (List ℤ) → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | c :: cs, f :: fs => ladd (lsmul c f) (sumL cs fs)

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
    simp only [sumL, evv_ladd, evv_lsmul, evv_cons, evv_sumL cs fs u]
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

end QCert.HadamardPi
