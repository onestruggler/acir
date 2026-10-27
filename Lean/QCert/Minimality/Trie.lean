/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Evaluating circuits in the kernel

`GateOps.eval` is the matrix of a circuit, a function of two basis states;
deciding an equation between two such matrices with `decide +kernel` makes
the kernel recompute products of functions entry by entry, which is
exponential in the length of the circuit.  Here a matrix is stored as data:
a *trie* of its rows, each row a trie of its entries, `d`-ary trees whose
first level is the digit of wire `0` (the shape of the framework's splitting
`split`, bottom wires first).  A gate on the bottom `a` wires combines the
subtries at depth `a` linearly (`Trie.bottom`), a generator moved up acts
inside each branch (`applyGen`), and the rows of the matrix of a circuit are
obtained by applying its generators to the rows of the identity
(`evalRows`).  The denotation of a trie (`LinRep.den`) is a function of
states, and `den_evalRows` says that the trie computed for a circuit
denotes its matrix.  Equal tries therefore give equal matrices
(`eval_eq_of_evalRows`); the tries are compared by `decide +kernel` on lists
of exact numbers.
-/
import QCert.Circuit.Eval

namespace QCert.Minimality

open Matrix

universe u v

/-! ### Lists of the digits -/

/-- `[0, 1, …, d - 1]`, by structural recursion (evaluated by the kernel). -/
def finList : (d : ℕ) → List (Fin d)
  | 0 => []
  | d + 1 => 0 :: (finList d).map Fin.succ

theorem finList_getD_map {α : Type u} {d : ℕ} (f : Fin d → α) (z : α) (i : Fin d) :
    ((finList d).map f).getD i z = f i := by
  induction d with
  | zero => exact i.elim0
  | succ d ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [finList, List.map_cons, List.map_map, Fin.val_succ, List.getD_cons_succ]
      exact ih (f ∘ Fin.succ) i

theorem finList_sum {M : Type*} [AddCommMonoid M] {d : ℕ} (f : Fin d → M) :
    ((finList d).map f).sum = ∑ i, f i := by
  induction d with
  | zero => simp [finList]
  | succ d ih =>
    simp only [finList, List.map_cons, List.map_map, List.sum_cons, Fin.sum_univ_succ]
    rw [ih (f ∘ Fin.succ)]; rfl

/-! ### Linear representations -/

/-- Linear operations on a type of values. -/
structure LinOps (K : Type) (L : Type u) where
  zero : L
  add : L → L → L
  smul : K → L → L

/-- Linear operations whose meaning lies in a module. -/
structure LinRep (K : Type) [Semiring K] (L : Type u) (V : Type v) [AddCommMonoid V]
    [Module K V] where
  ops : LinOps K L
  den : L → V
  den_zero : den ops.zero = 0
  den_add : ∀ a b, den (ops.add a b) = den a + den b
  den_smul : ∀ c a, den (ops.smul c a) = c • den a

/-- The scalars themselves. -/
def LinRep.base (K : Type) [CommRing K] : LinRep K K K where
  ops := ⟨0, (· + ·), (· * ·)⟩
  den := id
  den_zero := rfl
  den_add _ _ := rfl
  den_smul _ _ := rfl

/-! ### Tries -/

/-- Tries of depth `n` with values in `L`: `d`-ary trees, the first level
being the digit of wire `0`. -/
def Trie (L : Type u) (d : ℕ) : ℕ → Type u
  | 0 => L
  | n + 1 => List (Trie L d n)

instance Trie.decEq {L : Type u} [DecidableEq L] {d : ℕ} : (n : ℕ) → DecidableEq (Trie L d n)
  | 0 => inferInstanceAs (DecidableEq L)
  | n + 1 => @instDecidableEqList _ (Trie.decEq n)

namespace Trie

variable {K : Type} {L : Type u} {d : ℕ}

/-- The pointwise linear operations on tries. -/
def ops (o : LinOps K L) : (n : ℕ) → LinOps K (Trie L d n)
  | 0 => o
  | n + 1 =>
    { zero := ((finList d).map fun _ => (ops o n).zero : List (Trie L d n))
      add := fun a b => ((finList d).map fun (j : Fin d) =>
        (ops o n).add ((a : List (Trie L d n)).getD (j : ℕ) (ops o n).zero)
          ((b : List (Trie L d n)).getD (j : ℕ) (ops o n).zero) : List (Trie L d n))
      smul := fun c a => ((finList d).map fun (j : Fin d) =>
        (ops o n).smul c ((a : List (Trie L d n)).getD (j : ℕ) (ops o n).zero) : List (Trie L d n)) }

/-- The value at a state. -/
def get (o : LinOps K L) : (n : ℕ) → Trie L d n → State d n → L
  | 0, T, _ => T
  | n + 1, T, s => get o n ((T : List (Trie L d n)).getD (s 0) (ops o n).zero) (fun i => s i.succ)

/-- The trie of a function of states. -/
def ofFn : (n : ℕ) → (State d n → L) → Trie L d n
  | 0, f => f Fin.elim0
  | n + 1, f => ((finList d).map fun j => ofFn n (fun t => f (Fin.cons j t)) : List (Trie L d n))

theorem get_ofFn (o : LinOps K L) (n : ℕ) (f : State d n → L) (s : State d n) :
    get o n (ofFn n f) s = f s := by
  induction n with
  | zero => show f Fin.elim0 = f s; congr 1; funext i; exact i.elim0
  | succ n ih =>
    simp only [get, ofFn, finList_getD_map]
    rw [ih]
    congr 1
    exact Fin.cons_self_tail s

end Trie

variable {K : Type} [CommRing K] {L : Type u} {V : Type v} [AddCommMonoid V] [Module K V]
  {d : ℕ}

section TrieRep

variable (R : LinRep K L V)

theorem den_get_zero : ∀ (n : ℕ) (s : State d n),
    R.den (Trie.get R.ops n (Trie.ops R.ops n).zero s) = 0
  | 0, _ => R.den_zero
  | n + 1, s => by
    simp only [Trie.ops, Trie.get, finList_getD_map]
    exact den_get_zero n _

theorem den_get_add : ∀ (n : ℕ) (a b : Trie L d n) (s : State d n),
    R.den (Trie.get R.ops n ((Trie.ops R.ops n).add a b) s) =
      R.den (Trie.get R.ops n a s) + R.den (Trie.get R.ops n b s)
  | 0, a, b, _ => R.den_add a b
  | n + 1, a, b, s => by
    simp only [Trie.ops, Trie.get, finList_getD_map]
    exact den_get_add n _ _ _

theorem den_get_smul : ∀ (n : ℕ) (c : K) (a : Trie L d n) (s : State d n),
    R.den (Trie.get R.ops n ((Trie.ops R.ops n).smul c a) s) = c • R.den (Trie.get R.ops n a s)
  | 0, c, a, _ => R.den_smul c a
  | n + 1, c, a, s => by
    simp only [Trie.ops, Trie.get, finList_getD_map]
    exact den_get_smul n _ _ _

/-- Tries represent functions of states pointwise. -/
def LinRep.trie (n : ℕ) : LinRep K (Trie L d n) (State d n → V) where
  ops := Trie.ops R.ops n
  den T s := R.den (Trie.get R.ops n T s)
  den_zero := funext (den_get_zero R n)
  den_add a b := funext (den_get_add R n a b)
  den_smul c a := funext (den_get_smul R n c a)

theorem LinRep.trie_den (n : ℕ) (T : Trie L d n) (s : State d n) :
    (R.trie n).den T s = R.den (Trie.get R.ops n T s) := rfl

theorem LinRep.trie_den_succ (n : ℕ) (T : Trie L d (n + 1)) (s : State d (n + 1)) :
    (R.trie (n + 1)).den T s =
      (R.trie n).den ((T : List (Trie L d n)).getD (s 0) (R.trie n).ops.zero)
        (fun i => s i.succ) :=
  rfl

end TrieRep

/-! ### Linear combinations -/

/-- `c • x`, without multiplying by `1`. -/
def scaleBy [DecidableEq K] {X : Type u} (o : LinOps K X) (c : K) (x : X) : X :=
  if c = 1 then x else o.smul c x

/-- `∑ cᵢ • xᵢ`, skipping the zero coefficients and multiplying by no `1`. -/
def lincomb [DecidableEq K] {X : Type u} (o : LinOps K X) : List (K × X) → X
  | [] => o.zero
  | (c, x) :: rest =>
    if c = 0 then lincomb o rest
    else if rest.all (fun p => decide (p.1 = 0)) then scaleBy o c x
    else o.add (scaleBy o c x) (lincomb o rest)

theorem den_lincomb [DecidableEq K] {X : Type u} {W : Type v} [AddCommMonoid W] [Module K W]
    (R : LinRep K X W) (l : List (K × X)) :
    R.den (lincomb R.ops l) = (l.map fun p => p.1 • R.den p.2).sum := by
  induction l with
  | nil => simp [lincomb, R.den_zero]
  | cons p rest ih =>
    obtain ⟨c, x⟩ := p
    have hy : R.den (scaleBy R.ops c x) = c • R.den x := by
      unfold scaleBy
      split_ifs with h
      · rw [h, one_smul]
      · exact R.den_smul c x
    have hrest : rest.all (fun p => decide (p.1 = 0)) = true →
        (rest.map fun p => p.1 • R.den p.2).sum = 0 := by
      intro h
      apply List.sum_eq_zero
      intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      have := List.all_eq_true.1 h p hp
      simp only [decide_eq_true_eq] at this
      simp [this]
    simp only [lincomb, List.map_cons, List.sum_cons]
    split_ifs with h0 hall
    · rw [ih, h0, zero_smul, zero_add]
    · rw [hy, hrest hall, add_zero]
    · rw [R.den_add, hy, ih]

/-! ### All states -/

/-- All states of `a` wires. -/
def allSt : (a : ℕ) → List (State d a)
  | 0 => [Fin.elim0]
  | a + 1 => ((finList d).map fun j => (allSt a).map (Fin.cons j)).flatten

theorem allSt_sum {M : Type*} [AddCommMonoid M] (a : ℕ) (f : State d a → M) :
    ((allSt a).map f).sum = ∑ s, f s := by
  induction a with
  | zero =>
    simp only [allSt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Fintype.sum_unique]
    congr 1
  | succ a ih =>
    simp only [allSt, List.map_flatten, List.sum_flatten, List.map_map]
    have : (List.sum ∘ List.map f ∘ fun j => List.map (Fin.cons j) (allSt a)) =
        fun j : Fin d => ∑ t : State d a, f (Fin.cons j t) := by
      funext j
      simp only [Function.comp_apply, List.map_map]
      exact ih _
    rw [this, finList_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin d) _ _ (fun _ => rfl)

/-! ### Splitting the wires -/

section Split

variable {m : ℕ}

theorem split_snd_succ {a : ℕ} (s : State d (m + (a + 1))) :
    (split d m (a + 1) s).2 = (split d m a (fun i => s i.succ)).2 := by
  funext j
  simp only [split, Equiv.coe_fn_mk]
  congr 1
  ext
  simp only [Fin.val_succ]
  omega

theorem split_zero_snd (s : State d (m + 0)) : (split d m 0 s).2 = s := by
  funext j
  simp only [split, Equiv.coe_fn_mk]
  congr 1
  ext
  simp

theorem split_one_symm_zero {n : ℕ} (b : State d 1) (t : State d n) :
    ((split d n 1).symm (b, t) : State d (n + 1)) 0 = b 0 := rfl

theorem split_one_symm_succ {n : ℕ} (b : State d 1) (t : State d n) :
    (fun i : Fin n => ((split d n 1).symm (b, t) : State d (n + 1)) i.succ) = t := by
  funext i
  simp only [split, Equiv.coe_fn_symm_mk, Fin.val_succ]
  rw [dif_neg (by omega)]
  congr 1

theorem split_one_snd {n : ℕ} (s : State d (n + 1)) :
    (split d n 1 s).2 = fun i => s i.succ := by
  funext j
  simp only [split, Equiv.coe_fn_mk]
  congr 1
  ext
  simp only [Fin.val_succ]
  omega

end Split

/-! ### Gate application -/

namespace Trie

variable {m : ℕ}

/-- The subtrie at the digits `v` of the bottom `a` wires. -/
def sub (o : LinOps K L) : (a : ℕ) → Trie L d (m + a) → State d a → Trie L d m
  | 0, T, _ => T
  | a + 1, T, v => sub o a ((T : List (Trie L d (m + a))).getD (v 0) (ops o (m + a)).zero)
      (fun i => v i.succ)

/-- The trie whose subtrie at the digits `j` of the bottom `a` wires is `f j`. -/
def build : (a : ℕ) → (State d a → Trie L d m) → Trie L d (m + a)
  | 0, f => f Fin.elim0
  | a + 1, f => ((finList d).map fun j => build a (fun v => f (Fin.cons j v)) :
      List (Trie L d (m + a)))

end Trie

section Den

variable (R : LinRep K L V) {m : ℕ}

theorem den_sub (a : ℕ) (T : Trie L d (m + a)) (s : State d (m + a)) :
    (R.trie (m + a)).den T s =
      (R.trie m).den (Trie.sub R.ops a T (split d m a s).1) (split d m a s).2 := by
  induction a with
  | zero =>
    show (R.trie m).den T s = (R.trie m).den T _
    rw [split_zero_snd]
  | succ a ih =>
    show (R.trie (m + a + 1)).den T s = _
    rw [R.trie_den_succ, ih, split_snd_succ]
    rfl

theorem den_build (a : ℕ) (f : State d a → Trie L d m) (s : State d (m + a)) :
    (R.trie (m + a)).den (Trie.build a f) s =
      (R.trie m).den (f (split d m a s).1) (split d m a s).2 := by
  induction a with
  | zero =>
    show (R.trie m).den (f Fin.elim0) s = _
    have h0 : (split d m 0 s).1 = Fin.elim0 := funext fun i => i.elim0
    rw [split_zero_snd, h0]
  | succ a ih =>
    show (R.trie (m + a + 1)).den (Trie.build (a + 1) f) s = _
    rw [R.trie_den_succ]
    simp only [Trie.build, finList_getD_map]
    rw [ih, split_snd_succ]
    congr 3
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl

/-- A gate on the bottom `a` wires, applied to the rows of a matrix. -/
def Trie.bottom [DecidableEq K] (a m : ℕ) (G : Op K d a) (T : Trie L d (m + a)) :
    Trie L d (m + a) :=
  Trie.build a fun j =>
    lincomb (R.trie m).ops ((allSt a).map fun v => (G j v, Trie.sub R.ops a T v))

theorem den_bottom [DecidableEq K] (a m : ℕ) (G : Op K d a) (T : Trie L d (m + a))
    (s : State d (m + a)) :
    (R.trie (m + a)).den (Trie.bottom R a m G T) s =
      ∑ u, onBottom (n := m) G s u • (R.trie (m + a)).den T u := by
  have lhs : (R.trie (m + a)).den (Trie.bottom R a m G T) s =
      ∑ v, G (split d m a s).1 v • (R.trie m).den (Trie.sub R.ops a T v) (split d m a s).2 := by
    rw [Trie.bottom, den_build, den_lincomb, List.map_map]
    have := allSt_sum (d := d) a
      (fun v => G (split d m a s).1 v • (R.trie m).den (Trie.sub R.ops a T v))
    rw [show ((fun p : K × Trie L d m => p.1 • (R.trie m).den p.2) ∘
        fun v => (G (split d m a s).1 v, Trie.sub R.ops a T v)) =
        fun v => G (split d m a s).1 v • (R.trie m).den (Trie.sub R.ops a T v) from rfl, this]
    simp [Finset.sum_apply]
  rw [lhs, ← (split d m a).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single (split d m a s).2]
  · rw [onBottom_apply, Equiv.apply_symm_apply, if_pos rfl, den_sub, Equiv.apply_symm_apply]
  · intro h _ hh
    rw [onBottom_apply, Equiv.apply_symm_apply, if_neg (Ne.symm hh), zero_smul]
  · simp

end Den

/-! ### Circuits -/

section Apply

variable {Gate : ℕ → Type} [DecidableEq K] (R : LinRep K L V) (O : GateOps Gate K d)

/-- A generator applied to the rows of a matrix. -/
def applyGen : {n : ℕ} → Gen Gate n → Trie L d n → Trie L d n
  | n, .gate0 c, T => (Trie.ops R.ops n).smul (O.scalar c) T
  | _, .gate1 g, T => Trie.bottom R 1 _ (O.gate1 g) T
  | _, .gate2 g, T => Trie.bottom R 2 _ (O.gate2 g) T
  | _, .gate3 g, T => Trie.bottom R 3 _ (O.gate3 g) T
  | n + 1, .up g, T => ((finList d).map fun (j : Fin d) =>
      applyGen g ((T : List (Trie L d n)).getD (j : ℕ) (Trie.ops R.ops n).zero) : List (Trie L d n))

theorem den_applyGen : ∀ {n : ℕ} (g : Gen Gate n) (T : Trie L d n) (s : State d n),
    (R.trie n).den (applyGen R O g T) s = ∑ u, O.gen g s u • (R.trie n).den T u
  | n, .gate0 c, T, s => by
    show (R.trie n).den ((R.trie n).ops.smul (O.scalar c) T) s = _
    rw [(R.trie n).den_smul]
    simp only [GateOps.gen, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.smul_apply]
  | _, .gate1 g, T, s => den_bottom R 1 _ (O.gate1 g) T s
  | _, .gate2 g, T, s => den_bottom R 2 _ (O.gate2 g) T s
  | _, .gate3 g, T, s => den_bottom R 3 _ (O.gate3 g) T s
  | n + 1, .up g, T, s => by
    rw [R.trie_den_succ]
    simp only [applyGen, finList_getD_map]
    rw [den_applyGen g]
    show _ = ∑ u, onTop 1 (O.gen g) s u • (R.trie (n + 1)).den T u
    rw [← (split d n 1).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single (split d n 1 s).1]
    · apply Finset.sum_congr rfl
      intro u _
      rw [onTop_apply, Equiv.apply_symm_apply, if_pos rfl, split_one_snd, R.trie_den_succ,
        split_one_symm_zero, split_one_symm_succ]
      congr 3
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro u _
      rw [onTop_apply, Equiv.apply_symm_apply, if_neg (Ne.symm hb), zero_smul]
    · simp

/-- The rows of the matrix of a list of generators (operator order: the
head acts last). -/
def applyList {n : ℕ} (l : List (Gen Gate n)) (T : Trie L d n) : Trie L d n :=
  l.foldr (fun g acc => applyGen R O g acc) T

end Apply

/-! ### Matrices -/

section Matrices

variable [DecidableEq K]

/-- A column with `c` at the state `s` and zeros elsewhere. -/
def unitT : (n : ℕ) → State d n → K → Trie K d n
  | 0, _, c => c
  | n + 1, s, c => ((finList d).map fun j =>
      if j = s 0 then unitT n (fun i => s i.succ) c else (Trie.ops (LinRep.base K).ops n).zero :
      List (Trie K d n))

omit [DecidableEq K] in
theorem get_unitT : ∀ (n : ℕ) (s t : State d n) (c : K),
    Trie.get (LinRep.base K).ops n (unitT n s c) t = if s = t then c else 0
  | 0, s, t, c => by
    rw [if_pos (funext fun i => i.elim0)]; rfl
  | n + 1, s, t, c => by
    simp only [Trie.get, unitT, finList_getD_map]
    by_cases h0 : t 0 = s 0
    · rw [if_pos h0, get_unitT n]
      by_cases h : s = t
      · subst h; simp
      · have h' : ¬ (fun i : Fin n => s i.succ) = fun i => t i.succ := fun h' =>
          h (funext fun i => Fin.cases (motive := fun i => s i = t i) h0.symm
            (fun j => congrFun h' j) i)
        rw [if_neg h', if_neg h]
    · have h : ¬ s = t := fun h => h0 (by rw [h])
      rw [if_neg h0, if_neg h]
      exact den_get_zero (LinRep.base K) n _

/-- The representation of a matrix by the trie of its rows. -/
def rowsRep (d n : ℕ) : LinRep K (Trie (Trie K d n) d n) (Op K d n) :=
  ((LinRep.base K).trie n).trie n

/-- The rows of the identity. -/
def idRows (d n : ℕ) : Trie (Trie K d n) d n := Trie.ofFn n fun s => unitT n s 1

omit [DecidableEq K] in
theorem den_idRows (d n : ℕ) : (rowsRep (K := K) d n).den (idRows d n) = 1 := by
  funext s t
  show Trie.get (LinRep.base K).ops n
      (Trie.get ((LinRep.base K).trie n).ops n (Trie.ofFn n fun s => unitT n s 1) s) t = _
  rw [Trie.get_ofFn, get_unitT, Matrix.one_apply]

variable {Gate : ℕ → Type} (O : GateOps Gate K d)

/-- The rows of the matrix of a circuit, computed by applying its
generators to the rows of the identity. -/
def evalRows (n : ℕ) (w : Circuit Gate n) : Trie (Trie K d n) d n :=
  applyList ((LinRep.base K).trie n) O (FreeMonoid.toList w) (idRows d n)

theorem den_evalRows (n : ℕ) (w : Circuit Gate n) :
    (rowsRep d n).den (evalRows O n w) = O.eval n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact den_idRows d n
  | mul_of g w ih =>
    funext s t
    rw [evalRows, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append]
    show (rowsRep d n).den (applyGen ((LinRep.base K).trie n) O g (evalRows O n w)) s t = _
    rw [rowsRep, den_applyGen, ← rowsRep, ih, map_mul]
    have hg : O.eval n (FreeMonoid.of g) = O.gen g := FreeMonoid.lift_eval_of _ _
    rw [hg, Matrix.mul_apply, Finset.sum_apply]
    rfl

/-- Circuits whose row tries are equal have equal matrices. -/
theorem eval_eq_of_evalRows {n : ℕ} {w w' : Circuit Gate n}
    (h : evalRows O n w = evalRows O n w') : O.eval n w = O.eval n w' := by
  rw [← den_evalRows, ← den_evalRows, h]

/-- Scaled row tries give scaled matrices. -/
theorem eval_eq_smul_of_evalRows {n : ℕ} {w w' : Circuit Gate n} (c : K)
    (h : evalRows O n w = (rowsRep d n).ops.smul c (evalRows O n w')) :
    O.eval n w = c • O.eval n w' := by
  rw [← den_evalRows, ← den_evalRows, h, LinRep.den_smul]

/-- Equal scaled row tries give equal scaled matrices. -/
theorem smul_eval_eq_of_evalRows {n : ℕ} {w w' : Circuit Gate n} (c c' : K)
    (h : (rowsRep d n).ops.smul c (evalRows O n w) = (rowsRep d n).ops.smul c' (evalRows O n w')) :
    c • O.eval n w = c' • O.eval n w' := by
  rw [← den_evalRows, ← den_evalRows, ← LinRep.den_smul, ← LinRep.den_smul, h]

/-- The entry of a matrix read off the row trie. -/
theorem eval_apply_eq {n : ℕ} (w : Circuit Gate n) (s t : State d n) :
    O.eval n w s t = Trie.get (LinRep.base K).ops n
      (Trie.get ((LinRep.base K).trie n).ops n (evalRows O n w) s) t := by
  rw [← den_evalRows]; rfl

end Matrices

end QCert.Minimality
