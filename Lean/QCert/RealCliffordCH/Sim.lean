/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Deciding circuit identities by simulation

`decide` on the matrices `opsQ.eval n w` themselves is too slow: the
kernel multiplies functions on basis states, summing over the `Fintype` of
states for every entry.  Here a circuit is instead *simulated* on vectors
stored as nested pairs (`Vec n`, split on wire `0` first), one gate at a
time, column by column; `act g` is proved to compute the action of the
gate's operator (`gen_mulVec`), so that equal simulations give equal
operators (`eval_eq_of_check`, `eval_eq_of_checkM`).
-/
import QCert.RealCliffordCH.Semantics

namespace QCert.RealCliffordCH.Sim

open Matrix

/-- The scalars: ℚ(√2). -/
abbrev Q := QSqrt2

/-- Vectors on `n` wires, as nested pairs: the first component is the part
where wire `0` is `0`, and each component a vector on the wires above. -/
@[reducible] def Vec : ℕ → Type
  | 0 => Q
  | n + 1 => Vec n × Vec n

/-- The zero vector. -/
def zero : (n : ℕ) → Vec n
  | 0 => (0 : Q)
  | n + 1 => (zero n, zero n)

/-- Sum of vectors. -/
def add : {n : ℕ} → Vec n → Vec n → Vec n
  | 0, a, b => (a + b : Q)
  | _ + 1, a, b => (add a.1 b.1, add a.2 b.2)

/-- A vector times a scalar. -/
def smul : {n : ℕ} → Q → Vec n → Vec n
  | 0, c, a => (c * a : Q)
  | _ + 1, c, a => (smul c a.1, smul c a.2)

/-- The opposite of a vector. -/
def neg : {n : ℕ} → Vec n → Vec n
  | 0, a => (-a : Q)
  | _ + 1, a => (neg a.1, neg a.2)

/-- Difference of vectors. -/
def sub : {n : ℕ} → Vec n → Vec n → Vec n
  | 0, a, b => (a - b : Q)
  | _ + 1, a, b => (sub a.1 b.1, sub a.2 b.2)

/-- The vector as a function of basis states. -/
def toFun : {n : ℕ} → Vec n → State 2 n → Q
  | 0, a, _ => a
  | _ + 1, a, s => toFun (if s 0 = 0 then a.1 else a.2) (Fin.tail s)

/-- The entries of a vector, in order. -/
def toList : {n : ℕ} → Vec n → List Q
  | 0, a => [a]
  | _ + 1, a => toList a.1 ++ toList a.2

/-- The basis vector of a state. -/
def basis : {n : ℕ} → State 2 n → Vec n
  | 0, _ => (1 : Q)
  | n + 1, t => if t 0 = 0 then (basis (Fin.tail t), zero n) else (zero n, basis (Fin.tail t))

/-- All basis vectors. -/
def basisList : (n : ℕ) → List (Vec n)
  | 0 => [(1 : Q)]
  | n + 1 => (basisList n).map (fun b => (b, zero n)) ++ (basisList n).map (fun b => (zero n, b))

/-- The vector of a function of basis states. -/
def ofFun : {n : ℕ} → (State 2 n → Q) → Vec n
  | 0, f => f Fin.elim0
  | _ + 1, f => (ofFun fun s => f (Fin.cons 0 s), ofFun fun s => f (Fin.cons 1 s))

/-- All basis states. -/
def allStates : (n : ℕ) → List (State 2 n)
  | 0 => [Fin.elim0]
  | n + 1 => (allStates n).map (Fin.cons 0) ++ (allStates n).map (Fin.cons 1)

section Lemmas

variable {n : ℕ}

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨_ | _ | a, h⟩
  · left; rfl
  · right; rfl
  · omega

@[simp] theorem toFun_zero : ∀ n, toFun (zero n) = 0
  | 0 => rfl
  | n + 1 => by
    funext s; simp only [toFun, zero, ite_self, toFun_zero n]; rfl

theorem toFun_add : ∀ {n} (u v : Vec n), toFun (add u v) = toFun u + toFun v
  | 0, _, _ => rfl
  | _ + 1, u, v => by
    funext s
    simp only [toFun, add, Pi.add_apply]
    split_ifs <;> rw [toFun_add] <;> rfl

theorem toFun_smul : ∀ {n} (c : Q) (u : Vec n), toFun (smul c u) = c • toFun u
  | 0, _, _ => rfl
  | _ + 1, c, u => by
    funext s
    simp only [toFun, smul, Pi.smul_apply]
    split_ifs <;> rw [toFun_smul] <;> rfl

theorem toFun_neg : ∀ {n} (u : Vec n), toFun (neg u) = -toFun u
  | 0, _ => rfl
  | _ + 1, u => by
    funext s
    simp only [toFun, neg, Pi.neg_apply]
    split_ifs <;> rw [toFun_neg] <;> rfl

theorem toFun_sub : ∀ {n} (u v : Vec n), toFun (sub u v) = toFun u - toFun v
  | 0, _, _ => rfl
  | _ + 1, u, v => by
    funext s
    simp only [toFun, sub, Pi.sub_apply]
    split_ifs <;> rw [toFun_sub] <;> rfl

theorem length_toList : ∀ {n} (v : Vec n), (toList v).length = 2 ^ n
  | 0, _ => rfl
  | _ + 1, v => by simp [toList, length_toList, pow_succ]; ring

theorem toList_inj : ∀ {n} {u v : Vec n}, toList u = toList v → u = v
  | 0, u, v, h => by simpa [toList] using h
  | _ + 1, u, v, h => by
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_toList, length_toList])
    exact Prod.ext (toList_inj h1) (toList_inj h2)

theorem state_eq_iff {n : ℕ} (s t : State 2 (n + 1)) :
    s = t ↔ s 0 = t 0 ∧ Fin.tail s = Fin.tail t := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail s, ← Fin.cons_self_tail t, h0, ht]

theorem toFun_basis : ∀ {n} (t : State 2 n), toFun (basis t) = Pi.single t 1
  | 0, t => by
    funext s
    have : s = t := funext fun i => i.elim0
    subst this; simp [toFun, basis]
  | _ + 1, t => by
    funext s
    have e := state_eq_iff s t
    simp only [toFun, basis, Pi.single_apply, e]
    rcases fin2_cases (t 0) with ht | ht <;> rcases fin2_cases (s 0) with hs | hs <;>
      simp [ht, hs, toFun_basis, Pi.single_apply]

theorem basis_mem : ∀ {n} (t : State 2 n), basis t ∈ basisList n
  | 0, _ => by simp [basis, basisList]
  | _ + 1, t => by
    simp only [basis, basisList, List.mem_append, List.mem_map]
    split_ifs
    · exact Or.inl ⟨_, basis_mem _, rfl⟩
    · exact Or.inr ⟨_, basis_mem _, rfl⟩

theorem toFun_ofFun : ∀ {n} (f : State 2 n → Q), toFun (ofFun f) = f
  | 0, f => by
    funext s
    have : s = Fin.elim0 := funext fun i => i.elim0
    subst this; rfl
  | _ + 1, f => by
    funext s
    simp only [toFun, ofFun]
    rcases fin2_cases (s 0) with hs | hs
    · rw [if_pos hs, toFun_ofFun, ← hs, Fin.cons_self_tail]
    · rw [if_neg (by rw [hs]; decide), toFun_ofFun, ← hs, Fin.cons_self_tail]

theorem mem_allStates : ∀ {n} (t : State 2 n), t ∈ allStates n
  | 0, t => by
    have : t = Fin.elim0 := funext fun i => i.elim0
    subst this; simp [allStates]
  | _ + 1, t => by
    simp only [allStates, List.mem_append, List.mem_map]
    rcases fin2_cases (t 0) with ht | ht
    · exact Or.inl ⟨_, mem_allStates (Fin.tail t), by rw [← ht, Fin.cons_self_tail]⟩
    · exact Or.inr ⟨_, mem_allStates (Fin.tail t), by rw [← ht, Fin.cons_self_tail]⟩

end Lemmas

/-! ## Gates on vectors -/

/-- The one-wire state `b`. -/
def st1 (b : Fin 2) : State 2 1 := fun _ => b

/-- The two-wire state with `a` on wire `0` and `b` on wire `1`. -/
def st2 (a b : Fin 2) : State 2 2 := ![a, b]

/-- A one-wire operator on wire `0`. -/
def act1 (G : Op Q 2 1) {n : ℕ} (v : Vec (n + 1)) : Vec (n + 1) :=
  (add (smul (G (st1 0) (st1 0)) v.1) (smul (G (st1 0) (st1 1)) v.2),
   add (smul (G (st1 1) (st1 0)) v.1) (smul (G (st1 1) (st1 1)) v.2))

/-- One row of a two-wire operator on wires `0, 1`. -/
def row2 (G : Op Q 2 2) (a b : Fin 2) {n : ℕ} (v : Vec (n + 2)) : Vec n :=
  add (add (smul (G (st2 a b) (st2 0 0)) v.1.1) (smul (G (st2 a b) (st2 0 1)) v.1.2))
    (add (smul (G (st2 a b) (st2 1 0)) v.2.1) (smul (G (st2 a b) (st2 1 1)) v.2.2))

/-- A two-wire operator on wires `0, 1`. -/
def act2 (G : Op Q 2 2) {n : ℕ} (v : Vec (n + 2)) : Vec (n + 2) :=
  ((row2 G 0 0 v, row2 G 0 1 v), (row2 G 1 0 v, row2 G 1 1 v))

/-- `H` on wire `0`. -/
def actH {n : ℕ} (v : Vec (n + 1)) : Vec (n + 1) :=
  (smul QSqrt2.invSqrt2 (add v.1 v.2), smul QSqrt2.invSqrt2 (sub v.1 v.2))

/-- `Z` on wire `0`. -/
def actZ {n : ℕ} (v : Vec (n + 1)) : Vec (n + 1) := (v.1, neg v.2)

/-- `CZ` on wires `0, 1`. -/
def actCZ {n : ℕ} (v : Vec (n + 2)) : Vec (n + 2) := ((v.1.1, v.1.2), (v.2.1, neg v.2.2))

/-- `CH` from wire `1` onto wire `0`. -/
def actCH {n : ℕ} (v : Vec (n + 2)) : Vec (n + 2) :=
  ((v.1.1, smul QSqrt2.invSqrt2 (add v.1.2 v.2.2)),
   (v.2.1, smul QSqrt2.invSqrt2 (sub v.1.2 v.2.2)))

/-- The action of a generator. -/
def act : {n : ℕ} → Gen Gate n → Vec n → Vec n
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 .H, v => actH v
  | _, .gate1 .Z, v => actZ v
  | _, .gate2 .CZ, v => actCZ v
  | _, .gate2 .CH, v => actCH v
  | _, .gate3 g, _ => nomatch g
  | _, .up g, v => (act g v.1, act g v.2)

/-- The action of a circuit, in operator order. -/
def actW {n : ℕ} (w : Circ n) (v : Vec n) : Vec n :=
  w.toList.foldr act v

/-- Two circuits act alike on every basis vector. -/
def check {n : ℕ} (w w' : Circ n) : Bool :=
  (basisList n).all fun b => toList (actW w b) == toList (actW w' b)

/-- A circuit acts on every basis vector as an operator does. -/
def checkM {n : ℕ} (w : Circ n) (M : Op Q 2 n) : Bool :=
  (allStates n).all fun t => toList (actW w (basis t)) == toList (ofFun fun s => M s t)

/-! ## Correctness -/

section Correct

variable {n : ℕ}

theorem split1_fst (s : State 2 (n + 1)) : (split 2 n 1 s).1 = st1 (s 0) := by
  funext i; fin_cases i; rfl

theorem split1_snd (s : State 2 (n + 1)) : (split 2 n 1 s).2 = Fin.tail s := by
  funext j; simp only [split, Equiv.coe_fn_mk, Fin.tail]; congr 1; ext; simp; omega

theorem split1_symm (l : State 2 1) (h : State 2 n) :
    (split 2 n 1).symm (l, h) = Fin.cons (l 0) h := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.cons_succ, Fin.val_succ]
    rw [dif_neg (by omega)]; congr 1

theorem split2_fst (s : State 2 (n + 2)) : (split 2 n 2 s).1 = st2 (s 0) (s 1) := by
  funext i; fin_cases i <;> rfl

theorem split2_snd (s : State 2 (n + 2)) : (split 2 n 2 s).2 = Fin.tail (Fin.tail s) := by
  funext j; simp only [split, Equiv.coe_fn_mk, Fin.tail]; congr 1; ext; simp; omega

theorem split2_symm (l : State 2 2) (h : State 2 n) :
    (split 2 n 2).symm (l, h) = Fin.cons (l 0) (Fin.cons (l 1) h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · simp only [split, Equiv.coe_fn_symm_mk, Fin.cons_succ, Fin.val_succ]
      rw [dif_neg (by omega)]; congr 1

theorem sum_state1 (f : State 2 1 → Q) : ∑ l, f l = f (st1 0) + f (st1 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]; rfl

theorem sum_state2 (f : State 2 2 → Q) :
    ∑ l, f l = f (st2 0 0) + f (st2 0 1) + (f (st2 1 0) + f (st2 1 1)) := by
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rfl

theorem toFun_cons (v : Vec (n + 1)) (b : Fin 2) (h : State 2 n) :
    toFun v (Fin.cons b h) = toFun (if b = 0 then v.1 else v.2) h := by
  simp only [toFun, Fin.cons_zero, Fin.tail_cons]

theorem onBottom1_mulVec (G : Op Q 2 1) (v : Vec (n + 1)) :
    onBottom (n := n) G *ᵥ toFun v = toFun (act1 G v) := by
  funext s
  rw [mulVec, dotProduct, ← (split 2 n 1).symm.sum_comp, Fintype.sum_prod_type]
  simp only [onBottom_apply, Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_ite_eq _ _ _]
  simp only [Finset.mem_univ, if_true, split1_symm, toFun_cons, split1_fst, split1_snd]
  rw [sum_state1]
  simp only [st1, act1, toFun]
  rcases fin2_cases (s 0) with hs | hs <;>
    simp [hs, toFun_add, toFun_smul]

theorem onBottom2_mulVec (G : Op Q 2 2) (v : Vec (n + 2)) :
    onBottom (n := n) G *ᵥ toFun v = toFun (act2 G v) := by
  funext s
  rw [mulVec, dotProduct, ← (split 2 n 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [onBottom_apply, Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_ite_eq _ _ _]
  simp only [Finset.mem_univ, if_true, split2_symm, toFun_cons, split2_fst, split2_snd]
  rw [sum_state2]
  simp only [st2, act2, row2, toFun, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rcases fin2_cases (s 0) with hs | hs <;> rcases fin2_cases (s 1) with hs1 | hs1 <;>
    simp [hs, hs1, Fin.tail, toFun_add, toFun_smul]

theorem onTop1_mulVec (M : Op Q 2 n) (f : Vec n → Vec n)
    (hf : ∀ v, M *ᵥ toFun v = toFun (f v)) (v : Vec (n + 1)) :
    onTop 1 M *ᵥ toFun v = toFun ((f v.1, f v.2) : Vec (n + 1)) := by
  funext s
  rw [mulVec, dotProduct, ← (split 2 n 1).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [onTop_apply, Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl fun h _ => Finset.sum_ite_eq _ _ _]
  simp only [Finset.mem_univ, if_true, split1_symm, toFun_cons, split1_fst, split1_snd]
  have key : ∀ u : Vec n, ∑ h, M (Fin.tail s) h * toFun u h = toFun (f u) (Fin.tail s) := by
    intro u; rw [← hf u]; rfl
  simp only [st1, toFun]
  split_ifs <;> exact key _

theorem toFun_pair (a b : Vec n) (s : State 2 (n + 1)) :
    toFun ((a, b) : Vec (n + 1)) s = if s 0 = 0 then toFun a (Fin.tail s) else toFun b (Fin.tail s) := by
  show toFun (if s 0 = 0 then a else b) (Fin.tail s) = _
  split_ifs <;> rfl

theorem toFun_pair2 (a b c d : Vec n) (s : State 2 (n + 2)) :
    toFun (((a, b), (c, d)) : Vec (n + 2)) s =
      if s 0 = 0 then (if s 1 = 0 then toFun a (Fin.tail (Fin.tail s)) else toFun b (Fin.tail (Fin.tail s)))
      else (if s 1 = 0 then toFun c (Fin.tail (Fin.tail s)) else toFun d (Fin.tail (Fin.tail s))) := by
  show toFun (if Fin.tail s 0 = 0 then _ else _) (Fin.tail (Fin.tail s)) = _
  by_cases h0 : s 0 = 0 <;> by_cases h1 : s 1 = 0 <;>
    simp only [h0, h1, Fin.tail, Fin.succ_zero_eq_one, if_true, if_false]

theorem one_ne_zero_fin : (1 : Fin 2) ≠ 0 := by decide

/-- The linear-combination lemmas, pointwise. -/
theorem toFun_add_apply (u v : Vec n) (s : State 2 n) :
    toFun (add u v) s = toFun u s + toFun v s := by rw [toFun_add]; rfl

theorem toFun_sub_apply (u v : Vec n) (s : State 2 n) :
    toFun (sub u v) s = toFun u s - toFun v s := by rw [toFun_sub]; rfl

theorem toFun_smul_apply (c : Q) (u : Vec n) (s : State 2 n) :
    toFun (smul c u) s = c * toFun u s := by rw [toFun_smul]; rfl

theorem toFun_neg_apply (u : Vec n) (s : State 2 n) :
    toFun (neg u) s = -toFun u s := by rw [toFun_neg]; rfl

theorem act1_H (v : Vec (n + 1)) : toFun (act1 (opsQ.gate1 .H) v) = toFun (actH v) := by
  obtain ⟨h00, h01, h10, h11⟩ : opsQ.gate1 .H (st1 0) (st1 0) = QSqrt2.invSqrt2 ∧
      opsQ.gate1 .H (st1 0) (st1 1) = QSqrt2.invSqrt2 ∧
      opsQ.gate1 .H (st1 1) (st1 0) = QSqrt2.invSqrt2 ∧
      opsQ.gate1 .H (st1 1) (st1 1) = -QSqrt2.invSqrt2 := by decide +kernel
  funext s
  simp only [act1, actH, toFun_pair, h00, h01, h10, h11, toFun_add_apply, toFun_sub_apply,
    toFun_smul_apply]
  split_ifs <;> ring

theorem act1_Z (v : Vec (n + 1)) : toFun (act1 (opsQ.gate1 .Z) v) = toFun (actZ v) := by
  obtain ⟨h00, h01, h10, h11⟩ : opsQ.gate1 .Z (st1 0) (st1 0) = 1 ∧
      opsQ.gate1 .Z (st1 0) (st1 1) = 0 ∧ opsQ.gate1 .Z (st1 1) (st1 0) = 0 ∧
      opsQ.gate1 .Z (st1 1) (st1 1) = -1 := by decide +kernel
  funext s
  simp only [act1, actZ, toFun_pair, h00, h01, h10, h11, toFun_add_apply, toFun_neg_apply,
    toFun_smul_apply]
  split_ifs <;> ring

theorem act2_CZ (v : Vec (n + 2)) : toFun (act2 (opsQ.gate2 .CZ) v) = toFun (actCZ v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :
      opsQ.gate2 .CZ (st2 0 0) (st2 0 0) = 1 ∧ opsQ.gate2 .CZ (st2 0 0) (st2 0 1) = 0 ∧
      opsQ.gate2 .CZ (st2 0 0) (st2 1 0) = 0 ∧ opsQ.gate2 .CZ (st2 0 0) (st2 1 1) = 0 ∧
      opsQ.gate2 .CZ (st2 0 1) (st2 0 0) = 0 ∧ opsQ.gate2 .CZ (st2 0 1) (st2 0 1) = 1 ∧
      opsQ.gate2 .CZ (st2 0 1) (st2 1 0) = 0 ∧ opsQ.gate2 .CZ (st2 0 1) (st2 1 1) = 0 ∧
      opsQ.gate2 .CZ (st2 1 0) (st2 0 0) = 0 ∧ opsQ.gate2 .CZ (st2 1 0) (st2 0 1) = 0 ∧
      opsQ.gate2 .CZ (st2 1 0) (st2 1 0) = 1 ∧ opsQ.gate2 .CZ (st2 1 0) (st2 1 1) = 0 ∧
      opsQ.gate2 .CZ (st2 1 1) (st2 0 0) = 0 ∧ opsQ.gate2 .CZ (st2 1 1) (st2 0 1) = 0 ∧
      opsQ.gate2 .CZ (st2 1 1) (st2 1 0) = 0 ∧ opsQ.gate2 .CZ (st2 1 1) (st2 1 1) = -1 := by
    decide +kernel
  funext s
  simp only [act2, row2, actCZ, toFun_pair2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, toFun_add_apply, toFun_neg_apply, toFun_smul_apply]
  split_ifs <;> ring

theorem act2_CH (v : Vec (n + 2)) : toFun (act2 (opsQ.gate2 .CH) v) = toFun (actCH v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :
      opsQ.gate2 .CH (st2 0 0) (st2 0 0) = 1 ∧ opsQ.gate2 .CH (st2 0 0) (st2 0 1) = 0 ∧
      opsQ.gate2 .CH (st2 0 0) (st2 1 0) = 0 ∧ opsQ.gate2 .CH (st2 0 0) (st2 1 1) = 0 ∧
      opsQ.gate2 .CH (st2 0 1) (st2 0 0) = 0 ∧
      opsQ.gate2 .CH (st2 0 1) (st2 0 1) = QSqrt2.invSqrt2 ∧
      opsQ.gate2 .CH (st2 0 1) (st2 1 0) = 0 ∧
      opsQ.gate2 .CH (st2 0 1) (st2 1 1) = QSqrt2.invSqrt2 ∧
      opsQ.gate2 .CH (st2 1 0) (st2 0 0) = 0 ∧ opsQ.gate2 .CH (st2 1 0) (st2 0 1) = 0 ∧
      opsQ.gate2 .CH (st2 1 0) (st2 1 0) = 1 ∧ opsQ.gate2 .CH (st2 1 0) (st2 1 1) = 0 ∧
      opsQ.gate2 .CH (st2 1 1) (st2 0 0) = 0 ∧
      opsQ.gate2 .CH (st2 1 1) (st2 0 1) = QSqrt2.invSqrt2 ∧
      opsQ.gate2 .CH (st2 1 1) (st2 1 0) = 0 ∧
      opsQ.gate2 .CH (st2 1 1) (st2 1 1) = -QSqrt2.invSqrt2 := by
    decide +kernel
  funext s
  simp only [act2, row2, actCH, toFun_pair2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, toFun_add_apply, toFun_sub_apply, toFun_smul_apply]
  split_ifs <;> ring

theorem gen_mulVec : ∀ {n} (g : Gen Gate n) (v : Vec n), opsQ.gen g *ᵥ toFun v = toFun (act g v)
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 .H, v => (onBottom1_mulVec _ v).trans (act1_H v)
  | _, .gate1 .Z, v => (onBottom1_mulVec _ v).trans (act1_Z v)
  | _, .gate2 .CZ, v => (onBottom2_mulVec _ v).trans (act2_CZ v)
  | _, .gate2 .CH, v => (onBottom2_mulVec _ v).trans (act2_CH v)
  | _, .gate3 g, _ => nomatch g
  | _, .up g, v => onTop1_mulVec _ (act g) (gen_mulVec g) v

theorem eval_mulVec (w : Circ n) (v : Vec n) :
    opsQ.eval n w *ᵥ toFun v = toFun (actW w v) := by
  induction w using FreeMonoid.inductionOn' generalizing v with
  | one => simp [actW]
  | mul_of g w ih =>
    rw [map_mul, ← mulVec_mulVec, ih]
    show opsQ.gen g *ᵥ _ = _
    rw [gen_mulVec]; rfl

theorem eval_apply (w : Circ n) (s t : State 2 n) :
    opsQ.eval n w s t = toFun (actW w (basis t)) s := by
  rw [← eval_mulVec, toFun_basis, mulVec_single_one]; rfl

/-- Circuits that act alike on every basis vector have the same operator. -/
theorem eval_eq_of_check {w w' : Circ n} (h : check w w' = true) :
    opsQ.eval n w = opsQ.eval n w' := by
  funext s t
  rw [eval_apply, eval_apply]
  rw [check, List.all_eq_true] at h
  have := h _ (basis_mem t)
  rw [beq_iff_eq] at this
  rw [toList_inj this]

/-- A circuit that acts on every basis vector as `M` does has operator `M`. -/
theorem eval_eq_of_checkM {w : Circ n} {M : Op Q 2 n} (h : checkM w M = true) :
    opsQ.eval n w = M := by
  funext s t
  rw [eval_apply]
  rw [checkM, List.all_eq_true] at h
  have := h _ (mem_allStates t)
  rw [beq_iff_eq] at this
  rw [toList_inj this, toFun_ofFun]

end Correct

end QCert.RealCliffordCH.Sim
