/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Deciding circuit identities by state-vector simulation

`GateOps.eval` composes matrices that are functions on basis states, which
the kernel evaluates lazily; for products of more than a few gates on three
wires this is too slow.  Here a vector on `n` wires is a binary tree
(`Vec`), split on the bottom wire first, a gate acts on the tree by linear
combinations of subtrees (`app`), and a circuit by acting with its gates in
turn (`sim`).  `toFun_sim` says this computes the matrix-vector product, so
two circuits have the same matrix when they agree on every basis vector
(`eval_eq_of_check`), a Boolean that `decide +kernel` evaluates.  Nothing
here depends on the gate set.
-/
import QCert.Circuit.Eval

namespace QCert.Sim

open Matrix

universe u

/-- A vector indexed by the basis states of `n` wires: a binary tree,
split first on the bottom wire (`node v₀ v₁`: `v₀` is the part with wire
`0` in state `0`). -/
inductive Vec (R : Type u) : ℕ → Type u
  | leaf (r : R) : Vec R 0
  | node {n : ℕ} (v0 v1 : Vec R n) : Vec R (n + 1)

namespace Vec

variable {R : Type u} [CommRing R]

/-- The entries of a vector. -/
def toFun : {n : ℕ} → Vec R n → State 2 n → R
  | _, .leaf r, _ => r
  | _, .node v0 v1, s => if s 0 = 0 then v0.toFun (Fin.tail s) else v1.toFun (Fin.tail s)

/-- Sum of vectors. -/
def add : {n : ℕ} → Vec R n → Vec R n → Vec R n
  | _, .leaf a, .leaf b => .leaf (a + b)
  | _, .node a0 a1, .node b0 b1 => .node (add a0 b0) (add a1 b1)

/-- A vector times a scalar, entry by entry. -/
def smulRaw (c : R) : {n : ℕ} → Vec R n → Vec R n
  | _, .leaf a => .leaf (c * a)
  | _, .node a0 a1 => .node (smulRaw c a0) (smulRaw c a1)

/-- The zero vector. -/
def zero : (n : ℕ) → Vec R n
  | 0 => .leaf 0
  | n + 1 => .node (zero n) (zero n)

/-- A vector times a scalar, with no multiplication by `0` or `1`. -/
def smul [DecidableEq R] (c : R) {n : ℕ} (v : Vec R n) : Vec R n :=
  if c = 0 then zero n else if c = 1 then v else smulRaw c v

/-- The basis vector of a basis state. -/
def basis : {n : ℕ} → State 2 n → Vec R n
  | 0, _ => .leaf 1
  | n + 1, t => if t 0 = 0 then .node (basis (Fin.tail t)) (zero n)
      else .node (zero n) (basis (Fin.tail t))

/-- Equality of vectors, as a Boolean. -/
def beq [DecidableEq R] : {n : ℕ} → Vec R n → Vec R n → Bool
  | _, .leaf a, .leaf b => decide (a = b)
  | _, .node a0 a1, .node b0 b1 => beq a0 b0 && beq a1 b1

omit [CommRing R] in
theorem eq_of_beq [DecidableEq R] : ∀ {n : ℕ} {a b : Vec R n}, beq a b = true → a = b
  | _, .leaf a, .leaf b, h => by simp only [beq, decide_eq_true_eq] at h; rw [h]
  | _, .node a0 a1, .node b0 b1, h => by
    simp only [beq, Bool.and_eq_true] at h
    rw [eq_of_beq h.1, eq_of_beq h.2]

omit [CommRing R] in
theorem toFun_node_zero {n : ℕ} (v0 v1 : Vec R n) (t : State 2 n) :
    (node v0 v1).toFun (Fin.cons 0 t) = v0.toFun t := by
  simp [toFun]

omit [CommRing R] in
theorem toFun_node_one {n : ℕ} (v0 v1 : Vec R n) (t : State 2 n) :
    (node v0 v1).toFun (Fin.cons 1 t) = v1.toFun t := by
  simp [toFun]

theorem toFun_add : ∀ {n : ℕ} (a b : Vec R n), (add a b).toFun = a.toFun + b.toFun
  | _, .leaf a, .leaf b => rfl
  | _, .node a0 a1, .node b0 b1 => by
    funext s
    simp only [add, toFun, Pi.add_apply, toFun_add]
    split_ifs <;> rfl

theorem toFun_smulRaw (c : R) : ∀ {n : ℕ} (a : Vec R n), (smulRaw c a).toFun = c • a.toFun
  | _, .leaf a => rfl
  | _, .node a0 a1 => by
    funext s
    simp only [smulRaw, toFun, Pi.smul_apply, toFun_smulRaw]
    split_ifs <;> rfl

theorem toFun_zero : ∀ (n : ℕ), (zero n : Vec R n).toFun = 0
  | 0 => rfl
  | n + 1 => by
    funext s
    simp only [zero, toFun, toFun_zero, Pi.zero_apply, ite_self]

theorem toFun_smul [DecidableEq R] (c : R) {n : ℕ} (a : Vec R n) :
    (smul c a).toFun = c • a.toFun := by
  unfold smul
  split_ifs with h0 h1
  · rw [toFun_zero, h0, zero_smul]
  · rw [h1, one_smul]
  · exact toFun_smulRaw c a

theorem toFun_basis : ∀ {n : ℕ} (t s : State 2 n),
    (basis t : Vec R n).toFun s = if s = t then 1 else 0
  | 0, t, s => by simp [basis, toFun, Subsingleton.elim s t]
  | n + 1, t, s => by
    have hst : s = t ↔ s 0 = t 0 ∧ Fin.tail s = Fin.tail t := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h0, ht⟩
        rw [← Fin.cons_self_tail s, ← Fin.cons_self_tail t, h0, ht]
    have hb : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
    simp only [basis]
    split_ifs with h1 <;> simp only [toFun] <;> split_ifs with h2 <;>
      simp only [toFun_basis, toFun_zero, Pi.zero_apply] <;>
      rcases hb (s 0) with h3 | h3 <;> rcases hb (t 0) with h4 | h4 <;> simp_all

end Vec

open Vec

variable {Gate : ℕ → Type} {R : Type u} [CommRing R] [DecidableEq R]

/-! ### Gates on trees -/

/-- The state of one wire. -/
def st1 (a : Fin 2) : State 2 1 := fun _ => a
/-- The state of two wires, wire `0` first. -/
def st2 (a b : Fin 2) : State 2 2 := ![a, b]
/-- The state of three wires, wire `0` first. -/
def st3 (a b c : Fin 2) : State 2 3 := ![a, b, c]

/-- A one-wire operator on the bottom wire. -/
def ap1 (G : Op R 2 1) : {n : ℕ} → Vec R (n + 1) → Vec R (n + 1)
  | _, .node v0 v1 =>
    .node (add (smul (G (st1 0) (st1 0)) v0) (smul (G (st1 0) (st1 1)) v1))
      (add (smul (G (st1 1) (st1 0)) v0) (smul (G (st1 1) (st1 1)) v1))

/-- The component `a` of a two-wire combination. -/
def comb2 {n : ℕ} (G : Op R 2 2) (a b : Fin 2) (v00 v01 v10 v11 : Vec R n) : Vec R n :=
  add (add (smul (G (st2 a b) (st2 0 0)) v00) (smul (G (st2 a b) (st2 0 1)) v01))
    (add (smul (G (st2 a b) (st2 1 0)) v10) (smul (G (st2 a b) (st2 1 1)) v11))

/-- A two-wire operator on the bottom two wires. -/
def ap2 (G : Op R 2 2) : {n : ℕ} → Vec R (n + 2) → Vec R (n + 2)
  | _, .node (.node v00 v01) (.node v10 v11) =>
    .node (.node (comb2 G 0 0 v00 v01 v10 v11) (comb2 G 0 1 v00 v01 v10 v11))
      (.node (comb2 G 1 0 v00 v01 v10 v11) (comb2 G 1 1 v00 v01 v10 v11))

/-- The component `a b c` of a three-wire combination. -/
def comb3 {n : ℕ} (G : Op R 2 3) (a b c : Fin 2)
    (v000 v001 v010 v011 v100 v101 v110 v111 : Vec R n) : Vec R n :=
  add (add (add (smul (G (st3 a b c) (st3 0 0 0)) v000) (smul (G (st3 a b c) (st3 0 0 1)) v001))
    (add (smul (G (st3 a b c) (st3 0 1 0)) v010) (smul (G (st3 a b c) (st3 0 1 1)) v011)))
    (add (add (smul (G (st3 a b c) (st3 1 0 0)) v100) (smul (G (st3 a b c) (st3 1 0 1)) v101))
      (add (smul (G (st3 a b c) (st3 1 1 0)) v110) (smul (G (st3 a b c) (st3 1 1 1)) v111)))

/-- A three-wire operator on the bottom three wires. -/
def ap3 (G : Op R 2 3) : {n : ℕ} → Vec R (n + 3) → Vec R (n + 3)
  | _, .node (.node (.node v000 v001) (.node v010 v011))
      (.node (.node v100 v101) (.node v110 v111)) =>
    let c := fun a b d => comb3 G a b d v000 v001 v010 v011 v100 v101 v110 v111
    .node (.node (.node (c 0 0 0) (c 0 0 1)) (.node (c 0 1 0) (c 0 1 1)))
      (.node (.node (c 1 0 0) (c 1 0 1)) (.node (c 1 1 0) (c 1 1 1)))

/-- A generator acting on a tree. -/
def app (O : GateOps Gate R 2) : {n : ℕ} → Gen Gate n → Vec R n → Vec R n
  | _, .gate0 c, v => smul (O.scalar c) v
  | _, .gate1 g, v => ap1 (O.gate1 g) v
  | _, .gate2 g, v => ap2 (O.gate2 g) v
  | _, .gate3 g, v => ap3 (O.gate3 g) v
  | _, .up g, .node v0 v1 => .node (app O g v0) (app O g v1)

/-- A circuit acting on a tree, in operator order. -/
def sim (O : GateOps Gate R 2) {n : ℕ} (w : Circuit Gate n) (v : Vec R n) : Vec R n :=
  (FreeMonoid.toList w).foldr (app O) v

/-! ### Correctness -/

omit [DecidableEq R] in
/-- An operator on the bottom `k` of `m + k` wires, applied to a vector. -/
theorem onBottom_mulVec {m k : ℕ} (G : Op R 2 k) (f : State 2 (m + k) → R)
    (s : State 2 (m + k)) :
    (onBottom (n := m) G *ᵥ f) s =
      ∑ b, G (split 2 m k s).1 b * f ((split 2 m k).symm (b, (split 2 m k s).2)) := by
  simp only [mulVec, dotProduct]
  rw [← (split 2 m k).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (split 2 m k s).2]
  · rw [onBottom_apply, Equiv.apply_symm_apply, if_pos rfl]
  · intro c _ hc
    rw [onBottom_apply, Equiv.apply_symm_apply, if_neg (Ne.symm hc), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [DecidableEq R] in
/-- An operator moved up one wire, applied to a vector. -/
theorem onTop_mulVec {m : ℕ} (M : Op R 2 m) (f : State 2 (m + 1) → R) (s : State 2 (m + 1)) :
    (onTop 1 M *ᵥ f) s =
      (M *ᵥ fun t => f ((split 2 m 1).symm ((split 2 m 1 s).1, t))) (split 2 m 1 s).2 := by
  simp only [mulVec, dotProduct]
  rw [← (split 2 m 1).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single (split 2 m 1 s).1]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [onTop_apply, Equiv.apply_symm_apply, if_pos rfl]
  · intro a _ ha
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [onTop_apply, Equiv.apply_symm_apply, if_neg (Ne.symm ha), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem split1_fst {m : ℕ} (s : State 2 (m + 1)) : (split 2 m 1 s).1 = st1 (s 0) := by
  funext i; fin_cases i; rfl

theorem split1_snd {m : ℕ} (s : State 2 (m + 1)) : (split 2 m 1 s).2 = Fin.tail s := by
  funext j; simp only [split, Equiv.coe_fn_mk, Fin.tail]; congr 1; ext; simp; omega

theorem split1_symm {m : ℕ} (a : Fin 2) (t : State 2 m) :
    (split 2 m 1).symm (st1 a, t) = Fin.cons a t := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.cons_succ, Fin.val_succ]
    rw [dif_neg (by omega)]
    exact congrArg t (Fin.ext (by simp))

theorem split2_fst {m : ℕ} (s : State 2 (m + 2)) : (split 2 m 2 s).1 = st2 (s 0) (s 1) := by
  funext i; fin_cases i <;> rfl

theorem split2_snd {m : ℕ} (s : State 2 (m + 2)) :
    (split 2 m 2 s).2 = Fin.tail (Fin.tail s) := by
  funext j; simp only [split, Equiv.coe_fn_mk, Fin.tail]; congr 1; ext; simp; omega

theorem split2_symm {m : ℕ} (a b : Fin 2) (t : State 2 m) :
    (split 2 m 2).symm (st2 a b, t) = Fin.cons a (Fin.cons b t) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · rfl
  · rfl
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.cons_succ, Fin.val_succ]
    rw [dif_neg (by omega)]
    exact congrArg t (Fin.ext (by simp))

theorem split3_fst {m : ℕ} (s : State 2 (m + 3)) :
    (split 2 m 3 s).1 = st3 (s 0) (s 1) (s 2) := by
  funext i; fin_cases i <;> rfl

theorem split3_snd {m : ℕ} (s : State 2 (m + 3)) :
    (split 2 m 3 s).2 = Fin.tail (Fin.tail (Fin.tail s)) := by
  funext j; simp only [split, Equiv.coe_fn_mk, Fin.tail]; congr 1; ext; simp; omega

theorem split3_symm {m : ℕ} (a b c : Fin 2) (t : State 2 m) :
    (split 2 m 3).symm (st3 a b c, t) = Fin.cons a (Fin.cons b (Fin.cons c t)) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i
  · rfl
  · rfl
  · rfl
  · simp only [split, Equiv.coe_fn_symm_mk, Fin.cons_succ, Fin.val_succ]
    rw [dif_neg (by omega)]
    exact congrArg t (Fin.ext (by simp))

omit [DecidableEq R] in
theorem sum_st1 (g : State 2 1 → R) : ∑ b, g b = g (st1 0) + g (st1 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]; rfl

omit [DecidableEq R] in
theorem sum_st2 (g : State 2 2 → R) :
    ∑ b, g b = g (st2 0 0) + g (st2 0 1) + (g (st2 1 0) + g (st2 1 1)) := by
  rw [← (Fin.consEquiv fun _ : Fin 2 => Fin 2).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1 <;>
  · rw [← (Fin.consEquiv fun _ : Fin 1 => Fin 2).sum_comp, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_unique, Fintype.sum_unique]
    congr 1

omit [DecidableEq R] in
theorem sum_st3 (g : State 2 3 → R) :
    ∑ b, g b = g (st3 0 0 0) + g (st3 0 0 1) + (g (st3 0 1 0) + g (st3 0 1 1)) +
      (g (st3 1 0 0) + g (st3 1 0 1) + (g (st3 1 1 0) + g (st3 1 1 1))) := by
  rw [← (Fin.consEquiv fun _ : Fin 3 => Fin 2).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1 <;>
  · rw [← (Fin.consEquiv fun _ : Fin 2 => Fin 2).sum_comp, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    congr 1 <;>
    · rw [← (Fin.consEquiv fun _ : Fin 1 => Fin 2).sum_comp, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fintype.sum_unique, Fintype.sum_unique]
      congr 1

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

theorem toFun_ap1 {n : ℕ} (G : Op R 2 1) (v : Vec R (n + 1)) :
    (ap1 G v).toFun = onBottom (n := n) G *ᵥ v.toFun := by
  match v with
  | .node v0 v1 =>
    funext s
    rw [onBottom_mulVec, sum_st1, split1_fst, split1_snd, split1_symm, split1_symm]
    simp only [ap1, toFun, toFun_add, toFun_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.cons_zero, Fin.tail_cons]
    rcases fin2_cases (s 0) with h | h <;> simp [h]

theorem toFun_ap2 {n : ℕ} (G : Op R 2 2) (v : Vec R (n + 2)) :
    (ap2 G v).toFun = onBottom (n := n) G *ᵥ v.toFun := by
  match v with
  | .node (.node v00 v01) (.node v10 v11) =>
    funext s
    rw [onBottom_mulVec, sum_st2, split2_fst, split2_snd]
    simp only [split2_symm, ap2, comb2, toFun, toFun_add, toFun_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.tail_cons]
    rcases fin2_cases (s 0) with h | h <;> rcases fin2_cases (s 1) with h' | h' <;>
      simp [h, h', Fin.tail_def]

theorem toFun_ap3 {n : ℕ} (G : Op R 2 3) (v : Vec R (n + 3)) :
    (ap3 G v).toFun = onBottom (n := n) G *ᵥ v.toFun := by
  match v with
  | .node (.node (.node v000 v001) (.node v010 v011))
      (.node (.node v100 v101) (.node v110 v111)) =>
    funext s
    rw [onBottom_mulVec, sum_st3, split3_fst, split3_snd]
    simp only [split3_symm, ap3, comb3, toFun, toFun_add, toFun_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.tail_cons]
    rcases fin2_cases (s 0) with h | h <;> rcases fin2_cases (s 1) with h' | h' <;>
      rcases fin2_cases (s 2) with h'' | h'' <;> simp [h, h', h'', Fin.tail_def]

theorem toFun_app (O : GateOps Gate R 2) {n : ℕ} (g : Gen Gate n) (v : Vec R n) :
    (app O g v).toFun = O.gen g *ᵥ v.toFun := by
  induction g with
  | gate0 c =>
    rw [app, toFun_smul]
    show _ = (O.scalar c • (1 : Op R 2 _)) *ᵥ _
    rw [smul_mulVec, one_mulVec]
  | gate1 c => exact toFun_ap1 _ v
  | gate2 c => exact toFun_ap2 _ v
  | gate3 c => exact toFun_ap3 _ v
  | @up m g ih =>
    match v with
    | .node v0 v1 =>
      funext s
      show _ = (onTop 1 (O.gen g) *ᵥ _) s
      rw [onTop_mulVec, split1_fst, split1_snd]
      simp only [app, toFun, split1_symm, Fin.cons_zero, Fin.tail_cons]
      rcases fin2_cases (s 0) with h | h <;> simp [h, ih]

theorem toFun_sim (O : GateOps Gate R 2) {n : ℕ} (w : Circuit Gate n) (v : Vec R n) :
    (sim O w v).toFun = O.eval n w *ᵥ v.toFun := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [sim, GateOps.eval]
  | mul_of g w ih =>
    have : sim O (FreeMonoid.of g * w) v = app O g (sim O w v) := rfl
    rw [this, toFun_app, ih, map_mul, mulVec_mulVec]
    rfl

/-! ### Deciding -/

/-- All basis states on `n` wires. -/
def allStates : (n : ℕ) → List (State 2 n)
  | 0 => [Fin.elim0]
  | n + 1 => (allStates n).flatMap fun s => [Fin.cons 0 s, Fin.cons 1 s]

theorem mem_allStates : ∀ {n : ℕ} (s : State 2 n), s ∈ allStates n
  | 0, s => by simp [allStates]; funext i; exact i.elim0
  | n + 1, s => by
    simp only [allStates, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Fin.tail s, mem_allStates _, ?_⟩
    have h : s = Fin.cons (s 0) (Fin.tail s) := (Fin.cons_self_tail s).symm
    rcases fin2_cases (s 0) with h0 | h0 <;> rw [h0] at h <;> simp [← h]

/-- Two circuits, scaled by `a` and `b`, agree on every basis vector. -/
def check (O : GateOps Gate R 2) {n : ℕ} (a b : R) (w v : Circuit Gate n) : Bool :=
  (allStates n).all fun t =>
    beq (smulRaw a (sim O w (basis t))) (smulRaw b (sim O v (basis t)))

theorem eval_eq_of_check (O : GateOps Gate R 2) {n : ℕ} {a b : R}
    {w v : Circuit Gate n} (h : check O a b w v = true) :
    a • O.eval n w = b • O.eval n v := by
  simp only [check, List.all_eq_true] at h
  ext s t
  have e := congrArg Vec.toFun (eq_of_beq (h t (mem_allStates t)))
  rw [toFun_smulRaw, toFun_smulRaw, toFun_sim, toFun_sim] at e
  have := congrFun e s
  simpa [mulVec, dotProduct, toFun_basis] using this

/-! ### Gates rescaled by a scalar -/

/-- If each gate of `O'` is `c^k` times the same gate of `O`, `k` a weight of
the generator, then each circuit of `O'` is `c` to the total weight times
the same circuit of `O`. -/
theorem eval_weight {R : Type u} [CommRing R] (O O' : GateOps Gate R 2) (c : R)
    (k : {n : ℕ} → Gen Gate n → ℕ)
    (h : ∀ {n : ℕ} (g : Gen Gate n), O'.gen g = c ^ k g • O.gen g) {n : ℕ}
    (w : Circuit Gate n) :
    O'.eval n w = c ^ ((FreeMonoid.toList w).map k).sum • O.eval n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [GateOps.eval]
  | mul_of g w ih =>
    have e1 : O'.eval n (FreeMonoid.of g * w) = O'.gen g * O'.eval n w := by rw [map_mul]; rfl
    have e2 : O.eval n (FreeMonoid.of g * w) = O.gen g * O.eval n w := by rw [map_mul]; rfl
    rw [e1, e2, ih, h, smul_mul_smul_comm, ← pow_add, FreeMonoid.toList_of_mul]
    simp

end QCert.Sim
