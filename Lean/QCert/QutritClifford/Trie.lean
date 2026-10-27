/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Evaluating qutrit circuits on vectors stored as tries

`GateOps.eval` composes matrices indexed by basis states, and the kernel,
which does not share intermediate results, recomputes every entry of a
product from scratch: a product of `k` gates on `N` basis states costs
`N ^ (k - 1)` operations per entry.  Here a vector on `n` qutrits is a trie
of nested triples (`Vec R n`, wire 0 outermost), a gate acts on it by a
recursion on its wires (`act`), and two circuits have the same operator
when they send every basis vector to the same trie (`eval_eq_of_cols`).
Each gate application is then one pass over the trie, so `decide +kernel`
checks an equation between circuits of `k` gates on `n` qutrits in about
`k · 9ⁿ` ring operations.

This file is generic in the gate set: it serves any gate family on qutrits
over any commutative ring with decidable equality.
-/
import QCert.Circuit.Eval

namespace QCert.QutritClifford

open Matrix

universe u

/-- Vectors on `n` qutrits: a trie of nested triples, the outermost level
indexed by the digit on wire 0. -/
inductive Vec (R : Type u) : ℕ → Type u
  | leaf : R → Vec R 0
  | node {n : ℕ} : Vec R n → Vec R n → Vec R n → Vec R (n + 1)

namespace Vec

variable {R : Type u}

/-- The scalar of a trie on no wires. -/
def val : Vec R 0 → R
  | leaf a => a

/-- The sub-trie at the digit `x` of the outermost wire. -/
def sel {n : ℕ} : Vec R (n + 1) → Fin 3 → Vec R n
  | node a b c, x => ![a, b, c] x

/-- Decidable equality, by structural recursion. -/
def decEq [DecidableEq R] : {n : ℕ} → (u v : Vec R n) → Decidable (u = v)
  | _, leaf a, leaf b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | _, node a b c, node a' b' c' =>
    match decEq a a', decEq b b', decEq c c' with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (h1 ▸ h2 ▸ h3 ▸ rfl)
    | isFalse h1, _, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2, _ => isFalse (fun e => by cases e; exact h2 rfl)
    | _, _, isFalse h3 => isFalse (fun e => by cases e; exact h3 rfl)

instance [DecidableEq R] {n : ℕ} : DecidableEq (Vec R n) := decEq

/-- The entry at a basis state. -/
def get : {n : ℕ} → Vec R n → State 3 n → R
  | 0, v, _ => v.val
  | _ + 1, v, s => get (v.sel (s 0)) (Fin.tail s)

theorem get_node {n : ℕ} (a b c : Vec R n) (s : State 3 (n + 1)) :
    get (node a b c) s = get (![a, b, c] (s 0)) (Fin.tail s) := rfl

section Ring

variable [CommRing R]

/-- The zero vector. -/
def zero : (n : ℕ) → Vec R n
  | 0 => leaf 0
  | n + 1 => node (zero n) (zero n) (zero n)

/-- Sum. -/
def add : {n : ℕ} → Vec R n → Vec R n → Vec R n
  | _, leaf a, leaf b => leaf (a + b)
  | _, node a b c, node a' b' c' => node (add a a') (add b b') (add c c')

/-- Scalar multiple. -/
def smul (r : R) : {n : ℕ} → Vec R n → Vec R n
  | _, leaf a => leaf (r * a)
  | _, node a b c => node (smul r a) (smul r b) (smul r c)

/-- `acc + r • v`, skipping a zero coefficient. -/
def axpy [DecidableEq R] {n : ℕ} (r : R) (v acc : Vec R n) : Vec R n :=
  if r = 0 then acc else add (smul r v) acc

@[simp] theorem get_zero : {n : ℕ} → (s : State 3 n) → get (zero n : Vec R n) s = 0
  | 0, _ => rfl
  | n + 1, s => by
    rw [zero, get_node]
    have : ![zero n, zero n, zero n] (s 0) = (zero n : Vec R n) := by
      generalize s 0 = x; fin_cases x <;> rfl
    rw [this, get_zero]

theorem get_add : {n : ℕ} → (u v : Vec R n) → (s : State 3 n) →
    get (add u v) s = get u s + get v s
  | _, leaf a, leaf b, _ => rfl
  | _, node a b c, node a' b' c', s => by
    rw [add, get_node, get_node, get_node]
    generalize s 0 = x
    fin_cases x <;> exact get_add _ _ _

theorem get_smul (r : R) : {n : ℕ} → (v : Vec R n) → (s : State 3 n) →
    get (smul r v) s = r * get v s
  | _, leaf a, _ => rfl
  | _, node a b c, s => by
    rw [smul, get_node, get_node]
    generalize s 0 = x
    fin_cases x <;> exact get_smul r _ _

theorem get_axpy [DecidableEq R] {n : ℕ} (r : R) (v acc : Vec R n) (s : State 3 n) :
    get (axpy r v acc) s = r * get v s + get acc s := by
  unfold axpy
  split_ifs with h
  · rw [h, zero_mul, zero_add]
  · rw [get_add, get_smul]

end Ring

/-! ### The digits of the bottom wires -/

/-- All basis states of `k` qutrits. -/
def allStates : (k : ℕ) → List (State 3 k)
  | 0 => [fun i => i.elim0]
  | k + 1 => [0, 1, 2].flatMap fun x => (allStates k).map fun y => Fin.cons x y

theorem mem_allStates : {k : ℕ} → (s : State 3 k) → s ∈ allStates k
  | 0, s => by
    simp only [allStates, List.mem_singleton]
    funext i; exact i.elim0
  | k + 1, s => by
    simp only [allStates, List.mem_flatMap, List.mem_map]
    refine ⟨s 0, by generalize s 0 = x; fin_cases x <;> simp, Fin.tail s, mem_allStates _, Fin.cons_self_tail s⟩

theorem nodup_allStates : (k : ℕ) → (allStates k).Nodup
  | 0 => List.nodup_singleton _
  | k + 1 => by
    simp only [allStates]
    rw [List.nodup_flatMap]
    refine ⟨fun x _ => (nodup_allStates k).map (fun _ _ h => Fin.cons_right_injective (α := fun _ => Fin 3) x h), ?_⟩
    refine List.Nodup.pairwise_of_forall_ne (by decide) fun x _ x' _ hx => ?_
    rw [Function.onFun, List.disjoint_left]
    simp only [List.mem_map]
    rintro _ ⟨y, _, rfl⟩ ⟨y', _, h⟩
    exact hx (by simpa using (congrFun h 0).symm)

theorem sum_allStates {M : Type*} [AddCommMonoid M] {k : ℕ} (f : State 3 k → M) :
    ((allStates k).map f).sum = ∑ y, f y := by
  rw [← List.sum_toFinset f (nodup_allStates k)]
  congr 1
  ext y; simp [mem_allStates]

/-- A trie on `n + k` wires from the tries on the top `n` wires at each
basis state of the bottom `k`. -/
def build : (k : ℕ) → {n : ℕ} → (State 3 k → Vec R n) → Vec R (n + k)
  | 0, _, f => f fun i => i.elim0
  | k + 1, _, f =>
    node (build k fun y => f (Fin.cons 0 y)) (build k fun y => f (Fin.cons 1 y))
      (build k fun y => f (Fin.cons 2 y))

/-- The trie on the top `n` of `n + k` wires at a basis state of the
bottom `k`. -/
def sub : (k : ℕ) → {n : ℕ} → Vec R (n + k) → State 3 k → Vec R n
  | 0, _, v, _ => v
  | k + 1, _, v, y => sub k ((v : Vec R (_ + k + 1)).sel (y 0)) (Fin.tail y)

private theorem split_succ_fst {n k : ℕ} (s : State 3 (n + (k + 1))) :
    (split 3 n (k + 1) s).1 = Fin.cons (s 0) (split 3 n k (Fin.tail s)).1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [split, Equiv.coe_fn_mk, Fin.cons_succ, Fin.tail]
    congr 1

private theorem split_succ_snd {n k : ℕ} (s : State 3 (n + (k + 1))) :
    (split 3 n (k + 1) s).2 = (split 3 n k (Fin.tail s)).2 := by
  funext j
  simp only [split, Equiv.coe_fn_mk, Fin.tail]
  congr 1; ext; simp; omega

theorem get_build : (k : ℕ) → {n : ℕ} → (f : State 3 k → Vec R n) → (s : State 3 (n + k)) →
    get (build k f) s = get (f (split 3 n k s).1) (split 3 n k s).2
  | 0, n, f, s => by
    simp only [build]
    congr 1
    · congr 1; funext i; exact i.elim0
    · funext j; simp [split]
  | k + 1, n, f, s => by
    rw [build, get_node]
    have : ![build k (fun y => f (Fin.cons 0 y)), build k (fun y => f (Fin.cons 1 y)),
        build k (fun y => f (Fin.cons 2 y))] (s 0) = build k (fun y => f (Fin.cons (s 0) y)) := by
      generalize s 0 = x
      fin_cases x <;> rfl
    rw [this, get_build k, split_succ_fst, split_succ_snd]

theorem get_sub : (k : ℕ) → {n : ℕ} → (v : Vec R (n + k)) → (y : State 3 k) → (t : State 3 n) →
    get (sub k v y) t = get v ((split 3 n k).symm (y, t))
  | 0, n, v, y, t => by
    have : (split 3 n 0).symm (y, t) = t := by
      funext i
      simp only [split, Equiv.coe_fn_symm_mk]
      rw [dif_neg (by omega)]
      congr 1
    simp only [sub, this]
  | k + 1, n, v, y, t => by
    rw [sub, get_sub k]
    show _ = get ((v : Vec R (n + k + 1)).sel (((split 3 n (k + 1)).symm (y, t)) 0))
      (Fin.tail (α := fun _ => Fin 3) ((split 3 n (k + 1)).symm (y, t)))
    have e0 : ((split 3 n (k + 1)).symm (y, t)) 0 = y 0 := by
      simp [split]
    rw [e0]
    congr 1
    funext i
    simp only [split, Equiv.coe_fn_symm_mk, Fin.tail]
    by_cases h : (i : ℕ) < k
    · rw [dif_pos h, dif_pos (by simp; omega)]
      rfl
    · rw [dif_neg h, dif_neg (by simp; omega)]
      congr 1; ext; simp

/-! ### Gates acting on tries -/

variable [CommRing R] [DecidableEq R]

/-- A `k`-wire operator applied to the bottom `k` wires of a trie. -/
def actBottom (k : ℕ) {n : ℕ} (G : Op R 3 k) (v : Vec R (n + k)) : Vec R (n + k) :=
  build k fun x => (allStates k).foldr (fun y acc => axpy (G x y) (sub k v y) acc) (zero n)

theorem get_foldr {n k : ℕ} (G : Op R 3 k) (x : State 3 k) (v : Vec R (n + k)) (t : State 3 n)
    (l : List (State 3 k)) :
    get (l.foldr (fun y acc => axpy (G x y) (sub k v y) acc) (zero n)) t =
      (l.map fun y => G x y * get v ((split 3 n k).symm (y, t))).sum := by
  induction l with
  | nil => simp
  | cons y l ih => rw [List.foldr_cons, get_axpy, ih, get_sub]; simp

theorem get_actBottom (k : ℕ) {n : ℕ} (G : Op R 3 k) (v : Vec R (n + k)) :
    get (actBottom k G v) = onBottom (n := n) G *ᵥ get v := by
  funext s
  rw [actBottom, get_build, get_foldr, sum_allStates, mulVec, dotProduct,
    ← (split 3 n k).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (split 3 n k s).2]
  · rw [onBottom_apply, Equiv.apply_symm_apply, if_pos rfl]
  · intro t _ ht
    rw [onBottom_apply, Equiv.apply_symm_apply, if_neg (Ne.symm ht), zero_mul]
  · simp

variable {Gate : ℕ → Type}

/-- A generator applied to a trie. -/
def act (O : GateOps Gate R 3) : {n : ℕ} → Gen Gate n → Vec R n → Vec R n
  | _, .gate0 c, v => smul (O.scalar c) v
  | _, .gate1 g, v => actBottom 1 (O.gate1 g) v
  | _, .gate2 g, v => actBottom 2 (O.gate2 g) v
  | _, .gate3 g, v => actBottom 3 (O.gate3 g) v
  | _, .up g, node a b c => node (act O g a) (act O g b) (act O g c)

private theorem split_one_snd {n : ℕ} (s : State 3 (n + 1)) :
    (split 3 n 1 s).2 = Fin.tail s := by
  funext j; simp only [split, Equiv.coe_fn_mk, Fin.tail]; congr 1; ext; simp; omega

theorem get_act (O : GateOps Gate R 3) : {n : ℕ} → (g : Gen Gate n) → (v : Vec R n) →
    get (act O g v) = O.gen g *ᵥ get v
  | _, .gate0 c, v => by
    funext s
    rw [act, get_smul]
    simp [GateOps.gen, smul_mulVec]
  | _, .gate1 g, v => get_actBottom 1 _ v
  | _, .gate2 g, v => get_actBottom 2 _ v
  | _, .gate3 g, v => get_actBottom 3 _ v
  | n + 1, .up g, node a b c => by
    funext s
    show get (![act O g a, act O g b, act O g c] (s 0)) (Fin.tail s) = _
    have hsel : ![act O g a, act O g b, act O g c] (s 0) = act O g (![a, b, c] (s 0)) := by
      generalize s 0 = x; fin_cases x <;> rfl
    rw [hsel, get_act O g, GateOps.gen, mulVec, dotProduct, mulVec, dotProduct,
      ← (split 3 n 1).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single (split 3 n 1 s).1]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [onTop_apply, Equiv.apply_symm_apply, if_pos rfl, split_one_snd]
      congr 1
    · intro y _ hy
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [onTop_apply, Equiv.apply_symm_apply, if_neg (Ne.symm hy), zero_mul]
    · simp

/-- A circuit applied to a trie, in operator order. -/
def actW (O : GateOps Gate R 3) {n : ℕ} (w : Circuit Gate n) (v : Vec R n) : Vec R n :=
  w.toList.foldr (act O) v

theorem get_actW (O : GateOps Gate R 3) {n : ℕ} (w : Circuit Gate n) (v : Vec R n) :
    get (actW O w v) = O.eval n w *ᵥ get v := by
  induction w using FreeMonoid.inductionOn' generalizing v with
  | one => simp [actW, GateOps.eval]
  | mul_of g w ih =>
    rw [actW, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.foldr_cons, get_act, ← actW, ih, mulVec_mulVec, map_mul]
    rw [show O.eval n (FreeMonoid.of g) = O.gen g from FreeMonoid.lift_eval_of _ _]

/-- The basis vector of a state. -/
def basis : {n : ℕ} → State 3 n → Vec R n
  | 0, _ => leaf 1
  | n + 1, t =>
    node (if t 0 = 0 then basis (Fin.tail t) else zero n)
      (if t 0 = 1 then basis (Fin.tail t) else zero n)
      (if t 0 = 2 then basis (Fin.tail t) else zero n)

omit [DecidableEq R] in
theorem get_basis : {n : ℕ} → (t s : State 3 n) → get (basis t : Vec R n) s = if s = t then 1 else 0
  | 0, t, s => by
    rw [if_pos (funext fun i => i.elim0)]; rfl
  | n + 1, t, s => by
    rw [basis, get_node]
    have : ![if t 0 = 0 then basis (Fin.tail t) else zero n,
        if t 0 = 1 then basis (Fin.tail t) else zero n,
        if t 0 = 2 then basis (Fin.tail t) else zero n] (s 0) =
        (if t 0 = s 0 then basis (Fin.tail t) else zero n : Vec R n) := by
      generalize s 0 = x; fin_cases x <;> rfl
    rw [this]
    have hst : s = t ↔ s 0 = t 0 ∧ Fin.tail s = Fin.tail t := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h0, ht⟩
        rw [← Fin.cons_self_tail s, ← Fin.cons_self_tail t, h0, ht]
    split_ifs with h1 h2 h2
    · rw [get_basis, if_pos (hst.1 h2).2]
    · rw [get_basis, if_neg (fun h => h2 (hst.2 ⟨h1.symm, h⟩))]
    · exact absurd (hst.1 h2).1 (Ne.symm h1)
    · rw [get_zero]

/-- Two circuits, possibly over different gate sets, have the same operator if
they send every basis vector to the same trie. -/
theorem eval_eq_of_cols' {Gate' : ℕ → Type} (O : GateOps Gate R 3) (O' : GateOps Gate' R 3)
    {n : ℕ} {w : Circuit Gate n} {w' : Circuit Gate' n}
    (h : ∀ t ∈ allStates n, actW O w (basis t) = actW O' w' (basis t)) :
    O.eval n w = O'.eval n w' := by
  have key : ∀ {G : ℕ → Type} (O : GateOps G R 3) (u : Circuit G n) (s t : State 3 n),
      O.eval n u s t = get (actW O u (basis t)) s := by
    intro G O u s t
    rw [get_actW]
    have : (get (basis t : Vec R n)) = Pi.single t 1 := by
      funext s'; rw [get_basis]; by_cases h : s' = t
      · subst h; simp
      · simp [h]
    rw [this, mulVec_single_one]; rfl
  ext s t
  rw [key, key, h t (mem_allStates t)]

/-- Two circuits have the same operator if they send every basis vector to
the same trie. -/
theorem eval_eq_of_cols (O : GateOps Gate R 3) {n : ℕ} {w v : Circuit Gate n}
    (h : ∀ t ∈ allStates n, actW O w (basis t) = actW O v (basis t)) :
    O.eval n w = O.eval n v :=
  eval_eq_of_cols' O O h

end Vec

end QCert.QutritClifford
