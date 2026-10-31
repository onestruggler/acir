/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Fast evaluation of the gates on tries over `ℤ[ω]`

`Vec.actBottom` (`Trie.lean`) applies a gate to a trie generically, by
looking up every entry of the gate's matrix at every pair of basis states
of its wires: for a two-wire gate that is 81 lookups through `State`
functions per application, which the kernel pays for at every basis vector
of every rule.  Here each gate of the soundness proof is given directly as
a transformation of the outer levels of a trie over `ℤ[ω]` — the Hadamard
gate (scaled by `c = ω² - ω`, so `[ω^{jk}]`) as sums and rotations of the
three sub-tries, the diagonal gates as rotations, the swap and the
controlled additions as permutations of the nine sub-tries — and each is
shown equal to the generic application of its matrix (`actH_eq`, …):
the generic one unfolds, on `node a b c`, to a fixed expression in
`axpy`, which `smul_one`, `smul_om`, … rewrite into the direct one.  So
the direct actions inherit `Vec.get_act` and `Vec.eval_eq_of_cols'`.
-/
import QCert.QutritClifford.Trie
import QCert.QutritClifford.Eisenstein

namespace QCert.QutritClifford

open Matrix

namespace Vec

universe u

variable {R : Type u}

/-- A function applied to every entry. -/
def map (f : R → R) : {n : ℕ} → Vec R n → Vec R n
  | _, leaf a => leaf (f a)
  | _, node a b c => node (map f a) (map f b) (map f c)

/-- Boolean equality of tries. -/
def beq [DecidableEq R] : {n : ℕ} → Vec R n → Vec R n → Bool
  | _, leaf a, leaf b => decide (a = b)
  | _, node a b c, node a' b' c' => beq a a' && beq b b' && beq c c'

theorem eq_of_beq [DecidableEq R] : ∀ {n : ℕ} {u v : Vec R n}, beq u v = true → u = v
  | _, leaf a, leaf b, h => by
    simp only [beq, decide_eq_true_eq] at h; rw [h]
  | _, node a b c, node a' b' c', h => by
    simp only [beq, Bool.and_eq_true] at h
    rw [eq_of_beq h.1.1, eq_of_beq h.1.2, eq_of_beq h.2]

section Ring

variable [CommRing R]

theorem add_zero_right : ∀ {n : ℕ} (v : Vec R n), add v (zero n) = v
  | _, leaf a => by simp [add, zero]
  | _, node a b c => by simp only [zero, add, add_zero_right]

theorem smul_one : ∀ {n : ℕ} (v : Vec R n), smul 1 v = v
  | _, leaf a => by simp [smul]
  | _, node a b c => by simp only [smul, smul_one]

/-- A map that multiplies every entry by `r` is `smul r`. -/
theorem map_eq_smul {r : R} {f : R → R} (h : ∀ x, f x = r * x) :
    ∀ {n : ℕ} (v : Vec R n), map f v = smul r v
  | _, leaf a => by simp [map, smul, h]
  | _, node a b c => by simp only [map, smul, map_eq_smul h]

/-- Two circuits whose columns agree up to the scalars `a`, `b` have
evaluations that agree up to them. -/
theorem eval_eq_of_cols_smul [DecidableEq R] {Gate Gate' : ℕ → Type} (O : GateOps Gate R 3)
    (O' : GateOps Gate' R 3) {n : ℕ} {w : Circuit Gate n} {w' : Circuit Gate' n} {a b : R}
    (h : ∀ t ∈ allStates n, smul a (actW O w (basis t)) = smul b (actW O' w' (basis t))) :
    a • O.eval n w = b • O'.eval n w' := by
  have key : ∀ {G : ℕ → Type} (O : GateOps G R 3) (u : Circuit G n) (r : R) (s t : State 3 n),
      (r • O.eval n u) s t = get (smul r (actW O u (basis t))) s := by
    intro G O u r s t
    rw [get_smul, get_actW, smul_apply, smul_eq_mul]
    congr 1
    have : (get (basis t : Vec R n)) = Pi.single t 1 := by
      funext s'; rw [get_basis]; by_cases h : s' = t
      · subst h; simp
      · simp [h]
    rw [this, mulVec_single_one]; rfl
  ext s t
  rw [key, key, h t (mem_allStates t)]

/-- Operators that agree at every pair of basis states are equal. -/
theorem op_ext_of_all [DecidableEq R] {k : ℕ} {M N : Op R 3 k}
    (h : ((allStates k).all fun s => (allStates k).all fun t => decide (M s t = N s t)) = true) :
    M = N := by
  ext s t
  have := List.all_eq_true.1 h s (mem_allStates s)
  exact of_decide_eq_true (List.all_eq_true.1 this t (mem_allStates t))

end Ring

/-! ### The gates over `ℤ[ω]` -/

open Zω

/-- Multiplication of every entry by `ω`: `ω (a + b ω) = -b + (a - b) ω`. -/
def rotω {n : ℕ} : Vec Zω n → Vec Zω n := map fun x => ⟨-x.b, x.a - x.b⟩

/-- Multiplication by `ω²`: `ω² (a + b ω) = (b - a) - a ω`. -/
def rotω2 {n : ℕ} : Vec Zω n → Vec Zω n := map fun x => ⟨x.b - x.a, -x.a⟩

/-- Negation. -/
def neg {n : ℕ} : Vec Zω n → Vec Zω n := map fun x => ⟨-x.a, -x.b⟩

/-- Multiplication by `-ω`: `-ω (a + b ω) = b + (b - a) ω`. -/
def mulNegω {n : ℕ} : Vec Zω n → Vec Zω n := map fun x => ⟨x.b, x.b - x.a⟩

theorem smul_om {n : ℕ} (v : Vec Zω n) : smul om v = rotω v :=
  (map_eq_smul (fun x => by ext <;> simp [om] <;> ring) v).symm

theorem smul_om2 {n : ℕ} (v : Vec Zω n) : smul om2 v = rotω2 v :=
  (map_eq_smul (fun x => by ext <;> simp [om2] <;> ring) v).symm

theorem smul_neg_one {n : ℕ} (v : Vec Zω n) : smul (-1) v = neg v :=
  (map_eq_smul (fun x => by ext <;> simp) v).symm

theorem smul_negω {n : ℕ} (v : Vec Zω n) : smul Zω.negω v = mulNegω v :=
  (map_eq_smul (fun x => by ext <;> simp [Zω.negω] <;> ring) v).symm

/-- The entries of `c H = [ω^{jk}]`. -/
def hz (x y : Fin 3) : Zω :=
  match x.val, y.val with
  | 0, _ => 1
  | _, 0 => 1
  | 1, 1 => om
  | 1, 2 => om2
  | 2, 1 => om2
  | _, _ => om

/-- `c H`. -/
def HZ : Op Zω 3 1 := fun s t => hz (s 0) (t 0)

/-- `S = diag(ω, ω, 1)`. -/
def SZ : Op Zω 3 1 := fun s t => if s 0 = t 0 then (if s 0 = 2 then 1 else om) else 0

/-- `S' = diag(ω, 1, ω)`. -/
def SpZ : Op Zω 3 1 := fun s t => if s 0 = t 0 then (if s 0 = 1 then 1 else om) else 0

/-- The phase `ω^{xy}` of `CZ`. -/
def czp (x y : Fin 3) : Zω :=
  match x.val, y.val with
  | 1, 1 => om
  | 1, 2 => om2
  | 2, 1 => om2
  | 2, 2 => om
  | _, _ => 1

/-- `CZ`. -/
def CZZ : Op Zω 3 2 := fun s t => if s 0 = t 0 ∧ s 1 = t 1 then czp (s 0) (s 1) else 0

/-- The circuit (D6), `|x, y⟩ ↦ -|y, x⟩`. -/
def swapZ : Op Zω 3 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then -1 else 0

/-- `CX |x, y⟩ = |x, x + y⟩`, `x` on wire 1. -/
def cxZ : Op Zω 3 2 := fun s t => if s 1 = t 1 ∧ s 0 = t 0 + t 1 then 1 else 0

/-- `XC |x, y⟩ = |x + y, y⟩`, `y` on wire 0. -/
def xcZ : Op Zω 3 2 := fun s t => if s 0 = t 0 ∧ s 1 = t 1 + t 0 then 1 else 0

/-! ### The gates as transformations of tries

Wire `0` is the outermost level; a sub-trie `a_{ij}` below is at digit `i`
of wire `0` and digit `j` of wire `1`. -/

/-- `c H` on wire 0. -/
def actH {n : ℕ} : Vec Zω (n + 1) → Vec Zω (n + 1)
  | node a b c => node (add a (add b c)) (add a (add (rotω b) (rotω2 c)))
      (add a (add (rotω2 b) (rotω c)))

/-- `S` on wire 0. -/
def actS {n : ℕ} : Vec Zω (n + 1) → Vec Zω (n + 1)
  | node a b c => node (rotω a) (rotω b) c

/-- `S'` on wire 0. -/
def actSp {n : ℕ} : Vec Zω (n + 1) → Vec Zω (n + 1)
  | node a b c => node (rotω a) b (rotω c)

/-- `CZ` on wires 0, 1. -/
def actCZ {n : ℕ} : Vec Zω (n + 2) → Vec Zω (n + 2)
  | node (node a00 a01 a02) (node a10 a11 a12) (node a20 a21 a22) =>
    node (node a00 a01 a02) (node a10 (rotω a11) (rotω2 a12)) (node a20 (rotω2 a21) (rotω a22))

/-- `-SWAP` on wires 0, 1. -/
def actSWAP {n : ℕ} : Vec Zω (n + 2) → Vec Zω (n + 2)
  | node (node a00 a01 a02) (node a10 a11 a12) (node a20 a21 a22) =>
    node (node (neg a00) (neg a10) (neg a20)) (node (neg a01) (neg a11) (neg a21))
      (node (neg a02) (neg a12) (neg a22))

/-- `CX` on wires 0, 1: the entry at `(i, j)` comes from `(i - j, j)`. -/
def actCX {n : ℕ} : Vec Zω (n + 2) → Vec Zω (n + 2)
  | node (node a00 a01 a02) (node a10 a11 a12) (node a20 a21 a22) =>
    node (node a00 a21 a12) (node a10 a01 a22) (node a20 a11 a02)

/-- `XC` on wires 0, 1: the entry at `(i, j)` comes from `(i, j - i)`. -/
def actXC {n : ℕ} : Vec Zω (n + 2) → Vec Zω (n + 2)
  | node (node a00 a01 a02) (node a10 a11 a12) (node a20 a21 a22) =>
    node (node a00 a01 a02) (node a12 a10 a11) (node a21 a22 a20)

/-- `add (smul 1 a) (zero n)`, the shape left by `actBottom` at a unit entry. -/
local notation "W1 " a => add (smul (1 : Zω) a) (zero _)

theorem actH_eq {n : ℕ} (v : Vec Zω (n + 1)) : actH v = actBottom 1 HZ v := by
  cases v with
  | node a b c =>
    show _ = node (add (smul (1 : Zω) a) (add (smul (1 : Zω) b) (add (smul (1 : Zω) c) (zero n))))
      (add (smul (1 : Zω) a) (add (smul om b) (add (smul om2 c) (zero n))))
      (add (smul (1 : Zω) a) (add (smul om2 b) (add (smul om c) (zero n))))
    simp only [actH, smul_one, smul_om, smul_om2, add_zero_right]

theorem actS_eq {n : ℕ} (v : Vec Zω (n + 1)) : actS v = actBottom 1 SZ v := by
  cases v with
  | node a b c =>
    show _ = node (add (smul om a) (zero n)) (add (smul om b) (zero n)) (W1 c)
    simp only [actS, smul_one, smul_om, add_zero_right]

theorem actSp_eq {n : ℕ} (v : Vec Zω (n + 1)) : actSp v = actBottom 1 SpZ v := by
  cases v with
  | node a b c =>
    show _ = node (add (smul om a) (zero n)) (W1 b) (add (smul om c) (zero n))
    simp only [actSp, smul_one, smul_om, add_zero_right]

theorem actCZ_eq {n : ℕ} (v : Vec Zω (n + 2)) : actCZ v = actBottom 2 CZZ v := by
  cases v with
  | node v0 v1 v2 =>
    cases v0 with | node a00 a01 a02 =>
    cases v1 with | node a10 a11 a12 =>
    cases v2 with | node a20 a21 a22 =>
    show _ = node (node (W1 a00) (W1 a01) (W1 a02))
      (node (W1 a10) (add (smul om a11) (zero n)) (add (smul om2 a12) (zero n)))
      (node (W1 a20) (add (smul om2 a21) (zero n)) (add (smul om a22) (zero n)))
    simp only [actCZ, smul_one, smul_om, smul_om2, add_zero_right]

theorem actSWAP_eq {n : ℕ} (v : Vec Zω (n + 2)) : actSWAP v = actBottom 2 swapZ v := by
  cases v with
  | node v0 v1 v2 =>
    cases v0 with | node a00 a01 a02 =>
    cases v1 with | node a10 a11 a12 =>
    cases v2 with | node a20 a21 a22 =>
    show _ = node
      (node (add (smul (-1) a00) (zero n)) (add (smul (-1) a10) (zero n)) (add (smul (-1) a20) (zero n)))
      (node (add (smul (-1) a01) (zero n)) (add (smul (-1) a11) (zero n)) (add (smul (-1) a21) (zero n)))
      (node (add (smul (-1) a02) (zero n)) (add (smul (-1) a12) (zero n)) (add (smul (-1) a22) (zero n)))
    simp only [actSWAP, smul_neg_one, add_zero_right]

theorem actCX_eq {n : ℕ} (v : Vec Zω (n + 2)) : actCX v = actBottom 2 cxZ v := by
  cases v with
  | node v0 v1 v2 =>
    cases v0 with | node a00 a01 a02 =>
    cases v1 with | node a10 a11 a12 =>
    cases v2 with | node a20 a21 a22 =>
    show _ = node (node (W1 a00) (W1 a21) (W1 a12)) (node (W1 a10) (W1 a01) (W1 a22))
      (node (W1 a20) (W1 a11) (W1 a02))
    simp only [actCX, smul_one, add_zero_right]

theorem actXC_eq {n : ℕ} (v : Vec Zω (n + 2)) : actXC v = actBottom 2 xcZ v := by
  cases v with
  | node v0 v1 v2 =>
    cases v0 with | node a00 a01 a02 =>
    cases v1 with | node a10 a11 a12 =>
    cases v2 with | node a20 a21 a22 =>
    show _ = node (node (W1 a00) (W1 a01) (W1 a02)) (node (W1 a12) (W1 a10) (W1 a11))
      (node (W1 a21) (W1 a22) (W1 a20))
    simp only [actXC, smul_one, add_zero_right]

end Vec

end QCert.QutritClifford
