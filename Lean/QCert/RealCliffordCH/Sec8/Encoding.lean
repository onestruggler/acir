/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: the auxiliary alphabet `𝒫_N` and the encoding (Definition 8.2)

* The Gray code (Definition 8.1): the index `k ∈ {0, …, 2ⁿ - 1}` stands for
  the basis state whose bits (read top wire first) are `G_n(k)`; its value,
  with wire 0 the least significant bit, is `k xor (k / 2)`.  `gInv n s` is
  `G_n⁻¹`, the index of the basis state of value `s`.
* The alphabet `𝒫_N` (Proposition 4.6, Definition 4.9): the products
  `(-1)_[a](-1)_[c]`, `(-1)_[a]X_[c,d]`, `X_[a,b]X_[c,d]`, `H_[a,b]H_[c,d]`
  of one- and two-level matrices, `a ≠ b` and `c ≠ d`.  The letters carry
  their indices only; `PG.Proper` is the condition `a ≠ b ∧ c ≠ d`.
  A word denotes the product of its letters in written order
  (Definition 4.9), which is operator order.
* The encoding `E` (Definition 8.2) of the gates of an `n`-wire circuit,
  `k` wires above the gate and `ℓ` below; the products over the bitstrings
  `x` and `y` are taken with `x` outer and `y` inner (the paper leaves the
  order unspecified).  The swap is not a gate here (it is the circuit of
  Equation (8)), so its encoding `E_{k,ℓ}(swap)` is a separate definition
  (`encSwap`), used by Equations (36) and (37).
-/
import QCert.RealCliffordCH.Semantics
import QCert.Matrix.Level

namespace QCert.RealCliffordCH.Sec8

open Matrix

/-! ## The Gray code -/

/-- The value of the basis state `G_n(k)` (wire 0 the least significant bit). -/
def gray (k : ℕ) : ℕ := k ^^^ (k >>> 1)

/-- The inverse Gray code on `n` bits: `G_n⁻¹`. -/
def gInv (n s : ℕ) : ℕ := (List.range n).foldl (fun acc i => acc ^^^ (s >>> i)) 0

/-- An index of `{0, …, 2ⁿ - 1}` (reduced mod `2ⁿ`). -/
def ix (n v : ℕ) : Fin (2 ^ n) := ⟨v % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- `G_n⁻¹(s)` as an index. -/
def gx (n s : ℕ) : Fin (2 ^ n) := ix n (gInv n s)

/-- The basis state of `n` wires with value `v` (wire 0 the least significant bit). -/
def stateOf (n v : ℕ) : State 2 n := finFunctionFinEquiv.symm (ix n v)

/-- The basis state `G_n(i)` of the index `i`. -/
def grayState (n : ℕ) (i : Fin (2 ^ n)) : State 2 n := stateOf n (gray i)

/-- An operator on `n` wires as a `2ⁿ × 2ⁿ` matrix in the basis ordered by
the Gray code: the entry `(i, j)` is the entry at `G_n(i), G_n(j)`. -/
def toP {R : Type*} {n : ℕ} (M : Op R 2 n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  fun i j => M (grayState n i) (grayState n j)

/-! ## The alphabet `𝒫_N` -/

/-- The letters of `𝒫_N`, with their indices. -/
inductive PG (N : ℕ) : Type
  /-- `(-1)_[a](-1)_[c]` -/
  | zz (a c : Fin N)
  /-- `(-1)_[a]X_[c,d]` -/
  | zx (a c d : Fin N)
  /-- `X_[a,b]X_[c,d]` -/
  | xx (a b c d : Fin N)
  /-- `H_[a,b]H_[c,d]` -/
  | hh (a b c d : Fin N)
  deriving DecidableEq

/-- A letter of `𝒫_N` proper: its two-level matrices are on two distinct
indices. -/
def PG.Proper {N : ℕ} : PG N → Prop
  | .zz _ _ => True
  | .zx _ c d => c ≠ d
  | .xx a b c d => a ≠ b ∧ c ≠ d
  | .hh a b c d => a ≠ b ∧ c ≠ d

/-- A word over `𝒫_N`. -/
def ProperW {N : ℕ} (w : Word (PG N)) : Prop := ∀ p ∈ w.toList, p.Proper

section Matrices

variable {R : Type*} [CommRing R] {N : ℕ}

/-- `(-1)_[a]`. -/
def negM (a : Fin N) : Matrix (Fin N) (Fin N) R := levelMat ![a] !![-1]

/-- `X_[a,b]`. -/
def xM (a b : Fin N) : Matrix (Fin N) (Fin N) R := levelMat ![a, b] !![0, 1; 1, 0]

/-- `H_[a,b]`, with `s` standing for `1/√2`. -/
def hM (s : R) (a b : Fin N) : Matrix (Fin N) (Fin N) R := levelMat ![a, b] !![s, s; s, -s]

/-- The matrix of a letter. -/
def pMat (s : R) : PG N → Matrix (Fin N) (Fin N) R
  | .zz a c => negM a * negM c
  | .zx a c d => negM a * xM c d
  | .xx a b c d => xM a b * xM c d
  | .hh a b c d => hM s a b * hM s c d

/-- The matrix of a word: the product of its letters in written order. -/
def pWord (s : R) : Word (PG N) →* Matrix (Fin N) (Fin N) R := FreeMonoid.lift (pMat s)

end Matrices

/-- The real semantics of words over `𝒫_N`. -/
noncomputable def pSem {N : ℕ} (w : Word (PG N)) : Matrix (Fin N) (Fin N) ℝ :=
  pWord invSqrt2 w

/-! ## Definition 8.2: the encoding -/

/-- The words of a list of letters. -/
def wordOf {N : ℕ} (l : List (PG N)) : Word (PG N) := FreeMonoid.ofList l

/-- All pairs `(x, y)` with `x < 2^k`, `y < 2^j`, `x` outer. -/
def grid (k j : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 ^ k)).flatMap fun x => (List.range (2 ^ j)).map fun y => (x, y)

variable (n : ℕ)

/-- `E_{k,ℓ}` of a one-wire gate with `k` wires above and `ℓ` below. -/
def enc1 (g : Gate 1) (k ℓ : ℕ) : List (PG (2 ^ n)) :=
  match ℓ with
  | 0 =>
    -- the top bit `t` varies: `0x?`, `1x?`, `x ∈ {0,1}^(k-1)`
    let v := fun (t x b : ℕ) => t * 2 ^ k + x * 2 + b
    (List.range (2 ^ (k - 1))).map fun x => match g with
      | .Z => .zz (gx n (v 0 x 1)) (gx n (v 1 x 1))
      | .H => .hh (gx n (v 0 x 0)) (gx n (v 0 x 1)) (gx n (v 1 x 0)) (gx n (v 1 x 1))
  | ℓ + 1 =>
    -- `x a b y`: `a` the gate's bit, `b` the next bit below
    let v := fun (x a b y : ℕ) => x * 2 ^ (ℓ + 2) + a * 2 ^ (ℓ + 1) + b * 2 ^ ℓ + y
    (grid k ℓ).map fun p => match g with
      | .Z => .zz (gx n (v p.1 1 0 p.2)) (gx n (v p.1 1 1 p.2))
      | .H => .hh (gx n (v p.1 0 0 p.2)) (gx n (v p.1 1 0 p.2))
          (gx n (v p.1 0 1 p.2)) (gx n (v p.1 1 1 p.2))

/-- `E_{k,ℓ}` of a two-wire gate with `k` wires above and `ℓ` below. -/
def enc2 (g : Gate 2) (k ℓ : ℕ) : List (PG (2 ^ n)) :=
  match ℓ with
  | 0 =>
    let v := fun (t x a b : ℕ) => t * 2 ^ (k + 1) + x * 4 + a * 2 + b
    (List.range (2 ^ (k - 1))).map fun x => match g with
      | .CZ => .zz (gx n (v 0 x 1 1)) (gx n (v 1 x 1 1))
      | .CH => .hh (gx n (v 0 x 1 0)) (gx n (v 0 x 1 1)) (gx n (v 1 x 1 0)) (gx n (v 1 x 1 1))
  | ℓ + 1 =>
    -- `x 1 a b y`: the control bit `1`, the target bit `a`, the next bit `b`
    let v := fun (x a b y : ℕ) => x * 2 ^ (ℓ + 3) + 2 ^ (ℓ + 2) + a * 2 ^ (ℓ + 1) + b * 2 ^ ℓ + y
    (grid k ℓ).map fun p => match g with
      | .CZ => .zz (gx n (v p.1 1 0 p.2)) (gx n (v p.1 1 1 p.2))
      | .CH => .hh (gx n (v p.1 0 0 p.2)) (gx n (v p.1 1 0 p.2))
          (gx n (v p.1 0 1 p.2)) (gx n (v p.1 1 1 p.2))

/-- The encoding of a generator of `n`-wire circuits, `lo` wires below the
sub-circuit it is a generator of. -/
def encAt (lo : ℕ) : {m : ℕ} → Gen Gate m → List (PG (2 ^ n))
  | _, .gate0 c => nomatch c
  | _, .gate1 g => enc1 n g (n - 1 - lo) lo
  | _, .gate2 g => enc2 n g (n - 2 - lo) lo
  | _, .gate3 c => nomatch c
  | _, .up g => encAt (lo + 1) g

/-- Definition 8.2: the encoding of circuits, a monoid homomorphism. -/
def encW : Circ n →* Word (PG (2 ^ n)) := FreeMonoid.lift fun g => wordOf (encAt n 0 g)

/-- `E_{k,ℓ}(swap)` (Definition 8.2, last case), `k + 2 + ℓ = n`. -/
def encSwap (k ℓ : ℕ) : List (PG (2 ^ n)) :=
  let v := fun (x a b y : ℕ) => x * 2 ^ (ℓ + 2) + a * 2 ^ (ℓ + 1) + b * 2 ^ ℓ + y
  enc2 n .CZ k ℓ ++
    (grid k ℓ).map (fun p => .zx (gx n (v p.1 1 1 p.2)) (gx n (v p.1 1 0 p.2)) (gx n (v p.1 1 1 p.2))) ++
    (grid k ℓ).map (fun p => .zx (gx n (v p.1 0 1 p.2)) (gx n (v p.1 0 1 p.2)) (gx n (v p.1 1 1 p.2))) ++
    (grid k ℓ).map (fun p => .zx (gx n (v p.1 1 1 p.2)) (gx n (v p.1 1 0 p.2)) (gx n (v p.1 1 1 p.2)))

/-- `ℰ^{1-x}_{k,ℓ}(X)` (Appendix A.4.1), `k + 1 + ℓ = n`: empty when `x = 1`,
the encoding of `X` on the wire with `k` wires above when `x = 0`. -/
def encNeg (k ℓ x : ℕ) : List (PG (2 ^ n)) :=
  if x = 1 then [] else
    let v := fun (x a y : ℕ) => x * 2 ^ (ℓ + 1) + a * 2 ^ ℓ + y
    enc1 n .Z k ℓ ++
      (grid k ℓ).map (fun p => .zx (gx n (v p.1 1 p.2)) (gx n (v p.1 0 p.2)) (gx n (v p.1 1 p.2)))

/-- The statement that the encoding preserves the semantics (used in the
proofs of Lemma 7.6 and Theorem 8.9): the encoding of a circuit is proper,
and its matrix is the circuit's operator in the basis ordered by the Gray
code. -/
def ESem : Prop :=
  ∀ w : Circ n, ProperW (encW n w) ∧ pSem (encW n w) = toP (S.sem n w).1

end QCert.RealCliffordCH.Sec8
