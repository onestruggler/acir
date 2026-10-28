/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: placed and coloured multi-controlled gates

The conventions in which the auxiliary equations of Appendix D are stated
(see `PLAN.md`).

* `atBot N g`: a circuit `g` on `m ≤ N` wires on the bottom `m` of `N`
  wires, the wires above idle (`padTop` iterated; no cast when `m` is
  `N`, `N - 1`, … syntactically).
* `netL N ps`: the swap network that brings the wires `ps = [p₀, p₁, …]`
  down to `0, 1, …` in that order, one at a time (`moveDown`), the other
  wires keeping their vertical order.  `placeG N g ps` is `g` (on its own
  `ps.length` wires) put on the wires `ps`: the network, `g` at the bottom,
  the network backwards.  This is the paper's convention for a gate on
  wires that are not the bottom ones (Section 2.2, Definition 2.4): it is
  defined by conjugation with swaps, keeping the vertical order of the
  controls; Definition 8.3's `placeAt` and `placeAt2` are the instances
  `ps = t :: …` and `ps = b :: h :: …`.
* `colourW N ws g`: the controls on the wires `ws` white, i.e. `g`
  conjugated by `X` on those wires (Figure 3).
* `mc N K tg c`: the multi-controlled gate of kind `K` (Definition 2.4)
  with its special wires `tg` (the box wire for `box`; the target for
  `zx`/`xz`; the box wire then the `H` wire for `hg`) and a control on
  every other wire `j < N` with `c j = some b` (black for `b = true`,
  white for `b = false`); the wires with `c j = none` are idle.  The
  canonical gate (`box k`, `zx k`, `xz k`, `mch k`, `k` the number of
  controls) is placed by `placeG` on `tg ++ controls`, the controls in
  increasing order, and coloured.
-/
import QCert.RealCliffordCH.Sec8.Weak

namespace QCert.RealCliffordCH.Sec8

open Circuit

/-! ## Circuits at the bottom of wider ones -/

/-- `g` on the bottom wires of `N` wires, the wires above idle (the empty
circuit when `g` is wider than `N`). -/
def atBot : (N : ℕ) → {m : ℕ} → Circ m → Circ N
  | 0, _, _ => 1
  | N + 1, m, g => if h : m = N + 1 then h ▸ g else padTop (atBot N g)

@[simp] theorem atBot_self {m : ℕ} (g : Circ m) : atBot m g = g := by
  cases m with
  | zero =>
    show (1 : Circ 0) = g
    induction g using FreeMonoid.inductionOn' with
    | one => rfl
    | mul_of x _ _ => exact match x with | .gate0 c => nomatch c
  | succ m =>
    show (if h : m + 1 = m + 1 then h ▸ g else padTop (atBot m g)) = g
    rw [dif_pos rfl]

theorem atBot_succ {m : ℕ} (N : ℕ) (g : Circ m) (h : m ≠ N + 1) :
    atBot (N + 1) g = padTop (atBot N g) := by
  simp [atBot, h]

/-! ## Swap networks -/

/-- The swaps carrying wire `p` down to wire `i ≤ p`, the wires `i, …, p - 1`
moving up one wire. -/
def moveDown (N p i : ℕ) : List (Circ N) :=
  (List.range (p - i)).reverse.map fun d => swAt N (i + d)

/-- Where the original wire `q` is once the wires `ps.take i` have been
brought down to `0, …, i - 1` (for `q ∉ ps.take i`). -/
def curPos (ps : List ℕ) (i q : ℕ) : ℕ :=
  q + ((ps.take i).filter fun p => decide (q < p)).length

/-- The network bringing the wires `ps` down to `0, 1, …`, in order. -/
def netL (N : ℕ) (ps : List ℕ) : List (Circ N) :=
  (List.range ps.length).flatMap fun i => moveDown N (curPos ps i (ps.getD i 0)) i

/-- `g` on the wires `ps`: its wire `i` on wire `ps[i]`. -/
def placeG (N : ℕ) {m : ℕ} (g : Circ m) (ps : List ℕ) : Circ N :=
  drawn (netL N ps ++ [atBot N g] ++ (netL N ps).reverse)

/-- `g` with `X` on the wires `ws` on both sides: the controls on those
wires white. -/
def colourW (N : ℕ) (ws : List ℕ) (g : Circ N) : Circ N :=
  drawn (ws.map (xAt N) ++ [g] ++ ws.map (xAt N))

/-! ## Multi-controlled gates -/

/-- The kinds of multi-controlled gates of Definition 2.4. -/
inductive Kind
  /-- the multi-controlled `Z` (dashed box) -/
  | box
  /-- the multi-controlled `ZX` -/
  | zx
  /-- the multi-controlled `XZ` -/
  | xz
  /-- the multi-controlled `H` (with its dashed box) -/
  | hg
  deriving DecidableEq, Repr

/-- `(-1)^a ZX`: `ZX` for `a = false`, `XZ = -ZX` for `a = true`. -/
def Kind.sgnZX (a : Bool) : Kind := if a then .xz else .zx

/-- The control wires of `c` that are not special, increasing. -/
def ctrlWires (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) : List ℕ :=
  (List.range N).filter fun j => (c j).isSome && !(tg.contains j)

/-- The white control wires of `c`, increasing. -/
def whiteWires (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) : List ℕ :=
  (List.range N).filter fun j => c j == some false && !(tg.contains j)

/-- The canonical gate of kind `K` with `k` controls, on the wires `ps`. -/
def canonAt (N : ℕ) : Kind → ℕ → List ℕ → Circ N
  | .box, k, ps => placeG N (box k) ps
  | .zx, k, ps => placeG N (zx k) ps
  | .xz, k, ps => placeG N (xz k) ps
  | .hg, k, ps => placeG N (mch k) ps

/-- The multi-controlled gate of kind `K` on `N` wires, special wires `tg`,
controls `c` (`some true` black, `some false` white, `none` idle). -/
def mc (N : ℕ) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool) : Circ N :=
  colourW N (whiteWires N tg c) (canonAt N K (ctrlWires N tg c).length (tg ++ ctrlWires N tg c))

/-- Controls on the wires `lo ≤ j < hi`, all black. -/
def blackOn (lo hi : ℕ) : ℕ → Option Bool := fun j => if lo ≤ j ∧ j < hi then some true else none

/-- Controls given by a colour function `x` on the wires `lo ≤ j < hi`. -/
def colOn (lo hi : ℕ) (x : ℕ → Bool) : ℕ → Option Bool :=
  fun j => if lo ≤ j ∧ j < hi then some (x j) else none

/-- Two control assignments side by side: `c` where it is defined, else `d`. -/
def ctlOr (c d : ℕ → Option Bool) : ℕ → Option Bool := fun j => (c j).or (d j)

/-- A single control of colour `b` on wire `j`. -/
def ctlAt (j : ℕ) (b : Bool) : ℕ → Option Bool := fun i => if i = j then some b else none

/-- `c` with wire `w` set to `v`. -/
def setCtl (c : ℕ → Option Bool) (w : ℕ) (v : Option Bool) : ℕ → Option Bool :=
  fun j => if j = w then v else c j

/-- Two colourings of the wires `lo ≤ j < hi` differ somewhere. -/
def DiffOn (lo hi : ℕ) (x y : ℕ → Bool) : Prop := ∃ j, lo ≤ j ∧ j < hi ∧ x j ≠ y j

/-! ## Small gates on given wires -/

/-- `Z` on wire `j`. -/
def zAt (N j : ℕ) : Circ N := placeG N (z : Circ 1) [j]

/-- `H` on wire `j`. -/
def hAt (N j : ℕ) : Circ N := placeG N (h : Circ 1) [j]

/-- `CZ` between wires `i` and `j`. -/
def czAt (N i j : ℕ) : Circ N := placeG N (cz : Circ 2) [i, j]

/-- `CH` with its `H` on wire `t` and its control on wire `c`. -/
def chAt (N t c : ℕ) : Circ N := placeG N (ch : Circ 2) [t, c]

/-- `P ⊗ P` on wires `i` (its wire 0) and `j` (its wire 1). -/
def ppAt (N i j : ℕ) : Circ N := placeG N (pp : Circ 2) [i, j]

end QCert.RealCliffordCH.Sec8
