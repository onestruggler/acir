/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Definition 8.3: the decoding of `𝒫_{2ⁿ}` into `n`-wire circuits

The multi-controlled gates of Definition 2.4 at the standard position (box
on wire 0, controls above; the `H` gate on wire 1) are moved to the wires
the paper draws them on by swap networks (`down t` carries wire `t` to wire
0, the wires below moving up and keeping their order, as the paper's
convention asks), and a control of colour 0 (a white control) is the
control conjugated by `X`.  In `D((-1)_[a](-1)_[a+1])`,
`D((-1)_[a]X_[a,a+1])`, … the controls are on every other wire, with the
colours of `G_n(a)` (`Λ^x … Λ^y`).  The products `∏` of the paper are in
operator order (`∘`), here written with `drawn` in the order the gates
act.  Letters that are not proper decode to the empty circuit.
-/
import QCert.RealCliffordCH.Sec8.Fig8

namespace QCert.RealCliffordCH.Sec8

open Circuit

/-! ## Placing circuits on given wires -/

/-- A one-wire circuit on wire `j` of `N` wires. -/
def place1 : (N j : ℕ) → Circ 1 → Circ N
  | N + 1, j + 1, w => shift (place1 N j w)
  | k + 1, 0, w => Circuit.pad k w
  | _, _, _ => 1

/-- A two-wire circuit on wires `j, j + 1` of `N` wires. -/
def place2 : (N j : ℕ) → Circ 2 → Circ N
  | N + 1, j + 1, w => shift (place2 N j w)
  | k + 2, 0, w => Circuit.pad k w
  | _, _, _ => 1

variable (n : ℕ)

/-- The swap of wires `j, j + 1`. -/
def swAt (j : ℕ) : Circ n := place2 n j swap

/-- `X` on wire `j`. -/
def xAt (j : ℕ) : Circ n := place1 n j x

/-- The swap network carrying wire `t` down to wire 0. -/
def down (t : ℕ) : List (Circ n) := (List.range t).reverse.map (swAt n)

/-- The swap network carrying wire `h` down to wire 1 (`h ≥ 1`). -/
def down1 (h : ℕ) : List (Circ n) := ((List.range h).reverse.filter (· ≥ 1)).map (swAt n)

/-- The standard multi-controlled `Z` gate on `n` wires: the box on wire 0. -/
def stdBox : (N : ℕ) → Circ N
  | k + 1 => box k
  | 0 => 1

/-- The standard multi-controlled `ZX` gate on `n` wires: target wire 0. -/
def stdZX : (N : ℕ) → Circ N
  | k + 1 => zx k
  | 0 => 1

/-- The standard multi-controlled `XZ` gate on `n` wires: target wire 0. -/
def stdXZ : (N : ℕ) → Circ N
  | k + 1 => xz k
  | 0 => 1

/-- The standard multi-controlled `H` gate on `n` wires: box on wire 0, `H`
on wire 1. -/
def stdMch : (N : ℕ) → Circ N
  | k + 2 => mch k
  | _ => 1

/-- A gate moved from wire 0 to wire `t`. -/
def placeAt (g : Circ n) (t : ℕ) : Circ n :=
  drawn (down n t ++ [g] ++ (down n t).reverse)

/-- A gate moved from wires `1, 0` to the wires `h, b` (its `H` gate and its
box). -/
def placeAt2 (g : Circ n) (h b : ℕ) : Circ n :=
  let h1 := if h < b then h + 1 else h
  let net := down n b ++ down1 n h1
  drawn (net ++ [g] ++ net.reverse)

/-- The controls of colour 0 conjugated by `X`: `colours j` is the colour of
wire `j`, wires in `skip` untouched. -/
def colour (g : Circ n) (colours : ℕ → ℕ) (skip : ℕ → Bool) : Circ n :=
  let xs := ((List.range n).filter fun j => !skip j && colours j == 0).map (xAt n)
  drawn (xs ++ [g] ++ xs)

/-! ## The decoding -/

/-- `D((-1)_[a](-1)_[a+1])`: the multi-controlled `Z` gate with its box on the
wire where `G_n(a)` and `G_n(a+1)` differ. -/
def dZZ1 (a : ℕ) : Circ n :=
  let ga := gray a
  let t := ((List.range n).find? fun j => bitOf ga j ≠ bitOf (gray (a + 1)) j).getD 0
  colour n (placeAt n (stdBox n) t) (bitOf ga) (· == t)

/-- `D((-1)_[a]X_[a,a+1])` (`which = 0`) and `D((-1)_[a+1]X_[a,a+1])`
(`which = 1`): the multi-controlled `(-1)^β XZ`, resp. `(-1)^β ZX`. -/
def dZX1 (a which : ℕ) : Circ n :=
  let ga := gray a
  let t := ((List.range n).find? fun j => bitOf ga j ≠ bitOf (gray (a + 1)) j).getD 0
  let β := bitOf ga t
  let g := if (which = 0) = (β = 0) then stdXZ n else stdZX n
  colour n (placeAt n g t) (bitOf ga) (· == t)

/-- `D((-1)_[a](-1)_[b])`: the product of the `D((-1)_[k](-1)_[k+1])`. -/
def dZZ (a b : ℕ) : Circ n :=
  drawn ((List.range (max a b - min a b)).map fun i => dZZ1 n (min a b + i))

/-- `D((-1)_[s]X_[a,b])` for `a < b`, `s ∈ {a, b}`, by induction on `b - a`. -/
def dZXab : (fuel : ℕ) → (s a b : ℕ) → Circ n
  | 0, _, _, _ => 1
  | f + 1, s, a, b =>
    if b = a + 1 then dZX1 n a (if s = a then 0 else 1)
    else if (b - a) % 2 = 1 then
      if s = a then drawn [dZX1 n a 0, dZXab f (a + 1) (a + 1) b, dZX1 n a 1]
      else drawn [dZX1 n a 0, dZXab f b (a + 1) b, dZX1 n a 1]
    else
      if s = a then drawn [dZX1 n (b - 1) 1, dZXab f a a (b - 1), dZX1 n (b - 1) 0]
      else drawn [dZX1 n (b - 1) 1, dZXab f (b - 1) a (b - 1), dZX1 n (b - 1) 0]

/-- `D((-1)_[c]X_[a,b])`. -/
def dZX (c a b : ℕ) : Circ n :=
  let lo := min a b
  let hi := max a b
  if c = a ∨ c = b then dZXab n (hi - lo) c lo hi
  else drawn [dZXab n (hi - lo) a lo hi, dZZ n c a]

/-- `D(H_[a,b]H_[c,d])` for four distinct indices. -/
def dHH4 (a b c d : ℕ) : Circ n :=
  match patt n a b c d with
  | some (kind, u, w) =>
    let (h, bx) := if kind = 1 then (u, w) else (w, u)
    colour n (placeAt2 n (stdMch n) h bx) (bitOf (gray a)) (fun j => j == u || j == w)
  | none =>
    let gadget := colour n (placeAt2 n (stdMch n) 0 1) (fun _ => 0) (fun j => j < 2)
    let sw := sigmaW n a b c d
    let dW := fun (l : List (PG (2 ^ n))) => drawn ((l.map fun p => match p with
      | .zx s k i => dZX n s.val k.val i.val
      | _ => 1).reverse)
    drawn [dW sw.2, gadget, dW sw.1]

/-- Definition 8.3: the decoding of a letter. -/
def dec : PG (2 ^ n) → Circ n
  | .zz a c => dZZ n a.val c.val
  | .zx a c d => if c = d then 1 else dZX n a.val c.val d.val
  | .xx a b c d => if a = b ∨ c = d then 1 else drawn [dZX n b.val c.val d.val, dZX n a.val a.val b.val]
  | .hh a b c d =>
    if a = b ∨ c = d then 1
    else if Distinct4 a.val b.val c.val d.val then dHH4 n a.val b.val c.val d.val
    else
      let ef := freshPair n a.val b.val c.val d.val
      drawn [dHH4 n ef.1 ef.2 c.val d.val, dHH4 n a.val b.val ef.1 ef.2]

/-- The decoding of words, a monoid homomorphism. -/
def decW : Word (PG (2 ^ n)) →* Circ n := FreeMonoid.lift (dec n)

end QCert.RealCliffordCH.Sec8
