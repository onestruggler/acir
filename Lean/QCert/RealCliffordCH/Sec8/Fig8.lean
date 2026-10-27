/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Figure 8: the equational theory of `𝒫_N`, `N = 2ⁿ`

The equations (20)–(46) of Figure 8, one constructor each, with their side
conditions; indices are natural numbers below `2ⁿ`, and every two-level
matrix is on two distinct indices.  Equations (35)–(37) are stated for four
distinct indices (the other case is (42)), as in Definition 8.3:

* (35): when `(G_n(a), G_n(b), G_n(c), G_n(d))` has neither form of the
  caption, with `Σ_{a,b,c,d}` and `Σ'_{a,b,c,d}` of Definition E.1;
* (36): when it has the form `(x0y0z, x1y0z, x0y1z, x1y1z)`, with `𝒲₁`;
* (37): when it has the form `(x0y0z, x0y1z, x1y0z, x1y1z)`, with `𝒲₂`;

`𝒲₁` and `𝒲₂` are those of Appendix A.4.1 with one correction: the
negations are `ℰ^{x_j}_{j,n-j-1}(X)`, X on the wire with `j` wires above
where the bit is `1`; as printed (`ℰ^{1-x_j}_{j,n-j-2}`) they act on `n - 1`
wires and negate the other bits, and (36), (37) fail (see the README).
-/
import QCert.RealCliffordCH.Sec8.Encoding

namespace QCert.RealCliffordCH.Sec8

variable (n : ℕ)

/-- `((-1)_[a](-1)_[c])` -/
def Zz (a c : ℕ) : PG (2 ^ n) := .zz (ix n a) (ix n c)
/-- `((-1)_[a]X_[c,d])` -/
def Zx (a c d : ℕ) : PG (2 ^ n) := .zx (ix n a) (ix n c) (ix n d)
/-- `(X_[a,b]X_[c,d])` -/
def Xx (a b c d : ℕ) : PG (2 ^ n) := .xx (ix n a) (ix n b) (ix n c) (ix n d)
/-- `(H_[a,b]H_[c,d])` -/
def Hh (a b c d : ℕ) : PG (2 ^ n) := .hh (ix n a) (ix n b) (ix n c) (ix n d)

/-! ## Definition E.1: `Σ_{a,b,c,d}` and `Σ'_{a,b,c,d}` -/

/-- `τ^e_{k,i}`: the transposition of `k` and `i` when `e = 1`, the identity
when `e = 0`. -/
def tau (e k i v : ℕ) : ℕ := if e = 0 then v else if v = k then i else if v = i then k else v

/-- The words `Σ_{a,b,c,d}` and `Σ'_{a,b,c,d}` of Definition E.1. -/
def sigmaW (a b c d : ℕ) : List (PG (2 ^ n)) × List (PG (2 ^ n)) :=
  let e3 := if d ≠ 2 then 1 else 0
  let m3 := tau e3 d 2 4
  let i2 := tau e3 d 2 3
  let e2 := if c ≠ i2 then 1 else 0
  let m2 := tau e2 c i2 (tau e3 d 2 4)
  let i1 := tau e2 c i2 (tau e3 d 2 1)
  let e1 := if b ≠ i1 then 1 else 0
  let m1 := tau e1 b i1 (tau e2 c i2 (tau e3 d 2 4))
  let i0 := tau e1 b i1 (tau e2 c i2 (tau e3 d 2 0))
  let e0 := if a ≠ i0 then 1 else 0
  let m0 := tau e0 a i0 (tau e1 b i1 (tau e2 c i2 (tau e3 d 2 4)))
  let L := fun (e m k i : ℕ) => if e = 1 then [Zx n m k i] else []
  (L e0 m0 a i0 ++ L e1 m1 b i1 ++ L e2 m2 c i2 ++ L e3 m3 d 2,
   L e3 4 d 2 ++ L e2 m3 c i2 ++ L e1 m2 b i1 ++ L e0 m1 a i0)

/-! ## The patterns of (36) and (37), and `𝒲₁`, `𝒲₂` -/

/-- The bit of `v` on wire `i`. -/
def bitOf (v i : ℕ) : ℕ := (v >>> i) % 2

/-- `v` with the bits on wires `u` and `w` cleared. -/
def clear2 (v u w : ℕ) : ℕ := v - bitOf v u * 2 ^ u - bitOf v w * 2 ^ w

/-- The pattern of `(G_n(a), G_n(b), G_n(c), G_n(d))`: `some (1, u, w)` for the
form `(x0y0z, x1y0z, x0y1z, x1y1z)` and `some (2, u, w)` for the form
`(x0y0z, x0y1z, x1y0z, x1y1z)`, the two distinguished bits being on the
wires `u > w`; `none` otherwise. -/
def patt (a b c d : ℕ) : Option (ℕ × ℕ × ℕ) :=
  let g := fun t => gray t
  (List.range n).findSome? fun u => (List.range u).findSome? fun w =>
    let same := clear2 (g a) u w = clear2 (g b) u w ∧ clear2 (g a) u w = clear2 (g c) u w ∧
      clear2 (g a) u w = clear2 (g d) u w
    let bits := fun t => (bitOf (g t) u, bitOf (g t) w)
    if same ∧ bits a = (0, 0) ∧ bits b = (1, 0) ∧ bits c = (0, 1) ∧ bits d = (1, 1) then
      some (1, u, w)
    else if same ∧ bits a = (0, 0) ∧ bits b = (0, 1) ∧ bits c = (1, 0) ∧ bits d = (1, 1) then
      some (2, u, w)
    else none

/-- The `j`-th bit, from the top, of the bitstring `xyz` that `G_n(a)` leaves
out of the distinguished wires `u > w`. -/
def restBit (ga u w j : ℕ) : ℕ :=
  let p := n - 1 - u
  let q := n - 1 - w
  let i := if j < p then j else if j + 1 < q then j + 1 else j + 2
  bitOf ga (n - 1 - i)

/-- `𝒲₁` (`kind = 1`) and `𝒲₂` (`kind = 2`) of Appendix A.4.1, for the
distinguished wires `u > w` of the bitstrings `x y z` of `G_n(a)`. -/
def wW (kind ga u w : ℕ) : List (PG (2 ^ n)) :=
  let ℓ := u - w - 1
  let m := w
  let sw := fun (k j : ℕ) => encSwap n k j
  let neg := fun (j : ℕ) => encNeg n j (n - j - 1) (1 - restBit n ga u w j)
  let mid := if kind = 1 then sw (n - 2) 0 else []
  ((List.range ℓ).reverse.flatMap fun i => sw (n - (m + 1 + i) - 2) (m + 1 + i)) ++
  ((List.range m).reverse.flatMap fun j => sw (n - j - 2) j ++ sw (n - j - 3) (j + 1)) ++
  mid ++
  ((List.range (n - 2)).reverse.flatMap neg) ++
  [Hh n 0 1 3 2] ++
  ((List.range (n - 2)).flatMap neg) ++
  mid ++
  ((List.range m).flatMap fun j => sw (n - j - 3) (j + 1) ++ sw (n - j - 2) j) ++
  ((List.range ℓ).flatMap fun i => sw (n - (m + 1 + i) - 2) (m + 1 + i))

/-- The two smallest elements of `{0, …, 2ⁿ - 1} ∖ {a, b, c, d}`. -/
def freshPair (a b c d : ℕ) : ℕ × ℕ :=
  match (List.range (2 ^ n)).filter (fun e => e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d) with
  | e :: f :: _ => (e, f)
  | _ => (0, 0)

/-- Four pairwise distinct indices. -/
def Distinct4 (a b c d : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

instance (a b c d : ℕ) : Decidable (Distinct4 a b c d) := by
  unfold Distinct4; infer_instance

/-! ## The equations -/

/-- The equations of Figure 8, for `N = 2ⁿ`, `n ≥ 3`. -/
inductive Fig8 : WRel (PG (2 ^ n))
  /-- (20) -/
  | r20 (a : ℕ) (ha : a < 2 ^ n) : Fig8 (wordOf [Zz n a a]) (wordOf [])
  /-- (21) -/
  | r21 (a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) : Fig8 (wordOf [Zz n a b]) (wordOf [Zz n b a])
  /-- (22) -/
  | r22 (a b c : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) :
      Fig8 (wordOf [Zz n a b, Zz n b c]) (wordOf [Zz n a c])
  /-- (23) -/
  | r23 (a : ℕ) (ha : a + 1 < 2 ^ n) :
      Fig8 (wordOf [Zz n a (a + 1)]) (wordOf [Zx n a a (a + 1), Zx n a a (a + 1)])
  /-- (24) -/
  | r24 (a : ℕ) (ha : a + 2 < 2 ^ n) :
      Fig8 (wordOf [Zx n a a (a + 1), Zx n (a + 1) (a + 1) (a + 2), Zx n a a (a + 1)])
        (wordOf [Zx n (a + 1) (a + 1) (a + 2), Zx n a a (a + 1), Zx n (a + 1) (a + 1) (a + 2)])
  /-- (25) -/
  | r25 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (hodd : (c - a) % 2 = 1) :
      Fig8 (wordOf [Zx n a a c])
        (wordOf [Zx n (a + 1) a (a + 1), Zx n (a + 1) (a + 1) c, Zx n a a (a + 1)])
  /-- (26) -/
  | r26 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (hodd : (c - a) % 2 = 1) :
      Fig8 (wordOf [Zx n c a c])
        (wordOf [Zx n (a + 1) a (a + 1), Zx n c (a + 1) c, Zx n a a (a + 1)])
  /-- (27) -/
  | r27 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (heven : (c - a) % 2 = 0) :
      Fig8 (wordOf [Zx n a a c])
        (wordOf [Zx n (c - 1) (c - 1) c, Zx n a a (c - 1), Zx n c (c - 1) c])
  /-- (28) -/
  | r28 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (heven : (c - a) % 2 = 0) :
      Fig8 (wordOf [Zx n c a c])
        (wordOf [Zx n (c - 1) (c - 1) c, Zx n (c - 1) a (c - 1), Zx n c (c - 1) c])
  /-- (29) -/
  | r29 (a : ℕ) (ha : a + 1 < 2 ^ n) :
      Fig8 (wordOf [Zx n a a (a + 1), Zx n (a + 1) a (a + 1)]) (wordOf [])
  /-- (30) -/
  | r30 (a b c : ℕ) (hb : b < 2 ^ n) (ha : a < 2 ^ n) (hc : c < 2 ^ n) (hab : a ≠ b)
      (hca : c ≠ a) (hcb : c ≠ b) :
      Fig8 (wordOf [Zx n c a b]) (wordOf [Zz n c a, Zx n a a b])
  /-- (31) -/
  | r31 (a c : ℕ) (ha : a + 1 < 2 ^ n) (hc : c < 2 ^ n) (hca : c ≠ a) (hca1 : c ≠ a + 1) :
      Fig8 (wordOf [Zz n (a + 1) c, Zx n a a (a + 1)]) (wordOf [Zx n a a (a + 1), Zz n a c])
  /-- (32) -/
  | r32 (a b : ℕ) (hab : a + 1 < b) (hb : b + 1 < 2 ^ n) :
      Fig8 (wordOf [Zx n a a (a + 1), Zx n b b (b + 1)])
        (wordOf [Zx n b b (b + 1), Zx n a a (a + 1)])
  /-- (33) -/
  | r33 (a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
      Fig8 (wordOf [Zx n b a b]) (wordOf [Zx n b b a])
  /-- (34) -/
  | r34 (a b c d : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
      (hab : a ≠ b) (hcd : c ≠ d) :
      Fig8 (wordOf [Xx n a b c d]) (wordOf [Zx n a a b, Zx n b c d])
  /-- (35) -/
  | r35 (a b c d : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
      (h : Distinct4 a b c d) (hp : patt n a b c d = none) :
      Fig8 (wordOf [Hh n a b c d])
        (wordOf ((sigmaW n a b c d).1 ++ [Hh n 0 1 3 2] ++ (sigmaW n a b c d).2))
  /-- (36) -/
  | r36 (a b c d u w : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
      (h : Distinct4 a b c d) (hp : patt n a b c d = some (1, u, w)) :
      Fig8 (wordOf [Hh n a b c d]) (wordOf (wW n 1 (gray a) u w))
  /-- (37) -/
  | r37 (a b c d u w : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
      (h : Distinct4 a b c d) (hp : patt n a b c d = some (2, u, w)) :
      Fig8 (wordOf [Hh n a b c d]) (wordOf (wW n 2 (gray a) u w))
  /-- (38) -/
  | r38 (a : ℕ) (h4 : 4 ≤ a) (ha : a + 1 < 2 ^ n) :
      Fig8 (wordOf [Zx n a a (a + 1), Hh n 0 1 3 2]) (wordOf [Hh n 0 1 3 2, Zx n a a (a + 1)])
  /-- (39) -/
  | r39 : Fig8 (wordOf [Zz n 0 1, Hh n 0 1 3 2]) (wordOf [Hh n 0 1 3 2, Zz n 0 1])
  /-- (40) -/
  | r40 : Fig8 (wordOf [Zz n 3 4, Hh n 0 1 3 2]) (wordOf [Hh n 0 1 3 2, Zz n 3 4, Zx n 2 2 3])
  /-- (41) -/
  | r41 : Fig8 (wordOf [Hh n 0 1 3 2, Hh n 0 1 3 2]) (wordOf [])
  /-- (42) -/
  | r42 (a b c d : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
      (hab : a ≠ b) (hcd : c ≠ d) (h3 : ¬ Distinct4 a b c d) :
      Fig8 (wordOf [Hh n a b (freshPair n a b c d).1 (freshPair n a b c d).2,
          Hh n (freshPair n a b c d).1 (freshPair n a b c d).2 c d])
        (wordOf [Hh n a b c d])
  /-- (43) -/
  | r43 : Fig8 (wordOf [Hh n 0 1 3 2, Hh n 3 2 4 5])
      (wordOf [Xx n 0 3 1 2, Hh n 3 2 4 5, Xx n 0 3 1 2])
  /-- (44) -/
  | r44 : Fig8 (wordOf [Xx n 0 3 1 2, Hh n 0 1 3 2]) (wordOf [Hh n 0 1 3 2, Xx n 0 3 1 2])
  /-- (45) -/
  | r45 : Fig8
      (wordOf [Hh n 0 1 7 6, Hh n 0 3 1 2, Hh n 0 1 7 6, Zz n 0 1, Hh n 0 3 1 2])
      (wordOf [Hh n 0 3 1 2, Zz n 0 1, Hh n 0 1 7 6, Hh n 0 3 1 2, Hh n 0 1 7 6])
  /-- (46) -/
  | r46 : Fig8
      (wordOf [Hh n 0 1 7 6, Hh n 0 3 1 2, Hh n 3 4 2 5, Hh n 3 2 4 5, Hh n 7 6 4 5,
        Zz n 2 3, Hh n 3 4 2 5, Hh n 0 3 1 2])
      (wordOf [Hh n 0 3 1 2, Hh n 3 4 2 5, Zz n 2 3, Hh n 7 6 4 5, Hh n 3 2 4 5,
        Hh n 3 4 2 5, Hh n 0 3 1 2, Hh n 0 1 7 6])

end QCert.RealCliffordCH.Sec8
