/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Moving derivations along an order embedding of indices

A strictly increasing map `f : Fin m → Fin n` sends generators to
generators (it keeps `a < b`) and every instance of a relation of Figure 6 to
an instance of the same relation (it keeps the order and distinctness
conditions).  So a derivation found at the indices `0, 1, …, m-1` holds at any
increasing indices `f 0 < f 1 < … < f (m-1)` (`Derivable.map`).
-/
import QCert.HadamardPi.Derive

namespace QCert.HadamardPi

open FreeMonoid

variable {m n : ℕ}

/-- A generator moved along an order embedding. -/
def Gen.map (f : Fin m → Fin n) (hf : StrictMono f) : Gen m → Gen n
  | .Z a => .Z (f a)
  | .X a b h => .X (f a) (f b) (hf h)
  | .H a b h => .H (f a) (f b) (hf h)

/-- A word moved along an order embedding. -/
def wmap (f : Fin m → Fin n) (hf : StrictMono f) : Word (Gen m) →* Word (Gen n) :=
  FreeMonoid.map (Gen.map f hf)

theorem fig6_map (f : Fin m → Fin n) (hf : StrictMono f) {w v : Word (Gen m)} (h : Fig6 w v) :
    Fig6 (wmap f hf w) (wmap f hf v) := by
  have hi := hf.injective
  have ne : ∀ {a b : Fin m}, a ≠ b → f a ≠ f b := fun h e => h (hi e)
  cases h with
  | a1 a => exact Fig6.a1 (f a)
  | a2 h => exact Fig6.a2 (hf h)
  | a3 h => exact Fig6.a3 (hf h)
  | b1 h => exact Fig6.b1 (ne h)
  | b2 hbc hab hac => exact Fig6.b2 (hf hbc) (ne hab) (ne hac)
  | b3 hab hcd hac had hbc hbd =>
    exact Fig6.b3 (hf hab) (hf hcd) (ne hac) (ne had) (ne hbc) (ne hbd)
  | b4 hbc hab hac => exact Fig6.b4 (hf hbc) (ne hab) (ne hac)
  | b5 hab hcd hac had hbc hbd =>
    exact Fig6.b5 (hf hab) (hf hcd) (ne hac) (ne had) (ne hbc) (ne hbd)
  | b6 hab hcd hac had hbc hbd =>
    exact Fig6.b6 (hf hab) (hf hcd) (ne hac) (ne had) (ne hbc) (ne hbd)
  | c1 h => exact Fig6.c1 (hf h)
  | c2 hab hbc => exact Fig6.c2 (hf hab) (hf hbc)
  | c3 hab hbc => exact Fig6.c3 (hf hab) (hf hbc)
  | c4 hab hbc => exact Fig6.c4 (hf hab) (hf hbc)
  | c5 hab hbc => exact Fig6.c5 (hf hab) (hf hbc)
  | d1 h => exact Fig6.d1 (hf h)
  | d2 h => exact Fig6.d2 (hf h)
  | d3 hab hcd hac hbd hbc => exact Fig6.d3 (hf hab) (hf hcd) (hf hac) (hf hbd) (ne hbc)
  | d4 hac hbd hab hce hdf hef hbc hbe hcd hde =>
    exact Fig6.d4 (hf hac) (hf hbd) (hf hab) (hf hce) (hf hdf) (hf hef) (ne hbc) (ne hbe)
      (ne hcd) (ne hde)

/-- Derivations move along an order embedding. -/
theorem Derivable.map (f : Fin m → Fin n) (hf : StrictMono f) {w v : Word (Gen m)}
    (h : Derivable Fig6 w v) : Derivable Fig6 (wmap f hf w) (wmap f hf v) := by
  have : conGen (Fig6 (n := m)) ≤ (conGen (Fig6 (n := n))).comap (wmap f hf) (map_mul _) :=
    Con.conGen_le fun x y hxy => ConGen.Rel.of _ _ (fig6_map f hf hxy)
  exact this h

theorem wmap_ofList (f : Fin m → Fin n) (hf : StrictMono f) (l : List (Gen m)) :
    wmap f hf (ofList l) = ofList (l.map (Gen.map f hf)) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [ofList_cons, map_mul, ih, List.map_cons, ofList_cons]
    rfl

end QCert.HadamardPi
