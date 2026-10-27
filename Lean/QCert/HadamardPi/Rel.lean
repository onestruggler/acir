/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The relations of Figure 6 on lists, and a few derived ones

Each relation is restated as a derivation between explicit lists of
generators (`rl_a1`, …), ready for `rw_at`.  The derived relations are the
ones the squares of the Main Lemma use: how `X_[a,b]` and `H_[a,b]` move
`(-1)` across ((c1) and (d2) read in the other directions), and the
conjugation `H_[a,b] (-1)_[a] = (-1)_[a] (-1)_[b] X_[a,b] H_[a,b]`
((a1), (d1), (d2)).
-/
import QCert.HadamardPi.Derive

namespace QCert.HadamardPi

open FreeMonoid

variable {n : ℕ} {a b c d : Fin n}

local notation "D" => Derivable Fig6

theorem rl_a1 (a : Fin n) : D (ofList [.Z a, .Z a]) (ofList []) := Derivable.of (Fig6.a1 a)

theorem rl_a2 (h : a < b) : D (ofList [.X a b h, .X a b h]) (ofList []) :=
  Derivable.of (Fig6.a2 h)

theorem rl_a3 (h : a < b) : D (ofList [.H a b h, .H a b h]) (ofList []) :=
  Derivable.of (Fig6.a3 h)

theorem rl_b1 (h : a ≠ b) : D (ofList [.Z a, .Z b]) (ofList [.Z b, .Z a]) :=
  Derivable.of (Fig6.b1 h)

theorem rl_b2 (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
    D (ofList [.Z a, .X b c hbc]) (ofList [.X b c hbc, .Z a]) := Derivable.of (Fig6.b2 hbc hab hac)

theorem rl_b3 (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : D (ofList [.X a b hab, .X c d hcd]) (ofList [.X c d hcd, .X a b hab]) :=
  Derivable.of (Fig6.b3 hab hcd hac had hbc hbd)

theorem rl_b4 (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
    D (ofList [.Z a, .H b c hbc]) (ofList [.H b c hbc, .Z a]) := Derivable.of (Fig6.b4 hbc hab hac)

theorem rl_b5 (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : D (ofList [.X a b hab, .H c d hcd]) (ofList [.H c d hcd, .X a b hab]) :=
  Derivable.of (Fig6.b5 hab hcd hac had hbc hbd)

theorem rl_b6 (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : D (ofList [.H a b hab, .H c d hcd]) (ofList [.H c d hcd, .H a b hab]) :=
  Derivable.of (Fig6.b6 hab hcd hac had hbc hbd)

theorem rl_c1 (h : a < b) : D (ofList [.Z a, .X a b h]) (ofList [.X a b h, .Z b]) :=
  Derivable.of (Fig6.c1 h)

theorem rl_c2 (hab : a < b) (hbc : b < c) :
    D (ofList [.X b c hbc, .X a b hab]) (ofList [.X a b hab, .X a c (hab.trans hbc)]) :=
  Derivable.of (Fig6.c2 hab hbc)

theorem rl_c3 (hab : a < b) (hbc : b < c) :
    D (ofList [.X a c (hab.trans hbc), .X b c hbc]) (ofList [.X b c hbc, .X a b hab]) :=
  Derivable.of (Fig6.c3 hab hbc)

theorem rl_d1 (h : a < b) :
    D (ofList [.Z a, .Z b, .H a b h]) (ofList [.H a b h, .Z a, .Z b]) := Derivable.of (Fig6.d1 h)

theorem rl_d2 (h : a < b) : D (ofList [.Z b, .H a b h]) (ofList [.H a b h, .X a b h]) :=
  Derivable.of (Fig6.d2 h)

/-- (c1) read the other way: `X_[a,b] (-1)_[a] ≈ (-1)_[b] X_[a,b]`. -/
theorem rl_XZa (h : a < b) : D (ofList [.X a b h, .Z a]) (ofList [.Z b, .X a b h]) :=
  (rw_at [.X a b h, .Z a] 2 (rl_a2 h).symm rfl).trans <|
  (rw_at _ 1 (rl_c1 h) rfl).trans <|
  (rw_at _ 0 (rl_a2 h) rfl)

/-- `X_[a,b] (-1)_[b] ≈ (-1)_[a] X_[a,b]`. -/
theorem rl_XZb (h : a < b) : D (ofList [.X a b h, .Z b]) (ofList [.Z a, .X a b h]) :=
  (rw_at [.X a b h, .Z b] 0 (rl_a2 h).symm rfl).trans <|
  (rw_at _ 2 (rl_c1 h).symm rfl).trans <|
  (rw_at _ 0 (rl_a2 h) rfl)

/-- (d2) read the other way: `H_[a,b] (-1)_[b] ≈ X_[a,b] H_[a,b]`. -/
theorem rl_HZb (h : a < b) : D (ofList [.H a b h, .Z b]) (ofList [.X a b h, .H a b h]) :=
  (rw_at [.H a b h, .Z b] 2 (rl_a3 h).symm rfl).trans <|
  (rw_at _ 1 (rl_d2 h) rfl).trans <|
  (rw_at _ 0 (rl_a3 h) rfl)

/-- `H_[a,b] (-1)_[a] ≈ (-1)_[a] (-1)_[b] X_[a,b] H_[a,b]`, by (a1), (d1), (d2). -/
theorem rl_HZa (h : a < b) :
    D (ofList [.H a b h, .Z a]) (ofList [.Z a, .Z b, .X a b h, .H a b h]) :=
  (rw_at [.H a b h, .Z a] 2 (rl_a1 b).symm rfl).trans <|
  (rw_at _ 0 (rl_d1 h).symm rfl).trans <|
  (rw_at _ 2 (rl_HZb h) rfl)

end QCert.HadamardPi
