/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits

A gate set is a family `Gate : ℕ → Type`, `Gate k` the gates acting on `k`
wires (`Gate 0` are scalars).  Wires are numbered from `0` at the bottom.
A generator of an `n`-wire circuit is a gate acting on the bottom wires, or
a generator of an `n`-wire circuit shifted up by one wire (onto wires
`1, …, n` of `n + 1` wires); a circuit is a word of generators, read in
operator order (`w * v` applies `v` first) unless a development says
otherwise.

A rule set is stated on as many wires as each rule is drawn on.  To apply
the rules inside wider circuits, `Lift R` closes a family of rules `R n`
under the *structural rules*, which hold for every gate set: an equation
can be shifted up one wire, gates on disjoint wires commute, and a scalar
is the same on every wire.
-/
import QCert.Presentation

namespace QCert

/-- The generators of `n`-wire circuits over the gate set `Gate`. -/
inductive Gen (Gate : ℕ → Type) : ℕ → Type
  /-- A scalar, at any width. -/
  | gate0 {n : ℕ} (g : Gate 0) : Gen Gate n
  /-- A one-wire gate on wire `0`. -/
  | gate1 {n : ℕ} (g : Gate 1) : Gen Gate (n + 1)
  /-- A two-wire gate on wires `0, 1`. -/
  | gate2 {n : ℕ} (g : Gate 2) : Gen Gate (n + 2)
  /-- A three-wire gate on wires `0, 1, 2`. -/
  | gate3 {n : ℕ} (g : Gate 3) : Gen Gate (n + 3)
  /-- A generator moved up by one wire. -/
  | up {n : ℕ} (g : Gen Gate n) : Gen Gate (n + 1)

variable {Gate : ℕ → Type}

/-- Circuits on `n` wires. -/
abbrev Circuit (Gate : ℕ → Type) (n : ℕ) := Word (Gen Gate n)

namespace Circuit

/-- A circuit moved up by one wire. -/
def shift {n : ℕ} : Circuit Gate n →* Circuit Gate (n + 1) := FreeMonoid.map Gen.up

/-- A single gate as a circuit. -/
abbrev g0 {n : ℕ} (g : Gate 0) : Circuit Gate n := FreeMonoid.of (Gen.gate0 g)
abbrev g1 {n : ℕ} (g : Gate 1) : Circuit Gate (n + 1) := FreeMonoid.of (Gen.gate1 g)
abbrev g2 {n : ℕ} (g : Gate 2) : Circuit Gate (n + 2) := FreeMonoid.of (Gen.gate2 g)
abbrev g3 {n : ℕ} (g : Gate 3) : Circuit Gate (n + 3) := FreeMonoid.of (Gen.gate3 g)

@[simp] theorem shift_of {n : ℕ} (g : Gen Gate n) :
    shift (FreeMonoid.of g) = FreeMonoid.of g.up := rfl

end Circuit

/-- A rule set given at every width: `R n w v` says `w = v` is a rule on `n`
wires. -/
abbrev CRel (Gate : ℕ → Type) := (n : ℕ) → WRel (Gen Gate n)

open Circuit in
/-- The rules `R` together with the structural rules. -/
inductive Lift (R : CRel Gate) : CRel Gate
  /-- A rule of `R`. -/
  | rule {n : ℕ} {w v : Circuit Gate n} : R n w v → Lift R n w v
  /-- A rule moved up one wire. -/
  | shift {n : ℕ} {w v : Circuit Gate n} :
      Lift R n w v → Lift R (n + 1) (Circuit.shift w) (Circuit.shift v)
  /-- A one-wire gate commutes with a generator on the wires above it. -/
  | comm1 {n : ℕ} (h : Gate 1) (g : Gen Gate n) :
      Lift R (n + 1) (FreeMonoid.of g.up * g1 h) (g1 h * FreeMonoid.of g.up)
  /-- A two-wire gate commutes with a generator on the wires above it. -/
  | comm2 {n : ℕ} (h : Gate 2) (g : Gen Gate n) :
      Lift R (n + 2) (FreeMonoid.of g.up.up * g2 h) (g2 h * FreeMonoid.of g.up.up)
  /-- A three-wire gate commutes with a generator on the wires above it. -/
  | comm3 {n : ℕ} (h : Gate 3) (g : Gen Gate n) :
      Lift R (n + 3) (FreeMonoid.of g.up.up.up * g3 h) (g3 h * FreeMonoid.of g.up.up.up)
  /-- A scalar is the same on every wire. -/
  | scalar {n : ℕ} (c : Gate 0) :
      Lift R (n + 1) (FreeMonoid.of (Gen.gate0 c).up) (g0 c)

/-- The derivable equations of `n`-wire circuits under the rules `R` and the
structural rules. -/
abbrev Derives (R : CRel Gate) (n : ℕ) (w v : Circuit Gate n) : Prop :=
  Derivable (Lift R n) w v

end QCert
