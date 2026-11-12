/-
# Circuits

Translation of `Circuit/Base.agda`.

A gate set is a family `Gate : ℕ → Type`, `Gate k` the gates on `k` wires
(`Gate 0` the scalars).  Wires are numbered from `0` at the bottom.  A
generator of an `n`-wire circuit (`Gen Gate n`, the Agda's `Gen n`) is a
gate on the bottom wires (`gate0` … `gate3`, the Agda's `gate₀` … `gate₃`)
or a generator of an `(n - 1)`-wire circuit shifted up one wire (`up`, the
Agda's `_↥`); a circuit is a word of generators (`Circuit Gate n`).
`Circuit.shift` is the Agda's `_↑`, `Gen.pad n` / `Circuit.pad n` the
Agda's `_↧ᵏ n` / `_↓ᵏ n` (idle wires on top; the width is written `n + k`
where the Agda writes `k + n`).

`Lift R` is the Agda's `Lift-Relation`'s `_VRel,_===_`: a rule family `R`
(the Agda's `_SRel,_===_`, constructor `srel`, here `rule`) closed under
the five structural rules — `shift` (`cong↑`), `comm1`, `comm2`, `comm3`
(`comm₁`, `comm₂`, `comm₃`) and `scalar` (`ω↑=ω`) — and `Derives R n w v`
is its congruence at width `n`.  Lift-Relation's lemmas follow, in the
namespace `EquaCert.Circuit`: `lemma_cong_up` (`lemma-cong↑`),
`comm_gate₁_w`, `comm_gate₂_w`, `comm_gate₃_w` (`comm-gate₁-w↑`, …), and
`comm₀` (the Agda's `Central-Scalars` with `Single-Scalar`: when all scalars
are equal, a scalar commutes with every generator).

`Padded Base` applies rules stated on their own wires at every wider
width (the bottom wires), and `cl R n w` is the class of a circuit in the
quotient monoid, where derivability is equality (`cl_eq`).
-/
import EquaCert.Presentation.Definitions

namespace EquaCert

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

/-- A generator of `k`-wire circuits as a generator of `n + k`-wire
circuits: the same gate on the same wires, with `n` idle wires on top. -/
def Gen.pad (n : ℕ) : {k : ℕ} → Gen Gate k → Gen Gate (n + k)
  | _, .gate0 g => .gate0 g
  | _, .gate1 g => .gate1 g
  | _, .gate2 g => .gate2 g
  | _, .gate3 g => .gate3 g
  | _, .up g => .up (g.pad n)

/-- A `k`-wire circuit on the bottom `k` of `n + k` wires. -/
def Circuit.pad (n : ℕ) {k : ℕ} : Circuit Gate k →* Circuit Gate (n + k) :=
  FreeMonoid.map (Gen.pad n)

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

/-- Rules stated on their own wires, as a paper draws them (`Base k w v`
for an equation between `k`-wire circuits), applied on the bottom wires of
every wider circuit.  `Lift (Padded Base)` is then the full theory. -/
inductive Padded (Base : CRel Gate) : CRel Gate
  | pad {k : ℕ} (n : ℕ) {w v : Circuit Gate k} :
      Base k w v → Padded Base (n + k) (Circuit.pad n w) (Circuit.pad n v)

/-- The derivable equations of `n`-wire circuits under the rules `R` and the
structural rules. -/
abbrev Derives (R : CRel Gate) (n : ℕ) (w v : Circuit Gate n) : Prop :=
  Derivable (Lift R n) w v


namespace Circuit

open EquaCert

/-! ## The quotient monoid of a theory -/

section Quot

variable {Gate : ℕ → Type}

/-- The class of a circuit modulo the theory `Lift R` at width `n`. -/
def cl (R : CRel Gate) (n : ℕ) (w : Circuit Gate n) : (conGen (Lift R n)).Quotient :=
  (conGen (Lift R n)).mk' w

variable {R : CRel Gate} {n : ℕ}

theorem cl_eq {w v : Circuit Gate n} : cl R n w = cl R n v ↔ Derives R n w v :=
  (conGen (Lift R n)).eq

theorem cl_mul (w v : Circuit Gate n) : cl R n (w * v) = cl R n w * cl R n v :=
  map_mul (conGen (Lift R n)).mk' w v

theorem cl_one : cl R n (1 : Circuit Gate n) = 1 := map_one (conGen (Lift R n)).mk'

end Quot

/-! ## From `Circuit.Base`: the structural rules at circuits -/

section Base

variable {Gate : ℕ → Type} {R : CRel Gate}

/-- The congruence at width `n` lifts to width `n + 1` (the Agda's
`lemma-cong↑`). -/
theorem lemma_cong_up {n : ℕ} {w v : Circuit Gate n} (d : Derives R n w v) :
    Derives R (n + 1) (shift w) (shift v) := by
  let c : Con (Circuit Gate n) := (conGen (Lift R (n + 1))).comap shift (map_mul shift)
  have : conGen (Lift R n) ≤ c := Con.conGen_le fun x y r => Derivable.of (Lift.shift r)
  exact this d

/-- A one-wire gate at the bottom commutes with a circuit shifted up past it
(the Agda's `comm-gate₁-w↑`). -/
theorem comm_gate₁_w {n : ℕ} (g : Gate 1) (w : Circuit Gate n) :
    Derives R (n + 1) (shift w * g1 g) (g1 g * shift w) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have a : cl R (n + 1) (FreeMonoid.of x.up * g1 g) = cl R (n + 1) (g1 g * FreeMonoid.of x.up) :=
      cl_eq.2 (Derivable.of (Lift.comm1 g x))
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, shift_of, cl_mul, cl_mul, cl_mul, cl_mul, mul_assoc, ih, ← mul_assoc, a,
      mul_assoc]

/-- The Agda's `comm-gate₂-w↑↑`. -/
theorem comm_gate₂_w {n : ℕ} (g : Gate 2) (w : Circuit Gate n) :
    Derives R (n + 2) (shift (shift w) * g2 g) (g2 g * shift (shift w)) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have a : cl R (n + 2) (FreeMonoid.of x.up.up * g2 g) =
        cl R (n + 2) (g2 g * FreeMonoid.of x.up.up) :=
      cl_eq.2 (Derivable.of (Lift.comm2 g x))
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, map_mul, shift_of, shift_of, cl_mul, cl_mul, cl_mul, cl_mul, mul_assoc, ih,
      ← mul_assoc, a, mul_assoc]

/-- The Agda's `comm-gate₃-w↑↑↑`. -/
theorem comm_gate₃_w {n : ℕ} (g : Gate 3) (w : Circuit Gate n) :
    Derives R (n + 3) (shift (shift (shift w)) * g3 g) (g3 g * shift (shift (shift w))) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have a : cl R (n + 3) (FreeMonoid.of x.up.up.up * g3 g) =
        cl R (n + 3) (g3 g * FreeMonoid.of x.up.up.up) :=
      cl_eq.2 (Derivable.of (Lift.comm3 g x))
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, map_mul, map_mul, shift_of, shift_of, shift_of, cl_mul, cl_mul, cl_mul, cl_mul,
      mul_assoc, ih, ← mul_assoc, a, mul_assoc]

/-- A scalar shifted up is the scalar, at any width. -/
private theorem scalar_up {n : ℕ} (h : Gate 0) :
    Derives R (n + 1) (FreeMonoid.of (Gen.gate0 h).up) (g0 h) :=
  Derivable.of (Lift.scalar h)

/-- `Central-Scalars` with `Single-Scalar`: when the scalars are all equal,
a scalar commutes with every generator (the Agda's `comm₀`). -/
theorem comm₀ (one : ∀ h h' : Gate 0, h = h') (h : Gate 0) :
    ∀ {n : ℕ} (g : Gen Gate n),
      Derives R n (FreeMonoid.of g * g0 h) (g0 h * FreeMonoid.of g)
  | _, .gate0 h' => by rw [one h h']
  | _, @Gen.gate1 _ m h₁ =>
    have e := scalar_up (R := R) (n := m) h
    (((Derivable.refl _).mul e.symm).trans (Derivable.of (Lift.comm1 h₁ (Gen.gate0 h))).symm).trans
      (e.mul (Derivable.refl _))
  | _, @Gen.gate2 _ m h₂ =>
    have e : Derives R (m + 2) (FreeMonoid.of (Gen.gate0 h).up.up) (g0 h) :=
      (lemma_cong_up (scalar_up (R := R) (n := m) h)).trans (scalar_up h)
    (((Derivable.refl _).mul e.symm).trans (Derivable.of (Lift.comm2 h₂ (Gen.gate0 h))).symm).trans
      (e.mul (Derivable.refl _))
  | _, @Gen.gate3 _ m h₃ =>
    have e : Derives R (m + 3) (FreeMonoid.of (Gen.gate0 h).up.up.up) (g0 h) :=
      ((lemma_cong_up (lemma_cong_up (scalar_up (R := R) (n := m) h))).trans
        (lemma_cong_up (scalar_up h))).trans (scalar_up h)
    (((Derivable.refl _).mul e.symm).trans (Derivable.of (Lift.comm3 h₃ (Gen.gate0 h))).symm).trans
      (e.mul (Derivable.refl _))
  | _, @Gen.up _ m g =>
    have e := scalar_up (R := R) (n := m) h
    (((Derivable.refl _).mul e.symm).trans (lemma_cong_up (comm₀ one h g))).trans
      (e.mul (Derivable.refl _))

end Base


end Circuit

end EquaCert
