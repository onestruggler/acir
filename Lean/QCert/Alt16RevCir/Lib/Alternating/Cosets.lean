/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Alternating groups `𝔄ₙ`: Lafont's stairs as coset representatives

Translation of `Examples/Groups/Alternating/Cosets.agda`.

A canonical form on `n + 1` wires (Lafont, p. 268) is a canonical form on
the top `n` wires followed by a stairs, which sends wire 0 where the
permutation does: the stairs are representatives of the right cosets of `𝔄ₙ`
in `𝔄ₙ₊₁`, one for each target of wire 0.  A stairs of size `s` is
`ω₁ ω₂ … ω_s`, sending wire 0 to `s`, for `s ≤ n − 1`; the last coset, wire
0 sent to `n`, is the stairs of size `n − 1` with its last cycle doubled (the
fourth type of canonical form).  Here both are built one wire at a time:
`C.ωc` puts a cycle under a stairs one wire up, and `C.ωω` is the doubled
cycle on three wires that the last stairs ends in.  (The paper's "size of
the stairs" counts cycles; `C n` describes cosets on `n + 1` wires, and has
`n + 1` of them from `n = 2` on.)

**Deviations from the Agda.**  The Agda's constructor `ω•_` is `C.ωc`, and
its section map `[_]ᶜ` is `sec`, with its three clauses as the equations
`sec_ε`, `sec_ωc`, `sec_ωω`.  Elements of `Fin` are matched by their values
(`⟨0, _⟩`, `⟨k + 1, _⟩`).
-/
import QCert.Alt16RevCir.Lib.Alternating.Syntactics

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit

variable {n : ℕ}

/-! ## Coset type -/

/-- The cosets of `𝔄ₙ` in `𝔄ₙ₊₁`, as Lafont's stairs. -/
inductive C : ℕ → Type
  /-- The empty stairs. -/
  | ε {n : ℕ} : C n
  /-- A cycle under a stairs one wire up (the Agda's `ω•_`). -/
  | ωc {n : ℕ} : C (n + 1) → C (n + 2)
  /-- The doubled cycle on three wires. -/
  | ωω : C 2

/-! ## Section map -/

/-- The stairs of a coset (the Agda's `[_]ᶜ`). -/
def sec : {n : ℕ} → C n → Circ (n + 1)
  | _, .ε => 1
  | _, .ωc c => ω * shift (sec c)
  | _, .ωω => ω * ω

theorem sec_ε : sec (C.ε : C n) = 1 := rfl

theorem sec_ωc (c : C (n + 1)) : sec (C.ωc c) = ω * shift (sec c) := rfl

theorem sec_ωω : sec C.ωω = ω * ω := rfl

/-! ## Where a coset sends wire 0 -/

/-- The wire to which a stairs sends wire 0. -/
def target : {n : ℕ} → C n → Fin (n + 1)
  | _, .ε => 0
  | _, .ωc c => (target c).succ
  | _, .ωω => 2

theorem target_injective : ∀ {n : ℕ} {c c' : C n}, target c = target c' → c = c'
  | _, .ε, .ε, _ => rfl
  | _, .ωc _, .ωc _, eq => congrArg C.ωc (target_injective (Fin.succ_injective _ eq))
  | _, .ωω, .ωω, _ => rfl
  | _, .ε, .ωc _, eq => absurd eq.symm (Fin.succ_ne_zero _)
  | _, .ε, .ωω, eq => absurd eq (by decide)
  | _, .ωc _, .ε, eq => absurd eq (Fin.succ_ne_zero _)
  | _, .ωc .ε, .ωω, eq => absurd eq (by decide)
  | _, .ωω, .ε, eq => absurd eq (by decide)
  | _, .ωω, .ωc .ε, eq => absurd eq (by decide)

/-- From three wires on, every target has a coset. -/
def coset : {m : ℕ} → Fin (m + 3) → C (m + 2)
  | _, ⟨0, _⟩ => .ε
  | 0, ⟨1, _⟩ => .ωc .ε
  | 0, ⟨2, _⟩ => .ωω
  | 0, ⟨_ + 3, h⟩ => absurd h (by omega)
  | m + 1, ⟨j + 1, h⟩ => .ωc (coset (m := m) ⟨j, by omega⟩)

theorem target_coset : ∀ {m : ℕ} (j : Fin (m + 3)), target (coset j) = j
  | _, ⟨0, _⟩ => by rw [coset]; rfl
  | 0, ⟨1, _⟩ => rfl
  | 0, ⟨2, _⟩ => rfl
  | 0, ⟨_ + 3, h⟩ => absurd h (by omega)
  | m + 1, ⟨j + 1, h⟩ => by
    rw [coset, target, target_coset]
    rfl

end QCert.Alt16RevCir.Alternating
