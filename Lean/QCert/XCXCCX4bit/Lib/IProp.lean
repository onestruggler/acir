/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits in a PROP

Translation of the part of `Examples/Independence/Prop.agda` that the
four-bit development uses: a fragment's gates and the swap, as one gate
family (`PGate`), with the swap designated (`CircuitProp.HasSwap`), so that
`CircuitProp`'s swap rules and its `PropRel` lift the fragment's rules to a
PROP.  A fragment states its rules on their own wires, as a relation `SRel`
(`n SRel, w === v` in the Agda, one constructor per rule), and an instance
of a rule is `srel` of it (`CircuitProp.srel_rule`), a swap rule `σrel` of
one (`CircuitProp.sym_rule`).

The Agda's `⌈ g ⌉` is `PGate.gate g`.  The module `Axioms` (the selections
of axioms for independence) is not used by the four-bit development and is
not translated.

Wire 0 is the bottom wire, and words are in diagram order: `w * v` is `w`
followed by `v`.
-/
import QCert.XCXCCX4bit.Lib.CircuitProp

namespace QCert.XCXCCX4bit.IndepProp

open CircuitProp

/-- A fragment's gates and the swap. -/
inductive PGate (Gate : ℕ → Type) : ℕ → Type
  /-- A gate of the fragment (the Agda's `⌈ g ⌉`). -/
  | gate {n : ℕ} (g : Gate n) : PGate Gate n
  /-- The swap, a two-wire gate of its own. -/
  | swap : PGate Gate 2

instance (Gate : ℕ → Type) : HasSwap (PGate Gate) := ⟨PGate.swap⟩

end QCert.XCXCCX4bit.IndepProp
