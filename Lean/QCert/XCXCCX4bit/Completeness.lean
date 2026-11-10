/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness and completeness of the theory T on four wires

Translation of `Completeness.agda`.  `Four` reduces completeness on four
wires to the faithfulness of the circuits that keep wire 3, and `KFaithful`
proves it, so two four-wire circuits over X, CX and CCX with the same
function on the sixteen states are equal by the rules of Figure 1 and the
PROP laws; and conversely (`Semantics.sound`).
-/
import QCert.XCXCCX4bit.KFaithful
import QCert.XCXCCX4bit.Four

namespace QCert.XCXCCX4bit.Completeness

open QCert QCert.Circuit CircuitProp IndepProp

/-- Completeness: circuits with the same function are equal. -/
theorem complete₄ {u v : Circ 4} (e : sem u ≐ sem v) : 4 ⊢ u ≈ v :=
  Four.complete₄ KFaithful.faithful₃ e

/-- Soundness: equal circuits have the same function. -/
theorem sound₄ {u v : Circ 4} (d : 4 ⊢ u ≈ v) : sem u ≐ sem v :=
  sound d

end QCert.XCXCCX4bit.Completeness
