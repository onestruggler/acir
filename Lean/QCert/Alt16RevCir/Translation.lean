/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The translations, in both directions, between Lafont's cycles on sixteen points and the gates on four wires

Translation of `Translation.agda`.  The generators of the alternating group
on sixteen points are Lafont's cycles `ω₀, …, ω₁₃` (`Lib/Alternating` at
width 16), and those of the circuits the gates `X`, `CX`, `CCX` and `Ex` on
four wires (`Syntactics`).  This module translates each set of generators
into words in the other:

* `f` reads a gate as a word in the cycles: the permutation of the sixteen
  states that the gate carries out;

* `g` reads a cycle as a circuit: `g ωᵢ` is `Ω i`.

`Iso` proves that the two are inverse to each other on generators, and that
each carries the relations of its source to consequences of the relations
of its target.

The six gates on their own wires go to the words that the rules `gate_X`,
…, `gate_Ex₂` of `Syntactics` name.  A gate on other wires goes to the word
of that gate between the words of the swaps that carry it there: NOT one
wire up is `Ex * X * Ex`, and `CX` and `CCX` one wire up are `CX` and `CCX`
between the cycles `σ⁻[ 2 ]`, `σ[ 2 ]` and `σ⁻[ 3 ]`, `σ[ 3 ]` of
`CircuitProp`.

A cycle of Lafont's is the generator `ω` under some number of shifts, so `g`
is defined with that number as a parameter: `gd d` (the Agda's `gᵈ d`) reads
a generator at any width as the cycle `d` points further up.

Lafont's circuits and generators are `Alternating.Circ n` and
`Alternating.Gn n` (the Agda's `L.Circuit n`, `L.Gen n`); `cycG d` is the
Agda's `L.ω-gen` under `d` shifts, so that `ωᵢ` is the one-letter word of
`cycG i`.
-/
import QCert.Alt16RevCir.Syntactics
import QCert.Alt16RevCir.Lib.Alternating.Syntactics

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp

/-! ## Lafont's cycles on sixteen points -/

/-- Lafont's generator `d` points up (the Agda's `L.ω {m} L.↑ᵏ d`, as a
letter). -/
def cycG : (d : ℕ) → {m : ℕ} → Alternating.Gn (m + 3 + d)
  | 0, _ => .gate3 .ω_gate
  | d + 1, _ => (cycG d).up

/-! `ωᵢ` sends `i` to `i + 1`, `i + 1` to `i + 2` and `i + 2` to `i`. -/

def ω₀ : Alternating.Circ 16 := FreeMonoid.of (cycG 0 (m := 13))

def ω₁ : Alternating.Circ 16 := FreeMonoid.of (cycG 1 (m := 12))

def ω₂ : Alternating.Circ 16 := FreeMonoid.of (cycG 2 (m := 11))

def ω₃ : Alternating.Circ 16 := FreeMonoid.of (cycG 3 (m := 10))

def ω₄ : Alternating.Circ 16 := FreeMonoid.of (cycG 4 (m := 9))

def ω₅ : Alternating.Circ 16 := FreeMonoid.of (cycG 5 (m := 8))

def ω₆ : Alternating.Circ 16 := FreeMonoid.of (cycG 6 (m := 7))

def ω₇ : Alternating.Circ 16 := FreeMonoid.of (cycG 7 (m := 6))

def ω₈ : Alternating.Circ 16 := FreeMonoid.of (cycG 8 (m := 5))

def ω₉ : Alternating.Circ 16 := FreeMonoid.of (cycG 9 (m := 4))

def ω₁₀ : Alternating.Circ 16 := FreeMonoid.of (cycG 10 (m := 3))

def ω₁₁ : Alternating.Circ 16 := FreeMonoid.of (cycG 11 (m := 2))

def ω₁₂ : Alternating.Circ 16 := FreeMonoid.of (cycG 12 (m := 1))

def ω₁₃ : Alternating.Circ 16 := FreeMonoid.of (cycG 13 (m := 0))

/-! ## The gates as words in the cycles -/

/-! The gates on their own wires. -/

def fX : Alternating.Circ 16 := ω₁ * ω₀ * ω₅ * ω₄ * ω₉ * ω₈ * ω₁₃ * ω₁₂

def fCX : Alternating.Circ 16 := ω₃ * ω₂ * ω₁₁ * ω₁₀

def fCCX : Alternating.Circ 16 := ω₅ * ω₄ * ω₇ * ω₆ * ω₉ * ω₈

def fEx₀ : Alternating.Circ 16 := ω₁ * ω₃ * ω₂ * ω₄ * ω₉ * ω₁₁ * ω₁₀ * ω₁₂

def fEx₁ : Alternating.Circ 16 :=
  ω₂ * ω₃ * ω₄ * ω₂ * ω₅ * ω₃ * ω₈ * ω₉ * ω₁₀ * ω₈ * ω₁₁ * ω₉

def fEx₂ : Alternating.Circ 16 :=
  ω₆ * ω₇ * ω₈ * ω₉ * ω₁₀ * ω₁₁ * ω₁₂ * ω₁₃ *
  ω₄ * ω₅ * ω₆ * ω₇ * ω₈ * ω₉ * ω₁₀ * ω₁₁ *
  ω₆ * ω₇ * ω₈ * ω₉ * ω₄ * ω₅ * ω₆ * ω₇

/-! NOT, `CX` and `CCX` further up, between the swaps. -/

def fX₁ : Alternating.Circ 16 := fEx₀ * fX * fEx₀

def fX₂ : Alternating.Circ 16 := fEx₁ * fX₁ * fEx₁

def fX₃ : Alternating.Circ 16 := fEx₂ * fX₂ * fEx₂

def fCX₁ : Alternating.Circ 16 := (fEx₀ * fEx₁) * fCX * (fEx₁ * fEx₀)

def fCX₂ : Alternating.Circ 16 := (fEx₁ * fEx₂) * fCX₁ * (fEx₂ * fEx₁)

def fCCX₁ : Alternating.Circ 16 := (fEx₀ * fEx₁ * fEx₂) * fCCX * ((fEx₂ * fEx₁) * fEx₀)

def f : Gn 4 → Alternating.Circ 16
  | .gate0 g => nomatch g
  | .gate1 .X_gate => fX
  | .gate2 .CX_gate => fCX
  | .gate2 .Ex_gate => fEx₀
  | .gate3 .CCX_gate => fCCX
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => fX₁
  | .up (.gate2 .CX_gate) => fCX₁
  | .up (.gate2 .Ex_gate) => fEx₁
  | .up (.gate3 .CCX_gate) => fCCX₁
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => fX₂
  | .up (.up (.gate2 .CX_gate)) => fCX₂
  | .up (.up (.gate2 .Ex_gate)) => fEx₂
  | .up (.up (.up (.gate0 g))) => nomatch g
  | .up (.up (.up (.gate1 .X_gate))) => fX₃
  | .up (.up (.up (.up (.gate0 g)))) => nomatch g

/-! ## The cycles as circuits -/

/-- The generator `y`, `d` points further up, as a circuit (the Agda's
`gᵈ`). -/
def gd : {n : ℕ} → ℕ → Alternating.Gn n → Circ 4
  | _, _, .gate0 g => nomatch g
  | _, _, .gate1 g => nomatch g
  | _, _, .gate2 g => nomatch g
  | _, d, .gate3 .ω_gate => Ω d
  | _, d, .up y => gd (d + 1) y

def g : Alternating.Gn 16 → Circ 4 := gd 0

end QCert.Alt16RevCir
