/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two wires: the rules are complete, and the circuits present S₄

Translation of `Width2.agda`: the instance of `BySymmetric` at two wires and
four states, numbered along the Gray code 00, 01, 11, 10 (wire 1 first).
The transposition of two consecutive states is a controlled NOT: `Θ 0` is
`CX` with a white control, `Θ 1` is `CX` upside down, `Θ 2` is `CX`.  NOT on
wire 0 exchanges the states 0 1 and 2 3, `CX` the states 2 3, and the swap
the states 1 3; NOT on wire 1 is NOT on wire 0 between swaps.  The Coxeter
relations between the `Θ d` and the three gates' words are derived from the
rules (1)–(3) in `Width2.Derivations`.

The Agda's module application `Step₂` is the structure value `step₂`; its
`fin4`, for proofs by evaluation at the four states, is `decide`.
-/
import QCert.Alt16RevCir.BySymmetric
import QCert.Alt16RevCir.Width2.Derivations

namespace QCert.Alt16RevCir.Width2

open QCert QCert.Circuit CircuitProp Engine
open Symmetric (SG)
open Derivations (Θ)

/-! ## The gates as words in the transpositions of four points -/

def τ₀ : Word (SG 4) := Symmetric.s 0 (by decide)

def τ₁ : Word (SG 4) := Symmetric.s 1 (by decide)

def τ₂ : Word (SG 4) := Symmetric.s 2 (by decide)

def fX : Word (SG 4) := τ₀ * τ₂

def fCX : Word (SG 4) := τ₂

def fEx : Word (SG 4) := τ₁ * τ₂ * τ₁

def fX₁ : Word (SG 4) := fEx * fX * fEx

def f : Gn 2 → Word (SG 4)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => fX
  | .gate2 .CX_gate => fCX
  | .gate2 .Ex_gate => fEx
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => fX₁
  | .up (.up (.gate0 g)) => nomatch g

/-! ## The four states -/

def enc : Fin 4 → Bits 2
  | 0 => false ∷ false ∷ .nil
  | 1 => true ∷ false ∷ .nil
  | 2 => true ∷ true ∷ .nil
  | 3 => false ∷ true ∷ .nil

def dec : Bits 2 → Fin 4
  | false ∷ false ∷ .nil => 0
  | true ∷ false ∷ .nil => 1
  | true ∷ true ∷ .nil => 2
  | false ∷ true ∷ .nil => 3

theorem dec_enc : ∀ i, dec (enc i) = i := by decide

theorem enc_dec : ∀ x, enc (dec x) = x
  | false ∷ false ∷ .nil => rfl
  | true ∷ false ∷ .nil => rfl
  | true ∷ true ∷ .nil => rfl
  | false ∷ true ∷ .nil => rfl

/-! ## The hypotheses of the step -/

private def g (y : SG 4) : Circ 2 := Θ y.1

/-! The gates on their own wires, from the derivations. -/

private theorem gX : 2 ⊢ᵀ X ≈ FreeMonoid.lift g fX := Derivations.gate_X0.to rfl rfl

private theorem gCX : 2 ⊢ᵀ CX ≈ FreeMonoid.lift g fCX := Derivations.gate_CX0.to rfl rfl

private theorem gEx : 2 ⊢ᵀ Ex ≈ FreeMonoid.lift g fEx := Derivations.gate_Ex0.to rfl rfl

private theorem gate : ∀ x : Gn 2, 2 ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift g (f x)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => gX
  | .gate2 .CX_gate => gCX
  | .gate2 .Ex_gate => gEx
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => by
    show 2 ⊢ᵀ shift X ≈ FreeMonoid.lift g (fEx * fX * fEx)
    rw [map_mul, map_mul]
    exact X_up.trans ((gEx.mul gX).mul gEx)
  | .up (.up (.gate0 g)) => nomatch g

private theorem f_sem_gen : ∀ (x : Gn 2) (i : Fin 4),
    Symmetric.perm (f x) i = dec (semG x (enc i))
  | .gate0 g => nomatch g
  | .gate1 .X_gate => by decide +kernel
  | .gate2 .CX_gate => by decide +kernel
  | .gate2 .Ex_gate => by decide +kernel
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => by decide +kernel
  | .up (.up (.gate0 g)) => nomatch g

private theorem g_sem₀ : ∀ i : Fin 4,
    dec (sem (Θ 0) (enc i)) = Symmetric.perm (Symmetric.s 0 (by decide)) i := by
  decide +kernel

private theorem g_sem₁ : ∀ i : Fin 4,
    dec (sem (Θ 1) (enc i)) = Symmetric.perm (Symmetric.s 1 (by decide)) i := by
  decide +kernel

private theorem g_sem₂ : ∀ i : Fin 4,
    dec (sem (Θ 2) (enc i)) = Symmetric.perm (Symmetric.s 2 (by decide)) i := by
  decide +kernel

private theorem g_sem_gen : ∀ (y : SG 4) (i : Fin 4),
    dec (sem (g y) (enc i)) = Symmetric.perm (FreeMonoid.of y) i
  | ⟨0, _⟩ => g_sem₀
  | ⟨1, _⟩ => g_sem₁
  | ⟨2, _⟩ => g_sem₂
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-! ## The step -/

/-- The Agda's `Step₂`. -/
def step₂ : BySymmetric.Step 2 4 where
  Θ := Θ
  f := f
  enc := enc
  dec := dec
  dec_enc := dec_enc
  enc_dec := enc_dec
  order := Derivations.order
  braid := Derivations.braid
  far := Derivations.far
  gate := gate
  f_sem_gen := f_sem_gen
  g_sem_gen := g_sem_gen

/-- Two two-wire circuits with the same function are equal by the rules. -/
theorem complete₂ {w v : Circ 2} (e : sem w ≐ sem v) : 2 ⊢ᵀ w ≈ v :=
  step₂.complete e

theorem presentation₂ : IsPresentationOf (VRel TRel 2) step₂.semP :=
  step₂.presentation

end QCert.Alt16RevCir.Width2
