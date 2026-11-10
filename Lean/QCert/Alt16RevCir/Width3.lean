/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three wires: the rules are complete, and the circuits present S₈

Translation of `Width3.agda`: the instance of `BySymmetric` at three wires
and eight states, numbered along the Gray code 000, 001, 011, 010, 110, 111,
101, 100 (wire 2 first).  The transposition of two consecutive states is an
edge Toffoli `Θ d`: NOT on the wire that changes, controlled by the other
two, between NOT gates on the controls that are 0 and the swaps that bring
the wires into place (`Width3.Derivations` has the seven).  The gates on
their own wires are words in them (NOT on wire 0 exchanges the states 0 1,
2 3, 4 5 and 6 7, `CX` the states 2 3 and 4 5, `CCX` the states 4 5, the
swap of the wires 0 1 the states 1 3 and 4 6, and that of the wires 1 2 the
states 2 6 and 3 7), and NOT and `CX` further up are those between swaps.
The Coxeter relations between the `Θ d` and the five gates' words are
derived from the rules (1)–(6) in `Width3.Derivations`.

The Agda's module application `Step₃` is the structure value `step₃`; its
`fin8`, for proofs by evaluation at the eight states, is `decide`.
-/
import QCert.Alt16RevCir.BySymmetric
import QCert.Alt16RevCir.Width3.Derivations

namespace QCert.Alt16RevCir.Width3

open QCert QCert.Circuit CircuitProp Engine
open Symmetric (SG)
open Derivations (Θ)

/-! ## The gates as words in the transpositions of eight points -/

def τ₀ : Word (SG 8) := Symmetric.s 0 (by decide)

def τ₁ : Word (SG 8) := Symmetric.s 1 (by decide)

def τ₂ : Word (SG 8) := Symmetric.s 2 (by decide)

def τ₃ : Word (SG 8) := Symmetric.s 3 (by decide)

def τ₄ : Word (SG 8) := Symmetric.s 4 (by decide)

def τ₅ : Word (SG 8) := Symmetric.s 5 (by decide)

def τ₆ : Word (SG 8) := Symmetric.s 6 (by decide)

/-! The gates on their own wires. -/

def fX : Word (SG 8) := τ₀ * τ₂ * τ₄ * τ₆

def fCX : Word (SG 8) := τ₂ * τ₄

def fCCX : Word (SG 8) := τ₄

def fEx₀ : Word (SG 8) := τ₁ * τ₂ * τ₁ * τ₄ * τ₅ * τ₄

def fEx₁ : Word (SG 8) :=
  τ₂ * τ₃ * τ₄ * τ₅ * τ₄ * τ₃ * τ₂ * τ₃ * τ₄ * τ₅ * τ₆ * τ₅ * τ₄ * τ₃

/-! NOT and `CX` further up, between the swaps. -/

def fX₁ : Word (SG 8) := fEx₀ * fX * fEx₀

def fX₂ : Word (SG 8) := fEx₁ * fX₁ * fEx₁

def fCX₁ : Word (SG 8) := (fEx₀ * fEx₁) * fCX * (fEx₁ * fEx₀)

def f : Gn 3 → Word (SG 8)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => fX
  | .gate2 .CX_gate => fCX
  | .gate2 .Ex_gate => fEx₀
  | .gate3 .CCX_gate => fCCX
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => fX₁
  | .up (.gate2 .CX_gate) => fCX₁
  | .up (.gate2 .Ex_gate) => fEx₁
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => fX₂
  | .up (.up (.up (.gate0 g))) => nomatch g

/-! ## The eight states -/

def enc : Fin 8 → Bits 3
  | 0 => false ∷ false ∷ false ∷ .nil
  | 1 => true ∷ false ∷ false ∷ .nil
  | 2 => true ∷ true ∷ false ∷ .nil
  | 3 => false ∷ true ∷ false ∷ .nil
  | 4 => false ∷ true ∷ true ∷ .nil
  | 5 => true ∷ true ∷ true ∷ .nil
  | 6 => true ∷ false ∷ true ∷ .nil
  | 7 => false ∷ false ∷ true ∷ .nil

def dec : Bits 3 → Fin 8
  | false ∷ false ∷ false ∷ .nil => 0
  | true ∷ false ∷ false ∷ .nil => 1
  | true ∷ true ∷ false ∷ .nil => 2
  | false ∷ true ∷ false ∷ .nil => 3
  | false ∷ true ∷ true ∷ .nil => 4
  | true ∷ true ∷ true ∷ .nil => 5
  | true ∷ false ∷ true ∷ .nil => 6
  | false ∷ false ∷ true ∷ .nil => 7

theorem dec_enc : ∀ i, dec (enc i) = i := by decide

theorem enc_dec : ∀ x, enc (dec x) = x
  | false ∷ false ∷ false ∷ .nil => rfl
  | true ∷ false ∷ false ∷ .nil => rfl
  | true ∷ true ∷ false ∷ .nil => rfl
  | false ∷ true ∷ false ∷ .nil => rfl
  | false ∷ true ∷ true ∷ .nil => rfl
  | true ∷ true ∷ true ∷ .nil => rfl
  | true ∷ false ∷ true ∷ .nil => rfl
  | false ∷ false ∷ true ∷ .nil => rfl

/-! ## The hypotheses of the step -/

private def g (y : SG 8) : Circ 3 := Θ y.1

/-! The gates on their own wires, from the derivations. -/

private theorem gX : 3 ⊢ᵀ X ≈ FreeMonoid.lift g fX := Derivations.gate_X0.to rfl rfl

private theorem gCX : 3 ⊢ᵀ CX ≈ FreeMonoid.lift g fCX := Derivations.gate_CX0.to rfl rfl

private theorem gCCX : 3 ⊢ᵀ CCX ≈ FreeMonoid.lift g fCCX := Derivations.gate_CCX0.to rfl rfl

private theorem gEx₀ : 3 ⊢ᵀ Ex ≈ FreeMonoid.lift g fEx₀ := Derivations.gate_Ex0.to rfl rfl

private theorem gEx₁ : 3 ⊢ᵀ shift Ex ≈ FreeMonoid.lift g fEx₁ :=
  Derivations.gate_Ex1.to rfl rfl

/-! NOT and `CX` further up, by the naturality of the swap. -/

private theorem gX₁ : 3 ⊢ᵀ shift X ≈ FreeMonoid.lift g fX₁ := by
  rw [fX₁, map_mul, map_mul]
  exact X_up.trans ((gEx₀.mul gX).mul gEx₀)

private theorem gX₂ : 3 ⊢ᵀ shift (shift X) ≈ FreeMonoid.lift g fX₂ := by
  rw [fX₂, map_mul, map_mul]
  exact (lemma_cong_up (X_up (n := 0))).trans ((gEx₁.mul gX₁).mul gEx₁)

private theorem gCX₁ : 3 ⊢ᵀ shift CX ≈ FreeMonoid.lift g fCX₁ := by
  rw [fCX₁, map_mul, map_mul, map_mul, map_mul]
  exact CX_up.trans (((gEx₀.mul gEx₁).mul gCX).mul (gEx₁.mul gEx₀))

private theorem gate : ∀ x : Gn 3, 3 ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift g (f x)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => gX
  | .gate2 .CX_gate => gCX
  | .gate2 .Ex_gate => gEx₀
  | .gate3 .CCX_gate => gCCX
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => gX₁
  | .up (.gate2 .CX_gate) => gCX₁
  | .up (.gate2 .Ex_gate) => gEx₁
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => gX₂
  | .up (.up (.up (.gate0 g))) => nomatch g

private theorem f_sem_gen : ∀ (x : Gn 3) (i : Fin 8),
    Symmetric.perm (f x) i = dec (semG x (enc i))
  | .gate0 g => nomatch g
  | .gate1 .X_gate => by decide +kernel
  | .gate2 .CX_gate => by decide +kernel
  | .gate2 .Ex_gate => by decide +kernel
  | .gate3 .CCX_gate => by decide +kernel
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => by decide +kernel
  | .up (.gate2 .CX_gate) => by decide +kernel
  | .up (.gate2 .Ex_gate) => by decide +kernel
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => by decide +kernel
  | .up (.up (.up (.gate0 g))) => nomatch g

private theorem g_sem₀ : ∀ i : Fin 8,
    dec (sem (Θ 0) (enc i)) = Symmetric.perm (Symmetric.s 0 (by decide)) i := by
  decide +kernel

private theorem g_sem₁ : ∀ i : Fin 8,
    dec (sem (Θ 1) (enc i)) = Symmetric.perm (Symmetric.s 1 (by decide)) i := by
  decide +kernel

private theorem g_sem₂ : ∀ i : Fin 8,
    dec (sem (Θ 2) (enc i)) = Symmetric.perm (Symmetric.s 2 (by decide)) i := by
  decide +kernel

private theorem g_sem₃ : ∀ i : Fin 8,
    dec (sem (Θ 3) (enc i)) = Symmetric.perm (Symmetric.s 3 (by decide)) i := by
  decide +kernel

private theorem g_sem₄ : ∀ i : Fin 8,
    dec (sem (Θ 4) (enc i)) = Symmetric.perm (Symmetric.s 4 (by decide)) i := by
  decide +kernel

private theorem g_sem₅ : ∀ i : Fin 8,
    dec (sem (Θ 5) (enc i)) = Symmetric.perm (Symmetric.s 5 (by decide)) i := by
  decide +kernel

private theorem g_sem₆ : ∀ i : Fin 8,
    dec (sem (Θ 6) (enc i)) = Symmetric.perm (Symmetric.s 6 (by decide)) i := by
  decide +kernel

private theorem g_sem_gen : ∀ (y : SG 8) (i : Fin 8),
    dec (sem (g y) (enc i)) = Symmetric.perm (FreeMonoid.of y) i
  | ⟨0, _⟩ => g_sem₀
  | ⟨1, _⟩ => g_sem₁
  | ⟨2, _⟩ => g_sem₂
  | ⟨3, _⟩ => g_sem₃
  | ⟨4, _⟩ => g_sem₄
  | ⟨5, _⟩ => g_sem₅
  | ⟨6, _⟩ => g_sem₆
  | ⟨_ + 7, h⟩ => absurd h (by omega)

/-! ## The step -/

/-- The Agda's `Step₃`. -/
def step₃ : BySymmetric.Step 3 8 where
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

/-- Two three-wire circuits with the same function are equal by the
rules. -/
theorem complete₃ {w v : Circ 3} (e : sem w ≐ sem v) : 3 ⊢ᵀ w ≈ v :=
  step₃.complete e

theorem presentation₃ : IsPresentationOf (VRel TRel 3) step₃.semP :=
  step₃.presentation

end QCert.Alt16RevCir.Width3
