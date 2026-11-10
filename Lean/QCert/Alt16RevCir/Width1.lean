/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# One wire: the rules are complete, and the circuits present S₂

Translation of `Width1.agda`: the instance of `BySymmetric` at one wire and
two states.  The transposition of the two states is `X`, and `X * X = ε` is
rule (1).

The Agda's module application `Step₁ = Step Θ f enc dec …` is the structure
value `step₁`; `presentation₁` is stated for its `semP` (a generator read as
`op` of its permutation of the two states).
-/
import QCert.Alt16RevCir.BySymmetric

namespace QCert.Alt16RevCir.Width1

open QCert QCert.Circuit CircuitProp
open Symmetric (SG)

/-! ## The translations -/

def Θ : ℕ → Circ 1
  | 0 => X
  | _ => 1

def f : Gn 1 → Word (SG 2)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => Symmetric.s 0 (by decide)
  | .up (.gate0 g) => nomatch g

/-! ## The two states -/

def enc : Fin 2 → Bits 1
  | 0 => false ∷ .nil
  | 1 => true ∷ .nil

def dec : Bits 1 → Fin 2
  | false ∷ .nil => 0
  | true ∷ .nil => 1

theorem dec_enc : ∀ i, dec (enc i) = i := by decide

theorem enc_dec : ∀ x, enc (dec x) = x
  | false ∷ .nil => rfl
  | true ∷ .nil => rfl

/-! ## The hypotheses of the step -/

private theorem order : ∀ d, 2 + d ≤ 2 → 1 ⊢ᵀ Θ d * Θ d ≈ 1
  | 0, _ => srel_rule TRel.r1
  | _ + 1, _ => by omega

private theorem gate : ∀ x : Gn 1,
    1 ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift (fun y : SG 2 => Θ y.1) (f x)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => Derivable.refl _
  | .up (.gate0 g) => nomatch g

private theorem f_sem_gen : ∀ (x : Gn 1) (i : Fin 2),
    Symmetric.perm (f x) i = dec (semG x (enc i))
  | .gate0 g => nomatch g
  | .gate1 .X_gate => by decide +kernel
  | .up (.gate0 g) => nomatch g

private theorem g_sem₀ : ∀ i : Fin 2,
    dec (sem (Θ 0) (enc i)) = Symmetric.perm (Symmetric.s 0 (by decide)) i := by
  decide +kernel

private theorem g_sem_gen : ∀ (y : SG 2) (i : Fin 2),
    dec (sem (Θ y.1) (enc i)) = Symmetric.perm (FreeMonoid.of y) i
  | ⟨0, _⟩ => g_sem₀
  | ⟨_ + 1, h⟩ => absurd h (by omega)

/-! ## The step -/

/-- The Agda's `Step₁`. -/
def step₁ : BySymmetric.Step 1 2 where
  Θ := Θ
  f := f
  enc := enc
  dec := dec
  dec_enc := dec_enc
  enc_dec := enc_dec
  order := order
  braid := fun _ _ => by omega
  far := fun _ _ _ _ => by omega
  gate := gate
  f_sem_gen := f_sem_gen
  g_sem_gen := g_sem_gen

/-- Two one-wire circuits with the same function are equal by the rules. -/
theorem complete₁ {w v : Circ 1} (e : sem w ≐ sem v) : 1 ⊢ᵀ w ≈ v :=
  step₁.complete e

theorem presentation₁ : IsPresentationOf (VRel TRel 1) step₁.semP :=
  step₁.presentation

end QCert.Alt16RevCir.Width1
