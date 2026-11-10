/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Frames over the lower three wires, inside four wires

Translation of `PFrames.agda`.  `P` is the group of the circuits on wires 0,
1, 2 of a four-wire circuit, which act on both halves (wire 3 = 0 and wire
3 = 1) alike.  Its Coxeter system is `Width3`'s: the edge Toffolis `T d` of
the Gray order 000, 001, 011, 010, 110, 111, 101, 100 of the lower wires,
here with an idle wire on top (`T₄ d = Circuit.pad 1 (Width3.T d)`), whose
Coxeter relations are `Width3`'s padded (`cox₄`).  So the frame lemma
applies inside four wires: a four-wire circuit `b` that the `T₄ i` above `j`
commute with, conjugated by a Coxeter word, depends only on where the word
sends the states below `j` (`frame_eq`), and `P`-faithfulness for the words
of the `T₄ d` is `perm_complete`.  `P`-faithfulness for any three-wire
circuits is padded completeness on three wires (`P_eq`).

**Deviation from the Agda.**  The Agda re-exports `Coxeter 8`'s and
`Circuits 8 T₄`'s names with `T₄` and `cox₄` applied.  Here they are
abbreviations and theorems in the namespace `PFrames` with `T₄` and `cox₄`
fixed: `PFrames.Pc o p = Coxeter.Circuits.Pc T₄ o p`, `PFrames.Fr b p =
Coxeter.Circuits.Fr T₄ b p`, `PFrames.CommGe j b`, and `Pc_cong`,
`perm_complete`, `Pc_inv`, `Pc_inv'`, `Fr_conj` (an equation), `stab`,
`frame_eq` (the Agda's `frame≈`) without the `cox` argument.  `SG`, `CW`,
`act`, `inv`, `frame`, `frame_act` are `Coxeter`'s (re-exported).
-/
import QCert.XCXCCX4bit.Width3

namespace QCert.XCXCCX4bit.PFrames

open QCert QCert.Circuit CircuitProp IndepProp

export Coxeter (SG CW act inv frame frame_act)

/-- The edge Toffolis of the lower three wires. -/
def T₄ (d : ℕ) : Circ 4 := Circuit.pad 1 (Width3.T d)

theorem cox₄ : Coxeter.Circuits.Coxeter 8 T₄ (VRel SRel 4) where
  order i p := by
    have := pad₃ (Width3.cox.order i p) 1
    simp only [map_mul, map_one] at this
    exact this
  braid i p := by
    have := pad₃ (Width3.cox.braid i p) 1
    simp only [map_mul] at this
    exact this
  far i j p q := by
    have := pad₃ (Width3.cox.far i j p q) 1
    simp only [map_mul] at this
    exact this

/-- A Coxeter word of `S₈` as a circuit on the lower wires. -/
abbrev Pc (o : ℕ) {n : ℕ} : Word (SG n) →* Circ 4 := Coxeter.Circuits.Pc T₄ o

/-- A four-wire circuit conjugated by a Coxeter word of `S₈`. -/
abbrev Fr (b : Circ 4) (p : CW 8) : Circ 4 := Coxeter.Circuits.Fr T₄ b p

/-- The circuits that every `T₄ i` with `i ≥ j` commutes with. -/
abbrev CommGe (j : ℕ) (b : Circ 4) : Prop := Coxeter.Circuits.CommGe 8 T₄ (VRel SRel 4) j b

theorem Pc_cong {n : ℕ} {u v : Word (SG n)} (o : ℕ) (b : o + n ≤ 8)
    (h : Derivable (Symmetric.SymRel n) u v) : 4 ⊢ Pc o u ≈ Pc o v :=
  Coxeter.Circuits.Pc_cong cox₄ o b h

theorem perm_complete (p q : CW 8) (h : ∀ x, act p x = act q x) : 4 ⊢ Pc 0 p ≈ Pc 0 q :=
  Coxeter.Circuits.perm_complete cox₄ p q h

theorem Pc_inv {n : ℕ} (o : ℕ) (b : o + n ≤ 8) (p : Word (SG n)) :
    4 ⊢ Pc o p * Pc o (inv p) ≈ 1 :=
  Coxeter.Circuits.Pc_inv cox₄ o b p

theorem Pc_inv' {n : ℕ} (o : ℕ) (b : o + n ≤ 8) (p : Word (SG n)) :
    4 ⊢ Pc o (inv p) * Pc o p ≈ 1 :=
  Coxeter.Circuits.Pc_inv' cox₄ o b p

theorem Fr_conj (b : Circ 4) (r p : CW 8) : Pc 0 r * Fr b p * Pc 0 (inv r) = Fr b (r * p) :=
  Coxeter.Circuits.Fr_conj b r p

theorem stab (j m : ℕ) (bd : j + m ≤ 8) (b : Circ 4) (cb : CommGe j b) (r : Word (SG (j + m)))
    (fix : ∀ x : Fin (j + m), x.1 < j → act r x = x) : 4 ⊢ Pc 0 r * b ≈ b * Pc 0 r :=
  Coxeter.Circuits.stab cox₄ j m bd b cb r fix

/-- The Agda's `frame≈`. -/
theorem frame_eq (j m : ℕ) (bd : j + m ≤ 8) (b : Circ 4) (cb : CommGe j b)
    (p q : Word (SG (j + m))) (h : ∀ x : Fin (j + m), x.1 < j → act p x = act q x) :
    4 ⊢ Pc 0 p * b * Pc 0 (inv p) ≈ Pc 0 q * b * Pc 0 (inv q) :=
  Coxeter.Circuits.frame_eq cox₄ j m bd b cb p q h

/-- Two three-wire circuits with the same function are equal on the lower
wires of four. -/
theorem P_eq {w v : Circ 3} (e : sem w ≐ sem v) :
    (1 + 3) ⊢ Circuit.pad 1 w ≈ Circuit.pad 1 v :=
  pad₃ (Width3.complete₃ e) 1

end QCert.XCXCCX4bit.PFrames
