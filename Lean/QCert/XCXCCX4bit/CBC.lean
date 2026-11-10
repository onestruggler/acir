/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The five base commutations, and the relation calculus of the controlled matchings

Translation of `CBC.agda`.  `CRel`'s calculus needs `Ḡ` to commute with the
frame of `G` by each base word of `CLabels`: `Fr G (baseW k)` is `Q G Q⁻¹`
for the three-wire circuit `Q = baseQ k` (a three-wire identity for each
side), and the commutation is a three-wire identity for the first two base
types (on wires 0, 3 and on wires 0, 1, 3) and `BaseComm`'s derivations for
the other three.

Names.  The Agda's `Ḡl`, `Frl`, `pcQ`, `pcQ⁻`, `fr-list`, `Ḡ-list`,
`comm-list` are `Gbarl`, `Frl`, `pcQ`, `pcQinv`, `fr_list`, `Gbar_list`,
`commL` (`CBase.comm_list` is another lemma); `base` is `base`.

**Deviation from the Agda.**  The Agda opens `CRel.Calculus base` publicly;
here its theorems `X_inv`, `BC₀`, `BC`, `X_conj`, `X_klein` are restated
in this namespace, applied to `base` where they take it.  The checks of
`pcQ` and `pcQinv` are decided for the five base words at once.
-/
import QCert.XCXCCX4bit.BaseComm
import QCert.XCXCCX4bit.CRel

namespace QCert.XCXCCX4bit.CBC

open QCert QCert.Circuit CircuitProp IndepProp
open Placed ToPlaced PFrames CLabels
open CBase (Comm G Gbar)

/-- An identity of placed words on three wires. -/
private theorem nar (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (hs : eqF 4 (semPs u) (semPs v) = true) :
    4 ⊢ ιs u ≈ ιs v :=
  Narrow3.narrowP m u v hu hv (eqF_sound 4 _ _ hs)

/-- `Ḡ` as placed letters. -/
private def Gbarl : List PG := [PG.Xₚ 3, PG.CXₚ 3 0, PG.Xₚ 3]

/-- The frame of `G` by a base word, as placed letters. -/
private def Frl (k : Fin 5) : List PG := baseQ k ++ PG.CXₚ 3 0 :: (baseQ k).reverse

/-- The checks of `pcQ`: the circuit of a base word is its base circuit, on
the three lower wires. -/
private theorem pcQ_check : ∀ k : Fin 5,
    (every (avoids 3) (pg (Pc 0 (baseW k))) && every (avoids 3) (baseQ k) &&
      eqF 4 (semPs (pg (Pc 0 (baseW k)))) (semPs (baseQ k))) = true := by
  decide +kernel

/-- The checks of `pcQinv`: the circuit of the inverse word is the base
circuit reversed. -/
private theorem pcQinv_check : ∀ k : Fin 5,
    (every (avoids 3) (pg (Pc 0 (inv (baseW k)))) && every (avoids 3) (baseQ k).reverse &&
      eqF 4 (semPs (pg (Pc 0 (inv (baseW k))))) (semPs (baseQ k).reverse)) = true := by
  decide +kernel

/-- The circuit of a base word is its base circuit. -/
private theorem pcQ (k : Fin 5) : 4 ⊢ Pc 0 (baseW k) ≈ ιs (baseQ k) := by
  have h := pcQ_check k
  simp only [Bool.and_eq_true] at h
  exact (pg_ok _).trans (nar 3 _ _ h.1.1 h.1.2 h.2)

/-- The circuit of the inverse word is the base circuit reversed. -/
private theorem pcQinv (k : Fin 5) : 4 ⊢ Pc 0 (inv (baseW k)) ≈ ιs (baseQ k).reverse := by
  have h := pcQinv_check k
  simp only [Bool.and_eq_true] at h
  exact (pg_ok _).trans (nar 3 _ _ h.1.1 h.1.2 h.2)

private theorem fr_list (k : Fin 5) : 4 ⊢ Fr G (baseW k) ≈ ιs (Frl k) := by
  rw [Frl, ιs_append]
  have e : ιs (PG.CXₚ 3 0 :: (baseQ k).reverse) = G * ιs (baseQ k).reverse := rfl
  rw [e, ← mul_assoc]
  exact ((pcQ k).mul (Derivable.refl G)).mul (pcQinv k)

private theorem Gbar_list : 4 ⊢ Gbar ≈ ιs Gbarl := by
  have e : ιs Gbarl = Gbar := by
    simp only [Gbarl, ιs, mul_one, Gbar, CBase.G, mul_assoc]
  rw [e]

/-- The commutation, as an identity of placed words. -/
private theorem commL : ∀ k : Fin 5, 4 ⊢ ιs (Gbarl ++ Frl k) ≈ ιs (Frl k ++ Gbarl)
  | 0 => nar 1 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | 1 => nar 2 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | 2 => BaseComm.BC211E.prf
  | 3 => BaseComm.BC31E.prf
  | 4 => BaseComm.BC4E.prf
  | ⟨k + 5, h⟩ => absurd h (by omega)

/-- `Ḡ` commutes with the frame of `G` by each base word. -/
theorem base (k : Fin 5) : Comm Gbar (Fr G (baseW k)) := by
  have h := commL k
  rw [ιs_append, ιs_append] at h
  exact ((Gbar_list.mul (fr_list k)).trans h).trans ((fr_list k).mul Gbar_list).symm

/-! ## The calculus of the controlled matchings, given the base commutations -/

open CRel

theorem X_inv (x : L) : 4 ⊢ Xm x * Xm x ≈ 1 := Calculus.X_inv x

theorem BC₀ (F : CW 8) (h : BC₀_ok F = true) : Comm Gbar (Fr G F) := Calculus.BC₀ base F h

theorem BC (x y : L) (h : BC_ok x y = true) : Comm (Qbar (frm x)) (Xm y) :=
  Calculus.BC base x y h

theorem X_conj (x y : L) (h : conj_ok x y = true) : 4 ⊢ Xm x * Xm y * Xm x ≈ Xm (c3 x y) :=
  Calculus.X_conj base x y h

theorem X_klein (x y : L) (h : klein_ok x y = true) : 4 ⊢ Xm x * Xm y ≈ Xm (mul x y) :=
  Calculus.X_klein x y h

end QCert.XCXCCX4bit.CBC
