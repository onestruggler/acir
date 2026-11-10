/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The functions of the controlled matchings

Translation of `CSem.agda`.  A state of four wires with wire 3 set is a
state of the upper half, numbered by the Gray position of its lower wires
(`enc8`, the positions of `CFrame` and `CLabels`).  The controlled matching
`Xm l` fixes the lower half and acts on the upper half as the matching of its
label (`mF l`); this is decided for the 105 labels at once (`Xm_sem`).  Words
of labels then act as the products of their matchings (`mFs`, in
`LabelEngine`'s `Xs`).

Names.  The Agda's `mF*`, `mF*-++` are `mFs`, `mFs_append`.

**Deviation from the Agda.**  `pos_enc8` is one `decide`, where the Agda
lists its eight cases.
-/
import QCert.XCXCCX4bit.CRel

namespace QCert.XCXCCX4bit.CSem

open QCert QCert.Circuit CircuitProp IndepProp
open CRel (L Xm tbl)

/-! ## Finite checks -/

/-- Every element of `Fin n` satisfies `p`. -/
def allFin : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p 0 && allFin n (fun i => p i.succ)

theorem allFin_sound : ∀ (n : ℕ) (p : Fin n → Bool), allFin n p = true → ∀ i, p i = true
  | 0, _, _, i => i.elim0
  | n + 1, p, h, i => by
    simp only [allFin, Bool.and_eq_true] at h
    induction i using Fin.cases with
    | zero => exact h.1
    | succ i => exact allFin_sound n (fun j => p j.succ) h.2 i

/-! ## The upper half -/

/-- The state of the upper half at a Gray position. -/
def enc8 : Fin 8 → Bits 4
  | 0 => false ∷ false ∷ false ∷ true ∷ .nil
  | 1 => true ∷ false ∷ false ∷ true ∷ .nil
  | 2 => true ∷ true ∷ false ∷ true ∷ .nil
  | 3 => false ∷ true ∷ false ∷ true ∷ .nil
  | 4 => false ∷ true ∷ true ∷ true ∷ .nil
  | 5 => true ∷ true ∷ true ∷ true ∷ .nil
  | 6 => true ∷ false ∷ true ∷ true ∷ .nil
  | 7 => false ∷ false ∷ true ∷ true ∷ .nil
  | ⟨k + 8, h⟩ => absurd h (by omega)

/-- The Gray position of the lower wires of a state. -/
def pos : Bits 4 → Fin 8
  | false ∷ false ∷ false ∷ _ ∷ .nil => 0
  | true ∷ false ∷ false ∷ _ ∷ .nil => 1
  | true ∷ true ∷ false ∷ _ ∷ .nil => 2
  | false ∷ true ∷ false ∷ _ ∷ .nil => 3
  | false ∷ true ∷ true ∷ _ ∷ .nil => 4
  | true ∷ true ∷ true ∷ _ ∷ .nil => 5
  | true ∷ false ∷ true ∷ _ ∷ .nil => 6
  | false ∷ false ∷ true ∷ _ ∷ .nil => 7

theorem pos_enc8 : ∀ i : Fin 8, pos (enc8 i) = i := by decide

theorem enc8_injective {i j : Fin 8} (e : enc8 i = enc8 j) : i = j := by
  rw [← pos_enc8 i, e, pos_enc8]

/-! ## The function of a label -/

/-- The matching of the label on the upper half, the identity on the lower
half. -/
def mF (l : L) : Fun 4
  | a ∷ b ∷ c ∷ false ∷ .nil => a ∷ b ∷ c ∷ false ∷ .nil
  | a ∷ b ∷ c ∷ true ∷ .nil => enc8 (tbl l (pos (a ∷ b ∷ c ∷ true ∷ .nil)))

private theorem Xm_sem_ok : allFin 105 (fun l => eqF 4 (sem (Xm l)) (mF l)) = true := by
  decide +kernel

theorem Xm_sem (l : L) : sem (Xm l) ≐ mF l :=
  eqF_sound 4 _ _ (allFin_sound 105 (fun l => eqF 4 (sem (Xm l)) (mF l)) Xm_sem_ok l)

/-- A word of labels, its matchings in diagram order (the Agda's `mF*`). -/
def mFs : List L → Fun 4
  | [] => id
  | l :: ls => mF l ⨾ mFs ls

/-- The Agda's `mF*-++`. -/
theorem mFs_append : ∀ (ls ks : List L), mFs (ls ++ ks) ≐ (mFs ls ⨾ mFs ks)
  | [], _, _ => rfl
  | l :: ls, ks, x => mFs_append ls ks (mF l x)

end QCert.XCXCCX4bit.CSem
