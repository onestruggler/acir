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

**Deviation from the Agda.**  The check `Xm_sem_ok` evaluates the circuits
as the Agda's does, but on lists of bits after reading each circuit as a
list of gate codes (`code`, `semK`, with `semK_ok` relating it to `sem`):
with `sem` itself the kernel took 50 s, with `semK` about 13 s.  `pos_enc8`
is one `decide`, where the Agda lists its eight cases.
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

/-! ### Evaluating circuits on lists of bits

The check below evaluates the 105 circuits `Xm l` on the sixteen states, as
the Agda's does.  The kernel evaluates `sem` slowly (its pattern matching on
the indexed families `Gen` and `Bits` costs most of a minute here), so the
circuit is first read as a list of gate codes and then run on lists of bits
(`semK`), which `semK_ok` relates to `sem` — as the Agda's `CFrame` runs a
fast action beside `act`. -/

/-- A generator as its gate (1 `X`, 2 `CX`, 3 `CCX`, 4 the swap) and the
wire it starts on. -/
def code : {n : ℕ} → Gn n → ℕ × ℕ
  | _, .gate0 _ => (0, 0)
  | _, .gate1 _ => (1, 0)
  | _, .gate2 (.gate _) => (2, 0)
  | _, .gate2 .swap => (4, 0)
  | _, .gate3 _ => (3, 0)
  | _, .up g => ((code g).1, (code g).2 + 1)

/-- A gate on the bottom wires of a list of bits. -/
def opL : ℕ → List Bool → List Bool
  | 1, a :: xs => (!a) :: xs
  | 2, a :: b :: xs => (a ^^ b) :: b :: xs
  | 3, a :: b :: c :: xs => (a ^^ (b && c)) :: b :: c :: xs
  | 4, a :: b :: xs => b :: a :: xs
  | _, xs => xs

/-- A gate starting on wire `o`. -/
def atL (k : ℕ) : ℕ → List Bool → List Bool
  | 0, xs => opL k xs
  | _ + 1, [] => []
  | o + 1, a :: xs => a :: atL k o xs

/-- A list of gate codes run on a list of bits, in diagram order. -/
def semK : List (ℕ × ℕ) → List Bool → List Bool
  | [], xs => xs
  | c :: cs, xs => semK cs (atL c.1 c.2 xs)

/-- A state as a list of bits. -/
def bitsL : {n : ℕ} → Bits n → List Bool
  | _, .nil => []
  | _, a ∷ x => a :: bitsL x

theorem bitsL_inj : ∀ {n : ℕ} {x y : Bits n}, bitsL x = bitsL y → x = y
  | _, .nil, .nil, _ => rfl
  | _, a ∷ x, b ∷ y, h => by
    simp only [bitsL, List.cons.injEq] at h
    rw [h.1, bitsL_inj h.2]

theorem code_ok : ∀ {n : ℕ} (g : Gn n) (x : Bits n),
    bitsL (semG g x) = atL (code g).1 (code g).2 (bitsL x)
  | _, .gate0 (.gate g), _ => nomatch g
  | _, .gate1 (.gate .X_gate), _ ∷ _ => rfl
  | _, .gate2 (.gate .CX_gate), _ ∷ _ ∷ _ => rfl
  | _, .gate2 .swap, _ ∷ _ ∷ _ => rfl
  | _, .gate3 (.gate .CCX_gate), _ ∷ _ ∷ _ ∷ _ => rfl
  | _, .up g, a ∷ x => by
    show a :: bitsL (semG g x) = a :: atL (code g).1 (code g).2 (bitsL x)
    rw [code_ok g x]

theorem semK_ok {n : ℕ} (w : Circ n) (x : Bits n) :
    bitsL (sem w x) = semK ((FreeMonoid.toList w).map code) (bitsL x) := by
  show bitsL (semL (FreeMonoid.toList w) x) = _
  generalize FreeMonoid.toList w = l
  induction l generalizing x with
  | nil => rfl
  | cons g l ih => rw [List.map_cons, semK, ← code_ok, ← ih]; rfl

/-- Equality of lists of bits. -/
def eqBL : List Bool → List Bool → Bool
  | [], [] => true
  | a :: x, b :: y => eqB a b && eqBL x y
  | _, _ => false

theorem eqBL_sound : ∀ x y : List Bool, eqBL x y = true → x = y
  | [], [], _ => rfl
  | a :: x, b :: y, h => by
    simp only [eqBL, Bool.and_eq_true] at h
    rw [eqB_sound a b h.1, eqBL_sound x y h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- The circuit and the function agree on every state. -/
def xmCheck (l : L) : Bool :=
  allB 4 fun x => eqBL (semK ((FreeMonoid.toList (Xm l)).map code) (bitsL x)) (bitsL (mF l x))

private theorem Xm_sem_ok : allFin 105 xmCheck = true := by
  decide +kernel

theorem Xm_sem (l : L) : sem (Xm l) ≐ mF l := fun x =>
  bitsL_inj ((semK_ok _ x).trans
    (eqBL_sound _ _ (allB_sound 4 _ (allFin_sound 105 xmCheck Xm_sem_ok l) x)))

/-- A word of labels, its matchings in diagram order (the Agda's `mF*`). -/
def mFs : List L → Fun 4
  | [] => id
  | l :: ls => mF l ⨾ mFs ls

/-- The Agda's `mF*-++`. -/
theorem mFs_append : ∀ (ls ks : List L), mFs (ls ++ ks) ≐ (mFs ls ⨾ mFs ks)
  | [], _, _ => rfl
  | l :: ls, ks, x => mFs_append ls ks (mF l x)

end QCert.XCXCCX4bit.CSem
