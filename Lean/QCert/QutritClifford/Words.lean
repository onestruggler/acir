/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Letter words on more wires, and completeness from words

Toward Theorem 4.4.  Facts about the letter words of the engine
(`Engine.lean`, `Local.lean`) used by the completeness proofs:

* a word moved up one wire (`Lt.up`, `cw_up`, `E.up`) and a word on `k`
  wires placed under idle wires (`cw_pad`, `E.pad`);
* derivably equal circuits, and circuits with the same operator, act alike
  on Pauli data (`actC_eq_of_peq`, `actC_eq_of_sem`);
* **completeness from words** (`complete_of_words`): if every word of
  letters acting trivially on Pauli data is derivably trivial up to a
  phase, then the rules are complete on `n` wires.
-/
import QCert.QutritClifford.Local

namespace QCert.QutritClifford

open Matrix

instance (k : ℕ) (l : List Lt) : Decidable (Fits k l) :=
  inferInstanceAs (Decidable (∀ x ∈ l, x.hi < k))

/-! ### Words one wire up -/

/-- A letter one wire up. -/
def Lt.up : Lt → Lt
  | .H j => .H (j + 1)
  | .S j => .S (j + 1)
  | .C j => .C (j + 1)

@[simp] theorem Lt.lo_up (x : Lt) : x.up.lo = x.lo + 1 := by cases x <;> rfl
@[simp] theorem Lt.hi_up (x : Lt) : x.up.hi = x.hi + 1 := by cases x <;> rfl
@[simp] theorem Lt.down_up (x : Lt) : x.up.down = x := by cases x <;> rfl

theorem Lt.up_down (x : Lt) (h : 1 ≤ x.lo) : x.down.up = x := by
  cases x with
  | H j => cases j with
    | zero => simp [Lt.lo] at h
    | succ j => rfl
  | S j => cases j with
    | zero => simp [Lt.lo] at h
    | succ j => rfl
  | C j => cases j with
    | zero => simp [Lt.lo] at h
    | succ j => rfl

theorem gen_up_up (k : ℕ) (x : Lt) : Lt.gen (k + 1) x.up = .up (Lt.gen k x) := by
  cases x <;> rfl

theorem cw_up (k : ℕ) : ∀ l : List Lt, cw (k + 1) (l.map Lt.up) = Circuit.shift (cw k l)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, cw, map_mul, cw_up k l, gen_up_up, Circuit.shift_of]

theorem E.up {k : ℕ} {l r : List Lt} (h : E k l r) : E (k + 1) (l.map Lt.up) (r.map Lt.up) := by
  unfold E at *; rw [cw_up, cw_up]; exact PEq.shift h

/-! ### Words under idle wires -/

theorem gen_pad (m : ℕ) : ∀ (k : ℕ) (x : Lt), x.hi < k →
    Lt.gen (m + k) x = Gen.pad m (Lt.gen k x)
  | k + 1, .H 0, _ => rfl
  | k + 1, .S 0, _ => rfl
  | k + 2, .C 0, _ => rfl
  | k + 1, .H (j + 1), h => by
    show Gen.up (Lt.gen (m + k) (.H j)) = Gen.up (Gen.pad m (Lt.gen k (.H j)))
    rw [gen_pad m k (.H j) (by simp [Lt.hi] at h ⊢; omega)]
  | k + 1, .S (j + 1), h => by
    show Gen.up (Lt.gen (m + k) (.S j)) = Gen.up (Gen.pad m (Lt.gen k (.S j)))
    rw [gen_pad m k (.S j) (by simp [Lt.hi] at h ⊢; omega)]
  | k + 1, .C (j + 1), h => by
    show Gen.up (Lt.gen (m + k) (.C j)) = Gen.up (Gen.pad m (Lt.gen k (.C j)))
    rw [gen_pad m k (.C j) (by simp [Lt.hi] at h ⊢; omega)]
  | 0, x, h => by cases x <;> simp [Lt.hi] at h
  | 1, .C 0, h => by simp [Lt.hi] at h

theorem cw_pad (m : ℕ) {k : ℕ} : ∀ l : List Lt, Fits k l → cw (m + k) l = Circuit.pad m (cw k l)
  | [], _ => rfl
  | x :: l, h => by
    simp only [cw, map_mul, cw_pad m l (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      gen_pad m k x (h x List.mem_cons_self), Circuit.pad, FreeMonoid.map_of]

theorem E.pad (m : ℕ) {k : ℕ} {l r : List Lt} (h : E k l r) (hl : Fits k l) (hr : Fits k r) :
    E (m + k) l r := by
  unfold E at *; rw [cw_pad m l hl, cw_pad m r hr]; exact PEq.pad m h

theorem fits_mono {k k' : ℕ} {l : List Lt} (h : Fits k l) (hk : k ≤ k') : Fits k' l :=
  fun x hx => lt_of_lt_of_le (h x hx) hk

theorem fits_append {k : ℕ} {a b : List Lt} (ha : Fits k a) (hb : Fits k b) : Fits k (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h; exacts [ha x h, hb x h]

theorem fits_up {k : ℕ} {l : List Lt} (h : Fits k l) : Fits (k + 1) (l.map Lt.up) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  simpa using h y hy

/-! ### Derivations preserve the action on Pauli data -/

theorem actC_negω_pow' {n : ℕ} (t : ℕ) : actC n (negω ^ t) = 1 := by
  funext P; exact actC_negω_pow n t P

/-- Circuits with the same operator act alike on Pauli data. -/
theorem actC_eq_of_sem {n : ℕ} {w v : Circ n} (h : sem n w = sem n v) : actC n w = actC n v := by
  funext P
  apply PD.op_inj
  rw [← sem_conj, ← sem_conj, h]

/-- Circuits equal up to a phase act alike on Pauli data. -/
theorem actC_eq_of_peq {n : ℕ} {w v : Circ n} (h : PEq n w v) : actC n w = actC n v := by
  obtain ⟨t, ht⟩ := h
  rw [actC_eq_of_sem (sound ht), map_mul, actC_negω_pow', mul_one]

theorem actC_eq_of_E {n : ℕ} {l r : List Lt} (h : E n l r) : actC n (cw n l) = actC n (cw n r) :=
  actC_eq_of_peq h

/-! ### Completeness from words -/

/-- Every word of letters on `n` wires acting trivially on Pauli data is
derivably trivial up to a phase. -/
def WordsTrivial (n : ℕ) : Prop :=
  ∀ l : List Lt, Fits n l → actC n (cw n l) = 1 → E n l []

/-- **Completeness from words.** -/
theorem complete_of_words {n : ℕ} (h : WordsTrivial n) : Complete n := by
  intro w v hs
  obtain ⟨lw, hlw, hw⟩ := exists_word w
  obtain ⟨lv, hlv, hv⟩ := exists_word v
  have hcan : actC n (cw n (lv ++ invW lv)) = 1 := by
    rw [actC_eq_of_E (E_cancel lv hlv)]; exact map_one _
  have hact : actC n (cw n (lw ++ invW lv)) = 1 := by
    rw [cw_append, map_mul, ← actC_eq_of_peq hw, actC_eq_of_sem hs, actC_eq_of_peq hv,
      ← map_mul, ← cw_append, hcan]
  have h1 := h _ (fits_append hlw (fits_invW lv hlv)) hact
  have h2 : E n (lw ++ invW lv ++ lv) ([] ++ lv) := h1.append (E.refl lv)
  have h3 : E n (lw ++ invW lv ++ lv) (lw ++ []) := by
    rw [List.append_assoc]; exact (E.refl lw).append (E_cancel' lv hlv)
  have h4 : E n lw lv := by simpa using h3.symm.trans h2
  exact der_of_peq ((hw.trans h4).trans hv.symm) hs

end QCert.QutritClifford
