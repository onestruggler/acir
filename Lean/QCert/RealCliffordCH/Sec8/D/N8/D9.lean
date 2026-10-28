/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemmas D.9 and D.11: circuits on the wires below a box

(308): a circuit on the bottom `m` wires commutes with the box whose box
wire is `m - 1` and whose controls are the wires above; (314): the same for
the multi-controlled `H` with box wire `m - 1` and `H` on wire `m`.  The
paper proves both by induction on the circuit; here, for a family `G N m` of
gates that moves up one wire when shifted (`Gsh`), the commutation with one
generator is proved by induction on the width (`G_letter`):

* a generator below the box wire commutes structurally (the gate is a shift
  by `m - 1`, `G_high`);
* a generator touching the box wire but not wire `0` is the shift of one
  touching the box wire of `G (N - 1) (m - 1)`: the statement one width down
  (on two wires, completeness there);
* a generator touching wire `0` and the box wire is one of the cases at the
  canonical position, module parameters (`base1`: `H` and `Z` on the box wire
  `0`; `base2`: `CZ` and `CH` of the wires `0, 1`, box wire `1`).

Then `G_circ` multiplies them.
-/
import QCert.RealCliffordCH.Sec8.D.N8.I310

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

/-- The box of (308): box wire `m - 1`, controls `m, …, N - 1`. -/
abbrev BoxM (N m : ℕ) : Circ N := mc N .box [m - 1] (blackOn m N)
/-- The multi-controlled `H` of (314): box wire `m - 1`, `H` on wire `m`,
controls `m + 1, …, N - 1`. -/
abbrev HgM (N m : ℕ) : Circ N := mc N .hg [m - 1, m] (blackOn (m + 1) N)

theorem ctrlWires_top (N m : ℕ) (tg : List ℕ) (htg : ∀ t ∈ tg, t < m) :
    ctrlWires N tg (blackOn m N) = List.range' m (N - m) := by
  refine eq_of_lt_mem ((List.pairwise_lt_range).filter _) List.pairwise_lt_range' (fun j => ?_)
  simp only [ctrlWires, blackOn, List.mem_filter, List.mem_range, List.mem_range'_1,
    Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2, _⟩
    by_cases h : m ≤ j ∧ j < N
    · omega
    · simp [h] at h2
  · intro h
    refine ⟨by omega, by simp; omega, ?_⟩
    simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
    intro t ht e; have := htg t ht; omega

theorem whiteWires_top (N m : ℕ) (tg : List ℕ) : whiteWires N tg (blackOn m N) = [] := by
  simp only [whiteWires, List.filter_eq_nil_iff, blackOn]
  intro i _
  split_ifs <;> simp

theorem range'_cons1 (m k : ℕ) (hm : 1 ≤ m) :
    [m - 1] ++ List.range' m k = List.range' (m - 1) (k + 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp [List.range'_succ]

theorem range'_cons2 (m k : ℕ) (hm : 1 ≤ m) :
    [m - 1, m] ++ List.range' (m + 1) k = List.range' (m - 1) (k + 2) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp [List.range'_succ]

theorem boxM_place (N m k : ℕ) (h1 : 1 ≤ m) (hk : N = m + k) :
    BoxM N m = placeG N (box k) (List.range' (m - 1) (k + 1)) := by
  show mc N .box [m - 1] (blackOn m N) = _
  unfold mc
  rw [ctrlWires_top N m [m - 1] (by intro t ht; simp at ht; omega), whiteWires_top,
    show N - m = k by omega]
  simp only [colourW, List.map_nil, List.nil_append, List.append_nil, drawn_one, List.length_range']
  show placeG N (box k) ([m - 1] ++ List.range' m k) = _
  rw [range'_cons1 m k h1]

theorem hgM_place (N m k : ℕ) (h1 : 1 ≤ m) (hk : N = m + 1 + k) :
    HgM N m = placeG N (mch k) (List.range' (m - 1) (k + 2)) := by
  show mc N .hg [m - 1, m] (blackOn (m + 1) N) = _
  unfold mc
  rw [ctrlWires_top N (m + 1) [m - 1, m] (by intro t ht; simp at ht; omega), whiteWires_top,
    show N - (m + 1) = k by omega]
  simp only [colourW, List.map_nil, List.nil_append, List.append_nil, drawn_one, List.length_range']
  show placeG N (mch k) ([m - 1, m] ++ List.range' (m + 1) k) = _
  rw [range'_cons2 m k h1]

theorem range'_map_succ (a n : ℕ) : (List.range' a n).map (· + 1) = List.range' (a + 1) n := by
  have hf : (fun x : ℕ => x + 1) = (fun x => 1 + x) := funext fun x => Nat.add_comm x 1
  rw [hf, List.map_add_range']; congr 1; omega

theorem boxM_shift (N m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ N) :
    Derivable (theory (N + 1)) (BoxM (N + 1) (m + 1)) (shift (BoxM N m)) := by
  rw [boxM_place N m (N - m) h1 (by omega), boxM_place (N + 1) (m + 1) (N - m) (by omega) (by omega)]
  have h := shift_placeG (M := N) (box (N - m)) (ps := List.range' (m - 1) (N - m + 1))
    List.nodup_range' (fun p hp => by rw [List.mem_range'_1] at hp; omega) (by simp)
  rw [range'_map_succ, show m - 1 + 1 = m + 1 - 1 by omega] at h
  exact h.symm

theorem hgM_shift (N m : ℕ) (h1 : 1 ≤ m) (h2 : m + 1 ≤ N) :
    Derivable (theory (N + 1)) (HgM (N + 1) (m + 1)) (shift (HgM N m)) := by
  rw [hgM_place N m (N - m - 1) h1 (by omega),
    hgM_place (N + 1) (m + 1) (N - m - 1) (by omega) (by omega)]
  have h := shift_placeG (M := N) (mch (N - m - 1)) (ps := List.range' (m - 1) (N - m - 1 + 2))
    List.nodup_range' (fun p hp => by rw [List.mem_range'_1] at hp; omega) (by simp)
  rw [range'_map_succ, show m - 1 + 1 = m + 1 - 1 by omega] at h
  exact h.symm

theorem atBot_letter (x : L) {m : ℕ} (hx : x.lo + x.wd ≤ m) :
    ∀ N, m ≤ N → atBot N (x.circ m) = x.circ N
  | 0, h => by
    have : m = 0 := by omega
    subst this; simp
  | N + 1, h => by
    by_cases e : m = N + 1
    · subst e; simp
    · rw [atBot_succ N _ e, atBot_letter x hx N (by omega), circ_top N x (by omega)]

section Gen

variable (d : ℕ) (G : (N m : ℕ) → Circ N)
  (Gsh : ∀ N m, 1 ≤ m → m + d ≤ N → Derivable (theory (N + 1)) (G (N + 1) (m + 1)) (shift (G N m)))

include Gsh in
theorem G_high : ∀ (m N : ℕ), 1 ≤ m → m + d ≤ N →
    ∃ B : Circ N, Derivable (theory N) (G N m) B ∧ HighW (m - 1) B
  | 0, _, h, _ => absurd h (by omega)
  | 1, N, _, _ => ⟨G N 1, Derivable.refl _, fun _ _ => Nat.zero_le _⟩
  | m + 2, N, _, h => by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨B, hB, hh⟩ := G_high (m + 1) N' (by omega) (by omega)
    exact ⟨shift B, (Gsh N' (m + 1) (by omega) (by omega)).trans (derivable_shift hB),
      highW_shift hh⟩

variable
  (base1 : ∀ N, 3 ≤ N → IH N → 1 + d ≤ N → ∀ x : L, (x = .H 0 ∨ x = .Z 0) →
    Derivable (theory N) (G N 1 * x.circ N) (x.circ N * G N 1))
  (base2 : ∀ N, 3 ≤ N → IH N → 2 + d ≤ N → ∀ x : L, (x = .C 0 ∨ x = .K 0) →
    Derivable (theory N) (G N 2 * x.circ N) (x.circ N * G N 2))
  (base0 : CompleteAt 2 → ∀ m (x : L), 1 ≤ m → m + d ≤ 2 → x.lo + x.wd ≤ m → (∀ j, x ≠ .S j) →
    Derivable (theory 2) (G 2 m * x.circ 2) (x.circ 2 * G 2 m))

include Gsh base1 base2 base0 in
theorem G_letter : ∀ (N : ℕ), 3 ≤ N → IH N → ∀ (m : ℕ), 1 ≤ m → m + d ≤ N → ∀ (x : L),
    (∀ j, x ≠ .S j) → x.lo + x.wd ≤ m →
      Derivable (theory N) (G N m * x.circ N) (x.circ N * G N m) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro hN ih m hm hmN x hxS hx
  by_cases hlow : x.lo + x.wd ≤ m - 1
  · obtain ⟨B, hB, hh⟩ := G_high d G Gsh m N hm hmN
    have hc := comm_low_high (x.circ N) B
      (fun g hg => le_trans (lowW_letter N x g hg) hlow) hh
    exact (dright _ hB).trans (hc.trans (dleft _ hB.symm))
  have hwd : 1 ≤ x.wd := by cases x <;> simp [L.wd]
  by_cases h0 : x.lo = 0
  · have hwm : x.wd = m := by omega
    cases x with
    | H j => simp only [L.lo] at h0; subst h0; simp only [L.wd] at hwm; subst hwm
             exact base1 N hN ih (by omega) _ (Or.inl rfl)
    | Z j => simp only [L.lo] at h0; subst h0; simp only [L.wd] at hwm; subst hwm
             exact base1 N hN ih (by omega) _ (Or.inr rfl)
    | C j => simp only [L.lo] at h0; subst h0; simp only [L.wd] at hwm; subst hwm
             exact base2 N hN ih (by omega) _ (Or.inl rfl)
    | K j => simp only [L.lo] at h0; subst h0; simp only [L.wd] at hwm; subst hwm
             exact base2 N hN ih (by omega) _ (Or.inr rfl)
    | S j => exact absurd rfl (hxS j)
  -- the generator does not touch wire `0`: one width down
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hxl : 1 ≤ x.lo := by omega
  have hdS : ∀ j, x.down ≠ .S j := by
    intro j e; cases x <;> simp_all [L.down]
  have hdx : x.down.lo + x.down.wd ≤ m' := by rw [down_lo, down_wd]; omega
  have hinner : Derivable (theory N') (G N' m' * x.down.circ N') (x.down.circ N' * G N' m') := by
    rcases (by omega : N' = 2 ∨ 3 ≤ N') with rfl | h3
    · exact base0 (ih 2 (by omega)) m' x.down (by omega) (by omega) hdx hdS
    · exact IHN N' (by omega) h3 (ih.mono (by omega)) m' (by omega) (by omega) x.down hdS hdx
  have hs := Gsh N' m' (by omega) (by omega)
  rw [circ_shift N' x hxl]
  have h := derivable_shift hinner
  rw [map_mul, map_mul] at h
  exact (dright _ hs).trans (h.trans (dleft _ hs.symm))

/-- A circuit on the bottom `m` wires commutes with `G N m`. -/
theorem G_circ {N m : ℕ} (hmN : m ≤ N)
    (hl : ∀ x : L, (∀ j, x ≠ .S j) → x.lo + x.wd ≤ m →
      Derivable (theory N) (G N m * x.circ N) (x.circ N * G N m)) (C : Circ m) :
    Derivable (theory N) (drawn [atBot N C, G N m]) (drawn [G N m, atBot N C]) := by
  rw [drawn2, drawn2]
  induction C using FreeMonoid.inductionOn' with
  | one =>
    have e : atBot N (1 : Circ m) = 1 := by
      have := atBot_mul N (1 : Circ m) 1; rw [mul_one] at this; exact (mul_eq_left.1 this.symm)
    rw [e, mul_one, one_mul]
  | mul_of g C ihC =>
    rw [atBot_mul, ← genL_circ g, atBot_letter (genL g) (by rw [genL_fit]; exact gHi_le g) N hmN]
    have h1 := hl (genL g) (genL_notS g) (by rw [genL_fit]; exact gHi_le g)
    rw [← mul_assoc]
    refine (dright _ h1).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ ihC

end Gen

end QCert.RealCliffordCH.Sec8.D.N8
