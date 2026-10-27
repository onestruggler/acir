/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Permutations of the wires

A swap word `swp l = SW l₁ * ⋯ * SW lₖ` relabels the wires (`paQ_swp`).
The word `rho k = SW₀ * SW₁ * ⋯ * SW_{k-1}` brings wire `k` down to wire
`0` and moves the wires below it up by one (`bit_rho`).

**Normal form.**  Every swap word on `n + 1` wires is `sh u * rho k` for a
swap word `u` one wire up (`swp_nf`): the set of such products contains `1`
and is closed under multiplication on the right by a swap (`rho_mul_qSW`),
by the Coxeter relations (`SW² = 1`, the braid relation from the
naturality of the symmetry, and far swaps commuting).  So a swap word that
leaves wire `0` in place is a swap word one wire up (`swp_fix0`), and one
that leaves wires `0, 1` in place is a swap word two wires up (`swp_fix01`).

**Placement.**  An element supported on the bottom two wires, conjugated
by two swap words that bring the same two wires down, gives the same
result (`conj_bring2`); likewise for one wire (`conj_bring1`).  This is
what makes gates on arbitrary wires (`Place.lean`) independent of the swap
network used to place them.
-/
import QCert.CNOTDihedral.SemQ

namespace QCert.CNOTDihedral

open Circuit

/-! ### The Coxeter relations for the swaps -/

theorem qSW_sq {n : ℕ} (i : ℕ) : (qSW i : Q n) * qSW i = 1 := by
  induction n generalizing i with
  | zero => rw [qSW_out (by omega), one_mul]
  | succ n ih =>
    cases i with
    | zero =>
      cases n with
      | zero => rw [qSW_out (by omega), one_mul]
      | succ n =>
        have h := mk_rule n Rel.swap_swap
        simp only [tseq, map_mul, map_one, one_mul, Circuit.pad, FreeMonoid.map_of, Gen.pad] at h
        exact h
    | succ i => rw [← sh_qSW, ← map_mul, ih, map_one]

theorem qSW_sq_left {n : ℕ} (i : ℕ) (x : Q n) : qSW i * (qSW i * x) = x := by
  rw [← mul_assoc, qSW_sq, one_mul]

theorem qSW_inv {n : ℕ} (i : ℕ) : (qSW i : Q n)⁻¹ = qSW i :=
  inv_eq_of_mul_eq_one_left (qSW_sq i)

theorem qSW_braid {n : ℕ} : ∀ (i : ℕ), i + 2 < n →
    (qSW i : Q n) * qSW (i + 1) * qSW i = qSW (i + 1) * qSW i * qSW (i + 1)
  | 0, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h := mk_rule n (Rel.swap_nat2 Gate.SW)
    simp only [tseq, Circuit.pad, FreeMonoid.map_of, Gen.pad, map_mul, map_one, one_mul,
      Circuit.shift_of] at h
    exact h
  | i + 1, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := congrArg sh (qSW_braid (n := n) i (by omega))
    simpa only [map_mul, sh_qSW] using this

theorem qSW_comm {n : ℕ} {i j : ℕ} (h : i + 2 ≤ j ∨ j + 2 ≤ i) :
    Comm (qSW i : Q n) (qSW j) := comm_22 _ _ h

/-! ### Swap words -/

/-- A word of swaps, in operator order: `swp [i, j] = SW i * SW j`. -/
def swp {n : ℕ} : List ℕ → Q n
  | [] => 1
  | i :: l => qSW i * swp l

@[simp] theorem swp_nil {n : ℕ} : (swp [] : Q n) = 1 := rfl
@[simp] theorem swp_cons {n : ℕ} (i : ℕ) (l : List ℕ) : (swp (i :: l) : Q n) = qSW i * swp l := rfl

theorem swp_append {n : ℕ} (l l' : List ℕ) : (swp (l ++ l') : Q n) = swp l * swp l' := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, mul_assoc]

theorem swp_singleton {n : ℕ} (i : ℕ) : (swp [i] : Q n) = qSW i := by simp

theorem swp_inv {n : ℕ} (l : List ℕ) : (swp l : Q n)⁻¹ = swp l.reverse := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, swp_append, qSW_inv]

theorem sh_swp {n : ℕ} (l : List ℕ) : sh (swp l : Q n) = swp (l.map (· + 1)) := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- The relabelling of a swap word. -/
def sig {n : ℕ} : List ℕ → Equiv.Perm (Fin n)
  | [] => 1
  | i :: l => sig l * swq i

theorem paQ_swp {n : ℕ} (l : List ℕ) : paQ (swp l : Q n) = ⟨fun s => s ∘ sig l, 0⟩ := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [swp_cons, map_mul, ih, paQ_qSW]
    refine PA.ext' (fun s => ?_) (fun s => ?_)
    · rfl
    · simp

/-! ### Bits after a relabelling -/

theorem bit_mul {n : ℕ} (p q : Q n) (s : State 2 n) (j : ℕ) :
    bit ((paQ (p * q)).f s) j = bit ((paQ p).f ((paQ q).f s)) j := by
  rw [map_mul]; rfl


theorem state_ext {n : ℕ} {s t : State 2 n} (h : ∀ j : ℕ, bit s j = bit t j) : s = t := by
  funext j; have := h j; rwa [bit_val, bit_val] at this

theorem bit_zero_eq {n : ℕ} (t : State 2 (n + 1)) : bit t 0 = t 0 := by simp [bit]

theorem bit_comp_swq {n : ℕ} (s : State 2 n) {i : ℕ} (hi : i + 1 < n) (j : ℕ) :
    bit (s ∘ swq i) j = if j = i then bit s (i + 1) else if j = i + 1 then bit s i else bit s j := by
  have hσ : swq (n := n) i = Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ := dif_pos hi
  by_cases hj : j < n
  · have hb : bit (s ∘ swq i) j = s (swq i ⟨j, hj⟩) := by simp [bit, hj]
    rw [hb, hσ]
    by_cases h1 : j = i
    · subst h1
      rw [if_pos rfl]
      exact (congrArg s (Equiv.swap_apply_left _ _)).trans (bit_val s ⟨j + 1, hi⟩).symm
    · by_cases h2 : j = i + 1
      · subst h2
        rw [if_neg (by omega), if_pos rfl]
        exact (congrArg s (Equiv.swap_apply_right _ _)).trans (bit_val s ⟨i, by omega⟩).symm
      · rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne
          (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)]
        exact (bit_val s ⟨j, hj⟩).symm
  · have hjn : n ≤ j := by omega
    rw [bit_out _ hjn, if_neg (by omega), if_neg (by omega), bit_out _ hjn]

/-! ### Bringing a wire down -/

/-- `rho k = SW₀ * ⋯ * SW_{k-1}`: wire `k` goes to wire `0`, the wires
below it one up. -/
def rho {n : ℕ} (k : ℕ) : Q n := swp (List.range k)

theorem rho_zero {n : ℕ} : (rho 0 : Q n) = 1 := rfl

theorem rho_succ {n : ℕ} (k : ℕ) : (rho (k + 1) : Q (n + 1)) = qSW 0 * sh (rho k) := by
  rw [rho, rho, sh_swp, List.range_succ_eq_map, swp_cons]

theorem rho_succ' {n : ℕ} (k : ℕ) : (rho (k + 1) : Q n) = rho k * qSW k := by
  rw [rho, rho, List.range_succ, swp_append, swp_singleton]

theorem bit_rho {n : ℕ} {k : ℕ} (hk : k < n) (s : State 2 n) (j : ℕ) :
    bit ((paQ (rho k : Q n)).f s) j =
      if j = 0 then bit s k else if j ≤ k then bit s (j - 1) else bit s j := by
  induction k generalizing n s j with
  | zero =>
    simp only [rho_zero, map_one, PA.one_f, id]
    split_ifs with h h' <;> first | (subst h; rfl) | omega | rfl
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih' := fun (t : State 2 n) (j : ℕ) => ih (n := n) (by omega) t j
    rw [rho_succ, map_mul, PA.mul_f, Function.comp_apply, paQ_qSW]
    show bit ((paQ (sh (rho k))).f s ∘ swq 0) j = _
    rw [bit_comp_swq _ (by omega), paQ_sh_f]
    rcases j with _ | _ | j
    · rw [if_pos rfl, if_pos rfl, bit_cons_succ, ih', if_pos rfl, bit_tail]
    · rw [if_neg (by omega), if_pos rfl, bit_cons_zero, if_neg (by omega), if_pos (by omega)]
      simp [bit]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), bit_cons_succ, ih',
        if_neg (by omega)]
      by_cases hj : j + 1 ≤ k
      · rw [if_pos hj, if_pos (by omega), bit_tail]; congr 1
      · rw [if_neg hj, if_neg (by omega), bit_tail]

/-! ### The normal form of swap words -/

theorem qSW_rho_comm {n : ℕ} : ∀ {k i : ℕ}, k + 1 ≤ i → Comm (rho k : Q n) (qSW i)
  | 0, i, _ => by simp [Comm, rho_zero]
  | k + 1, i, h => by
    cases n with
    | zero => simp [Comm, qSW_out]
    | succ n =>
      obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      unfold Comm
      rw [rho_succ, ← sh_qSW, mul_assoc, ← map_mul, qSW_rho_comm (n := n) (k := k) (by omega),
        map_mul, sh_qSW, ← mul_assoc, ← mul_assoc]
      congr 1
      exact (qSW_comm (by omega)).symm

theorem rho_mul_qSW_low {n : ℕ} : ∀ {k i : ℕ}, k < n → i + 2 ≤ k →
    (rho k : Q n) * qSW i = qSW (i + 1) * rho k
  | 0, _, _, h => by omega
  | 1, _, _, h => by omega
  | k + 2, i, hk, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    cases i with
    | zero =>
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rho_succ, rho_succ, map_mul, sh_qSW]
      have c := qSW0_comm_sh2 (rho k : Q n)
      calc qSW 0 * (qSW 1 * sh (sh (rho k))) * qSW 0
          = qSW 0 * qSW 1 * (sh (sh (rho k)) * qSW 0) := by simp only [mul_assoc]
        _ = qSW 0 * qSW 1 * (qSW 0 * sh (sh (rho k))) := by rw [c]
        _ = (qSW 0 * qSW 1 * qSW 0) * sh (sh (rho k)) := by simp only [mul_assoc]
        _ = (qSW 1 * qSW 0 * qSW 1) * sh (sh (rho k)) := by rw [qSW_braid 0 (by omega)]
        _ = qSW (0 + 1) * (qSW 0 * (qSW 1 * sh (sh (rho k)))) := by simp only [mul_assoc]
    | succ i =>
      rw [rho_succ (k + 1), ← sh_qSW, mul_assoc, ← map_mul,
        rho_mul_qSW_low (n := n) (k := k + 1) (i := i) (by omega) (by omega), map_mul, sh_qSW,
        ← mul_assoc, ← mul_assoc]
      congr 1
      exact (qSW_comm (by omega)).symm

/-- Multiplying `rho k` by a swap on the right. -/
theorem rho_mul_qSW {n : ℕ} {k : ℕ} (hk : k < n + 1) (i : ℕ) :
    ∃ u : List ℕ, ∃ k' < n + 1, (rho k : Q (n + 1)) * qSW i = sh (swp u) * rho k' := by
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · rcases Nat.lt_or_ge (i + 1) k with h' | h'
    · refine ⟨[i], k, hk, ?_⟩
      rw [rho_mul_qSW_low hk (by omega), swp_singleton, sh_qSW]
    · obtain rfl : k = i + 1 := by omega
      refine ⟨[], i, by omega, ?_⟩
      rw [rho_succ', mul_assoc, qSW_sq, mul_one, swp_nil, map_one, one_mul]
  · by_cases hi : i < n
    · exact ⟨[], i + 1, by omega, by rw [rho_succ', swp_nil, map_one, one_mul]⟩
    · refine ⟨[], i, hk, ?_⟩
      rw [qSW_out (by omega), mul_one, swp_nil, map_one, one_mul]
  · obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine ⟨[i], k, hk, ?_⟩
    rw [qSW_rho_comm (by omega), swp_singleton, sh_qSW]

/-- Every swap word on `n + 1` wires is a swap word one wire up followed
by `rho k`. -/
theorem swp_nf {n : ℕ} (l : List ℕ) :
    ∃ u : List ℕ, ∃ k < n + 1, (swp l : Q (n + 1)) = sh (swp u) * rho k := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], 0, by omega, by simp [rho_zero]⟩
  | append_singleton l i ih =>
    obtain ⟨u, k, hk, e⟩ := ih
    obtain ⟨u', k', hk', e'⟩ := rho_mul_qSW hk i
    refine ⟨u ++ u', k', hk', ?_⟩
    rw [swp_append, e, swp_singleton, mul_assoc, e', ← mul_assoc, ← map_mul, ← swp_append]

/-- A swap word that leaves wire `0` in place is a swap word one wire up. -/
theorem swp_fix0 {n : ℕ} (l : List ℕ)
    (h : ∀ s : State 2 (n + 1), bit ((paQ (swp l : Q (n + 1))).f s) 0 = bit s 0) :
    ∃ u : List ℕ, (swp l : Q (n + 1)) = sh (swp u) := by
  obtain ⟨u, k, hk, e⟩ := swp_nf (n := n) l
  have h1 := h (ei 0)
  rw [e, bit_mul, paQ_sh_f, bit_cons_zero, ← bit_zero_eq ((paQ (rho k)).f (ei 0)), bit_rho hk,
    if_pos rfl] at h1
  have hk0 : k = 0 := by
    by_contra hne
    simp [bit_ei, hne] at h1
  subst hk0
  exact ⟨u, by rw [e, rho_zero, mul_one]⟩

/-- A swap word that leaves wires `0, 1` in place is a swap word two wires
up. -/
theorem swp_fix01 {n : ℕ} (l : List ℕ)
    (h0 : ∀ s : State 2 (n + 2), bit ((paQ (swp l : Q (n + 2))).f s) 0 = bit s 0)
    (h1 : ∀ s : State 2 (n + 2), bit ((paQ (swp l : Q (n + 2))).f s) 1 = bit s 1) :
    ∃ u : List ℕ, (swp l : Q (n + 2)) = sh (sh (swp u)) := by
  obtain ⟨u, e⟩ := swp_fix0 l h0
  have hu : ∀ t : State 2 (n + 1), bit ((paQ (swp u : Q (n + 1))).f t) 0 = bit t 0 := by
    intro t
    have := h1 (Fin.cons 0 t)
    rwa [e, paQ_sh_f, bit_cons_succ, Fin.tail_cons, bit_cons_succ] at this
  obtain ⟨u', e'⟩ := swp_fix0 u hu
  exact ⟨u', by rw [e, e']⟩

/-! ### Relabelling by an inverse -/

theorem paQ_inv_f {n : ℕ} (q : Q n) (s : State 2 n) : (paQ q).f ((paQ q⁻¹).f s) = s := by
  have h : (paQ (q * q⁻¹)).f s = (paQ 1).f s := by rw [mul_inv_cancel]
  rw [map_mul, map_one] at h
  exact h

theorem paQ_inv_f' {n : ℕ} (q : Q n) (s : State 2 n) : (paQ q⁻¹).f ((paQ q).f s) = s := by
  have h : (paQ (q⁻¹ * q)).f s = (paQ 1).f s := by rw [inv_mul_cancel]
  rw [map_mul, map_one] at h
  exact h

/-- If `q` carries wire `x` to wire `i`, then `q⁻¹` carries wire `i` to
wire `x`. -/
theorem bit_inv {n : ℕ} (q : Q n) {i x : ℕ}
    (h : ∀ t : State 2 n, bit ((paQ q).f t) i = bit t x) (s : State 2 n) :
    bit ((paQ q⁻¹).f s) x = bit s i := by
  have := h ((paQ q⁻¹).f s)
  rw [paQ_inv_f] at this
  exact this.symm

/-- The inverse of a swap word relabels by the inverse permutation. -/
theorem paQ_swp_inv {n : ℕ} (l : List ℕ) :
    paQ (swp l : Q n)⁻¹ = ⟨fun s => s ∘ (sig l).symm, 0⟩ := by
  refine PA.ext' (fun s => ?_) (fun s => ?_)
  · have h1 := paQ_inv_f (swp l : Q n) s
    rw [paQ_swp] at h1
    funext j
    have := congrFun h1 ((sig l).symm j)
    simpa using this
  · rw [swp_inv, paQ_swp]

/-! ### Placement on the bottom wires -/

/-- Conjugation by two swap words that bring the same wire to wire `0`
agrees on anything supported on wire `0`. -/
theorem conj_fix1 {n : ℕ} (E : Q (n + 1)) (hE : ∀ u : Q n, Comm E (sh u)) (l l' : List ℕ)
    (h : ∀ s, bit ((paQ (swp l : Q (n + 1))).f s) 0 = bit ((paQ (swp l' : Q (n + 1))).f s) 0) :
    (swp l : Q (n + 1))⁻¹ * E * swp l = (swp l')⁻¹ * E * swp l' := by
  obtain ⟨u, hu⟩ := swp_fix0 (n := n) (l' ++ l.reverse) (fun s => by
    rw [swp_append, ← swp_inv, bit_mul, ← h, ← bit_mul, mul_inv_cancel, map_one]; rfl)
  rw [swp_append, ← swp_inv] at hu
  have e : (swp l' : Q (n + 1)) = sh (swp u) * swp l := by rw [← hu]; group
  have hc : (sh (swp u))⁻¹ * E * sh (swp u) = E := by
    rw [mul_assoc, hE (swp u), ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e, show ((sh (swp u) * swp l)⁻¹ * E * (sh (swp u) * swp l)) =
    (swp l)⁻¹ * ((sh (swp u))⁻¹ * E * sh (swp u)) * swp l by group, hc]

/-- Conjugation by two swap words that bring the same two wires to wires
`0, 1` agrees on anything supported on wires `0, 1`. -/
theorem conj_fix2 {n : ℕ} (E : Q (n + 2)) (hE : ∀ u : Q n, Comm E (sh (sh u))) (l l' : List ℕ)
    (h0 : ∀ s, bit ((paQ (swp l : Q (n + 2))).f s) 0 = bit ((paQ (swp l' : Q (n + 2))).f s) 0)
    (h1 : ∀ s, bit ((paQ (swp l : Q (n + 2))).f s) 1 = bit ((paQ (swp l' : Q (n + 2))).f s) 1) :
    (swp l : Q (n + 2))⁻¹ * E * swp l = (swp l')⁻¹ * E * swp l' := by
  obtain ⟨u, hu⟩ := swp_fix01 (n := n) (l' ++ l.reverse)
    (fun s => by rw [swp_append, ← swp_inv, bit_mul, ← h0, ← bit_mul, mul_inv_cancel, map_one]; rfl)
    (fun s => by rw [swp_append, ← swp_inv, bit_mul, ← h1, ← bit_mul, mul_inv_cancel, map_one]; rfl)
  rw [swp_append, ← swp_inv] at hu
  have e : (swp l' : Q (n + 2)) = sh (sh (swp u)) * swp l := by rw [← hu]; group
  have hc : (sh (sh (swp u)))⁻¹ * E * sh (sh (swp u)) = E := by
    rw [mul_assoc, hE (swp u), ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e, show ((sh (sh (swp u)) * swp l)⁻¹ * E * (sh (sh (swp u)) * swp l)) =
    (swp l)⁻¹ * ((sh (sh (swp u)))⁻¹ * E * sh (sh (swp u))) * swp l by group, hc]

/-! ### Bringing given wires down -/

/-- The index of a wire after wire `w` has been brought down to `0` and the
bottom wire removed. -/
def adj (w j : ℕ) : ℕ := if j < w then j else j - 1

/-- A swap word bringing the wires `ws` (distinct) down to `0, 1, …`. -/
def bringL : List ℕ → List ℕ
  | [] => []
  | w :: ws => (bringL (ws.map (adj w))).map (· + 1) ++ List.range w
termination_by ws => ws.length
decreasing_by simp

theorem swp_bringL_cons {n : ℕ} (w : ℕ) (ws : List ℕ) :
    (swp (bringL (w :: ws)) : Q (n + 1)) = sh (swp (bringL (ws.map (adj w)))) * rho w := by
  rw [bringL, swp_append, sh_swp]; rfl

theorem bit_bringL : ∀ {n : ℕ} (ws : List ℕ), ws.Nodup → (∀ w ∈ ws, w < n) →
    ∀ (s : State 2 n) (i x : ℕ), ws[i]? = some x →
      bit ((paQ (swp (bringL ws) : Q n)).f s) i = bit s x
  | _, [], _, _, _, i, x, hx => by simp at hx
  | n, w :: ws, hnd, hlt, s, i, x, hx => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hlt w (by simp); omega⟩
    have hw : w < n + 1 := hlt w (by simp)
    rw [swp_bringL_cons, bit_mul, paQ_sh_f]
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      have := bit_rho hw s 0
      rw [if_pos rfl, bit_zero_eq] at this
      rw [bit_cons_zero, this]
    · simp only [List.getElem?_cons_succ] at hx
      have hxm : x ∈ ws := List.mem_of_getElem? hx
      have hxw : x ≠ w := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hxm)
      have hxn : x < n + 1 := hlt x (List.mem_cons_of_mem _ hxm)
      have hnd' : (ws.map (adj w)).Nodup := by
        rw [List.nodup_cons] at hnd
        refine hnd.2.map_on ?_
        intro y hy z hz hyz
        have hyw : y ≠ w := fun h => hnd.1 (h ▸ hy)
        have hzw : z ≠ w := fun h => hnd.1 (h ▸ hz)
        unfold adj at hyz; split_ifs at hyz <;> omega
      have hlt' : ∀ v ∈ ws.map (adj w), v < n := by
        intro v hv
        rw [List.mem_map] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        have hyw : y ≠ w := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hy)
        have := hlt y (List.mem_cons_of_mem _ hy)
        unfold adj; split_ifs <;> omega
      rw [bit_cons_succ, bit_bringL (ws.map (adj w)) hnd' hlt' _ i (adj w x)
        (by simp [List.getElem?_map, hx]), bit_tail, bit_rho hw]
      by_cases hlt2 : x < w
      · have ha : adj w x = x := if_pos hlt2
        rw [ha, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]
      · have ha : adj w x = x - 1 := if_neg hlt2
        rw [ha, if_neg (by omega), if_neg (by omega), Nat.sub_add_cancel (by omega)]

theorem length_le_of_nodup {n : ℕ} {xs : List ℕ} (hnd : xs.Nodup) (hlt : ∀ w ∈ xs, w < n) :
    xs.length ≤ n := by
  have := List.Nodup.length_le_card (α := Fin n) (l := xs.attach.map fun w => ⟨w.1, hlt w.1 w.2⟩)
    (by
      refine List.Nodup.map (fun x y h => ?_) hnd.attach
      simp only [Fin.mk.injEq] at h; exact Subtype.ext h)
  simpa using this

end QCert.CNOTDihedral
