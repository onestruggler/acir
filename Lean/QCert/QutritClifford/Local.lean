/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Letters on one, two and three wires

Toward Theorem 4.4, the instances of the engine (`Engine.lean`):

* words are stored as natural numbers in base 9 (`decW`), one digit per
  letter, the first letter least significant;
* the free steps on two and three wires (`fo2`, `fo3`): a segment on the
  bottom or top `k - 1` wires (`cw_lo2`, `cw_hi`, `cw_lo3`) replaced by one
  acting alike on the Paulis there, sound with completeness on `k - 1`
  wires (`fo2_sound`, `fo3_sound`);
* the base tables: (C6)-(C14) on two wires (`base2`), (C15)-(C18) on three
  (`base3`), each an instance of its rule (`E_of_rule`);
* inverse words (`invW`, a letter's inverse is a power of it) and their
  cancellation (`E_cancel`);
* every circuit is, up to a phase, a word of letters (`exists_word`).
-/
import QCert.QutritClifford.Engine

namespace QCert.QutritClifford

open Lt

/-! ### Pauli tableaux

The action of a word on one or two wires on the Pauli generators, computed
on explicit data (`run1`, `run2`) rather than through `actC`, whose
evaluation is slow; the two agree letter by letter (`t1_ok`, `t2_ok`,
decided on all data). -/

def P1.pd (p : P1) : PD 1 := ⟨p.c, ![p.a], ![p.b]⟩
def P2.pd (p : P2) : PD 2 := ⟨p.c, ![p.a0, p.a1], ![p.b0, p.b1]⟩

theorem t1H : ∀ c a b : Fin 3, actGen (Lt.gen 1 (.H 0)) (P1.pd ⟨c, a, b⟩) =
    (t1 (.H 0) ⟨c, a, b⟩).pd := by decide +kernel
theorem t1S : ∀ c a b : Fin 3, actGen (Lt.gen 1 (.S 0)) (P1.pd ⟨c, a, b⟩) =
    (t1 (.S 0) ⟨c, a, b⟩).pd := by decide +kernel

theorem t1_ok (x : Lt) (hx : in1 x = true) (p : P1) :
    actGen (Lt.gen 1 x) p.pd = (t1 x p).pd := by
  obtain ⟨c, a, b⟩ := p
  match x, hx with
  | .H 0, _ => exact t1H c a b
  | .S 0, _ => exact t1S c a b

theorem t2H0 : ∀ c a0 b0 a1 b1 : Fin 3, actGen (Lt.gen 2 (.H 0)) (P2.pd ⟨c, a0, b0, a1, b1⟩) =
    (t2 (.H 0) ⟨c, a0, b0, a1, b1⟩).pd := by decide +kernel
theorem t2S0 : ∀ c a0 b0 a1 b1 : Fin 3, actGen (Lt.gen 2 (.S 0)) (P2.pd ⟨c, a0, b0, a1, b1⟩) =
    (t2 (.S 0) ⟨c, a0, b0, a1, b1⟩).pd := by decide +kernel
theorem t2H1 : ∀ c a0 b0 a1 b1 : Fin 3, actGen (Lt.gen 2 (.H 1)) (P2.pd ⟨c, a0, b0, a1, b1⟩) =
    (t2 (.H 1) ⟨c, a0, b0, a1, b1⟩).pd := by decide +kernel
theorem t2S1 : ∀ c a0 b0 a1 b1 : Fin 3, actGen (Lt.gen 2 (.S 1)) (P2.pd ⟨c, a0, b0, a1, b1⟩) =
    (t2 (.S 1) ⟨c, a0, b0, a1, b1⟩).pd := by decide +kernel
theorem t2C0 : ∀ c a0 b0 a1 b1 : Fin 3, actGen (Lt.gen 2 (.C 0)) (P2.pd ⟨c, a0, b0, a1, b1⟩) =
    (t2 (.C 0) ⟨c, a0, b0, a1, b1⟩).pd := by decide +kernel

theorem t2_ok (x : Lt) (hx : in2 x = true) (p : P2) :
    actGen (Lt.gen 2 x) p.pd = (t2 x p).pd := by
  obtain ⟨c, a0, b0, a1, b1⟩ := p
  match x, hx with
  | .H 0, _ => exact t2H0 c a0 b0 a1 b1
  | .S 0, _ => exact t2S0 c a0 b0 a1 b1
  | .H 1, _ => exact t2H1 c a0 b0 a1 b1
  | .S 1, _ => exact t2S1 c a0 b0 a1 b1
  | .C 0, _ => exact t2C0 c a0 b0 a1 b1

theorem actC_gen {n : ℕ} (g : Gen Gate n) (P : PD n) :
    actC n (FreeMonoid.of g) P = actGen g P := by
  have := actC_of g 1 P
  rwa [mul_one, actC_one] at this

theorem run1_ok : ∀ (l : List Lt), l.all in1 = true → ∀ p : P1,
    actC 1 (cw 1 l) p.pd = (run1 l p).pd
  | [], _, _ => actC_one _
  | x :: l, h, p => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [cw, actC_mul, actC_gen, t1_ok x h.1, run1_ok l h.2]; rfl

theorem run2_ok : ∀ (l : List Lt), l.all in2 = true → ∀ p : P2,
    actC 2 (cw 2 l) p.pd = (run2 l p).pd
  | [], _, _ => actC_one _
  | x :: l, h, p => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [cw, actC_mul, actC_gen, t2_ok x h.1, run2_ok l h.2]; rfl

theorem xat1 : PD.Xat (0 : Fin 1) = P1.pd ⟨0, 1, 0⟩ := by decide
theorem zat1 : PD.Zat (0 : Fin 1) = P1.pd ⟨0, 0, 1⟩ := by decide
theorem xat20 : PD.Xat (0 : Fin 2) = P2.pd ⟨0, 1, 0, 0, 0⟩ := by decide
theorem zat20 : PD.Zat (0 : Fin 2) = P2.pd ⟨0, 0, 1, 0, 0⟩ := by decide
theorem xat21 : PD.Xat (1 : Fin 2) = P2.pd ⟨0, 0, 0, 1, 0⟩ := by decide
theorem zat21 : PD.Zat (1 : Fin 2) = P2.pd ⟨0, 0, 0, 0, 1⟩ := by decide

theorem same1_sound {s t : List Lt} (hs : s.all in1 = true) (ht : t.all in1 = true)
    (h : same1 s t = true) : actC 1 (cw 1 s) = actC 1 (cw 1 t) := by
  simp only [same1, Bool.and_eq_true, beq_iff_eq] at h
  apply actC_eq_of_gens
  · intro j
    rw [Subsingleton.elim j 0, xat1, run1_ok s hs, run1_ok t ht, h.1]
  · intro j
    rw [Subsingleton.elim j 0, zat1, run1_ok s hs, run1_ok t ht, h.2]

theorem same2_sound {s t : List Lt} (hs : s.all in2 = true) (ht : t.all in2 = true)
    (h : same2 s t = true) : actC 2 (cw 2 s) = actC 2 (cw 2 t) := by
  simp only [same2, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  apply actC_eq_of_gens
  · intro j
    match j with
    | 0 => rw [xat20, run2_ok s hs, run2_ok t ht, h1]
    | 1 => rw [xat21, run2_ok s hs, run2_ok t ht, h3]
  · intro j
    match j with
    | 0 => rw [zat20, run2_ok s hs, run2_ok t ht, h2]
    | 1 => rw [zat21, run2_ok s hs, run2_ok t ht, h4]

/-! ### Free steps -/

theorem gen_lo2 (x : Lt) (h : lo2 x = true) : gen 2 x = Gen.pad 1 (gen 1 x) := by
  match x, h with
  | .H 0, _ => rfl
  | .S 0, _ => rfl

theorem gen_lo3 (x : Lt) (h : lo3 x = true) : gen 3 x = Gen.pad 1 (gen 2 x) := by
  match x, h with
  | .H 0, _ => rfl
  | .H 1, _ => rfl
  | .S 0, _ => rfl
  | .S 1, _ => rfl
  | .C 0, _ => rfl

theorem cw_lo2 : ∀ l : List Lt, l.all lo2 = true → cw 2 l = Circuit.pad 1 (cw 1 l)
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [cw, map_mul, cw_lo2 l h.2, gen_lo2 x h.1, Circuit.pad, FreeMonoid.map_of]

theorem cw_lo3 : ∀ l : List Lt, l.all lo3 = true → cw 3 l = Circuit.pad 1 (cw 2 l)
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [cw, map_mul, cw_lo3 l h.2, gen_lo3 x h.1, Circuit.pad, FreeMonoid.map_of]

theorem cw_hi (k : ℕ) : ∀ l : List Lt, l.all hi1 = true →
    cw (k + 1) l = Circuit.shift (cw k (l.map down))
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true, hi1, decide_eq_true_eq] at h
    simp only [cw, List.map_cons, map_mul, cw_hi k l (by simpa [hi1] using h.2),
      gen_up k x h.1, Circuit.shift_of]

theorem all_mono {l : List Lt} {p q : Lt → Bool} (h : l.all p = true)
    (hpq : ∀ x, p x = true → q x = true) : l.all q = true := by
  simp only [List.all_eq_true] at h ⊢; exact fun x hx => hpq x (h x hx)

theorem all_map_down {l : List Lt} {p q : Lt → Bool} (h : l.all p = true)
    (hpq : ∀ x, p x = true → q (down x) = true) : (l.map down).all q = true := by
  simp only [List.all_eq_true, List.mem_map] at h ⊢
  rintro _ ⟨x, hx, rfl⟩; exact hpq x (h x hx)

theorem hi2_hi1 (x : Lt) (hx : hi2 x = true) : hi1 x = true := by
  cases x <;> simp [hi2, hi1, Lt.lo, Lt.hi] at hx ⊢ <;> omega

theorem hi2_in1 (x : Lt) (hx : hi2 x = true) : in1 (down x) = true := by
  cases x <;> simp [hi2, in1, Lt.lo, Lt.hi, down] at hx ⊢ <;> omega

theorem hi3_hi1 (x : Lt) (hx : hi3 x = true) : hi1 x = true := by
  cases x <;> simp [hi3, hi1, Lt.lo, Lt.hi] at hx ⊢ <;> omega

theorem hi3_in2 (x : Lt) (hx : hi3 x = true) : in2 (down x) = true := by
  cases x <;> simp [hi3, in2, Lt.lo, Lt.hi, down] at hx ⊢ <;> omega

theorem fo2_sound (hc : Complete 1) (s t : List Lt) (h : fo2 s t = true) : E 2 s t := by
  simp only [fo2, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hs, ht⟩, hg⟩ | ⟨⟨hs, ht⟩, hg⟩
  · have h0 : ∀ x, lo2 x = true → in1 x = true := fun x hx => hx
    unfold E; rw [cw_lo2 s hs, cw_lo2 t ht]
    exact PEq.pad 1 (pcomplete hc (same1_sound (all_mono hs h0) (all_mono ht h0) hg))
  · have h1 := hi2_hi1
    have h2 := hi2_in1
    unfold E; rw [cw_hi 1 s (all_mono hs h1), cw_hi 1 t (all_mono ht h1)]
    exact PEq.shift (pcomplete hc (same1_sound (all_map_down hs h2) (all_map_down ht h2) hg))

theorem fo3_sound (hc : Complete 2) (s t : List Lt) (h : fo3 s t = true) : E 3 s t := by
  simp only [fo3, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hs, ht⟩, hg⟩ | ⟨⟨hs, ht⟩, hg⟩
  · have h0 : ∀ x, lo3 x = true → in2 x = true := fun x hx => hx
    unfold E; rw [cw_lo3 s hs, cw_lo3 t ht]
    exact PEq.pad 1 (pcomplete hc (same2_sound (all_mono hs h0) (all_mono ht h0) hg))
  · have h1 := hi3_hi1
    have h2 := hi3_in2
    unfold E; rw [cw_hi 2 s (all_mono hs h1), cw_hi 2 t (all_mono ht h1)]
    exact PEq.shift (pcomplete hc (same2_sound (all_map_down hs h2) (all_map_down ht h2) hg))

/-! ### Base tables -/

theorem negω_pow_comm {n : ℕ} (s : ℕ) (v : Circ n) : Der n (negω ^ s * v) (v * negω ^ s) := by
  induction s with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ s ih =>
    rw [pow_succ, mul_assoc]
    refine ((Derivable.refl _).mul (negω_comm v)).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact (ih.mul (Derivable.refl _))

/-- A rule of Figure 1 as an equation of words, its scalar dropped. -/
theorem E_of_rule {k : ℕ} {w v : Circ k} (h : Rule k w v) {l r : List Lt} (t : ℕ)
    (hl : Circuit.pad 0 w = cw (0 + k) l) (hr : Circuit.pad 0 v = negω ^ t * cw (0 + k) r) :
    E (0 + k) l r := by
  have d : Der (0 + k) (Circuit.pad 0 w) (Circuit.pad 0 v) := derives_rule h
  rw [hl, hr] at d
  exact ⟨t, d.trans (negω_pow_comm t _)⟩

theorem base2_valid : Valid 2 base2 := by
  intro e he
  simp only [base2, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E_of_rule Rule.C6 0 rfl rfl
  · exact E_of_rule Rule.C7 0 rfl rfl
  · exact E_of_rule Rule.C8 0 rfl rfl
  · exact E_of_rule Rule.C9 0 rfl rfl
  · exact E_of_rule Rule.C10 0 rfl rfl
  · exact E_of_rule Rule.C11 0 rfl rfl
  · exact E_of_rule Rule.C12 0 rfl rfl
  · exact E_of_rule Rule.C13 8 rfl rfl
  · exact E_of_rule Rule.C14 4 rfl rfl

theorem base3_valid : Valid 3 base3 := by
  intro e he
  simp only [base3, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact E_of_rule Rule.C15 0 rfl rfl
  · exact E_of_rule Rule.C16 0 rfl rfl
  · exact E_of_rule Rule.C17 0 rfl rfl
  · exact E_of_rule Rule.C18 0 rfl rfl

/-! ### Inverse words -/

/-- A letter followed by its inverse. -/
theorem E_letter : ∀ (k : ℕ) (x : Lt), x.hi < k → E k (x :: invL x) []
  | k + 1, .H 0, _ => by
    have := E_of_rule (l := [.H 0, .H 0, .H 0, .H 0]) (r := []) Rule.C2 0 rfl rfl
    exact PEq.pad k this
  | k + 1, .S 0, _ => by
    have := E_of_rule (l := [.S 0, .S 0, .S 0]) (r := []) Rule.C3 0 rfl rfl
    exact PEq.pad k this
  | k + 2, .C 0, _ => by
    have := E_of_rule (l := [.C 0, .C 0, .C 0]) (r := []) Rule.C6 0 rfl rfl
    exact PEq.pad k this
  | k + 1, .H (j + 1), h => by
    have := PEq.shift (E_letter k (.H j) (by simp [Lt.hi] at h ⊢; omega))
    exact this
  | k + 1, .S (j + 1), h => by
    have := PEq.shift (E_letter k (.S j) (by simp [Lt.hi] at h ⊢; omega))
    exact this
  | k + 1, .C (j + 1), h => by
    have := PEq.shift (E_letter k (.C j) (by simp [Lt.hi] at h ⊢; omega))
    exact this
  | 0, x, h => by cases x <;> simp [Lt.hi] at h
  | 1, .C 0, h => by simp [Lt.hi] at h

/-- Words of letters fitting on `k` wires. -/
def Fits (k : ℕ) (l : List Lt) : Prop := ∀ x ∈ l, x.hi < k

theorem E_invL_letter (k : ℕ) (x : Lt) (h : x.hi < k) : E k (invL x ++ [x]) [] := by
  have : invL x ++ [x] = x :: invL x := by cases x <;> rfl
  rw [this]; exact E_letter k x h

theorem E_cancel {k : ℕ} : ∀ l : List Lt, Fits k l → E k (l ++ invW l) []
  | [], _ => E.refl _
  | x :: l, h => by
    have h1 : E k (l ++ invW l) [] := E_cancel l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    show E k (x :: (l ++ (invW l ++ invL x))) []
    have e1 : E k (x :: (l ++ (invW l ++ invL x))) ([x] ++ [] ++ invL x) := by
      have := ((E.refl [x]).append h1).append (E.refl (invL x))
      simpa [List.append_assoc] using this
    exact e1.trans (E_letter k x (h x List.mem_cons_self))

theorem E_cancel' {k : ℕ} : ∀ l : List Lt, Fits k l → E k (invW l ++ l) []
  | [], _ => E.refl _
  | x :: l, h => by
    have h1 : E k (invW l ++ l) [] := E_cancel' l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    show E k (invW l ++ invL x ++ x :: l) []
    have e1 : E k (invW l ++ invL x ++ x :: l) (invW l ++ [] ++ l) := by
      have := ((E.refl (invW l)).append (E_invL_letter k x (h x List.mem_cons_self))).append
        (E.refl l)
      simpa [List.append_assoc] using this
    exact e1.trans (by simpa using h1)

theorem fits_invW {k : ℕ} : ∀ l : List Lt, Fits k l → Fits k (invW l)
  | [], _ => fun _ h => nomatch h
  | x :: l, h => by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact fits_invW l (fun z hz => h z (List.mem_cons_of_mem _ hz)) y hy
    · have hx := h x List.mem_cons_self
      cases x <;> simp [invL] at hy <;> subst hy <;> exact hx

/-- Cancel a common suffix. -/
theorem E.cancel_right {k : ℕ} {a b : List Lt} (l : List Lt) (hl : Fits k l)
    (h : E k (a ++ l) (b ++ l)) : E k a b := by
  have h1 : E k (a ++ l ++ invW l) (b ++ l ++ invW l) := h.append (E.refl _)
  have ca : E k (a ++ l ++ invW l) (a ++ []) := by
    rw [List.append_assoc]; exact (E.refl a).append (E_cancel l hl)
  have cb : E k (b ++ l ++ invW l) (b ++ []) := by
    rw [List.append_assoc]; exact (E.refl b).append (E_cancel l hl)
  simpa using ca.symm.trans (h1.trans cb)

/-- Cancel a common prefix. -/
theorem E.cancel_left {k : ℕ} {a b : List Lt} (l : List Lt) (hl : Fits k l)
    (h : E k (l ++ a) (l ++ b)) : E k a b := by
  have h1 : E k (invW l ++ (l ++ a)) (invW l ++ (l ++ b)) := (E.refl _).append h
  have ca : E k (invW l ++ (l ++ a)) ([] ++ a) := by
    rw [← List.append_assoc]; exact (E_cancel' l hl).append (E.refl a)
  have cb : E k (invW l ++ (l ++ b)) ([] ++ b) := by
    rw [← List.append_assoc]; exact (E_cancel' l hl).append (E.refl b)
  simpa using ca.symm.trans (h1.trans cb)

/-! ### Circuits as words -/

theorem scalar_gen : ∀ {k : ℕ} (g : Gen Gate k), (∀ x : Lt, x.hi < k → g ≠ gen k x) →
    PEq k (FreeMonoid.of g) 1
  | n, .gate0 .negω, _ => by
    have := PEq.negω_absorb (1 : Circ n) 1
    simpa [negω, pow_one, one_mul] using this
  | k + 1, .gate1 .H, h => absurd rfl (h (.H 0) (by simp [Lt.hi]))
  | k + 1, .gate1 .S, h => absurd rfl (h (.S 0) (by simp [Lt.hi]))
  | k + 2, .gate2 .CZ, h => absurd rfl (h (.C 0) (by simp [Lt.hi]))
  | _, .gate3 g, _ => nomatch g
  | k + 1, .up g, h => by
    have hg : ∀ x : Lt, x.hi < k → g ≠ gen k x := by
      intro x hxk hx
      apply h (match x with | .H j => .H (j + 1) | .S j => .S (j + 1) | .C j => .C (j + 1))
      · cases x <;> simp [Lt.hi] at hxk ⊢ <;> omega
      · cases x <;> simp [gen, hx]
    have := PEq.shift (scalar_gen g hg)
    simpa using this

theorem exists_word_gen {k : ℕ} (g : Gen Gate k) :
    (∃ x : Lt, x.hi < k ∧ g = gen k x) ∨ PEq k (FreeMonoid.of g) 1 := by
  by_cases h : ∃ x : Lt, x.hi < k ∧ g = gen k x
  · exact Or.inl h
  · exact Or.inr (scalar_gen g (fun x hx e => h ⟨x, hx, e⟩))

/-- Every circuit is, up to a phase, a word of letters fitting its wires. -/
theorem exists_word {k : ℕ} (u : Circ k) : ∃ l : List Lt, Fits k l ∧ PEq k u (cw k l) := by
  induction u using FreeMonoid.inductionOn' with
  | one => exact ⟨[], fun _ h => by simp at h, PEq.refl _⟩
  | mul_of g u ih =>
    obtain ⟨l, hl, hu⟩ := ih
    rcases exists_word_gen g with ⟨x, hx, rfl⟩ | hg
    · refine ⟨l ++ [x], ?_, ?_⟩
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hl y hy
        · rw [List.mem_singleton.1 hy]; exact hx
      · rw [cw_append]; simp only [cw, one_mul]; exact PEq.mul (PEq.refl _) hu
    · exact ⟨l, hl, by simpa using hg.mul hu⟩


/-! ### Stored libraries -/

/-! ### Libraries checked lemma by lemma

A stored library is checked one lemma per declaration (`libLemOk`), each
over the entries of the table before it, so that no single kernel check
holds the whole library. -/

/-- The first `n` entries of the table hold. -/
def ValidUpTo (k : ℕ) (T : Tbl) (n : ℕ) : Prop := ∀ i < n, ∀ e, T[i]? = some e → E k e.1 e.2

theorem validUpTo_base {k : ℕ} {B : Tbl} (hB : Valid k B) (D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ))) :
    ValidUpTo k (libTbl B (decLib D)) B.length := by
  intro i hi e he
  apply hB e
  rw [libTbl, List.getElem?_append_left hi] at he
  exact List.mem_of_getElem? he

theorem valid_take {k : ℕ} {T : Tbl} {n : ℕ} (h : ValidUpTo k T n) : Valid k (T.take n) := by
  intro e he
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  rw [List.getElem_take] at hie
  have hin : i < n := by simp [List.length_take] at hi; omega
  exact h i hin e (by rw [← hie]; exact List.getElem?_eq_getElem _)

theorem validUpTo_step {k : ℕ} (fo : List Lt → List Lt → Bool)
    (hfo : ∀ s t, fo s t = true → E k s t) {B : Tbl}
    {D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ))} {i : ℕ}
    (h : ValidUpTo k (libTbl B (decLib D)) (B.length + i)) (hi : libLemOk fo B D i = true) :
    ValidUpTo k (libTbl B (decLib D)) (B.length + i + 1) := by
  unfold libLemOk at hi
  split at hi
  · exact nomatch hi
  · rename_i e he
    have hE := lemOk_E fo hfo (valid_take h) hi
    intro j hj e' he'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h j hj e' he'
    · have hD : i < D.length := (List.getElem?_eq_some_iff.1 he).1
      rw [libTbl, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_map, decLib, List.getElem?_map, he] at he'
      simp only [Option.map_some, Option.some.injEq] at he'
      subst he'
      exact hE

/-- A stored library all of whose lemmas below `n` check. -/
theorem validUpTo_all {k : ℕ} (fo : List Lt → List Lt → Bool)
    (hfo : ∀ s t, fo s t = true → E k s t) {B : Tbl} (hB : Valid k B)
    (D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ))) :
    ∀ n, (∀ i < n, libLemOk fo B D i = true) → ValidUpTo k (libTbl B (decLib D)) (B.length + n)
  | 0, _ => validUpTo_base hB D
  | n + 1, h => validUpTo_step fo hfo (validUpTo_all fo hfo hB D n (fun i hi => h i (by omega)))
      (h n (by omega))

/-- An entry of a table of which the first `n` entries hold. -/
theorem ValidUpTo.get {k : ℕ} {T : Tbl} {n : ℕ} (h : ValidUpTo k T n) (i : ℕ) (hi : i < n)
    {l r : List Lt} (he : T[i]? = some (l, r)) : E k l r :=
  h i hi (l, r) he

end QCert.QutritClifford
