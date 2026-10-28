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

/-! ### Words as numbers -/

/-- The letter of a digit: `1`-`8` are `H₀ S₀ H₁ S₁ H₂ S₂ C₀ C₁`. -/
def digL : ℕ → Lt
  | 1 => .H 0
  | 2 => .S 0
  | 3 => .H 1
  | 4 => .S 1
  | 5 => .H 2
  | 6 => .S 2
  | 7 => .C 0
  | _ => .C 1

def decWF : ℕ → ℕ → List Lt
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else digL (n % 9) :: decWF f (n / 9)

/-- The word of a number. -/
def decW (n : ℕ) : List Lt := decWF 250 n

/-! ### Free steps -/

/-- On two wires: the letters on wire 0 and on wire 1. -/
def lo2 (x : Lt) : Bool := x.hi == 0
def hi1 (x : Lt) : Bool := 1 ≤ x.lo

/-- On three wires: the letters on wires 0, 1 and on wires 1, 2. -/
def lo3 (x : Lt) : Bool := x.hi ≤ 1

def fo2 (s t : List Lt) : Bool :=
  (s.all lo2 && t.all lo2 && sameGens (cw 1 s) (cw 1 t)) ||
  (s.all hi1 && t.all hi1 && sameGens (cw 1 (s.map down)) (cw 1 (t.map down)))

def fo3 (s t : List Lt) : Bool :=
  (s.all lo3 && t.all lo3 && sameGens (cw 2 s) (cw 2 t)) ||
  (s.all hi1 && t.all hi1 && sameGens (cw 2 (s.map down)) (cw 2 (t.map down)))

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

theorem fo2_sound (hc : Complete 1) (s t : List Lt) (h : fo2 s t = true) : E 2 s t := by
  simp only [fo2, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hs, ht⟩, hg⟩ | ⟨⟨hs, ht⟩, hg⟩
  · unfold E; rw [cw_lo2 s hs, cw_lo2 t ht]
    exact PEq.pad 1 (pcomplete_gens hc hg)
  · unfold E; rw [cw_hi 1 s hs, cw_hi 1 t ht]
    exact PEq.shift (pcomplete_gens hc hg)

theorem fo3_sound (hc : Complete 2) (s t : List Lt) (h : fo3 s t = true) : E 3 s t := by
  simp only [fo3, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hs, ht⟩, hg⟩ | ⟨⟨hs, ht⟩, hg⟩
  · unfold E; rw [cw_lo3 s hs, cw_lo3 t ht]
    exact PEq.pad 1 (pcomplete_gens hc hg)
  · unfold E; rw [cw_hi 2 s hs, cw_hi 2 t ht]
    exact PEq.shift (pcomplete_gens hc hg)

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

def W0 : List Lt := [.H 0, .H 1, .C 0, .H 0, .H 1, .C 0, .H 0, .H 1, .C 0]
def W1 : List Lt := [.H 1, .H 2, .C 1, .H 1, .H 2, .C 1, .H 1, .H 2, .C 1]
def XCw : List Lt := [.H 1, .C 0, .H 1, .H 1, .H 1]
def Spw : List Lt := [.H 0, .H 0, .S 0, .H 0, .H 0]

/-- (C6)-(C14), scalars dropped. -/
def base2 : Tbl :=
  [([.C 0, .C 0, .C 0], []),
   (W0 ++ W0, []),
   ([.S 1, .C 0], [.C 0, .S 1]),
   ([.H 1, .H 1, .C 0, .C 0], [.C 0, .H 1, .H 1]),
   ([.S 1] ++ W0, W0 ++ [.S 0]),
   ([.H 1] ++ W0, W0 ++ [.H 0]),
   ([.C 0] ++ W0, W0 ++ [.C 0]),
   ([.S 1] ++ XCw, XCw ++ [.C 0, .S 1] ++ Spw),
   ([.C 0] ++ XCw, XCw ++ [.C 0] ++ Spw ++ [.S 0])]

/-- (C15)-(C18). -/
def base3 : Tbl :=
  [([.C 0, .C 1], [.C 1, .C 0]),
   (W1 ++ W0 ++ W1, W0 ++ W1 ++ W0),
   ([.C 0] ++ W1 ++ W0, W1 ++ W0 ++ [.C 1]),
   ([.H 1, .C 1, .H 1, .H 1, .H 1, .C 0], [.C 0, .H 1, .C 1, .H 1, .H 1, .H 1] ++ W0 ++ [.C 1] ++ W0)]

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

/-- The inverse of a letter, a power of it. -/
def invL : Lt → List Lt
  | .H j => [.H j, .H j, .H j]
  | .S j => [.S j, .S j]
  | .C j => [.C j, .C j]

/-- The inverse of a word. -/
def invW : List Lt → List Lt
  | [] => []
  | x :: l => invW l ++ invL x

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

/-- A stored step: `(0, i, rev, u, v)` a rule, `(1, u, s, t, v)` a free step. -/
def decStep : ℕ × ℕ × ℕ × ℕ × ℕ → Step
  | (0, i, r, u, v) => .rule i (r == 1) (decW u) (decW v)
  | (_, u, s, t, v) => .free (decW u) (decW s) (decW t) (decW v)

/-- A stored library. -/
def decLib (L : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ))) :
    List (List Lt × List Lt × List Step) :=
  L.map fun e => (decW e.1, decW e.2.1, e.2.2.map decStep)

end QCert.QutritClifford
