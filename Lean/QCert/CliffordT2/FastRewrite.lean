/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checked rewriting on numbers

The same certificates as `Rewrite.lean`, replayed on words coded as
numbers: a word `a₀ a₁ … aₙ₋₁` is `κ a₀ + 16 κ a₁ + ⋯ + 16ⁿ⁻¹ κ aₙ₋₁` for a
coding `κ` of the letters by `1 … 15` (`enc`).  A rewriting step is then a
few operations on numbers, which the kernel evaluates eagerly (with GMP),
where the list version builds and re-traverses lazy terms; this makes
certificates of hundreds of thousands of steps checkable.  The soundness
of the replay (`derivable_of_chunks`) is proved once, from the arithmetic
of the coding.

The kernel pays for every unfolding and almost nothing for arithmetic on
literals, so the replay is written for it: the rules are compiled once to
the codes and lengths of their sides (`compileRules`), a step looks its
rule up by primitive recursion (`nthC`) and tests with `Nat.beq`/`Nat.ble`
rather than `Decidable` instances (`replaceB`), and the loops are explicit
`Nat.rec`/`List.rec`.  This took the replay of 5 000 steps from 4.3 s to
1.3 s of kernel time.
-/
import QCert.CliffordT2.Rewrite
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QCert

universe u

section Enc

variable {α : Type u} (κ : α → ℕ)

/-- The number coding a word, the first letter as the lowest digit. -/
def enc : List α → ℕ
  | [] => 0
  | a :: w => κ a + 16 * enc w

theorem enc_append (u v : List α) : enc κ (u ++ v) = enc κ u + 16 ^ u.length * enc κ v := by
  induction u with
  | nil => simp [enc]
  | cons a u ih => simp only [List.cons_append, enc, ih, List.length_cons, pow_succ]; ring

variable {κ}

theorem enc_lt (hκ : ∀ a, κ a < 16) (w : List α) : enc κ w < 16 ^ w.length := by
  induction w with
  | nil => simp [enc]
  | cons a w ih =>
    simp only [enc, List.length_cons, pow_succ]
    have := hκ a
    nlinarith

theorem enc_take_drop (hκ : ∀ a, κ a < 16) (w : List α) (p : ℕ) :
    enc κ w % 16 ^ p = enc κ (w.take p) ∧ enc κ w / 16 ^ p = enc κ (w.drop p) := by
  by_cases hp : p ≤ w.length
  · have e := enc_append κ (w.take p) (w.drop p)
    rw [List.take_append_drop, List.length_take_of_le hp] at e
    have hlt := enc_lt hκ (w.take p)
    rw [List.length_take_of_le hp] at hlt
    have hpos : 0 < 16 ^ p := by positivity
    constructor
    · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
  · rw [not_le] at hp
    have hlt := enc_lt hκ w
    have : 16 ^ w.length ≤ 16 ^ p := Nat.pow_le_pow_right (by norm_num) hp.le
    rw [List.take_of_length_le hp.le, List.drop_of_length_le hp.le]
    have h' : enc κ w < 16 ^ p := lt_of_lt_of_le hlt this
    exact ⟨Nat.mod_eq_of_lt h', by simp [enc, Nat.div_eq_of_lt h']⟩

theorem enc_injective (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ) :
    Function.Injective (enc κ) := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v => simp only [enc] at h; have := (hκ b).1; omega
  | cons a u ih =>
    intro v h
    cases v with
    | nil => simp only [enc] at h; have := (hκ a).1; omega
    | cons b v =>
      simp only [enc] at h
      have ha := (hκ a).2
      have hb := (hκ b).2
      have h1 : κ a = κ b := by omega
      have h2 : enc κ u = enc κ v := by omega
      rw [hinj h1, ih h2]

theorem length_le_of_pow (hκ : ∀ a, 0 < κ a ∧ κ a < 16) {w : List α} {p : ℕ}
    (h : p = 0 ∨ 16 ^ p ≤ 16 * enc κ w) : p ≤ w.length := by
  rcases h with h | h
  · omega
  · by_contra hp
    rw [not_le] at hp
    have hlt := enc_lt (fun a => (hκ a).2) w
    have : 16 ^ (w.length + 1) ≤ 16 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    rw [pow_succ] at this
    omega

end Enc

variable {α : Type u} [DecidableEq α] {Γ : WRel α} (κ : α → ℕ)

/-- Replace, at position `p`, an occurrence of `l` by `r`, on codes. -/
def replaceN (l r : List α) (p c : ℕ) : Option ℕ :=
  if (p = 0 ∨ 16 ^ p ≤ 16 * c) ∧ c / 16 ^ p % 16 ^ l.length = enc κ l then
    some (c % 16 ^ p + 16 ^ p * (enc κ r + 16 ^ r.length * (c / 16 ^ p / 16 ^ l.length)))
  else none

/-- A rule compiled to numbers: the codes and the lengths of its two sides,
computed once per rule rather than once per step. -/
abbrev CRule := ℕ × ℕ × ℕ × ℕ

/-- The compiled form of a rule. -/
def compileRule (ρ : Rule Γ) : CRule := (enc κ ρ.lhs, ρ.lhs.length, enc κ ρ.rhs, ρ.rhs.length)

/-- The compiled forms of the rules of a certificate. -/
def compileRules (rules : List (Rule Γ)) : List CRule := rules.map (compileRule κ)

/-- `tbl[i]?` by primitive recursion, which the kernel unfolds directly
(`GetElem?` on lists goes through `List.length`, a `Decidable` test and
`brecOn`). -/
def nthC (tbl : List CRule) : ℕ → Option CRule :=
  List.rec (motive := fun _ => ℕ → Option CRule) (fun _ => none)
    (fun a _ ih i => Nat.rec (motive := fun _ => Option CRule) (some a) (fun i' _ => ih i') i) tbl

/-- `replaceN` on a compiled rule, with Boolean tests: `Nat.beq` and
`Nat.ble` on literals are one kernel operation each, where a `Decidable`
instance costs a dozen unfoldings. -/
def replaceB (lc ll rc rl p c : ℕ) : Option ℕ :=
  bif (p.beq 0 || Nat.ble (16 ^ p) (16 * c)) && Nat.beq (c / 16 ^ p % 16 ^ ll) lc then
    some (c % 16 ^ p + 16 ^ p * (rc + 16 ^ rl * (c / 16 ^ p / 16 ^ ll)))
  else none

/-- One packed step on codes: bit 0 is the direction, bits 1-12 the rule,
the rest the position. -/
def stepC (tbl : List CRule) (c s : ℕ) : Option ℕ :=
  match nthC tbl (s / 2 % 4096) with
  | none => none
  | some (lc, ll, rc, rl) =>
    bif (s % 2).beq 1 then replaceB lc ll rc rl (s / 2 / 4096) c
    else replaceB rc rl lc ll (s / 2 / 4096) c

/-- Replay `n` packed steps on codes, by direct recursion on `n`. -/
def runFast (tbl : List CRule) (n : ℕ) : ℕ → ℕ → Option ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Option ℕ) (fun _ c => some c)
    (fun _ ih code c =>
      match stepC tbl c (code % 33554432) with
      | some c' => ih (code / 33554432) c'
      | none => none) n

/-- Replay a certificate cut into chunks `(n, code)` of packed steps, so that
no number in the kernel computation is large. -/
def runChunks (tbl : List CRule) : List (ℕ × ℕ) → ℕ → Option ℕ
  | [], c => some c
  | (n, code) :: cs, c =>
    match runFast tbl n code c with
    | some c' => runChunks tbl cs c'
    | none => none

variable {κ}

omit [DecidableEq α] in
theorem replaceN_sound (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    {l r w : List α} {p c' : ℕ}
    (hl : Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r))
    (h : replaceN κ l r p (enc κ w) = some c') :
    ∃ w', c' = enc κ w' ∧ Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold replaceN at h
  split_ifs at h with hc
  obtain ⟨hp, hm⟩ := hc
  simp only [Option.some.injEq] at h
  have h16 : ∀ a, κ a < 16 := fun a => (hκ a).2
  have hpw := length_le_of_pow hκ hp
  obtain ⟨hmod, hdiv⟩ := enc_take_drop h16 w p
  obtain ⟨hmod2, hdiv2⟩ := enc_take_drop h16 (w.drop p) l.length
  rw [hdiv, hmod2] at hm
  have htake : (w.drop p).take l.length = l := enc_injective hκ hinj hm
  have hw : w = w.take p ++ l ++ (w.drop p).drop l.length := by
    conv_lhs => rw [← List.take_append_drop p w, ← List.take_append_drop l.length (w.drop p)]
    rw [htake, List.append_assoc]
  refine ⟨w.take p ++ r ++ (w.drop p).drop l.length, ?_, ?_⟩
  · rw [← h, hmod, hdiv, hdiv2, enc_append, enc_append, List.length_append,
      List.length_take_of_le hpw, pow_add]
    ring
  · have := derivable_ofList_append_middle hl (w.take p) ((w.drop p).drop l.length)
    rwa [← hw] at this

omit [DecidableEq α] in
/-- The Boolean replacement on the compiled form of a rule is `replaceN`. -/
theorem replaceB_eq (l r : List α) (p c : ℕ) :
    replaceB (enc κ l) l.length (enc κ r) r.length p c = replaceN κ l r p c := by
  unfold replaceB replaceN
  have key : ((p.beq 0 || Nat.ble (16 ^ p) (16 * c)) &&
      Nat.beq (c / 16 ^ p % 16 ^ l.length) (enc κ l)) = true ↔
      (p = 0 ∨ 16 ^ p ≤ 16 * c) ∧ c / 16 ^ p % 16 ^ l.length = enc κ l := by
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq]
  cases hb : ((p.beq 0 || Nat.ble (16 ^ p) (16 * c)) &&
      Nat.beq (c / 16 ^ p % 16 ^ l.length) (enc κ l))
  · rw [if_neg (fun h => Bool.false_ne_true (hb.symm.trans (key.2 h)))]; rfl
  · rw [if_pos (key.1 hb)]; rfl

/-- A looked-up compiled rule is one of the table. -/
theorem nthC_mem {tbl : List CRule} {i : ℕ} {x : CRule} (h : nthC tbl i = some x) : x ∈ tbl := by
  induction tbl generalizing i with
  | nil =>
    have h' : (none : Option CRule) = some x := h
    cases h'
  | cons a tbl ih =>
    cases i with
    | zero =>
      have := Option.some.inj (show some a = some x from h)
      subst this
      exact List.mem_cons.2 (Or.inl rfl)
    | succ i => exact List.mem_cons.2 (Or.inr (ih (show nthC tbl i = some x from h)))

omit [DecidableEq α] in
theorem stepC_sound (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) {w : List α} {s c' : ℕ}
    (h : stepC (compileRules κ rules) (enc κ w) s = some c') :
    ∃ w', c' = enc κ w' ∧ Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold stepC at h
  cases hx : nthC (compileRules κ rules) (s / 2 % 4096) with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some x =>
    obtain ⟨lc, ll, rc, rl⟩ := x
    rw [hx] at h
    obtain ⟨ρ, -, hρ⟩ := List.mem_map.1 (nthC_mem hx)
    simp only [compileRule, Prod.mk.injEq] at hρ
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hρ
    simp only [replaceB_eq] at h
    cases hs : (s % 2).beq 1 <;> rw [hs] at h
    · exact replaceN_sound hκ hinj ρ.sound.symm h
    · exact replaceN_sound hκ hinj ρ.sound h

theorem runFast_sound (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (n : ℕ) :
    ∀ (code : ℕ) (w : List α) (c' : ℕ),
      runFast (compileRules κ rules) n code (enc κ w) = some c' →
      ∃ w', c' = enc κ w' ∧ Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction n with
  | zero =>
    intro code w c' h
    simp only [runFast, Nat.rec_zero, Option.some.injEq] at h
    exact ⟨w, h.symm, Derivable.refl _⟩
  | succ n ih =>
    intro code w c' h
    simp only [runFast] at h
    split at h
    · rename_i c₁ h₁
      obtain ⟨w₁, rfl, d₁⟩ := stepC_sound hκ hinj rules h₁
      obtain ⟨w₂, rfl, d₂⟩ := ih (code / 33554432) w₁ c' h
      exact ⟨w₂, rfl, d₁.trans d₂⟩
    · simp at h

theorem runChunks_sound (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (cs : List (ℕ × ℕ)) :
    ∀ (w : List α) (c' : ℕ), runChunks (compileRules κ rules) cs (enc κ w) = some c' →
      ∃ w', c' = enc κ w' ∧ Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction cs with
  | nil =>
    intro w c' h
    simp only [runChunks, Option.some.injEq] at h
    exact ⟨w, h.symm, Derivable.refl _⟩
  | cons nc cs ih =>
    intro w c' h
    obtain ⟨n, code⟩ := nc
    simp only [runChunks] at h
    split at h
    · rename_i c₁ h₁
      obtain ⟨w₁, rfl, d₁⟩ := runFast_sound hκ hinj rules n code w c₁ h₁
      obtain ⟨w₂, rfl, d₂⟩ := ih w₁ c' h
      exact ⟨w₂, rfl, d₁.trans d₂⟩
    · simp at h

/-- A rule proved by a chunked certificate replayed on codes. -/
def Rule.byChunks (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (l r : List α) (cs : List (ℕ × ℕ))
    (h : runChunks (compileRules κ rules) cs (enc κ l) = some (enc κ r)) : Rule Γ :=
  ⟨l, r, by
    obtain ⟨w', hw', d⟩ := runChunks_sound hκ hinj rules cs _ _ h
    have e := enc_injective hκ hinj hw'
    subst e
    exact d⟩

/-- A chunked certificate replayed on codes proves an equation. -/
theorem derivable_of_chunks (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (w v : Word α) (cs : List (ℕ × ℕ))
    (h : runChunks (compileRules κ rules) cs (enc κ (FreeMonoid.toList w)) =
      some (enc κ (FreeMonoid.toList v))) :
    Derivable Γ w v := by
  obtain ⟨w', hw', d⟩ := runChunks_sound hκ hinj rules cs _ _ h
  have := enc_injective hκ hinj hw'
  subst this
  simpa using d

/-- A rule proved by a packed certificate replayed on codes. -/
def Rule.byFast (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (l r : List α) (n code : ℕ)
    (h : runFast (compileRules κ rules) n code (enc κ l) = some (enc κ r)) : Rule Γ :=
  ⟨l, r, by
    obtain ⟨w', hw', d⟩ := runFast_sound hκ hinj rules n code _ _ h
    have e := enc_injective hκ hinj hw'
    subst e
    exact d⟩

/-- A packed certificate replayed on codes proves an equation. -/
theorem derivable_of_fast (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (w v : Word α) (n code : ℕ)
    (h : runFast (compileRules κ rules) n code (enc κ (FreeMonoid.toList w)) =
      some (enc κ (FreeMonoid.toList v))) :
    Derivable Γ w v := by
  obtain ⟨w', hw', d⟩ := runFast_sound hκ hinj rules n code _ _ h
  have := enc_injective hκ hinj hw'
  subst this
  simpa using d

end QCert
