/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Corollary A.5 at symbolic indices, decided on numerals

Two lists of Hadamard-free letters on the numerals `0, …, m-1` that have
the same signed permutation keep having the same signed permutation after
renaming the numerals by any injective map `ρ` (`NL.ren`): at `ρ i` both act
as at `i`, and away from the image of `ρ` both are the identity.  So an
equation between Hadamard-free words at symbolic distinct indices is
Corollary A.5 once it is decided at numerals (`A5ren`, the check by
`decide`).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBTools

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- A letter renamed by `ρ`. -/
def NL.ren (ρ : ℕ → ℕ) : NL → NL
  | .zz a c => .zz (ρ a) (ρ c)
  | .zx a c d => .zx (ρ a) (ρ c) (ρ d)
  | .xx a b c d => .xx (ρ a) (ρ b) (ρ c) (ρ d)

/-- The indices of a letter are below `m`. -/
def NL.Lt (m : ℕ) : NL → Prop
  | .zz a c => a < m ∧ c < m
  | .zx a c d => a < m ∧ c < m ∧ d < m
  | .xx a b c d => a < m ∧ b < m ∧ c < m ∧ d < m

instance (m : ℕ) (x : NL) : Decidable (x.Lt m) := by
  cases x <;> unfold NL.Lt <;> infer_instance

theorem swN_ltm {m c d i : ℕ} (hc : c < m) (hd : d < m) (hi : i < m) : swN c d i < m := by
  unfold swN; split_ifs <;> assumption

section Ren

variable {ρ : ℕ → ℕ} {m : ℕ} (hρ : ∀ i < m, ∀ j < m, ρ i = ρ j → i = j)
include hρ

theorem swN_ren {c d i : ℕ} (hc : c < m) (hd : d < m) (hi : i < m) :
    swN (ρ c) (ρ d) (ρ i) = ρ (swN c d i) := by
  unfold swN
  by_cases h1 : i = c
  · subst h1; simp
  · have h1' : ρ i ≠ ρ c := fun e => h1 (hρ i hi c hc e)
    by_cases h2 : i = d
    · subst h2; simp [h1, h1']
    · have h2' : ρ i ≠ ρ d := fun e => h2 (hρ i hi d hd e)
      simp [h1, h1', h2, h2']

theorem perm_ren {x : NL} (hx : x.Lt m) {i : ℕ} (hi : i < m) :
    (x.ren ρ).perm (ρ i) = ρ (x.perm i) ∧ x.perm i < m ∧ (x.ren ρ).neg (ρ i) = x.neg i := by
  have inj : ∀ {u v}, u < m → v < m → (ρ u = ρ v ↔ u = v) := fun hu hv =>
    ⟨hρ _ hu _ hv, fun e => e ▸ rfl⟩
  cases x with
  | zz a c =>
    obtain ⟨ha, hc⟩ := hx
    refine ⟨rfl, hi, ?_⟩
    simp only [NL.ren, NL.neg, inj hi ha, inj hi hc]
  | zx a c d =>
    obtain ⟨ha, hc, hd⟩ := hx
    refine ⟨swN_ren hρ hc hd hi, swN_ltm hc hd hi, ?_⟩
    simp only [NL.ren, NL.neg, swN_ren hρ hc hd hi, inj (swN_ltm hc hd hi) ha]
  | xx a b c d =>
    obtain ⟨ha, hb, hc, hd⟩ := hx
    refine ⟨?_, swN_ltm ha hb (swN_ltm hc hd hi), rfl⟩
    simp only [NL.ren, NL.perm, swN_ren hρ hc hd hi, swN_ren hρ ha hb (swN_ltm hc hd hi)]

theorem permL_ren {L : List NL} (hL : ∀ x ∈ L, x.Lt m) {i : ℕ} (hi : i < m) :
    permL (L.map (NL.ren ρ)) (ρ i) = ρ (permL L i) ∧ permL L i < m ∧
      negL (L.map (NL.ren ρ)) (ρ i) = negL L i := by
  induction L with
  | nil => exact ⟨rfl, hi, rfl⟩
  | cons x L ih =>
    obtain ⟨e1, e2, e3⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    obtain ⟨f1, f2, f3⟩ := perm_ren hρ (hL x (by simp)) e2
    refine ⟨?_, f2, ?_⟩
    · simp only [List.map_cons, permL, e1, f1]
    · simp only [List.map_cons, negL, e1, f3, e3]

end Ren

theorem perm_ren_out {ρ : ℕ → ℕ} {m : ℕ} {x : NL} (hx : x.Lt m) {j : ℕ}
    (hj : ∀ i < m, ρ i ≠ j) : (x.ren ρ).perm j = j ∧ (x.ren ρ).neg j = false := by
  cases x with
  | zz a c =>
    obtain ⟨ha, hc⟩ := hx
    refine ⟨rfl, ?_⟩
    simp [NL.ren, NL.neg, Ne.symm (hj a ha), Ne.symm (hj c hc)]
  | zx a c d =>
    obtain ⟨ha, hc, hd⟩ := hx
    have e : swN (ρ c) (ρ d) j = j := by simp [swN, Ne.symm (hj c hc), Ne.symm (hj d hd)]
    refine ⟨e, ?_⟩
    simp [NL.ren, NL.neg, e, Ne.symm (hj a ha)]
  | xx a b c d =>
    obtain ⟨ha, hb, hc, hd⟩ := hx
    refine ⟨?_, rfl⟩
    simp [NL.ren, NL.perm, swN, Ne.symm (hj a ha), Ne.symm (hj b hb), Ne.symm (hj c hc),
      Ne.symm (hj d hd)]

theorem permL_ren_out {ρ : ℕ → ℕ} {m : ℕ} {L : List NL} (hL : ∀ x ∈ L, x.Lt m) {j : ℕ}
    (hj : ∀ i < m, ρ i ≠ j) :
    permL (L.map (NL.ren ρ)) j = j ∧ negL (L.map (NL.ren ρ)) j = false := by
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons x L ih =>
    obtain ⟨e1, e2⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    obtain ⟨f1, f2⟩ := perm_ren_out (hL x (by simp)) hj
    simp only [List.map_cons, permL, negL, e1, e2, f1, f2]
    simp

theorem ren_bd {ρ : ℕ → ℕ} {m : ℕ} (hbd : ∀ i < m, ρ i < 2 ^ n) {x : NL} (hx : x.Lt m) :
    (x.ren ρ).Bd n := by
  cases x with
  | zz a c => exact ⟨hbd a hx.1, hbd c hx.2⟩
  | zx a c d => exact ⟨hbd a hx.1, hbd c hx.2.1, hbd d hx.2.2⟩
  | xx a b c d => exact ⟨hbd a hx.1, hbd b hx.2.1, hbd c hx.2.2.1, hbd d hx.2.2.2⟩

theorem ren_pr {ρ : ℕ → ℕ} {m : ℕ} (hρ : ∀ i < m, ∀ j < m, ρ i = ρ j → i = j) {x : NL}
    (hx : x.Lt m) (hp : x.Pr) : (x.ren ρ).Pr := by
  cases x with
  | zz a c => trivial
  | zx a c d => exact fun e => hp (hρ c hx.2.1 d hx.2.2 e)
  | xx a b c d =>
    exact ⟨fun e => hp.1 (hρ a hx.1 b hx.2.1 e), fun e => hp.2 (hρ c hx.2.2.1 d hx.2.2.2 e)⟩

instance (x : NL) : Decidable x.Pr := by
  cases x <;> unfold NL.Pr <;> infer_instance

/-- Renaming numerals keeps two signed permutations equal. -/
theorem ren_point {m : ℕ} (L L' : List NL)
    (hc : (∀ x ∈ L, x.Lt m ∧ x.Pr) ∧ (∀ x ∈ L', x.Lt m ∧ x.Pr) ∧
      ∀ i < m, permL L i = permL L' i ∧ negL L i = negL L' i)
    {ρ : ℕ → ℕ} (hρ : ∀ i < m, ∀ j < m, ρ i = ρ j → i = j) (j : ℕ) :
    permL (L.map (NL.ren ρ)) j = permL (L'.map (NL.ren ρ)) j ∧
      negL (L.map (NL.ren ρ)) j = negL (L'.map (NL.ren ρ)) j := by
  obtain ⟨hL, hL', hc⟩ := hc
  by_cases hj : ∃ i < m, ρ i = j
  · obtain ⟨i, hi, rfl⟩ := hj
    obtain ⟨a1, -, a3⟩ := permL_ren hρ (fun x hx => (hL x hx).1) hi
    obtain ⟨b1, -, b3⟩ := permL_ren hρ (fun x hx => (hL' x hx).1) hi
    rw [a1, b1, a3, b3, (hc i hi).1, (hc i hi).2]
    exact ⟨rfl, rfl⟩
  · push Not at hj
    obtain ⟨a1, a2⟩ := permL_ren_out (fun x hx => (hL x hx).1) hj
    obtain ⟨b1, b2⟩ := permL_ren_out (fun x hx => (hL' x hx).1) hj
    rw [a1, b1, a2, b2]
    exact ⟨rfl, rfl⟩

/-- An inverse pair of words on numerals, renamed. -/
theorem ren_inv {m : ℕ} (L : List NL)
    (hc : (∀ x ∈ L, x.Lt m ∧ x.Pr) ∧ (∀ x ∈ ([] : List NL), x.Lt m ∧ x.Pr) ∧
      ∀ i < m, permL L i = permL [] i ∧ negL L i = negL [] i)
    {ρ : ℕ → ℕ} (hρ : ∀ i < m, ∀ j < m, ρ i = ρ j → i = j) (j : ℕ) :
    permL (L.map (NL.ren ρ)) j = j ∧ negL (L.map (NL.ren ρ)) j = false :=
  ren_point L [] hc hρ j

theorem ren_bdL {ρ : ℕ → ℕ} {m : ℕ} (hbd : ∀ i < m, ρ i < 2 ^ n) {L : List NL}
    (hL : ∀ x ∈ L, x.Lt m ∧ x.Pr) : ∀ y ∈ L.map (NL.ren ρ), y.Bd n := by
  intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact ren_bd hbd (hL x hx).1

theorem ren_prL {ρ : ℕ → ℕ} {m : ℕ} (hρ : ∀ i < m, ∀ j < m, ρ i = ρ j → i = j) {L : List NL}
    (hL : ∀ x ∈ L, x.Lt m ∧ x.Pr) : ∀ y ∈ L.map (NL.ren ρ), y.Pr := by
  intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact ren_pr hρ (hL x hx).1 (hL x hx).2

/-- **Corollary A.5 by renaming**: an equation between Hadamard-free words on
the numerals `0, …, m-1`, decided there, holds after renaming them injectively. -/
theorem A5ren (hN : 4 ≤ 2 ^ n) {m : ℕ} (L L' : List NL)
    (hc : (∀ x ∈ L, x.Lt m ∧ x.Pr) ∧ (∀ x ∈ L', x.Lt m ∧ x.Pr) ∧
      ∀ i < m, permL L i = permL L' i ∧ negL L i = negL L' i)
    {ρ : ℕ → ℕ} (hρ : ∀ i < m, ∀ j < m, ρ i = ρ j → i = j) (hbd : ∀ i < m, ρ i < 2 ^ n) :
    D8 n ((L.map (NL.ren ρ)).map (NL.toPG n)) ((L'.map (NL.ren ρ)).map (NL.toPG n)) :=
  A5NL hN (ren_bdL hbd hc.1) (ren_bdL hbd hc.2.1) (ren_prL hρ hc.1) (ren_prL hρ hc.2.1)
    fun j _ => ren_point L L' hc hρ j

/-- The renaming given by a list of distinct indices. -/
def rv (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

theorem rv_eq {l : List ℕ} {i : ℕ} (hi : i < l.length) : rv l i = l[i] := by
  unfold rv
  simp [List.getD, hi]

theorem rv_inj {l : List ℕ} (h : l.Nodup) :
    ∀ i < l.length, ∀ j < l.length, rv l i = rv l j → i = j := by
  intro i hi j hj e
  rw [rv_eq hi, rv_eq hj] at e
  exact (List.Nodup.getElem_inj_iff h).1 e

theorem rv_bd {l : List ℕ} {N : ℕ} (h : ∀ x ∈ l, x < N) : ∀ i < l.length, rv l i < N := by
  intro i hi
  rw [rv_eq hi]
  exact h _ (List.getElem_mem hi)

/-- Corollary A.5 by renaming, the renaming given by a list of distinct indices. -/
theorem A5v (hN : 4 ≤ 2 ^ n) {m : ℕ} (l : List ℕ) (hm : l.length = m) (hnd : l.Nodup)
    (hb : ∀ x ∈ l, x < 2 ^ n) (L L' : List NL)
    (hc : (∀ x ∈ L, x.Lt m ∧ x.Pr) ∧ (∀ x ∈ L', x.Lt m ∧ x.Pr) ∧
      ∀ i < m, permL L i = permL L' i ∧ negL L i = negL L' i) :
    D8 n ((L.map (NL.ren (rv l))).map (NL.toPG n)) ((L'.map (NL.ren (rv l))).map (NL.toPG n)) :=
  A5ren hN L L' hc (hm ▸ rv_inj hnd) (hm ▸ rv_bd hb)

/-- An inverse pair, renamed by a list of distinct indices. -/
theorem inv_v {m : ℕ} (l : List ℕ) (hm : l.length = m) (hnd : l.Nodup) (L : List NL)
    (hc : (∀ x ∈ L, x.Lt m ∧ x.Pr) ∧ (∀ x ∈ ([] : List NL), x.Lt m ∧ x.Pr) ∧
      ∀ i < m, permL L i = permL [] i ∧ negL L i = negL [] i) (j : ℕ) :
    permL (L.map (NL.ren (rv l))) j = j ∧ negL (L.map (NL.ren (rv l))) j = false :=
  ren_inv L hc (hm ▸ rv_inj hnd) j

end QCert.RealCliffordCH.Sec8
