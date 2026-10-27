/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The four shapes of the encoding of a gate

The encoding of a gate (Definition 8.2) is a word of pair letters
(`hhList`, `zzList`) over one of four lists of pairs, according to whether
the gate is a one- or two-wire gate and whether wires lie below it:

* `pairs1a k`: a one-wire gate on wire `0`, paired with the top wire `k`;
* `pairs1b k ℓ`: a one-wire gate on wire `ℓ + 1`, paired with wire `ℓ`;
* `pairs2a k`: a two-wire gate on wires `0, 1`, paired with the top wire;
* `pairs2b k ℓ`: a two-wire gate on wires `ℓ + 1, ℓ + 2`, paired with
  wire `ℓ`.

For each: the pairs are fit (`PairsOK`), and the state `s` lies in one of
the pairs exactly when the control bit (if any) of `s` is `1`.
-/
import QCert.RealCliffordCH.Sec8.ESem.Pairs
import Mathlib.Data.List.ProdSigma

namespace QCert.RealCliffordCH.Sec8

/-! ## Lists of pairs given by a function -/

theorem mem_flat_map {α : Type*} (D : List α) (F : α → ℕ → ℕ) (u : ℕ) :
    u ∈ flat (D.map fun a => (F a 0, F a 1)) ↔ ∃ a ∈ D, ∃ b < 2, F a b = u := by
  simp only [flat, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, h | h⟩
    · exact ⟨a, ha, 0, by norm_num, h.symm⟩
    · exact ⟨a, ha, 1, by norm_num, h.symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp

theorem flat_map_nodup {α : Type*} (D : List α) (hD : D.Nodup) (F : α → ℕ → ℕ)
    (hinj : ∀ a ∈ D, ∀ a' ∈ D, ∀ b < 2, ∀ b' < 2, F a b = F a' b' → a = a' ∧ b = b') :
    (flat (D.map fun a => (F a 0, F a 1))).Nodup := by
  induction D with
  | nil => simp [flat]
  | cons a D ih =>
    rw [List.nodup_cons] at hD
    have ih' := ih hD.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy))
    have hnot : ∀ b < 2, F a b ∉ flat (D.map fun a => (F a 0, F a 1)) := by
      intro b hb hm
      obtain ⟨a', ha', b', hb', e⟩ := (mem_flat_map D F _).1 hm
      have := (hinj a (by simp) a' (List.mem_cons_of_mem _ ha') b hb b' hb' e.symm).1
      exact hD.1 (this ▸ ha')
    show (F a 0 :: F a 1 :: flat (D.map fun a => (F a 0, F a 1))).Nodup
    rw [List.nodup_cons, List.nodup_cons, List.mem_cons]
    refine ⟨?_, hnot 1 (by norm_num), ih'⟩
    rintro (h | h)
    · exact absurd (hinj a (by simp) a (by simp) 0 (by norm_num) 1 (by norm_num) h).2 (by norm_num)
    · exact hnot 0 (by norm_num) h

theorem grid_nodup (k j : ℕ) : (grid k j).Nodup :=
  List.Nodup.product List.nodup_range List.nodup_range

theorem mem_grid {k j : ℕ} {q : ℕ × ℕ} : q ∈ grid k j ↔ q.1 < 2 ^ k ∧ q.2 < 2 ^ j := by
  obtain ⟨x, y⟩ := q
  simp [grid, List.mem_flatMap, List.mem_map, List.mem_range]

theorem bit_zero (u : ℕ) : bit 0 u = u % 2 := by simp [bit]

theorem bit_one (u : ℕ) : bit 1 u = u / 2 % 2 := by simp [bit]

/-- `X * 2^ℓ + y` with `y < 2^ℓ`, split. -/
theorem split_low (ℓ c : ℕ) : c = c / 2 ^ ℓ * 2 ^ ℓ + c % 2 ^ ℓ := (Nat.div_add_mod' c _).symm

/-! ## A one-wire gate on wire `ℓ + 1` -/

/-- `x 0 b y` (the gate's bit `0`, the bit below `b`). -/
def f1b (ℓ x b y : ℕ) : ℕ := (4 * x + b) * 2 ^ ℓ + y

def pairs1b (k ℓ : ℕ) : List (ℕ × ℕ) := (grid k ℓ).map fun q => (f1b ℓ q.1 0 q.2, f1b ℓ q.1 1 q.2)

theorem pairs1b_ok {n k ℓ : ℕ} (hn : n = k + ℓ + 2) : PairsOK n (ℓ + 1) (pairs1b k ℓ) where
  nodup := flat_map_nodup (grid k ℓ) (grid_nodup k ℓ) (fun q b => f1b ℓ q.1 b q.2) <| by
    rintro ⟨x, y⟩ hq ⟨x', y'⟩ hq' b hb b' hb' e
    rw [mem_grid] at hq hq'
    have h1 := div_mod_mul_add (4 * x + b) hq.2
    have h2 := div_mod_mul_add (4 * x' + b') hq'.2
    simp only [f1b] at e
    rw [e] at h1
    have := h1.1.symm.trans h2.1; have := h1.2.symm.trans h2.2
    simp only [Prod.mk.injEq]; omega
  bit0 := by
    intro u hu
    obtain ⟨⟨x, y⟩, hq, b, hb, rfl⟩ := (mem_flat_map (grid k ℓ) (fun q b => f1b ℓ q.1 b q.2) u).1 hu
    rw [mem_grid] at hq
    simp only [f1b]; rw [bit_mul_add _ 1 _ hq.2]; omega
  lt := by
    intro u hu
    obtain ⟨⟨x, y⟩, hq, b, hb, rfl⟩ := (mem_flat_map (grid k ℓ) (fun q b => f1b ℓ q.1 b q.2) u).1 hu
    rw [mem_grid] at hq
    have h3 : (4 * x + b + 3) * 2 ^ ℓ ≤ (4 * 2 ^ k) * 2 ^ ℓ := Nat.mul_le_mul_right _ (by omega)
    have e : 2 ^ n = 4 * 2 ^ k * 2 ^ ℓ := by subst hn; ring
    simp only [f1b]; rw [e, pow_succ]; nlinarith [hq.2]

theorem mem_pairs1b {n k ℓ s : ℕ} (hn : n = k + ℓ + 2) (hs : s < 2 ^ n) :
    clr (ℓ + 1) s ∈ flat (pairs1b k ℓ) := by
  refine (mem_flat_map (grid k ℓ) (fun q b => f1b ℓ q.1 b q.2) _).2 ?_
  set c := clr (ℓ + 1) s
  have hb : bit (ℓ + 1) c = 0 := bit_clr _ _
  have hc : c < 2 ^ n := lt_of_le_of_lt (clr_le _ _) hs
  have hr := Nat.mod_lt c (Nat.two_pow_pos ℓ)
  have hd := split_low ℓ c
  rw [hd, bit_mul_add _ 1 _ hr] at hb
  have hQ : c / 2 ^ ℓ < 4 * 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ)]
    rw [show 4 * 2 ^ k * 2 ^ ℓ = 2 ^ n by subst hn; ring]; exact hc
  refine ⟨(c / 2 ^ ℓ / 4, c % 2 ^ ℓ), mem_grid.2 ⟨by simp; omega, hr⟩, c / 2 ^ ℓ % 2,
    Nat.mod_lt _ (by norm_num), ?_⟩
  simp only [f1b]
  rw [show 4 * (c / 2 ^ ℓ / 4) + c / 2 ^ ℓ % 2 = c / 2 ^ ℓ by simp at hb; omega]
  exact hd.symm

/-! ## A one-wire gate on wire `0`, paired with the top wire -/

/-- `t x 0`, `t` the top bit. -/
def f1a (K x t : ℕ) : ℕ := t * (2 * K) + x * 2

def pairs1a (K : ℕ) : List (ℕ × ℕ) := (List.range K).map fun x => (f1a K x 0, f1a K x 1)

theorem pairs1a_ok {n K : ℕ} (hn : 2 ^ n = 4 * K) : PairsOK n 0 (pairs1a K) where
  nodup := flat_map_nodup _ List.nodup_range (fun x t => f1a K x t) <| by
    intro x hx x' hx' b hb b' hb' e
    rw [List.mem_range] at hx hx'
    simp only [f1a] at e
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1) with rfl | rfl <;> omega
  bit0 := by
    intro u hu
    obtain ⟨x, hx, b, hb, rfl⟩ := (mem_flat_map _ (fun x t => f1a K x t) u).1 hu
    rw [bit_zero]; simp only [f1a]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega
  lt := by
    intro u hu
    obtain ⟨x, hx, b, hb, rfl⟩ := (mem_flat_map _ (fun x t => f1a K x t) u).1 hu
    rw [List.mem_range] at hx
    rw [hn]; simp only [f1a, pow_zero]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega

theorem mem_pairs1a {n K s : ℕ} (hn : 2 ^ n = 4 * K) (hs : s < 2 ^ n) :
    clr 0 s ∈ flat (pairs1a K) := by
  refine (mem_flat_map _ (fun x t => f1a K x t) _).2 ?_
  set c := clr 0 s
  have hb : bit 0 c = 0 := bit_clr _ _
  have hc : c < 2 ^ n := lt_of_le_of_lt (clr_le _ _) hs
  rw [bit_zero] at hb; rw [hn] at hc
  by_cases h : c < 2 * K
  · exact ⟨c / 2, List.mem_range.2 (by omega), 0, by norm_num, by simp only [f1a]; omega⟩
  · exact ⟨(c - 2 * K) / 2, List.mem_range.2 (by omega), 1, by norm_num,
      by simp only [f1a]; omega⟩

/-! ## A two-wire gate on wires `0, 1`, paired with the top wire -/

/-- `t x 1 0`, `t` the top bit. -/
def f2a (K x t : ℕ) : ℕ := t * (4 * K) + x * 4 + 2

def pairs2a (K : ℕ) : List (ℕ × ℕ) := (List.range K).map fun x => (f2a K x 0, f2a K x 1)

theorem pairs2a_ok {n K : ℕ} (hn : 2 ^ n = 8 * K) : PairsOK n 0 (pairs2a K) where
  nodup := flat_map_nodup _ List.nodup_range (fun x t => f2a K x t) <| by
    intro x hx x' hx' b hb b' hb' e
    rw [List.mem_range] at hx hx'
    simp only [f2a] at e
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1) with rfl | rfl <;> omega
  bit0 := by
    intro u hu
    obtain ⟨x, hx, b, hb, rfl⟩ := (mem_flat_map _ (fun x t => f2a K x t) u).1 hu
    rw [bit_zero]; simp only [f2a]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega
  lt := by
    intro u hu
    obtain ⟨x, hx, b, hb, rfl⟩ := (mem_flat_map _ (fun x t => f2a K x t) u).1 hu
    rw [List.mem_range] at hx
    rw [hn]; simp only [f2a, pow_zero]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega

theorem mem_pairs2a {n K s : ℕ} (hn : 2 ^ n = 8 * K) (hs : s < 2 ^ n) :
    clr 0 s ∈ flat (pairs2a K) ↔ bit 1 s = 1 := by
  rw [pairs2a, show _ ∈ _ ↔ _ from mem_flat_map _ (fun x t => f2a K x t) _,
    ← bit_clr_ne 0 1 s (by norm_num)]
  set c := clr 0 s
  have hb : bit 0 c = 0 := bit_clr _ _
  have hc : c < 2 ^ n := lt_of_le_of_lt (clr_le _ _) hs
  rw [bit_zero] at hb; rw [hn] at hc; rw [bit_one]
  constructor
  · rintro ⟨x, hx, b, hb, e⟩
    rw [List.mem_range] at hx
    rw [← e]; simp only [f2a]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega
  · intro h1
    by_cases h : c < 4 * K
    · exact ⟨c / 4, List.mem_range.2 (by omega), 0, by norm_num, by simp only [f2a]; omega⟩
    · exact ⟨(c - 4 * K) / 4, List.mem_range.2 (by omega), 1, by norm_num,
        by simp only [f2a]; omega⟩

/-! ## A two-wire gate on wires `ℓ + 1, ℓ + 2`, paired with wire `ℓ` -/

/-- `x 1 0 b y` (control `1`, the gate's bit `0`, the bit below `b`). -/
def f2b (ℓ x b y : ℕ) : ℕ := (8 * x + 4 + b) * 2 ^ ℓ + y

def pairs2b (k ℓ : ℕ) : List (ℕ × ℕ) := (grid k ℓ).map fun q => (f2b ℓ q.1 0 q.2, f2b ℓ q.1 1 q.2)

theorem pairs2b_ok {n k ℓ : ℕ} (hn : n = k + ℓ + 3) : PairsOK n (ℓ + 1) (pairs2b k ℓ) where
  nodup := flat_map_nodup (grid k ℓ) (grid_nodup k ℓ) (fun q b => f2b ℓ q.1 b q.2) <| by
    rintro ⟨x, y⟩ hq ⟨x', y'⟩ hq' b hb b' hb' e
    rw [mem_grid] at hq hq'
    have h1 := div_mod_mul_add (8 * x + 4 + b) hq.2
    have h2 := div_mod_mul_add (8 * x' + 4 + b') hq'.2
    simp only [f2b] at e
    rw [e] at h1
    have := h1.1.symm.trans h2.1; have := h1.2.symm.trans h2.2
    simp only [Prod.mk.injEq]; omega
  bit0 := by
    intro u hu
    obtain ⟨⟨x, y⟩, hq, b, hb, rfl⟩ := (mem_flat_map (grid k ℓ) (fun q b => f2b ℓ q.1 b q.2) u).1 hu
    rw [mem_grid] at hq
    simp only [f2b]; rw [bit_mul_add _ 1 _ hq.2]; omega
  lt := by
    intro u hu
    obtain ⟨⟨x, y⟩, hq, b, hb, rfl⟩ := (mem_flat_map (grid k ℓ) (fun q b => f2b ℓ q.1 b q.2) u).1 hu
    rw [mem_grid] at hq
    have h3 : (8 * x + 4 + b + 3) * 2 ^ ℓ ≤ (8 * 2 ^ k) * 2 ^ ℓ := Nat.mul_le_mul_right _ (by omega)
    have e : 2 ^ n = 8 * 2 ^ k * 2 ^ ℓ := by subst hn; ring
    simp only [f2b]; rw [e, pow_succ]; nlinarith [hq.2]

theorem mem_pairs2b {n k ℓ s : ℕ} (hn : n = k + ℓ + 3) (hs : s < 2 ^ n) :
    clr (ℓ + 1) s ∈ flat (pairs2b k ℓ) ↔ bit (ℓ + 2) s = 1 := by
  rw [pairs2b, show _ ∈ _ ↔ _ from mem_flat_map (grid k ℓ) (fun q b => f2b ℓ q.1 b q.2) _,
    ← bit_clr_ne (ℓ + 1) (ℓ + 2) s (by omega)]
  set c := clr (ℓ + 1) s
  have hb : bit (ℓ + 1) c = 0 := bit_clr _ _
  have hc : c < 2 ^ n := lt_of_le_of_lt (clr_le _ _) hs
  have hr := Nat.mod_lt c (Nat.two_pow_pos ℓ)
  have hd := split_low ℓ c
  rw [hd, bit_mul_add _ 1 _ hr] at hb
  rw [hd, bit_mul_add _ 2 _ hr]
  have hQ : c / 2 ^ ℓ < 8 * 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ)]
    rw [show 8 * 2 ^ k * 2 ^ ℓ = 2 ^ n by subst hn; ring]; exact hc
  simp only [pow_one] at hb; simp only [show (2 : ℕ) ^ 2 = 4 by norm_num]
  constructor
  · rintro ⟨⟨x, y⟩, hq, b, hb', e⟩
    rw [mem_grid] at hq
    simp only [f2b] at e
    have h1 := div_mod_mul_add (8 * x + 4 + b) hq.2
    rw [e, ← hd] at h1
    rw [h1.1]; omega
  · intro h1
    refine ⟨(c / 2 ^ ℓ / 8, c % 2 ^ ℓ), mem_grid.2 ⟨by simp; omega, hr⟩, c / 2 ^ ℓ % 2,
      Nat.mod_lt _ (by norm_num), ?_⟩
    simp only [f2b]
    rw [show 8 * (c / 2 ^ ℓ / 8) + 4 + c / 2 ^ ℓ % 2 = c / 2 ^ ℓ by omega]

end QCert.RealCliffordCH.Sec8
