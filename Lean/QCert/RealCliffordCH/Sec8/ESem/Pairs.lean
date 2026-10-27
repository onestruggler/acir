/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Products of letters acting on disjoint pairs of indices

The letters of the encoding of a gate (Definition 8.2) are products of two
level matrices, each on a pair of indices `G⁻¹(u), G⁻¹(u + 2^p)` (`u` with
its bit on the target wire `p` cleared).  When all the `u` are distinct,
the word acts on each pair by the factor on it and as the identity off the
pairs (`pWord_hhList`, `pWord_zzList`).
-/
import QCert.RealCliffordCH.Sec8.ESem.Basic

namespace QCert.RealCliffordCH.Sec8

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

theorem one_gx {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) :
    (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) (gx n s) (gx n t) = if s = t then 1 else 0 := by
  rw [one_apply]; simp only [gx_eq_iff hs ht]

theorem mul_apply_congr_right {A B C : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} {i j : Fin (2 ^ n)}
    (h : ∀ k, A i k * B k j = A i k * C k j) : (A * B) i j = (A * C) i j := by
  simp only [mul_apply]; exact Finset.sum_congr rfl fun k _ => h k

theorem exists_gx (k : Fin (2 ^ n)) : ∃ v < 2 ^ n, gx n v = k := ⟨gray k, gray_lt k.2, gx_gray k⟩

/-- A product of matrices each acting on the pair of `u`, over distinct `u`. -/
theorem prod_pairs {p : ℕ} (G : ℕ → ℕ → R) (E : ℕ → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) :
    ∀ (L : List ℕ), L.Nodup →
    (∀ u ∈ L, ∀ s < 2 ^ n, ∀ t < 2 ^ n, E u (gx n s) (gx n t) =
      if clr p s = u ∧ clr p t = u then G (bit p s) (bit p t) else if s = t then 1 else 0) →
    ∀ s < 2 ^ n, ∀ t < 2 ^ n, (L.map E).prod (gx n s) (gx n t) =
      if clr p s ∈ L ∧ clr p t = clr p s then G (bit p s) (bit p t) else if s = t then 1 else 0
  | [], _, _, s, hs, t, ht => by simp [one_gx hs ht]
  | u :: L, hL, hE, s, hs, t, ht => by
    rw [List.nodup_cons] at hL
    have ih := prod_pairs G E L hL.2 (fun u' hu' => hE u' (List.mem_cons_of_mem _ hu'))
    rw [List.map_cons, List.prod_cons]
    by_cases hsu : clr p s = u
    · rw [mul_apply_congr_right (C := 1) ?_, Matrix.mul_one, hE u (by simp) s hs t ht]
      · by_cases htu : clr p t = u
        · simp [hsu, htu]
        · have hst : s ≠ t := fun h => htu (h ▸ hsu)
          simp [hsu, htu, hst]
      · intro k
        obtain ⟨v, hv, rfl⟩ := exists_gx k
        rw [ih v hv t ht, one_gx hv ht]
        by_cases hvu : clr p v = u
        · rw [hvu, if_neg (fun h => hL.1 h.1)]
        · have hsv : s ≠ v := fun h => hvu (h ▸ hsu)
          rw [hE u (by simp) s hs v hv]
          simp [hvu, hsv]
    · rw [show (E u * (L.map E).prod) (gx n s) (gx n t) =
          ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) * (L.map E).prod) (gx n s) (gx n t)
          from ?_, Matrix.one_mul,
          ih s hs t ht]
      · simp [hsu]
      · simp only [mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        obtain ⟨v, hv, rfl⟩ := exists_gx k
        rw [hE u (by simp) s hs v hv, if_neg (fun h => hsu h.1), one_gx hs hv]

/-! ## The two kinds of factors -/

/-- The entries of `H` on bits. -/
def hEnt (σ : R) (a b : ℕ) : R := if a = 1 ∧ b = 1 then -σ else σ

/-- The entries of `Z` on bits. -/
def zEnt (a b : ℕ) : R := if a = b then (if a = 1 then -1 else 1) else 0

section Pair

variable {p u : ℕ} (hu : bit p u = 0) (hlt : u + 2 ^ p < 2 ^ n)
include hu hlt

theorem pair_lt (b : ℕ) (hb : b < 2) : u + b * 2 ^ p < 2 ^ n := by
  have := Nat.two_pow_pos p
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega

theorem clr_pair {v : ℕ} (hv : clr p v = u) : v = u + bit p v * 2 ^ p := by
  rw [← hv, clr_add_bit]

theorem clr_pair_iff {v : ℕ} : clr p v = u ↔ v = u ∨ v = u + 2 ^ p := by
  constructor
  · intro hv
    rcases (by have := bit_lt p v; omega : bit p v = 0 ∨ bit p v = 1) with h | h
    · left; rw [clr_pair hu hlt hv, h]; simp
    · right; rw [clr_pair hu hlt hv, h]; simp
  · rintro (rfl | rfl)
    · exact clr_of_bit hu
    · exact (bit_add_pow hu).2

/-- The pair of `u`, indexed by the bit on wire `p`. -/
def pairF (n p u : ℕ) : Fin 2 → Fin (2 ^ n) := ![gx n u, gx n (u + 2 ^ p)]

omit hu hlt in
theorem pairF_apply (b : Fin 2) : pairF n p u b = gx n (u + b * 2 ^ p) := by
  fin_cases b <;> simp [pairF]

theorem pairF_inj : Function.Injective (pairF n p u) := by
  intro a b h
  rw [pairF_apply, pairF_apply] at h
  have := gx_inj (pair_lt hu hlt a a.2) (pair_lt hu hlt b b.2) h
  have hp := Nat.two_pow_pos p
  ext; rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with ha | ha <;>
    rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;> subst ha hb <;> simp_all

theorem pairF_of {v : ℕ} (hv : clr p v = u) : gx n v = pairF n p u ⟨bit p v, bit_lt p v⟩ := by
  rw [pairF_apply]; congr 1; exact clr_pair hu hlt hv

theorem pairF_ne {v : ℕ} (hvn : v < 2 ^ n) (hv : clr p v ≠ u) (b : Fin 2) : pairF n p u b ≠ gx n v := by
  rw [pairF_apply]; intro h
  have := gx_inj (pair_lt hu hlt b b.2) hvn h
  apply hv; rw [clr_pair_iff hu hlt]
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with hb | hb <;> subst hb <;> simp_all

theorem hM_pair (σ : R) {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) :
    hM σ (gx n u) (gx n (u + 2 ^ p)) (gx n s) (gx n t) =
      if clr p s = u ∧ clr p t = u then hEnt σ (bit p s) (bit p t) else if s = t then 1 else 0 := by
  have e : hM σ (gx n u) (gx n (u + 2 ^ p)) = levelMat (pairF n p u) !![σ, σ; σ, -σ] := rfl
  rw [e]
  by_cases hs' : clr p s = u
  · by_cases ht' : clr p t = u
    · rw [if_pos ⟨hs', ht'⟩, pairF_of hu hlt hs', pairF_of hu hlt ht',
        levelMat_apply_apply (pairF_inj hu hlt)]
      have a := bit_lt p s; have b := bit_lt p t
      generalize bit_lt p s = ha; generalize bit_lt p t = hb
      generalize bit p s = x at *; generalize bit p t = y at *
      rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
        rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp [hEnt, Fin.zero_eta, Fin.mk_one]
    · rw [if_neg (fun h => ht' h.2), levelMat_apply_of_right _ _ (pairF_ne hu hlt ht ht'),
        one_gx hs ht, if_neg (show s ≠ t from fun h => ht' (h ▸ hs'))]
  · rw [if_neg (fun h => hs' h.1), levelMat_apply_of_left _ (pairF_ne hu hlt hs hs'), one_gx hs ht]

theorem negM_pair {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) :
    (negM (gx n (u + 2 ^ p)) : Matrix _ _ R) (gx n s) (gx n t) =
      if clr p s = u ∧ clr p t = u then zEnt (bit p s) (bit p t) else if s = t then 1 else 0 := by
  have hn : ∀ i j : Fin (2 ^ n), (negM (gx n (u + 2 ^ p)) : Matrix _ _ R) i j =
      if i = j then (if i = gx n (u + 2 ^ p) then -1 else 1) else 0 := by
    intro i j
    have hf : Function.Injective ![gx n (u + 2 ^ p)] := fun x y _ => Subsingleton.elim x y
    unfold negM
    by_cases hi : i = gx n (u + 2 ^ p)
    · by_cases hj : j = gx n (u + 2 ^ p)
      · subst hi hj
        have := levelMat_apply_apply hf (!![-1] : Matrix (Fin 1) (Fin 1) R) 0 0
        simpa using this
      · rw [levelMat_apply_of_right _ _ (fun l => by fin_cases l; exact Ne.symm hj)]
        simp [one_apply, hi, Ne.symm hj, hj]
    · rw [levelMat_apply_of_left _ (fun l => by fin_cases l; exact Ne.symm hi)]
      simp [one_apply, hi]
  rw [hn]; simp only [gx_eq_iff hs ht, gx_eq_iff hs hlt]
  have hb1 := (bit_add_pow hu).1
  have hc1 := (bit_add_pow hu).2
  have hcs := clr_pair_iff hu hlt (v := s)
  have hct := clr_pair_iff hu hlt (v := t)
  have h0 : bit p u = 0 := hu
  have hcu : clr p u = u := clr_of_bit hu
  have hp := Nat.two_pow_pos p
  by_cases hst : s = t
  · subst hst
    by_cases h1 : s = u + 2 ^ p
    · subst h1; simp [hb1, hc1, zEnt]
    · rw [if_neg h1]
      by_cases hc : clr p s = u
      · have : s = u := by rcases hcs.1 hc with h | h; exact h; exact absurd h h1
        subst this; simp [h0, hcu, zEnt]
      · simp [hc]
  · rw [if_neg hst, if_neg hst]
    by_cases hc : clr p s = u ∧ clr p t = u
    · rw [if_pos hc, zEnt]
      rcases hcs.1 hc.1 with h | h <;> rcases hct.1 hc.2 with h' | h' <;> subst h h' <;>
        simp_all
    · rw [if_neg hc]

end Pair

/-! ## Words of pair letters -/

/-- The letters `H_[G⁻¹(u), G⁻¹(u + 2^p)] H_[G⁻¹(u'), G⁻¹(u' + 2^p)]`. -/
def hhList (n p : ℕ) (l : List (ℕ × ℕ)) : List (PG (2 ^ n)) :=
  l.map fun q => .hh (gx n q.1) (gx n (q.1 + 2 ^ p)) (gx n q.2) (gx n (q.2 + 2 ^ p))

/-- The letters `(-1)_[G⁻¹(u + 2^p)] (-1)_[G⁻¹(u' + 2^p)]`. -/
def zzList (n p : ℕ) (l : List (ℕ × ℕ)) : List (PG (2 ^ n)) :=
  l.map fun q => .zz (gx n (q.1 + 2 ^ p)) (gx n (q.2 + 2 ^ p))

/-- The `u` of the pairs. -/
def flat (l : List (ℕ × ℕ)) : List ℕ := l.flatMap fun q => [q.1, q.2]

theorem pWord_hhList (σ : R) (p : ℕ) (l : List (ℕ × ℕ)) :
    pWord σ (wordOf (hhList n p l)) =
      ((flat l).map fun u => hM σ (gx n u) (gx n (u + 2 ^ p))).prod := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [hhList, List.map_cons, wordOf, FreeMonoid.ofList_cons, map_mul, ← wordOf, ← hhList, ih]
    simp [flat, pWord, pMat, mul_assoc]

theorem pWord_zzList (σ : R) (p : ℕ) (l : List (ℕ × ℕ)) :
    pWord σ (wordOf (zzList n p l)) =
      ((flat l).map fun u => (negM (gx n (u + 2 ^ p)) : Matrix _ _ R)).prod := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [zzList, List.map_cons, wordOf, FreeMonoid.ofList_cons, map_mul, ← wordOf, ← zzList, ih]
    simp [flat, pWord, pMat, mul_assoc]

/-- A list of pairs fit for the encoding of a gate on wire `p`. -/
structure PairsOK (n p : ℕ) (l : List (ℕ × ℕ)) : Prop where
  nodup : (flat l).Nodup
  bit0 : ∀ u ∈ flat l, bit p u = 0
  lt : ∀ u ∈ flat l, u + 2 ^ p < 2 ^ n

theorem pWord_hhList_apply (σ : R) {p : ℕ} {l : List (ℕ × ℕ)} (h : PairsOK n p l)
    {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) :
    pWord σ (wordOf (hhList n p l)) (gx n s) (gx n t) =
      if clr p s ∈ flat l ∧ clr p t = clr p s then hEnt σ (bit p s) (bit p t)
      else if s = t then 1 else 0 := by
  rw [pWord_hhList]
  exact prod_pairs _ _ _ h.nodup (fun u hu s hs t ht => hM_pair (h.bit0 u hu) (h.lt u hu) σ hs ht)
    s hs t ht

theorem pWord_zzList_apply (σ : R) {p : ℕ} {l : List (ℕ × ℕ)} (h : PairsOK n p l)
    {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) :
    pWord σ (wordOf (zzList n p l)) (gx n s) (gx n t) =
      if clr p s ∈ flat l ∧ clr p t = clr p s then zEnt (bit p s) (bit p t)
      else if s = t then 1 else 0 := by
  rw [pWord_zzList]
  exact prod_pairs _ _ _ h.nodup (fun u hu s hs t ht => negM_pair (h.bit0 u hu) (h.lt u hu) hs ht)
    s hs t ht

theorem proper_zzList (p : ℕ) (l : List (ℕ × ℕ)) : ProperW (wordOf (zzList n p l)) := by
  intro x hx
  simp only [wordOf, FreeMonoid.toList_ofList, zzList, List.mem_map] at hx
  obtain ⟨q, _, rfl⟩ := hx; trivial

theorem proper_hhList {p : ℕ} {l : List (ℕ × ℕ)} (h : PairsOK n p l) :
    ProperW (wordOf (hhList n p l)) := by
  intro x hx
  simp only [wordOf, FreeMonoid.toList_ofList, hhList, List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have m1 : q.1 ∈ flat l := List.mem_flatMap.2 ⟨q, hq, by simp⟩
  have m2 : q.2 ∈ flat l := List.mem_flatMap.2 ⟨q, hq, by simp⟩
  have hp := Nat.two_pow_pos p
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := gx_inj (by have := h.lt _ m1; omega) (h.lt _ m1) e; omega
  · have := gx_inj (by have := h.lt _ m2; omega) (h.lt _ m2) e; omega

end QCert.RealCliffordCH.Sec8
