/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The encoding of a generator preserves its semantics

`encAt_sem`: for every generator `g` of `n`-wire circuits (`n ≥ 3`), the
encoding `encAt n 0 g` of Definition 8.2 is a proper word whose matrix is
the operator of `g` in the basis ordered by the Gray code.
-/
import QCert.RealCliffordCH.Sec8.ESem.Gates

namespace QCert.RealCliffordCH.Sec8

open Matrix

variable {n : ℕ}

/-! ## The eight encodings as words of pair letters -/

theorem enc1_forms {lo : ℕ} (hn : 3 ≤ n) (hlo : lo + 1 ≤ n) :
    ∃ l, PairsOK n lo l ∧ (∀ s < 2 ^ n, clr lo s ∈ flat l) ∧
      enc1 n .H (n - 1 - lo) lo = hhList n lo l ∧ enc1 n .Z (n - 1 - lo) lo = zzList n lo l := by
  rcases lo with _ | ℓ
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have e4 : 2 ^ n = 4 * 2 ^ (n - 1 - 0 - 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    refine ⟨pairs1a (2 ^ (n - 1 - 0 - 1)), pairs1a_ok e4, fun s hs => mem_pairs1a e4 hs, ?_, ?_⟩ <;>
    · simp only [enc1, hhList, zzList, pairs1a, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      have e : 2 ^ (n - 1 - 0) = 2 * 2 ^ (n - 1 - 0 - 1) := by
        rw [← pow_succ']; congr 1; omega
      simp only [Function.comp_apply, f1a, pow_zero, e]
      try (congr 2 <;> ring)
  · obtain ⟨k, hk⟩ : ∃ k, n = k + ℓ + 2 := ⟨n - ℓ - 2, by omega⟩
    have ek : n - 1 - (ℓ + 1) = k := by omega
    rw [ek]
    refine ⟨pairs1b k ℓ, pairs1b_ok hk, fun s hs => mem_pairs1b hk hs, ?_, ?_⟩ <;>
    · simp only [enc1, hhList, zzList, pairs1b, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, f1b]
      try (congr 2 <;> ring)

theorem enc2_forms {lo : ℕ} (hn : 3 ≤ n) (hlo : lo + 2 ≤ n) :
    ∃ l, PairsOK n lo l ∧ (∀ s < 2 ^ n, clr lo s ∈ flat l ↔ bit (lo + 1) s = 1) ∧
      enc2 n .CH (n - 2 - lo) lo = hhList n lo l ∧ enc2 n .CZ (n - 2 - lo) lo = zzList n lo l := by
  rcases lo with _ | ℓ
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have e8 : 2 ^ n = 8 * 2 ^ (n - 2 - 0 - 1) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
    refine ⟨pairs2a (2 ^ (n - 2 - 0 - 1)), pairs2a_ok e8, fun s hs => mem_pairs2a e8 hs, ?_, ?_⟩ <;>
    · simp only [enc2, hhList, zzList, pairs2a, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      have e : 2 ^ (n - 2 - 0 + 1) = 4 * 2 ^ (n - 2 - 0 - 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      simp only [Function.comp_apply, f2a, pow_zero, e]
      try (congr 2 <;> ring)
  · obtain ⟨k, hk⟩ : ∃ k, n = k + ℓ + 3 := ⟨n - ℓ - 3, by omega⟩
    have ek : n - 2 - (ℓ + 1) = k := by omega
    rw [ek]
    refine ⟨pairs2b k ℓ, pairs2b_ok hk, fun s hs => mem_pairs2b hk hs, ?_, ?_⟩ <;>
    · simp only [enc2, hhList, zzList, pairs2b, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, f2b]
      try (congr 2 <;> ring)

/-! ## The induction on generators -/

theorem div_pow_lt {lo m s : ℕ} (h : lo + m = n) (hs : s < 2 ^ n) : s / 2 ^ lo < 2 ^ m := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos lo), ← pow_add, Nat.add_comm, h]; exact hs

theorem mod_pow_succ_iff (lo s t : ℕ) :
    s % 2 ^ (lo + 1) = t % 2 ^ (lo + 1) ↔ s % 2 ^ lo = t % 2 ^ lo ∧ s / 2 ^ lo % 2 = t / 2 ^ lo % 2 := by
  rw [Nat.mod_pow_succ, Nat.mod_pow_succ]
  constructor
  · intro h
    have hs := Nat.mod_lt s (Nat.two_pow_pos lo)
    have ht := Nat.mod_lt t (Nat.two_pow_pos lo)
    have h1 := div_mod_mul_add (s / 2 ^ lo % 2) hs
    have h2 := div_mod_mul_add (t / 2 ^ lo % 2) ht
    have e1 : s / 2 ^ lo % 2 * 2 ^ lo + s % 2 ^ lo = t / 2 ^ lo % 2 * 2 ^ lo + t % 2 ^ lo := by
      linarith
    rw [e1] at h1
    exact ⟨h1.2.symm.trans h2.2, h1.1.symm.trans h2.1⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-- The encoding of a generator placed `lo` wires up. -/
theorem enc_gen (hn : 3 ≤ n) : ∀ {m : ℕ} (g : Gen Gate m) (lo : ℕ), lo + m = n →
    ProperW (wordOf (encAt n lo g)) ∧ ∀ s < 2 ^ n, ∀ t < 2 ^ n,
      pSem (wordOf (encAt n lo g)) (gx n s) (gx n t) =
        if s % 2 ^ lo = t % 2 ^ lo then (S.gen g).1 (stateOf m (s / 2 ^ lo)) (stateOf m (t / 2 ^ lo))
        else 0
  | _, .gate0 c, _, _ => nomatch c
  | _, .gate3 c, _, _ => nomatch c
  | _, .up g, lo, h => by
    obtain ⟨hp, he⟩ := enc_gen hn g (lo + 1) (by omega)
    refine ⟨hp, fun s hs t ht => ?_⟩
    show pSem (wordOf (encAt n (lo + 1) g)) _ _ = _
    rw [he s hs t ht, sem_up, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ]
    simp only [mod_pow_succ_iff]
    by_cases h1 : s % 2 ^ lo = t % 2 ^ lo <;> by_cases h2 : s / 2 ^ lo % 2 = t / 2 ^ lo % 2 <;>
      simp [h1, h2]
  | m + 1, .gate1 G, lo, h => by
    obtain ⟨l, hok, hmem, eH, eZ⟩ := enc1_forms (n := n) (lo := lo) hn (by omega)
    have hv := fun s (hs : s < 2 ^ n) => div_pow_lt h hs
    cases G
    · show ProperW (wordOf (enc1 n .H (n - 1 - lo) lo)) ∧ ∀ s < 2 ^ n, ∀ t < 2 ^ n,
        pWord invSqrt2 (wordOf (enc1 n .H (n - 1 - lo) lo)) (gx n s) (gx n t) = _
      rw [eH]
      refine ⟨proper_hhList hok, fun s hs t ht => ?_⟩
      rw [pWord_hhList_apply _ hok hs ht, sem_gate1 _ (hv s hs) (hv t ht), gate1_H]
      simp only [hmem s hs, true_and]
      exact cmp1 _ lo s t
    · show ProperW (wordOf (enc1 n .Z (n - 1 - lo) lo)) ∧ ∀ s < 2 ^ n, ∀ t < 2 ^ n,
        pWord invSqrt2 (wordOf (enc1 n .Z (n - 1 - lo) lo)) (gx n s) (gx n t) = _
      rw [eZ]
      refine ⟨proper_zzList _ _, fun s hs t ht => ?_⟩
      rw [pWord_zzList_apply _ hok hs ht, sem_gate1 _ (hv s hs) (hv t ht), gate1_Z]
      simp only [hmem s hs, true_and]
      exact cmp1 _ lo s t
  | m + 2, .gate2 G, lo, h => by
    obtain ⟨l, hok, hmem, eH, eZ⟩ := enc2_forms (n := n) (lo := lo) hn (by omega)
    have hv := fun s (hs : s < 2 ^ n) => div_pow_lt h hs
    cases G
    · show ProperW (wordOf (enc2 n .CZ (n - 2 - lo) lo)) ∧ ∀ s < 2 ^ n, ∀ t < 2 ^ n,
        pWord invSqrt2 (wordOf (enc2 n .CZ (n - 2 - lo) lo)) (gx n s) (gx n t) = _
      rw [eZ]
      refine ⟨proper_zzList _ _, fun s hs t ht => ?_⟩
      rw [pWord_zzList_apply _ hok hs ht, sem_gate2 _ (hv s hs) (hv t ht), gate2_CZ]
      exact cmp2 _ lo s t _ (hmem s hs)
    · show ProperW (wordOf (enc2 n .CH (n - 2 - lo) lo)) ∧ ∀ s < 2 ^ n, ∀ t < 2 ^ n,
        pWord invSqrt2 (wordOf (enc2 n .CH (n - 2 - lo) lo)) (gx n s) (gx n t) = _
      rw [eH]
      refine ⟨proper_hhList hok, fun s hs t ht => ?_⟩
      rw [pWord_hhList_apply _ hok hs ht, sem_gate2 _ (hv s hs) (hv t ht), gate2_CH]
      exact cmp2 _ lo s t _ (hmem s hs)

/-- The encoding of a generator is proper and preserves its semantics. -/
theorem encAt_sem (hn : 3 ≤ n) (g : Gen Gate n) :
    ProperW (wordOf (encAt n 0 g)) ∧ pSem (wordOf (encAt n 0 g)) = toP (S.gen g).1 := by
  obtain ⟨hp, he⟩ := enc_gen hn g 0 (by simp)
  refine ⟨hp, ext_gx fun s hs t ht => ?_⟩
  rw [he s hs t ht, toP_gx _ hs ht, pow_zero, Nat.mod_one, Nat.mod_one, Nat.div_one, Nat.div_one,
    if_pos rfl]

end QCert.RealCliffordCH.Sec8
