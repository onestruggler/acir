/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-free derivations: the sign part of the normal form

`SWl n b xs = ∏_{x ∈ xs, b x} (-1)_[0](-1)_[x]`.  Over a list of distinct
indices containing `y`, appending `(-1)_[0](-1)_[y]` toggles `b y`
(`toggle`); so any word of signs can be absorbed (`absorb_zzs`).
-/
import QCert.RealCliffordCH.Sec8.A.Perm

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- The sign part: `(-1)_[0](-1)_[x]` for the `x ∈ xs` with `b x`. -/
def SWl (n : ℕ) (b : ℕ → Bool) (xs : List ℕ) : List (PG (2 ^ n)) :=
  xs.flatMap fun x => if b x then [Zz n 0 x] else []

theorem SWl_cons (b : ℕ → Bool) (x : ℕ) (xs : List ℕ) :
    SWl n b (x :: xs) = (if b x then [Zz n 0 x] else []) ++ SWl n b xs := by
  simp [SWl]

theorem SWl_congr {b b' : ℕ → Bool} {xs : List ℕ} (h : ∀ x ∈ xs, b x = b' x) :
    SWl n b xs = SWl n b' xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [SWl_cons, SWl_cons, h x (by simp), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem g_pass {b : ℕ → Bool} {y : ℕ} (hy : y < 2 ^ n) :
    ∀ xs : List ℕ, (∀ x ∈ xs, x < 2 ^ n) →
      DH n (SWl n b xs ++ [Zz n 0 y]) ([Zz n 0 y] ++ SWl n b xs)
  | [], _ => DR.refl _
  | x :: xs, hxs => by
    rw [SWl_cons]
    have ih := g_pass (b := b) hy xs fun z hz => hxs z (List.mem_cons_of_mem _ hz)
    have h1 := DR.left (if b x then [Zz n 0 x] else []) ih
    refine (DR.rfl' (by simp)).trans (h1.trans ?_)
    by_cases hb : b x
    · simp only [hb, if_true]
      exact (DR.right (SWl n b xs) (g_comm (Nat.two_pow_pos n) (hxs x (by simp)) hy)).trans
        (DR.rfl' (by simp))
    · simp [hb]; exact DR.refl _

theorem toggle {b : ℕ → Bool} {y : ℕ} (hy : y < 2 ^ n) :
    ∀ xs : List ℕ, xs.Nodup → (∀ x ∈ xs, x < 2 ^ n) → y ∈ xs →
      DH n (SWl n b xs ++ [Zz n 0 y]) (SWl n (Function.update b y (!b y)) xs)
  | [], _, _, hm => absurd hm (by simp)
  | x :: xs, hnd, hxs, hm => by
    rw [List.nodup_cons] at hnd
    have hxs' : ∀ z ∈ xs, z < 2 ^ n := fun z hz => hxs z (List.mem_cons_of_mem _ hz)
    rw [SWl_cons, SWl_cons]
    by_cases hxy : x = y
    · subst hxy
      rw [SWl_congr (b := Function.update b x (!b x)) (b' := b)
        (fun z hz => by rw [Function.update_of_ne (fun e : z = x => hnd.1 (e ▸ hz))]),
        Function.update_self]
      have h1 := DR.left (if b x then [Zz n 0 x] else []) (g_pass (b := b) hy xs hxs')
      refine (DR.rfl' (by simp)).trans (h1.trans ?_)
      cases hb : b x
      · simp; exact DR.refl _
      · simp only [if_true, Bool.not_true]
        exact (DR.right (SWl n b xs) (zz_sq (Nat.two_pow_pos n) hy)).trans (DR.rfl' (by simp))
    · have hm' : y ∈ xs := by simpa [Ne.symm hxy] using hm
      rw [Function.update_of_ne hxy]
      exact (DR.rfl' (by simp)).trans (DR.left _ (toggle hy xs hnd.2 hxs' hm'))

/-- The indices `1, …, 2ⁿ - 1` of the sign part. -/
def sidx (n : ℕ) : List ℕ := List.range' 1 (2 ^ n - 1)

theorem sidx_nodup : (sidx n).Nodup := List.nodup_range' ..

theorem sidx_lt : ∀ x ∈ sidx n, x < 2 ^ n := by
  intro x hx; simp only [sidx, List.mem_range'] at hx; omega

theorem mem_sidx {x : ℕ} (h1 : 1 ≤ x) (h2 : x < 2 ^ n) : x ∈ sidx n := by
  simp only [sidx, List.mem_range']; exact ⟨x - 1, by omega, by omega⟩

/-- Appending `(-1)_[0](-1)_[y]` to the sign part. -/
theorem absorb_g (b : ℕ → Bool) {y : ℕ} (hy : y < 2 ^ n) :
    ∃ b', DH n (SWl n b (sidx n) ++ [Zz n 0 y]) (SWl n b' (sidx n)) := by
  by_cases h0 : y = 0
  · subst h0; exact ⟨b, (DR.left _ (e20 n hy)).trans (DR.rfl' (by simp))⟩
  · exact ⟨_, toggle hy (sidx n) sidx_nodup sidx_lt (mem_sidx (by omega) hy)⟩

theorem absorb_zz (b : ℕ → Bool) {c d : ℕ} (hc : c < 2 ^ n) (hd : d < 2 ^ n) :
    ∃ b', DH n (SWl n b (sidx n) ++ [Zz n c d]) (SWl n b' (sidx n)) := by
  obtain ⟨b1, h1⟩ := absorb_g (n := n) b hc
  obtain ⟨b2, h2⟩ := absorb_g (n := n) b1 hd
  refine ⟨b2, (DR.left _ (zz_split (Nat.two_pow_pos n) hc hd)).trans ?_⟩
  exact (DR.rfl' (by simp)).trans ((DR.right [Zz n 0 d] h1).trans h2)

theorem absorb_zzs (b : ℕ → Bool) :
    ∀ ps : List (ℕ × ℕ), PairsBd n ps →
      ∃ b', DH n (SWl n b (sidx n) ++ zzs n ps) (SWl n b' (sidx n))
  | [], _ => ⟨b, DR.rfl' (by simp [zzs])⟩
  | p :: ps, hps => by
    obtain ⟨b1, h1⟩ := absorb_zz (n := n) b (hps p (by simp)).1 (hps p (by simp)).2
    obtain ⟨b2, h2⟩ := absorb_zzs b1 ps fun q hq => hps q (List.mem_cons_of_mem _ hq)
    exact ⟨b2, (DR.rfl' (by simp [zzs])).trans ((DR.right (zzs n ps) h1).trans h2)⟩

end QCert.RealCliffordCH.Sec8
