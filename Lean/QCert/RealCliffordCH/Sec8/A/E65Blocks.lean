/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The blocks of `𝒲₁`, `𝒲₂` as signed permutations

`SOp n B f σ`: the word `B` sends the index of the basis state `s` to that of
`f s`, with sign `σ s`.  `E_{k,ℓ}(swap)` exchanges the wires `ℓ + 1, ℓ`
(`sop_encSwap`) and `ℰ_{k,ℓ}(X)` flips the wire `ℓ` (`sop_encNeg`), both with
no sign.

The proofs go through letters whose indices are basis states (`NL.rel`
relabels them by `G⁻¹`): a word of sign pairs on distinct states signs
exactly those states (`zzS_spec`), and a word of mixed letters on disjoint
pairs `u, u + 2^p` acts on each pair by its letter (`zxPairs_spec`).
-/
import QCert.RealCliffordCH.Sec8.A.E65Bits

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Relabelling letters by `G⁻¹` -/

/-- A letter with its indices relabelled by `g`. -/
def NL.rel (g : ℕ → ℕ) : NL → NL
  | .zz a c => .zz (g a) (g c)
  | .zx a c d => .zx (g a) (g c) (g d)
  | .xx a b c d => .xx (g a) (g b) (g c) (g d)

theorem gInv_inj {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) (h : gInv n s = gInv n t) :
    s = t := by
  rw [← gray_gInv hs, ← gray_gInv ht, h]

theorem gInv_eq_iff {s t : ℕ} (hs : s < 2 ^ n) (ht : t < 2 ^ n) : gInv n s = gInv n t ↔ s = t :=
  ⟨gInv_inj hs ht, fun h => h ▸ rfl⟩

theorem swN_rel {c d s : ℕ} (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hs : s < 2 ^ n) :
    swN (gInv n c) (gInv n d) (gInv n s) = gInv n (swN c d s) := by
  unfold swN
  simp only [gInv_eq_iff hs hc, gInv_eq_iff hs hd]
  split_ifs <;> rfl

theorem NL.rel_perm {x : NL} (hx : x.Bd n) {s : ℕ} (hs : s < 2 ^ n) :
    (x.rel (gInv n)).perm (gInv n s) = gInv n (x.perm s) := by
  cases x with
  | zz a c => rfl
  | zx a c d => exact swN_rel hx.2.1 hx.2.2 hs
  | xx a b c d =>
    show swN _ _ (swN _ _ _) = _
    rw [swN_rel hx.2.2.1 hx.2.2.2 hs, swN_rel hx.1 hx.2.1 (swN_lt hx.2.2.1 hx.2.2.2 hs)]
    rfl

theorem NL.rel_neg {x : NL} (hx : x.Bd n) {s : ℕ} (hs : s < 2 ^ n) :
    (x.rel (gInv n)).neg (gInv n s) = x.neg s := by
  cases x with
  | zz a c =>
    simp only [NL.rel, NL.neg, gInv_eq_iff hs hx.1, gInv_eq_iff hs hx.2]
  | zx a c d =>
    simp only [NL.rel, NL.neg, swN_rel hx.2.1 hx.2.2 hs, gInv_eq_iff (swN_lt hx.2.1 hx.2.2 hs) hx.1]
  | xx a b c d => rfl

theorem NL.rel_bd {x : NL} (hx : x.Bd n) : (x.rel (gInv n)).Bd n := by
  cases x with
  | zz a c => exact ⟨gInv_lt hx.1, gInv_lt hx.2⟩
  | zx a c d => exact ⟨gInv_lt hx.1, gInv_lt hx.2.1, gInv_lt hx.2.2⟩
  | xx a b c d => exact ⟨gInv_lt hx.1, gInv_lt hx.2.1, gInv_lt hx.2.2.1, gInv_lt hx.2.2.2⟩

theorem NL.rel_pr {x : NL} (hx : x.Bd n) (hp : x.Pr) : (x.rel (gInv n)).Pr := by
  cases x with
  | zz a c => trivial
  | zx a c d => exact fun e => hp (gInv_inj hx.2.1 hx.2.2 e)
  | xx a b c d =>
    exact ⟨fun e => hp.1 (gInv_inj hx.1 hx.2.1 e), fun e => hp.2 (gInv_inj hx.2.2.1 hx.2.2.2 e)⟩

theorem relL : ∀ (L : List NL), (∀ x ∈ L, x.Bd n) → ∀ s < 2 ^ n,
    permL (L.map (NL.rel (gInv n))) (gInv n s) = gInv n (permL L s) ∧
      negL (L.map (NL.rel (gInv n))) (gInv n s) = negL L s
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: L, hL, s, hs => by
    have hL' : ∀ y ∈ L, y.Bd n := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    obtain ⟨ih1, ih2⟩ := relL L hL' s hs
    have hlt := permL_lt hL' hs
    have hx := hL x (by simp)
    refine ⟨?_, ?_⟩
    · show (x.rel (gInv n)).perm (permL (L.map (NL.rel (gInv n))) (gInv n s)) = _
      rw [ih1, NL.rel_perm hx hlt]; rfl
    · show (if (x.rel (gInv n)).neg (permL (L.map (NL.rel (gInv n))) (gInv n s)) then _ else _) = _
      rw [ih1, ih2, NL.rel_neg hx hlt]; rfl

/-! ## Signed permutations of basis states -/

/-- The word `B` sends the index of the basis state `s` to that of `f s`, with
sign `σ s`. -/
def SOp (n : ℕ) (B : List (PG (2 ^ n))) (f : ℕ → ℕ) (σ : ℕ → Bool) : Prop :=
  HP B ∧ ∀ s < 2 ^ n, f s < 2 ^ n ∧ (spW (wordOf B)).perm (gx n s) = gx n (f s) ∧
    (spW (wordOf B)).neg (gx n s) = σ s

theorem SOp.nil : SOp n [] id fun _ => false :=
  ⟨HP.nil, fun s hs => ⟨hs, rfl, rfl⟩⟩

theorem SOp.append {B₁ B₂ : List (PG (2 ^ n))} {f₁ f₂ : ℕ → ℕ} {σ₁ σ₂ : ℕ → Bool}
    (h₁ : SOp n B₁ f₁ σ₁) (h₂ : SOp n B₂ f₂ σ₂) :
    SOp n (B₁ ++ B₂) (f₁ ∘ f₂) (fun s => xor (σ₁ (f₂ s)) (σ₂ s)) := by
  refine ⟨h₁.1.append h₂.1, fun s hs => ?_⟩
  obtain ⟨l2, p2, n2⟩ := h₂.2 s hs
  obtain ⟨l1, p1, n1⟩ := h₁.2 _ l2
  refine ⟨l1, ?_, ?_⟩
  · rw [spW_wordOf_append, SP.mul_perm, p2, p1]; rfl
  · rw [spW_wordOf_append, SP.mul_neg, p2, n1, n2]

theorem SOp.congr {B : List (PG (2 ^ n))} {f f' : ℕ → ℕ} {σ σ' : ℕ → Bool} (h : SOp n B f σ)
    (hf : ∀ s < 2 ^ n, f s = f' s) (hσ : ∀ s < 2 ^ n, σ s = σ' s) : SOp n B f' σ' :=
  ⟨h.1, fun s hs => by
    obtain ⟨l, p, q⟩ := h.2 s hs
    exact ⟨hf s hs ▸ l, hf s hs ▸ p, hσ s hs ▸ q⟩⟩

theorem SOp.ofNL {L : List NL} {B : List (PG (2 ^ n))} {f : ℕ → ℕ} {σ : ℕ → Bool}
    (hB : B = (L.map (NL.rel (gInv n))).map (NL.toPG n)) (hbd : ∀ x ∈ L, x.Bd n)
    (hpr : ∀ x ∈ L, x.Pr) (h : ∀ s < 2 ^ n, permL L s = f s ∧ negL L s = σ s) :
    SOp n B f σ := by
  subst hB
  have hbd' : ∀ x ∈ L.map (NL.rel (gInv n)), x.Bd n := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact NL.rel_bd (hbd y hy)
  have hpr' : ∀ x ∈ L.map (NL.rel (gInv n)), x.Pr := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact NL.rel_pr (hbd y hy) (hpr y hy)
  refine ⟨HP_NL hbd' hpr', fun s hs => ?_⟩
  obtain ⟨e1, e2⟩ := relL L hbd s hs
  have hf : f s < 2 ^ n := (h s hs).1 ▸ permL_lt hbd hs
  refine ⟨hf, ?_, ?_⟩
  · apply Fin.ext
    rw [(spW_NL hbd' (gx n s)).1, gx_val hs, e1, (h s hs).1, gx_val hf]
  · rw [(spW_NL hbd' (gx n s)).2, gx_val hs, e2, (h s hs).2]

/-! ## Sign pairs on distinct states -/

/-- The sign pairs of a list of pairs. -/
def zzS (ps : List (ℕ × ℕ)) : List NL := ps.map fun q => NL.zz q.1 q.2

theorem zzS_spec : ∀ ps : List (ℕ × ℕ), (flat ps).Nodup → ∀ s,
    permL (zzS ps) s = s ∧ negL (zzS ps) s = decide (s ∈ flat ps)
  | [], _, s => ⟨rfl, by simp [zzS, negL, flat]⟩
  | q :: ps, hnd, s => by
    have e : flat (q :: ps) = q.1 :: q.2 :: flat ps := rfl
    rw [e, List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨ih1, ih2⟩ := zzS_spec ps hnd.2.2 s
    refine ⟨ih1, ?_⟩
    show (if (NL.zz q.1 q.2).neg (permL (zzS ps) s) then !negL (zzS ps) s else negL (zzS ps) s) = _
    rw [ih1, ih2, e]
    simp only [NL.neg, List.mem_cons]
    by_cases h1 : s = q.1
    · subst h1
      simp [hnd.1.1, hnd.1.2]
    · by_cases h2 : s = q.2
      · subst h2; simp [h1, hnd.2.1]
      · simp [h1, h2]

theorem flat_shift (c : ℕ) : ∀ l : List (ℕ × ℕ),
    flat (l.map fun q => (q.1 + c, q.2 + c)) = (flat l).map (· + c)
  | [] => rfl
  | q :: l => by
    show (q.1 + c) :: (q.2 + c) :: flat (l.map fun q => (q.1 + c, q.2 + c)) =
      (q.1 + c) :: (q.2 + c) :: (flat l).map (· + c)
    rw [flat_shift c l]

/-- The encoding of `Z` or `CZ`: the sign on the states `u + 2^p`, `u` in the pairs. -/
theorem sop_zzList {p : ℕ} {l : List (ℕ × ℕ)} (h : PairsOK n p l) :
    SOp n (zzList n p l) id fun s => decide (bit p s = 1 ∧ clr p s ∈ flat l) := by
  have hnd : (flat (l.map fun q => (q.1 + 2 ^ p, q.2 + 2 ^ p))).Nodup := by
    rw [flat_shift]; exact h.nodup.map (add_left_injective _)
  refine SOp.ofNL (L := zzS (l.map fun q => (q.1 + 2 ^ p, q.2 + 2 ^ p))) ?_ ?_ ?_ ?_
  · simp only [zzList, zzS, List.map_map]; rfl
  · intro x hx
    simp only [zzS, List.mem_map] at hx
    obtain ⟨q', ⟨q, hq, rfl⟩, rfl⟩ := hx
    have m1 : q.1 ∈ flat l := List.mem_flatMap.2 ⟨q, hq, by simp⟩
    have m2 : q.2 ∈ flat l := List.mem_flatMap.2 ⟨q, hq, by simp⟩
    exact ⟨h.lt _ m1, h.lt _ m2⟩
  · intro x hx
    simp only [zzS, List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx; trivial
  · intro s hs
    obtain ⟨e1, e2⟩ := zzS_spec _ hnd s
    refine ⟨e1, ?_⟩
    rw [e2, flat_shift]
    congr 1
    apply propext
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨b1, c1⟩ := bit_add_pow (h.bit0 u hu)
      exact ⟨b1, by rw [c1]; exact hu⟩
    · rintro ⟨hb, hm⟩
      refine ⟨clr p s, hm, ?_⟩
      have := clr_add_bit p s
      rw [hb, one_mul] at this
      exact this

/-! ## Mixed letters on disjoint pairs -/

/-- Mixed letters on the pairs `u, u + 2^p`, `u ∈ D`, the sign on `u + 2^p`
(`up`) or on `u`. -/
def zxPairs (p : ℕ) (up : Bool) (D : List ℕ) : List NL :=
  D.map fun u => NL.zx (if up then u + 2 ^ p else u) u (u + 2 ^ p)

theorem mem_pair {p u s : ℕ} (hu : bit p u = 0) : (s = u ∨ s = u + 2 ^ p) ↔ clr p s = u := by
  constructor
  · rintro (rfl | rfl)
    · exact clr_of_bit hu
    · exact (bit_add_pow hu).2
  · intro h
    have e := clr_add_bit p s
    rw [h] at e
    rcases (by have := bit_lt p s; omega : bit p s = 0 ∨ bit p s = 1) with hb | hb
    · left; rw [hb] at e; omega
    · right; rw [hb] at e; omega

theorem zxPairs_spec (p : ℕ) (up : Bool) : ∀ D : List ℕ, D.Nodup → (∀ u ∈ D, bit p u = 0) →
    ∀ s, permL (zxPairs p up D) s = (if clr p s ∈ D then flipB p s else s) ∧
      negL (zxPairs p up D) s =
        (decide (clr p s ∈ D) && (if up then decide (bit p s = 0) else decide (bit p s = 1)))
  | [], _, _, s => by simp [zxPairs, permL, negL]
  | u :: D, hnd, hbit, s => by
    rw [List.nodup_cons] at hnd
    have hbu := hbit u (by simp)
    obtain ⟨ih1, ih2⟩ := zxPairs_spec p up D hnd.2 (fun v hv => hbit v (List.mem_cons_of_mem _ hv)) s
    have hpow := Nat.two_pow_pos p
    have hne : u ≠ u + 2 ^ p := by omega
    by_cases hs : clr p s = u
    · have hsD : clr p s ∉ D := hs ▸ hnd.1
      rw [if_neg hsD] at ih1
      simp only [hsD, decide_false, Bool.false_and] at ih2
      have hsu := (mem_pair hbu).2 hs
      have hfl : flipB p s = u + (1 - bit p s) * 2 ^ p := by unfold flipB; rw [hs]
      refine ⟨?_, ?_⟩
      · show swN u (u + 2 ^ p) (permL (zxPairs p up D) s) = _
        rw [ih1, if_pos (by simp [hs]), hfl]
        rcases hsu with rfl | rfl
        · rw [hbu]; unfold swN; simp
        · rw [(bit_add_pow hbu).1]; unfold swN; simp [hne.symm]
      · show (if NL.neg (NL.zx (if up then u + 2 ^ p else u) u (u + 2 ^ p))
          (permL (zxPairs p up D) s) then !negL (zxPairs p up D) s else negL (zxPairs p up D) s) = _
        rw [ih1, ih2]
        simp only [NL.neg, List.mem_cons, hs, true_or, decide_true, Bool.true_and]
        rcases hsu with rfl | rfl
        · rw [hbu]; cases up <;> simp [swN, hne]
        · rw [(bit_add_pow hbu).1]; cases up <;> simp [swN, hne.symm]
    · have hm : clr p s ∈ u :: D ↔ clr p s ∈ D := by simp [hs]
      have hnot : ∀ t, clr p t = clr p s → t ≠ u ∧ t ≠ u + 2 ^ p := by
        intro t ht
        constructor
        · rintro rfl; exact hs (ht.symm.trans (clr_of_bit hbu))
        · rintro rfl; exact hs (ht.symm.trans (bit_add_pow hbu).2)
      have hct : clr p (permL (zxPairs p up D) s) = clr p s := by
        rw [ih1]; split_ifs
        · exact clr_flipB p s
        · rfl
      obtain ⟨n1, n2⟩ := hnot _ hct
      refine ⟨?_, ?_⟩
      · show swN u (u + 2 ^ p) (permL (zxPairs p up D) s) = _
        unfold swN; rw [if_neg n1, if_neg n2, ih1]
        simp only [hm]
      · show (if NL.neg (NL.zx (if up then u + 2 ^ p else u) u (u + 2 ^ p))
          (permL (zxPairs p up D) s) then !negL (zxPairs p up D) s else negL (zxPairs p up D) s) = _
        have : NL.neg (NL.zx (if up then u + 2 ^ p else u) u (u + 2 ^ p))
            (permL (zxPairs p up D) s) = false := by
          simp only [NL.neg, swN, if_neg n1, if_neg n2]
          cases up
          · simp [n1]
          · simp [n2]
        rw [this, ih2]
        simp only [hm, Bool.false_eq_true, if_false]

/-! ## Mixed letters over a grid -/

/-- The states `(K x + r) 2^ℓ + y`, `x < 2^k`, `y < 2^ℓ`. -/
def gridB (k ℓ K r : ℕ) : List ℕ := (grid k ℓ).map fun q => (K * q.1 + r) * 2 ^ ℓ + q.2

theorem lin_lt {k ℓ K r x y : ℕ} (hr : r < K) (hx : x < 2 ^ k) (hy : y < 2 ^ ℓ) :
    (K * x + r) * 2 ^ ℓ + y < K * 2 ^ k * 2 ^ ℓ := by
  have h1 : K * x + r + 1 ≤ K * 2 ^ k := by nlinarith
  have h2 : (K * x + r + 1) * 2 ^ ℓ ≤ K * 2 ^ k * 2 ^ ℓ := Nat.mul_le_mul_right _ h1
  nlinarith

/-- Mixed letters on the pairs of `gridB k ℓ K r`. -/
theorem sop_grid {k ℓ p K r : ℕ} (up : Bool) (hK : 0 < K)
    (hbit : ∀ x y, y < 2 ^ ℓ → bit p ((K * x + r) * 2 ^ ℓ + y) = 0)
    (htop : ∀ x y, x < 2 ^ k → y < 2 ^ ℓ → (K * x + r) * 2 ^ ℓ + y + 2 ^ p < 2 ^ n)
    {B : List (PG (2 ^ n))}
    (hB : B = (gridB k ℓ K r).map fun u =>
        PG.zx (gx n (if up then u + 2 ^ p else u)) (gx n u) (gx n (u + 2 ^ p))) :
    SOp n B (fun s => if clr p s ∈ gridB k ℓ K r then flipB p s else s)
      (fun s => decide (clr p s ∈ gridB k ℓ K r) &&
        (if up then decide (bit p s = 0) else decide (bit p s = 1))) := by
  have hpos := Nat.two_pow_pos p
  have hnd : (gridB k ℓ K r).Nodup := grid_map_nodup fun x _ y hy x' _ y' hy' e =>
    lin_inj hK hy hy' e
  have hb : ∀ u ∈ gridB k ℓ K r, bit p u = 0 := by
    intro u hu
    obtain ⟨x, _, y, hy, rfl⟩ := mem_grid_map.1 hu
    exact hbit x y hy
  have hlt : ∀ u ∈ gridB k ℓ K r, u + 2 ^ p < 2 ^ n := by
    intro u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_grid_map.1 hu
    exact htop x y hx hy
  refine SOp.ofNL (L := zxPairs p up (gridB k ℓ K r)) ?_ ?_ ?_
    (fun s _ => zxPairs_spec p up _ hnd hb s)
  · rw [hB]; simp only [zxPairs, List.map_map]
    refine List.map_congr_left fun u _ => ?_
    cases up <;> rfl
  · intro x hx
    simp only [zxPairs, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have := hlt u hu
    refine ⟨?_, by omega, this⟩
    cases up <;> simp <;> omega
  · intro x hx
    simp only [zxPairs, List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    show u ≠ u + 2 ^ p
    omega

theorem pow_split {n k ℓ c : ℕ} (h : k + c + ℓ = n) : 2 ^ n = 2 ^ c * 2 ^ k * 2 ^ ℓ := by
  rw [← h, pow_add, pow_add]; ring

/-! ## `ℰ_{k,ℓ}(X)` -/

/-- `ℰ_{k,ℓ}(X)` flips the wire `ℓ`, with no sign. -/
theorem sop_encNeg (hn : 3 ≤ n) {k ℓ x : ℕ} (h : k + 1 + ℓ = n) :
    SOp n (encNeg n k ℓ x) (if x = 1 then id else flipB ℓ) fun _ => false := by
  by_cases hx : x = 1
  · simp only [encNeg, if_pos hx]; exact SOp.nil
  rw [if_neg hx]
  have hN := pow_split h
  rw [pow_one] at hN
  have hZX : SOp n ((grid k ℓ).map fun p =>
      PG.zx (gx n (p.1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2)) (gx n (p.1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
        (gx n (p.1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2)))
      (fun s => if clr ℓ s ∈ gridB k ℓ 2 0 then flipB ℓ s else s)
      (fun s => decide (clr ℓ s ∈ gridB k ℓ 2 0) && decide (bit ℓ s = 0)) := by
    refine sop_grid (k := k) (ℓ := ℓ) (p := ℓ) (K := 2) (r := 0) true (by norm_num)
      (fun x y hy => by rw [(bit_lin ℓ 2 x 0 hy).1]; omega)
      (fun x y hx hy => by
        have := lin_lt (K := 2) (r := 1) (by norm_num) hx hy
        rw [hN]; linarith) ?_
    simp only [gridB, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp, if_true]
    congr 2 <;> ring
  have hmem : ∀ s < 2 ^ n, clr ℓ s ∈ gridB k ℓ 2 0 := by
    intro s hs
    refine mem_grid_map.2 ⟨s / 2 ^ (ℓ + 1), ?_, s % 2 ^ ℓ, Nat.mod_lt _ (Nat.two_pow_pos ℓ), ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      rw [hN] at hs; rw [pow_succ]; linarith
    · rw [clr_def]; ring
  obtain ⟨l, hok, hm, -, eZ⟩ := enc1_forms (n := n) (lo := ℓ) hn (by omega)
  have ek : n - 1 - ℓ = k := by omega
  rw [ek] at eZ
  simp only [encNeg, if_neg hx]
  rw [eZ]
  refine (SOp.append (sop_zzList hok) hZX).congr (fun s hs => ?_) (fun s hs => ?_)
  · simp [hmem s hs]
  · have hf := flipB_lt hs (show ℓ < n by omega)
    simp only [hmem s hs, if_true, decide_true, Bool.true_and, bit_flipB_self, hm _ hf, and_true]
    have := bit_lt ℓ s
    rcases (by omega : bit ℓ s = 0 ∨ bit ℓ s = 1) with e | e <;> simp [e]

/-! ## `E_{k,ℓ}(swap)` -/

/-- `E_{k,ℓ}(swap)` exchanges the wires `ℓ + 1` and `ℓ`, with no sign. -/
theorem sop_encSwap (hn : 3 ≤ n) {k ℓ : ℕ} (h : k + 2 + ℓ = n) :
    SOp n (encSwap n k ℓ) (swapB ℓ) fun _ => false := by
  have hN := pow_split h
  norm_num at hN
  have hp := Nat.two_pow_pos ℓ
  have hR1 : SOp n ((grid k ℓ).map fun p =>
      PG.zx (gx n (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
        (gx n (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
        (gx n (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2)))
      (fun s => if clr ℓ s ∈ gridB k ℓ 4 2 then flipB ℓ s else s)
      (fun s => decide (clr ℓ s ∈ gridB k ℓ 4 2) && decide (bit ℓ s = 0)) := by
    refine sop_grid (k := k) (ℓ := ℓ) (p := ℓ) (K := 4) (r := 2) true (by norm_num)
      (fun x y hy => by rw [(bit_lin ℓ 4 x 2 hy).1]; omega)
      (fun x y hx hy => by
        have := lin_lt (K := 4) (r := 3) (by norm_num) hx hy
        rw [hN]; linarith) ?_
    simp only [gridB, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp, if_true]
    congr 2 <;> ring
  have hR2 : SOp n ((grid k ℓ).map fun p =>
      PG.zx (gx n (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
        (gx n (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
        (gx n (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2)))
      (fun s => if clr (ℓ + 1) s ∈ gridB k ℓ 4 1 then flipB (ℓ + 1) s else s)
      (fun s => decide (clr (ℓ + 1) s ∈ gridB k ℓ 4 1) && decide (bit (ℓ + 1) s = 1)) := by
    refine sop_grid (k := k) (ℓ := ℓ) (p := ℓ + 1) (K := 4) (r := 1) false (by norm_num)
      (fun x y hy => by rw [(bit_lin ℓ 4 x 1 hy).2]; omega)
      (fun x y hx hy => by
        have := lin_lt (K := 4) (r := 3) (by norm_num) hx hy
        rw [hN, pow_succ]; linarith) ?_
    simp only [gridB, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp, Bool.false_eq_true, if_false]
    congr 2 <;> ring
  have hX : ∀ s < 2 ^ n, s / 2 ^ (ℓ + 2) < 2 ^ k := fun s hs => by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [hN] at hs; rw [pow_succ, pow_succ]; linarith
  have m1 : ∀ s < 2 ^ n, clr ℓ s ∈ gridB k ℓ 4 2 ↔ bit (ℓ + 1) s = 1 := by
    intro s hs
    rw [gridB, mem_grid_map]
    constructor
    · rintro ⟨x, -, y, hy, e⟩
      rw [← bit_clr_ne ℓ (ℓ + 1) s (by omega), ← e, (bit_lin ℓ 4 x 2 hy).2]; omega
    · intro hb
      refine ⟨s / 2 ^ (ℓ + 2), hX s hs, s % 2 ^ ℓ, Nat.mod_lt _ hp, ?_⟩
      have e1 := div_succ_eq (ℓ + 1) s
      rw [hb] at e1
      rw [clr_def, e1]; ring
  have m2 : ∀ s < 2 ^ n, clr (ℓ + 1) s ∈ gridB k ℓ 4 1 ↔ bit ℓ s = 1 := by
    intro s hs
    rw [gridB, mem_grid_map]
    constructor
    · rintro ⟨x, -, y, hy, e⟩
      rw [← bit_clr_ne (ℓ + 1) ℓ s (by omega), ← e, (bit_lin ℓ 4 x 1 hy).1]; omega
    · intro hb
      refine ⟨s / 2 ^ (ℓ + 2), hX s hs, s % 2 ^ ℓ, Nat.mod_lt _ hp, ?_⟩
      have e1 := mod_succ_eq ℓ s
      rw [hb] at e1
      rw [clr_def, e1]; ring
  have hR1' := hR1.congr (f' := fun s => if bit (ℓ + 1) s = 1 then flipB ℓ s else s)
    (σ' := fun s => decide (bit (ℓ + 1) s = 1) && decide (bit ℓ s = 0))
    (fun s hs => by simp only [m1 s hs]) (fun s hs => by simp only [m1 s hs])
  have hR2' := hR2.congr (f' := fun s => if bit ℓ s = 1 then flipB (ℓ + 1) s else s)
    (σ' := fun s => decide (bit ℓ s = 1) && decide (bit (ℓ + 1) s = 1))
    (fun s hs => by simp only [m2 s hs]) (fun s hs => by simp only [m2 s hs])
  obtain ⟨l, hok, hm, -, eZ⟩ := enc2_forms (n := n) (lo := ℓ) hn (by omega)
  have ek : n - 2 - ℓ = k := by omega
  rw [ek] at eZ
  have hCZ := (sop_zzList hok).congr (f' := id)
    (σ' := fun s => decide (bit ℓ s = 1 ∧ bit (ℓ + 1) s = 1)) (fun _ _ => rfl)
    (fun s hs => by simp only [hm s hs])
  simp only [encSwap]
  rw [eZ]
  have h1 : ℓ + 1 ≠ ℓ := by omega
  have h2 : ℓ ≠ ℓ + 1 := by omega
  refine (SOp.append (SOp.append (SOp.append hCZ hR1') hR2') hR1').congr
    (fun s hs => ?_) (fun s hs => ?_)
  · have a0 := bit_lt ℓ s
    have a1 := bit_lt (ℓ + 1) s
    rcases (by omega : bit ℓ s = 0 ∨ bit ℓ s = 1) with e0 | e0 <;>
      rcases (by omega : bit (ℓ + 1) s = 0 ∨ bit (ℓ + 1) s = 1) with e1 | e1
    · rw [swapB_of_eq (by rw [e0, e1])]; simp [e0, e1]
    · rw [swapB_of_ne (by rw [e0, e1]; omega)]
      simp [e0, e1, bit_flipB, h1, h2]
    · rw [swapB_of_ne (by rw [e0, e1]; omega)]
      simp [e0, e1, bit_flipB, h1, h2, flipB_comm ℓ (ℓ + 1)]
    · rw [swapB_of_eq (by rw [e0, e1])]
      simp [e0, e1, bit_flipB, h1, h2, flipB_flipB]
  · have a0 := bit_lt ℓ s
    have a1 := bit_lt (ℓ + 1) s
    rcases (by omega : bit ℓ s = 0 ∨ bit ℓ s = 1) with e0 | e0 <;>
      rcases (by omega : bit (ℓ + 1) s = 0 ∨ bit (ℓ + 1) s = 1) with e1 | e1 <;>
      simp [e0, e1, bit_flipB, h1, h2, flipB_flipB]

end QCert.RealCliffordCH.Sec8
