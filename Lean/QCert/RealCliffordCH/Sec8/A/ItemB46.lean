/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): the relation of Equation (46), at the indices `2, …, 7`

Away from the indices `0` and `1`, the coset action `τ` writes `H_[a,b]` as
`H_[a,b]H_[0,1]` or `H_[0,1]H_[a,b]` (by the `H`-parity of the coset), and
`(-1)_[a]` as `(-1)_[1](-1)_[a]` or `(-1)_[a]X_[0,1]` (`psi01`, `hstar_psi`):
the pair `0, 1` is a frame, with no sign tag needed when the signs come in
pairs.  So the relation `w46L ≈ w46R` of Figure 6 on the indices `2, …, 7`,
whose two-letter images are Equation (46) renamed by the even permutation
`(0 2 5 7)(1 3 4 6)` (the frame pair `7, 6` becoming `0, 1`), is in the
congruence of Claim B, at every `n ≥ 3` (`gb46`).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBRen8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## The coset action away from `0` and `1` -/

/-- The letter `τ` gives a generator away from `0, 1`, by the `H`-parity `b` of the coset. -/
def psiG (n : ℕ) (b : Bool) : HG (2 ^ n) → PG (2 ^ n)
  | .H x y _ => if b then Hh n 0 1 x y else Hh n x y 0 1
  | .Z x => if b then Zx n x 0 1 else Zz n 1 x
  | .X x y _ => if b then Xx n x y 0 1 else Zx n 1 x y

/-- The word `τ**` gives a list of generators away from `0, 1`. -/
def psi01 (n : ℕ) : Bool → List (HG (2 ^ n)) → List (PG (2 ^ n))
  | _, [] => []
  | b, y :: w => psiG n b y :: psi01 n (xor b (gbits y).1) w

/-- The `H`-parity of a coset. -/
def Cos.isH : Cos → Bool
  | .h => true
  | .hz => true
  | _ => false

theorem isH_act (c : Cos) (y : HG (2 ^ n)) :
    (c.act (gbits y)).isH = xor c.isH (gbits y).1 := by
  cases c <;> cases y <;> rfl

theorem tau_psi (c : Cos) (y : HG (2 ^ n)) (hy : ∀ i ∈ gix y, i ≠ 0 ∧ i ≠ 1) :
    (tauA n c y).1.toList = [psiG n c.isH y] := by
  cases y with
  | Z a =>
    obtain ⟨ha0, ha1⟩ := hy a (by simp [gix])
    cases c <;> simp [tauA, tauZH_list, tauZHn, psiG, Cos.isH, Zz, Zx, ix_fin, ha0, ha1]
  | X a b hab =>
    obtain ⟨ha0, ha1⟩ := hy a (by simp [gix])
    obtain ⟨hb0, hb1⟩ := hy b (by simp [gix])
    cases c <;> simp [tauA, tauX_list, tXn, psiG, Cos.isH, Zx, Xx, ix_fin, ha0, ha1, hb0, hb1]
  | H a b hab =>
    obtain ⟨ha0, ha1⟩ := hy a (by simp [gix])
    obtain ⟨hb0, hb1⟩ := hy b (by simp [gix])
    cases c <;> simp [tauA, psiG, Cos.isH, Hh, ix_fin, ha0, ha1, hb0, hb1]

/-- `τ**` along a list away from `0, 1`. -/
theorem hstar_psi (l : List (HG (2 ^ n))) (hl : ∀ y ∈ l, ∀ i ∈ gix y, i ≠ 0 ∧ i ≠ 1) (c : Cos) :
    (hstar (tauA n) c (FreeMonoid.ofList l)).1.toList = psi01 n c.isH l := by
  induction l generalizing c with
  | nil => rfl
  | cons y l ih =>
    simp only [FreeMonoid.ofList_cons, hstar_mul, hstar_of, FreeMonoid.toList_mul]
    rw [tau_psi c y (hl y (by simp)), ih (fun z hz => hl z (by simp [hz])), tauA_snd, isH_act]
    rfl

/-! ## Equation (46) at the indices `2, …, 7` -/

/-- Equation (46). -/
theorem e46 : D8 n [Hh n 0 1 7 6, Hh n 0 3 1 2, Hh n 3 4 2 5, Hh n 3 2 4 5, Hh n 7 6 4 5,
    Zz n 2 3, Hh n 3 4 2 5, Hh n 0 3 1 2]
    [Hh n 0 3 1 2, Hh n 3 4 2 5, Zz n 2 3, Hh n 7 6 4 5, Hh n 3 2 4 5, Hh n 3 4 2 5,
      Hh n 0 3 1 2, Hh n 0 1 7 6] :=
  DR.ax (Fig8.r46 (n := n))

/-- The two sides of (46) as lists of `CL` letters. -/
def L46c : List CL := [CL.hh 0 1 7 6, CL.hh 0 3 1 2, CL.hh 3 4 2 5, CL.hh 3 2 4 5, CL.hh 7 6 4 5,
  CL.zz 2 3, CL.hh 3 4 2 5, CL.hh 0 3 1 2]
/-- The right-hand side. -/
def R46c : List CL := [CL.hh 0 3 1 2, CL.hh 3 4 2 5, CL.zz 2 3, CL.hh 7 6 4 5, CL.hh 3 2 4 5,
  CL.hh 3 4 2 5, CL.hh 0 3 1 2, CL.hh 0 1 7 6]

/-- The permutation `(0 2 5 7)(1 3 4 6)` as a product of three double exchanges. -/
def P46 : List NL := [NL.xx 0 7 1 6, NL.xx 0 5 1 4, NL.xx 0 2 1 3]
/-- Its inverse. -/
def P46' : List NL := [NL.xx 0 2 1 3, NL.xx 0 5 1 4, NL.xx 0 7 1 6]

/-- Equation (46) at the indices `0, …, 7 ↦ 2, 3, 5, 4, 6, 7, 1, 0`. -/
theorem e46_ren (h8 : 8 ≤ 2 ^ n) (hE : E65 n) :
    D8 n [Hh n 2 3 0 1, Hh n 2 4 3 5, Hh n 4 6 5 7, Hh n 4 5 6 7, Hh n 0 1 6 7, Zz n 5 4,
      Hh n 4 6 5 7, Hh n 2 4 3 5]
      [Hh n 2 4 3 5, Hh n 4 6 5 7, Zz n 5 4, Hh n 0 1 6 7, Hh n 4 5 6 7, Hh n 4 6 5 7,
        Hh n 2 4 3 5, Hh n 2 3 0 1] := by
  have hbd : ∀ y ∈ P46, y.Bd n := by
    intro y hy
    simp only [P46, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega⟩
  have hbd' : ∀ y ∈ P46', y.Bd n := by
    intro y hy
    simp only [P46', List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega⟩
  have hpr : ∀ y ∈ P46, y.Pr := by simp [P46, NL.Pr]
  have hpr' : ∀ y ∈ P46', y.Pr := by simp [P46', NL.Pr]
  have hinv : ∀ v < 2 ^ n, permL (P46 ++ P46') v = v ∧ negL (P46 ++ P46') v = false := by
    intro v _
    have k := inv_v (m := 8) [0, 1, 2, 3, 4, 5, 6, 7] rfl (by decide) (P46 ++ P46')
      (by decide) v
    have e : (P46 ++ P46').map (NL.ren (rv [0, 1, 2, 3, 4, 5, 6, 7])) = P46 ++ P46' := rfl
    rwa [e] at k
  have neg0 : ∀ v, negL P46 v = false := fun v => by simp [P46, negL, NL.neg]
  have ok : ∀ x ∈ L46c ++ R46c, x.Ok n P46 := by
    intro x hx
    simp only [L46c, R46c, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [CL.Ok] <;>
      first
      | exact ⟨by omega, by omega⟩
      | exact ⟨by omega, by omega, by omega, by omega, by decide, by simp [neg0], by simp [neg0]⟩
  have k := ren_eq h8 hE hbd hbd' hpr hpr' hinv (L := L46c) (R := R46c)
    (fun x hx => ok x (List.mem_append_left _ hx)) (fun x hx => ok x (List.mem_append_right _ hx))
    e46
  simpa [L46c, R46c, CL.ren, CL.toPG, P46, permL, NL.perm, swN] using k

/-! ## The relation and its two images -/

/-- The relation of (46) on the indices `0, …, 5` of Figure 6's generators. -/
def W46L : List (HadamardPi.Gen 6) := [hL' 0 1, hL' 0 2, hL' 1 3, hL' 2 4, hL' 3 5, hL' 2 3, hL' 4 5,
  hL' 4 5, .Z 3, .Z 2, hL' 2 4, hL' 3 5, hL' 0 2, hL' 1 3]
where hL' (a b : Fin 6) (h : a < b := by decide) : HadamardPi.Gen 6 := .H a b h

/-- The right-hand side. -/
def W46R : List (HadamardPi.Gen 6) := [W46L.hL' 0 2, W46L.hL' 1 3, W46L.hL' 2 4, W46L.hL' 3 5, .Z 3, .Z 2,
  W46L.hL' 4 5, W46L.hL' 2 3, W46L.hL' 4 5, W46L.hL' 2 4, W46L.hL' 3 5, W46L.hL' 0 2,
  W46L.hL' 1 3, W46L.hL' 0 1]

/-- The indices `2, …, 7`. -/
def f27 (hn : 3 ≤ n) : Fin 6 → Fin (2 ^ n) := fun i => ⟨i + 2, by have := h8_of hn; omega⟩

theorem f27_val (hn : 3 ≤ n) (i : Fin 6) : ((f27 hn i : Fin (2 ^ n)) : ℕ) = i + 2 := rfl

theorem f27_mono (hn : 3 ≤ n) : StrictMono (f27 hn) := by
  intro i j hij; simp only [f27, Fin.mk_lt_mk]; exact Nat.add_lt_add_right hij 2

section Images

variable (hn : 3 ≤ n)
include hn

/-- `H_[x,y]H_[0,1] · H_[0,1]H_[z,w] ≈ H_[x,y]H_[z,w]`. -/
theorem hp1 (x y z w : ℕ) (h : x < 8 ∧ y < 8 ∧ z < 8 ∧ w < 8 ∧ x ≠ y ∧ z ≠ w := by decide) :
    D8 n [Hh n x y 0 1, Hh n 0 1 z w] [Hh n x y z w] := by
  have := h8_of hn
  obtain ⟨hx, hy, hz, hw, hxy, hzw⟩ := h
  exact e71 this (e65 n hn) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hxy (by norm_num) hzw

/-- `H_[0,1]H_[x,y] ≈ H_[x,y]H_[0,1]`. -/
theorem hfl (x y : ℕ) (h : x < 8 ∧ y < 8 ∧ x ≠ y ∧ x ≠ 0 ∧ x ≠ 1 ∧ y ≠ 0 ∧ y ≠ 1 := by decide) :
    D8 n [Hh n 0 1 x y] [Hh n x y 0 1] := by
  have := h8_of hn
  obtain ⟨hx, hy, hxy, hx0, hx1, hy0, hy1⟩ := h
  exact e66 this (e65 n hn) (by omega) (by omega) (by omega) (by omega)
    ⟨by norm_num, Ne.symm hx0, Ne.symm hy0, Ne.symm hx1, Ne.symm hy1, hxy⟩

/-- `H_[0,1]H_[x,y] · H_[z,w]H_[0,1] ≈ H_[x,y]H_[z,w]`. -/
theorem hp2 (x y z w : ℕ) (h : (x < 8 ∧ y < 8 ∧ x ≠ y ∧ x ≠ 0 ∧ x ≠ 1 ∧ y ≠ 0 ∧ y ≠ 1) ∧
    (z < 8 ∧ w < 8 ∧ z ≠ w ∧ z ≠ 0 ∧ z ≠ 1 ∧ w ≠ 0 ∧ w ≠ 1) := by decide) :
    D8 n [Hh n 0 1 x y, Hh n z w 0 1] [Hh n x y z w] :=
  (DR.append (hfl hn x y h.1) (hfl hn z w h.2).symm).trans
    (hp1 hn x y z w ⟨h.1.1, h.1.2.1, h.2.1, h.2.2.1, h.1.2.2.1, h.2.2.2.1⟩)

theorem zz1 : D8 n [Zz n 1 5, Zz n 1 4] [Zz n 5 4] := by
  have := h8_of hn
  have k := A5v (n := n) (m := 3) (by omega) [1, 4, 5] rfl (by decide)
    (by intro x hx; simp at hx; omega) [NL.zz 0 2, NL.zz 0 1] [NL.zz 2 1] (by decide)
  simpa [rv, NL.ren, NL.toPG] using k

theorem zx1 : D8 n [Zx n 5 0 1, Zx n 4 0 1] [Zz n 5 4] := by
  have := h8_of hn
  have k := A5v (n := n) (m := 4) (by omega) [0, 1, 4, 5] rfl (by decide)
    (by intro x hx; simp at hx; omega) [NL.zx 3 0 1, NL.zx 2 0 1] [NL.zz 3 2] (by decide)
  simpa [rv, NL.ren, NL.toPG] using k

/-- The renamed left-hand side of (46). -/
abbrev T46L (n : ℕ) : List (PG (2 ^ n)) := [Hh n 2 3 0 1, Hh n 2 4 3 5, Hh n 4 6 5 7,
  Hh n 4 5 6 7, Hh n 0 1 6 7, Zz n 5 4, Hh n 4 6 5 7, Hh n 2 4 3 5]
/-- The renamed right-hand side. -/
abbrev T46R (n : ℕ) : List (PG (2 ^ n)) := [Hh n 2 4 3 5, Hh n 4 6 5 7, Zz n 5 4, Hh n 0 1 6 7,
  Hh n 4 5 6 7, Hh n 4 6 5 7, Hh n 2 4 3 5, Hh n 2 3 0 1]

omit hn in
theorem psiL_false (hn : 3 ≤ n) : psi01 n false (W46L.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn))) =
    [Hh n 2 3 0 1, Hh n 0 1 2 4, Hh n 3 5 0 1, Hh n 0 1 4 6, Hh n 5 7 0 1, Hh n 0 1 4 5,
      Hh n 6 7 0 1, Hh n 0 1 6 7, Zz n 1 5, Zz n 1 4, Hh n 4 6 0 1, Hh n 0 1 5 7, Hh n 2 4 0 1,
      Hh n 0 1 3 5] := by
  simp [psi01, psiG, W46L, W46R, W46L.hL', HadamardPi.Gen.map, gbits, f27_val]

omit hn in
theorem psiL_true (hn : 3 ≤ n) : psi01 n true (W46L.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn))) =
    [Hh n 0 1 2 3, Hh n 2 4 0 1, Hh n 0 1 3 5, Hh n 4 6 0 1, Hh n 0 1 5 7, Hh n 4 5 0 1,
      Hh n 0 1 6 7, Hh n 6 7 0 1, Zx n 5 0 1, Zx n 4 0 1, Hh n 0 1 4 6, Hh n 5 7 0 1,
      Hh n 0 1 2 4, Hh n 3 5 0 1] := by
  simp [psi01, psiG, W46L, W46R, W46L.hL', HadamardPi.Gen.map, gbits, f27_val]

omit hn in
theorem psiR_false (hn : 3 ≤ n) : psi01 n false (W46R.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn))) =
    [Hh n 2 4 0 1, Hh n 0 1 3 5, Hh n 4 6 0 1, Hh n 0 1 5 7, Zz n 1 5, Zz n 1 4, Hh n 6 7 0 1,
      Hh n 0 1 4 5, Hh n 6 7 0 1, Hh n 0 1 4 6, Hh n 5 7 0 1, Hh n 0 1 2 4, Hh n 3 5 0 1,
      Hh n 0 1 2 3] := by
  simp [psi01, psiG, W46L, W46R, W46L.hL', HadamardPi.Gen.map, gbits, f27_val]

omit hn in
theorem psiR_true (hn : 3 ≤ n) : psi01 n true (W46R.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn))) =
    [Hh n 0 1 2 4, Hh n 3 5 0 1, Hh n 0 1 4 6, Hh n 5 7 0 1, Zx n 5 0 1, Zx n 4 0 1,
      Hh n 0 1 6 7, Hh n 4 5 0 1, Hh n 0 1 6 7, Hh n 4 6 0 1, Hh n 0 1 5 7, Hh n 2 4 0 1,
      Hh n 0 1 3 5, Hh n 2 3 0 1] := by
  simp [psi01, psiG, W46L, W46R, W46L.hL', HadamardPi.Gen.map, gbits, f27_val]

theorem imgL (b : Bool) : D8 n (psi01 n b (W46L.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn)))) (T46L n) := by
  cases b
  · rw [psiL_false hn]
    exact DR.append (DR.refl [Hh n 2 3 0 1]) <| DR.append (hp2 hn 2 4 3 5) <|
      DR.append (hp2 hn 4 6 5 7) <| DR.append (hp2 hn 4 5 6 7) <|
      DR.append (DR.refl [Hh n 0 1 6 7]) <| DR.append (zz1 hn) <|
      DR.append (hp1 hn 4 6 5 7) (hp1 hn 2 4 3 5)
  · rw [psiL_true hn]
    exact DR.append (hfl hn 2 3) <| DR.append (hp1 hn 2 4 3 5) <|
      DR.append (hp1 hn 4 6 5 7) <| DR.append (hp1 hn 4 5 6 7) <|
      DR.append (hfl hn 6 7).symm <| DR.append (zx1 hn) <|
      DR.append (hp2 hn 4 6 5 7) (hp2 hn 2 4 3 5)

theorem imgR (b : Bool) : D8 n (psi01 n b (W46R.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn)))) (T46R n) := by
  cases b
  · rw [psiR_false hn]
    exact DR.append (hp1 hn 2 4 3 5) <| DR.append (hp1 hn 4 6 5 7) <|
      DR.append (zz1 hn) <| DR.append (hfl hn 6 7).symm <|
      DR.append (hp2 hn 4 5 6 7) <| DR.append (hp2 hn 4 6 5 7) <|
      DR.append (hp2 hn 2 4 3 5) (hfl hn 2 3)
  · rw [psiR_true hn]
    exact DR.append (hp2 hn 2 4 3 5) <| DR.append (hp2 hn 4 6 5 7) <|
      DR.append (zx1 hn) <| DR.append (DR.refl [Hh n 0 1 6 7]) <|
      DR.append (hp1 hn 4 5 6 7) <| DR.append (hp1 hn 4 6 5 7) <|
      DR.append (hp1 hn 2 4 3 5) (DR.refl [Hh n 2 3 0 1])

theorem avoid01 (l : List (HadamardPi.Gen 6)) :
    ∀ y ∈ l.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn)), ∀ i ∈ gix y, i ≠ 0 ∧ i ≠ 1 := by
  intro y hy i hi
  obtain ⟨y0, -, rfl⟩ := List.mem_map.1 hy
  cases y0 <;> simp [gix, HadamardPi.Gen.map, f27] at hi <;> constructor <;> omega

/-- The relation of (46) at the indices `2, …, 7` is in `GB`. -/
theorem gb46 : GB n (FreeMonoid.ofList (W46L.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn))))
    (FreeMonoid.ofList (W46R.map (HadamardPi.Gen.map (f27 hn) (f27_mono hn)))) := by
  show rsRel (tauA n) (Fig8 n) _ _
  intro c
  refine ⟨?_, ?_⟩
  · rw [hstar_snd, hstar_snd]
    refine hpar_of ?_ c
    simp [parL, pxor, W46L, W46R, W46L.hL', HadamardPi.Gen.map, gbits]
  · have k := (imgL hn c.isH).trans ((e46_ren (h8_of hn) (e65 n hn)).trans (imgR hn c.isH).symm)
    rw [← hstar_psi _ (avoid01 hn W46L) c, ← hstar_psi _ (avoid01 hn W46R) c] at k
    simpa [DR, FreeMonoid.ofList_toList] using k

end Images

end QCert.RealCliffordCH.Sec8
