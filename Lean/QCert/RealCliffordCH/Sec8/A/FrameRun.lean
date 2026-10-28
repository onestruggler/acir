/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The frame: the coset action along a word

With the coset representatives `T_c` of `FrameSteps.lean` (`Tc`, and their
inverses `Tc'`), every step of the coset action is `T_c · Φ(y) ≈ τ(c, y)₁ ·
T_{τ(c, y)₂}` (`fs_all`, from the cases of `FrameCases.lean`), so along a
word away from the tags `T_c · Φ(w) ≈ τ**(c, w)₁ · T_{τ**(c, w)₂}`
(`frame_run`).  The coset reached is `c` moved by the parities of `w`
(`hstar_snd`: the number of `H` letters and the number of `(-1)` and `X`
letters, mod 2).  Hence a pair of words with the same parities whose frame
images are equal by Figure 8 satisfies hypothesis (b) of the
Reidemeister–Schreier theorem (`good_frame`).
-/
import QCert.RealCliffordCH.Sec8.A.FrameCases

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

theorem ix_fin (a : Fin (2 ^ n)) : ix n (a : ℕ) = a := Fin.ext (Nat.mod_eq_of_lt a.2)

/-! ## The coset representatives -/

variable (n) in
/-- The coset representatives over `𝒫_N`, with the tags `e, f, g`. -/
def Tc (e f g : ℕ) : Cos → List (PG (2 ^ n))
  | .e => []
  | .z => [Zz n 1 g]
  | .h => [Hh n 0 1 e f]
  | .hz => [Hh n 0 1 e f, Zz n 1 g]

variable (n) in
/-- Their inverses. -/
def Tc' (e f g : ℕ) : Cos → List (PG (2 ^ n))
  | .e => []
  | .z => [Zz n 1 g]
  | .h => [Hh n 0 1 e f]
  | .hz => [Zz n 1 g, Hh n 0 1 e f]

theorem Tc_cancel (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g) (c : Cos) :
    D8 n (Tc n e f g c ++ Tc' n e f g c) [] := by
  obtain ⟨he, hf, hg, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have zs : D8 n [Zz n 1 g, Zz n 1 g] [] := (zz_sq (by omega) hg).toD8
  have hs : D8 n [Hh n 0 1 e f, Hh n 0 1 e f] [] :=
    hh_sq h8 hE (by omega) (by omega) he hf ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  cases c with
  | e => exact DR.refl _
  | z => exact zs
  | h => exact hs
  | hz =>
    exact (D8.seg [Hh n 0 1 e f] [Hh n 0 1 e f] zs (by simp [Tc, Tc']) (by simp)).trans hs

/-! ## The words of `τ` on natural-number indices -/

section Conv

variable (a b : Fin (2 ^ n))

theorem conv_zz : (FreeMonoid.of (PG.zz (o1 n) a)).toList = [Zz n 1 a] := by
  simp [Zz, ix_fin]

theorem tauZH_list : (tauZH n a).toList = tauZHn n a := by
  unfold tauZH tauZHn
  split_ifs <;> simp [Zz, Zx, ix_fin]

theorem ix_ite (p : Prop) [Decidable p] (x y : Fin (2 ^ n)) :
    ix n (if p then (x : ℕ) else y) = if p then x else y := by
  split_ifs <;> exact ix_fin _

theorem tauX_list (isH : Bool) : (tauX n isH a b).toList = tXn n isH a b := by
  unfold tauX tXn
  by_cases h01 : (a : ℕ) = 0 ∧ (b : ℕ) = 1
  · rw [if_pos h01, if_pos h01]
    cases isH <;> simp [Zx, ix_fin]
  rw [if_neg h01, if_neg h01]
  by_cases h0 : (a : ℕ) = 0
  · rw [if_pos h0, if_pos h0]
    have e1 : notZero n a b = b := by simp [notZero, h0]
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, e1, Xx, Hh,
      ix_fin, if_pos h0]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : (a : ℕ) = 1
  · rw [if_pos h1, if_pos h1]
    have e1 : notOne n a b = b := by simp [notOne, h1]
    cases isH <;> simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      e1, Xx, Zx, Hh, ix_fin, if_pos h1, if_true, if_false, Bool.false_eq_true,
      List.cons_append, List.nil_append] <;> rfl
  rw [if_neg h1, if_neg h1]
  simp [Xx, ix_fin]

end Conv

end QCert.RealCliffordCH.Sec8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

section Conv2

variable (a b : Fin (2 ^ n))

theorem tauEX_list (h : a < b) : (tauA n .e (.X a b h)).1.toList = w2n n a b := by
  simp only [tauA, w2n]
  by_cases h1 : (a : ℕ) = 1 ∨ (b : ℕ) = 1
  · rw [if_pos h1, if_pos h1]
    by_cases ha : (a : ℕ) = 1
    · have e1 : notOne n a b = b := by simp [notOne, ha]
      simp only [e1, if_pos ha, FreeMonoid.toList_of, Zx, ix_fin]
    · have e1 : notOne n a b = a := by simp [notOne, ha]
      simp only [e1, if_neg ha, FreeMonoid.toList_of, Zx, ix_fin]
  · rw [if_neg h1, if_neg h1]
    simp [Zx, ix_fin]

theorem tauZH_list' (h : a < b) : (tauA n .z (.H a b h)).1.toList = w3n n a b := by
  simp only [tauA, w3n]
  split_ifs <;> simp [Zx, Hh, ix_fin]

theorem tauHZH_list (h : a < b) : (tauA n .hz (.H a b h)).1.toList = w7n n a b := by
  simp only [tauA, w7n]
  split_ifs <;> simp [Zx, Hh, ix_fin]

end Conv2

/-- The indices of a generator. -/
def gix {N : ℕ} : HG N → List ℕ
  | .Z a => [a]
  | .X a b _ => [a, b]
  | .H a b _ => [a, b]

/-- Every step of the coset action. -/
theorem fs_all (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g) (c : Cos)
    (y : HG (2 ^ n)) (hy : ∀ i ∈ gix y, i ≠ e ∧ i ≠ f ∧ i ≠ g) :
    D8 n (Tc n e f g c ++ phiG n e f g y)
      ((tauA n c y).1.toList ++ Tc n e f g (tauA n c y).2) := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  cases y with
  | Z a =>
    obtain ⟨hae, haf, hag⟩ := hy a (by simp [gix])
    have ha : (a : ℕ) < 2 ^ n := a.2
    cases c with
    | e =>
      simp only [Tc, phiG, tauA, conv_zz, List.nil_append, List.singleton_append]
      exact tl_Ze h8 ha hg hg1 hag
    | z =>
      simp only [Tc, phiG, tauA, conv_zz, List.singleton_append, List.append_nil]
      exact tl_Zz h8 ha hg hg1 hag
    | h =>
      simp only [Tc, phiG, tauA, tauZH_list, List.singleton_append]
      exact fs_Zh h8 hE T ha hae haf hag
    | hz =>
      simp only [Tc, phiG, tauA, tauZH_list, List.cons_append, List.nil_append]
      exact fs_Zhz h8 hE T ha hae haf hag
  | X a b hab =>
    obtain ⟨hae, haf, hag⟩ := hy a (by simp [gix])
    obtain ⟨hbe, hbf, hbg⟩ := hy b (by simp [gix])
    have hb : (b : ℕ) < 2 ^ n := b.2
    have hab' : (a : ℕ) < b := hab
    cases c with
    | e =>
      simp only [Tc, phiG, List.nil_append]
      rw [tauEX_list a b hab]
      exact fs_Xe h8 hE T hab' hb hag hbg
    | z =>
      simp only [Tc, phiG, tauA, List.append_nil, List.singleton_append]
      have : (FreeMonoid.of (PG.zx (o1 n) a b)).toList = [Zx n 1 a b] := by simp [Zx, ix_fin]
      rw [this]
      exact fs_Xz h8 hE T hab' hb hag hbg
    | h =>
      simp only [Tc, phiG, tauA, tauX_list, List.singleton_append]
      exact fs_Xh h8 hE T hab' hb hae haf hag hbe hbf hbg
    | hz =>
      simp only [Tc, phiG, tauA, tauX_list, List.cons_append, List.nil_append]
      exact fs_Xhz h8 hE T hab' hb hae haf hag hbe hbf hbg
  | H a b hab =>
    obtain ⟨hae, haf, hag⟩ := hy a (by simp [gix])
    obtain ⟨hbe, hbf, hbg⟩ := hy b (by simp [gix])
    have ha : (a : ℕ) < 2 ^ n := a.2
    have hb : (b : ℕ) < 2 ^ n := b.2
    have hab' : (a : ℕ) ≠ b := fun e => absurd (Fin.lt_def.1 hab) (by omega)
    cases c with
    | e =>
      simp only [Tc, phiG, tauA, List.nil_append]
      have : (FreeMonoid.of (PG.hh a b (o0 n) (o1 n))).toList = [Hh n a b 0 1] := by
        simp [Hh, ix_fin]
      rw [this]
      exact fs_He h8 hE ha hb hab' he hf hef
    | z =>
      simp only [Tc, phiG]
      rw [tauZH_list' a b hab]
      exact fs_Hz h8 hE T ha hb hab' hae haf hag hbe hbf hbg
    | h =>
      simp only [Tc, phiG, tauA, List.append_nil]
      have : (FreeMonoid.of (PG.hh (o0 n) (o1 n) a b)).toList = [Hh n 0 1 a b] := by
        simp [Hh, ix_fin]
      rw [this]
      exact fs_Hh h8 hE T ha hb hab' hae haf hbe hbf
    | hz =>
      simp only [Tc, phiG, List.cons_append, List.nil_append]
      rw [tauHZH_list a b hab]
      exact fs_Hhz h8 hE T ha hb hab' hae haf hag hbe hbf hbg

end QCert.RealCliffordCH.Sec8

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Along a word -/

/-- A word away from the tags. -/
def Away (e f g : ℕ) {N : ℕ} (w : Word (HG N)) : Prop :=
  ∀ y ∈ w.toList, ∀ i ∈ gix y, i ≠ e ∧ i ≠ f ∧ i ≠ g

theorem frame_run (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g)
    (w : Word (HG (2 ^ n))) (hw : Away e f g w) (c : Cos) :
    D8 n (Tc n e f g c ++ phiW n e f g w)
      ((hstar (tauA n) c w).1.toList ++ Tc n e f g (hstar (tauA n) c w).2) := by
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => exact DR.rfl' (by simp [phiW_one, hstar_one])
  | mul_of y w ih =>
    have hy : ∀ i ∈ gix y, i ≠ e ∧ i ≠ f ∧ i ≠ g := hw y (by simp)
    have hw' : Away e f g w := fun z hz => hw z (by simp [hz])
    rw [hstar_mul, hstar_of, phiW_mul, phiW_of]
    have s1 := DR.right (phiW n e f g w) (fs_all h8 hE T c y hy)
    have s2 := DR.left (tauA n c y).1.toList (ih hw' (tauA n c y).2)
    refine (DR.rfl' (by simp)).trans (s1.trans ((DR.rfl' (by simp)).trans (s2.trans
      (DR.rfl' (by simp [FreeMonoid.toList_mul])))))

/-! ## The cosets reached -/

/-- The parities of a generator: an `H` letter, a `(-1)` or `X` letter. -/
def gbits {N : ℕ} : HG N → Bool × Bool
  | .Z _ => (false, true)
  | .X _ _ _ => (false, true)
  | .H _ _ _ => (true, false)

/-- A coset moved by parities. -/
def Cos.act : Cos → Bool × Bool → Cos
  | c, (false, false) => c
  | .e, (true, false) => .h
  | .z, (true, false) => .hz
  | .h, (true, false) => .e
  | .hz, (true, false) => .z
  | .e, (false, true) => .z
  | .z, (false, true) => .e
  | .h, (false, true) => .hz
  | .hz, (false, true) => .h
  | .e, (true, true) => .hz
  | .z, (true, true) => .h
  | .h, (true, true) => .z
  | .hz, (true, true) => .e

theorem tauA_snd (c : Cos) (y : HG (2 ^ n)) : (tauA n c y).2 = c.act (gbits y) := by
  cases c <;> cases y <;> rfl

theorem hstar_snd (w : Word (HG (2 ^ n))) (c : Cos) :
    (hstar (tauA n) c w).2 = w.toList.foldl (fun c y => c.act (gbits y)) c := by
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => rfl
  | mul_of y w ih =>
    rw [hstar_mul, hstar_of, ih, tauA_snd]
    simp [FreeMonoid.toList_mul]

/-! ## Hypothesis (b) from the frame -/

/-- A pair of words with the same parities whose frame images are equal by
Figure 8 satisfies hypothesis (b). -/
theorem good_frame (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g)
    {w w' : Word (HG (2 ^ n))} (hw : Away e f g w) (hw' : Away e f g w')
    (hpar : ∀ c : Cos, w.toList.foldl (fun c y => c.act (gbits y)) c =
      w'.toList.foldl (fun c y => c.act (gbits y)) c)
    (hphi : D8 n (phiW n e f g w) (phiW n e f g w')) : rsRel (tauA n) (Fig8 n) w w' := by
  intro c
  have hc : (hstar (tauA n) c w).2 = (hstar (tauA n) c w').2 := by
    rw [hstar_snd, hstar_snd, hpar]
  refine ⟨hc, ?_⟩
  set c'' := (hstar (tauA n) c w).2
  have k := frame_run h8 hE T w hw c
  have k' := frame_run h8 hE T w' hw' c
  rw [← hc] at k'
  have can := Tc_cancel h8 hE T c''
  set A := (hstar (tauA n) c w).1.toList
  set A' := (hstar (tauA n) c w').1.toList
  have ins : ∀ B : List (PG (2 ^ n)), D8 n B ((B ++ Tc n e f g c'') ++ Tc' n e f g c'') := by
    intro B
    have := DR.left B can
    exact (DR.rfl' (by simp)).trans (this.symm.trans (DR.rfl' (by simp)))
  have s2 : D8 n ((A ++ Tc n e f g c'') ++ Tc' n e f g c'')
      ((Tc n e f g c ++ phiW n e f g w) ++ Tc' n e f g c'') := DR.right _ k.symm
  have s3 : D8 n ((Tc n e f g c ++ phiW n e f g w) ++ Tc' n e f g c'')
      ((Tc n e f g c ++ phiW n e f g w') ++ Tc' n e f g c'') := DR.right _ (DR.left _ hphi)
  have s4 : D8 n ((Tc n e f g c ++ phiW n e f g w') ++ Tc' n e f g c'')
      ((A' ++ Tc n e f g c'') ++ Tc' n e f g c'') := DR.right _ k'
  have d : D8 n A A' := (ins A).trans (s2.trans (s3.trans (s4.trans (ins A').symm)))
  simpa [DR, FreeMonoid.ofList_toList] using d

end QCert.RealCliffordCH.Sec8
