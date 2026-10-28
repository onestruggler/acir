/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The frame steps: the equations

`T_c · Φ(y) ≈ τ(c, y)₁ · T_{τ(c, y)₂}` on natural-number indices, for every
coset `c` and every kind of generator `y` (`fs_Z*`, `fs_X*`, `fs_H*`, the
letter after `fs_` the generator, the rest the coset), from the moves of
`FrameSteps.lean` and the comparisons of `FrameFS.lean`.
-/
import QCert.RealCliffordCH.Sec8.A.FrameFS

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

section Steps

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g)
include h8 hE T

/-! ### `(-1)_[a]` -/

/-- `τ(H[0,1], (-1)[a])`. -/
theorem fs_Zh {a : ℕ} (ha : a < 2 ^ n) (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g) :
    D8 n [Hh n 0 1 e f, Zz n a g] (tauZHn n a ++ [Hh n 0 1 e f, Zz n 1 g]) := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  unfold tauZHn
  by_cases h0 : a = 0
  · subst h0
    rw [if_pos (Or.inl rfl)]
    have s1 : D8 n [Zz n 1 0, Hh n 0 1 e f, Zz n 1 g] [Hh n 0 1 e f, Zz n 1 0, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_zz10 h8 hE T) (by simp) (by simp)
    exact (s1.trans (D8.seg [Hh n 0 1 e f] [] (tl_Zh0 h8 hg (Ne.symm hag) hg1)
      (by simp) (by simp))).symm
  by_cases h1 : a = 1
  · subst h1
    rw [if_pos (Or.inr rfl)]
    exact (D8.seg [] [Hh n 0 1 e f, Zz n 1 g] (tl_Z11 h8) (by simp) (by simp)).symm
  · rw [if_neg (by omega)]
    have s1 : D8 n [Zx n a 0 1, Hh n 0 1 e f, Zz n 1 g]
        [Hh n 0 1 e f, Zx n 1 0 1, Zx n a 0 1, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_zxa01 h8 hE T ha h0 h1 hae haf) (by simp) (by simp)
    exact (s1.trans (D8.seg [Hh n 0 1 e f] [] (tl_Zh h8 ha hg h0 h1 hg1 hag)
      (by simp) (by simp))).symm

/-- `τ(H[0,1](-1)[1], (-1)[a])`. -/
theorem fs_Zhz {a : ℕ} (ha : a < 2 ^ n) (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g) :
    D8 n [Hh n 0 1 e f, Zz n 1 g, Zz n a g] (tauZHn n a ++ [Hh n 0 1 e f]) := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  unfold tauZHn
  by_cases h0 : a = 0
  · subst h0
    rw [if_pos (Or.inl rfl)]
    have s1 : D8 n [Hh n 0 1 e f, Zz n 1 g, Zz n 0 g] [Hh n 0 1 e f, Zz n 1 0] :=
      D8.seg [Hh n 0 1 e f] [] (tl_Zhz0 h8 hg (Ne.symm hag) hg1) (by simp) (by simp)
    exact s1.trans (push_zz10 h8 hE T).symm
  by_cases h1 : a = 1
  · subst h1
    rw [if_pos (Or.inr rfl)]
    have s1 : D8 n [Hh n 0 1 e f, Zz n 1 g, Zz n 1 g] [Hh n 0 1 e f, Zz n 1 1] :=
      D8.seg [Hh n 0 1 e f] [] (tl_Zhz1 h8 hg hg1) (by simp) (by simp)
    have s2 : D8 n [Hh n 0 1 e f, Zz n 1 1] [Hh n 0 1 e f] :=
      D8.seg [Hh n 0 1 e f] [] (tl_Z11 h8) (by simp) (by simp)
    have s3 : D8 n [Zz n 1 1, Hh n 0 1 e f] [Hh n 0 1 e f] :=
      D8.seg [] [Hh n 0 1 e f] (tl_Z11 h8) (by simp) (by simp)
    exact (s1.trans s2).trans s3.symm
  · rw [if_neg (by omega)]
    have s1 : D8 n [Hh n 0 1 e f, Zz n 1 g, Zz n a g] [Hh n 0 1 e f, Zx n 1 0 1, Zx n a 0 1] :=
      D8.seg [Hh n 0 1 e f] [] (tl_Zhz h8 ha hg h0 h1 hg1 hag) (by simp) (by simp)
    exact s1.trans (push_zxa01 h8 hE T ha h0 h1 hae haf).symm

/-! ### `X_[a,b]` -/

/-- `τ(ε, X_[a,b])`. -/
theorem fs_Xe {a b : ℕ} (hab : a < b) (hb : b < 2 ^ n) (hag : a ≠ g) (hbg : b ≠ g) :
    D8 n [Zx n g a b] (w2n n a b ++ [Zz n 1 g]) := by
  obtain ⟨-, -, hg, -, -, -, -, -, -, -, hg1⟩ := T
  unfold w2n
  by_cases h1 : a = 1
  · subst h1
    rw [if_pos (Or.inl rfl), if_pos rfl]
    exact tl_Xe1b h8 hb hg (by omega) hg1 hbg
  by_cases h2 : b = 1
  · subst h2
    have : a = 0 := by omega
    subst this
    rw [if_pos (Or.inr rfl), if_neg (by omega)]
    exact tl_Xe01 h8 hg (Ne.symm hag) hg1
  · rw [if_neg (by omega)]
    exact tl_Xeab h8 (by omega) hb hg (by omega) h1 h2 hg1 hag hbg

/-- `τ((-1)[1], X_[a,b])`. -/
theorem fs_Xz {a b : ℕ} (hab : a < b) (hb : b < 2 ^ n) (hag : a ≠ g) (hbg : b ≠ g) :
    D8 n [Zz n 1 g, Zx n g a b] [Zx n 1 a b] := by
  obtain ⟨-, -, hg, -, -, -, -, -, -, -, hg1⟩ := T
  exact tl_Xz h8 (by omega) hb (by omega) hg1 hag hbg hg

/-- `τ(H[0,1], X_[a,b])`. -/
theorem fs_Xh {a b : ℕ} (hab : a < b) (hb : b < 2 ^ n) (hae : a ≠ e) (haf : a ≠ f)
    (hag : a ≠ g) (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g) :
    D8 n [Hh n 0 1 e f, Zx n g a b] (tXn n true a b ++ [Hh n 0 1 e f, Zz n 1 g]) := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  have ha : a < 2 ^ n := by omega
  unfold tXn
  by_cases h01 : a = 0 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h01
    simp only [and_self, if_true, List.singleton_append]
    have s1 : D8 n [Zx n 1 0 1, Hh n 0 1 e f, Zz n 1 g]
        [Hh n 0 1 e f, Zx n 1 0 1, Zx n 1 0 1, Zx n 1 0 1, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_zx101 h8 hE T) (by simp) (by simp)
    exact (s1.trans (D8.seg [Hh n 0 1 e f] [] (tl_Xh01 h8 hg (Ne.symm hag) hg1)
      (by simp) (by simp))).symm
  rw [if_neg h01]
  by_cases h0 : a = 0
  · subst h0
    rw [if_pos rfl, if_pos rfl]
    have hb1 : b ≠ 1 := fun h => h01 ⟨rfl, h⟩
    have c1 : D8 n [Hh n b 1 0 1, Hh n 0 1 e f] [Hh n b 1 e f] :=
      e71 h8 hE hb (by omega) (by omega) (by omega) he hf hb1 (by omega) hef
    have s1 : D8 n [Xx n 0 1 0 b, Hh n b 1 0 1, Hh n 0 1 e f, Zz n 1 g]
        [Xx n 0 1 0 b, Hh n b 1 e f, Zz n 1 g] :=
      D8.seg [Xx n 0 1 0 b] [Zz n 1 g] c1 (by simp) (by simp)
    have s2 : D8 n [Xx n 0 1 0 b, Hh n b 1 e f, Zz n 1 g]
        [Hh n 0 1 e f, Zx n 1 0 1, Xx n 0 1 0 b, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_xx010b h8 hE T hb (by omega) hb1 hbe hbf) (by simp) (by simp)
    exact ((s1.trans s2).trans (D8.seg [Hh n 0 1 e f] []
      (tl_Xh0b h8 hb hg (by omega) hb1 (Ne.symm hag) hg1 hbg) (by simp) (by simp))).symm
  rw [if_neg h0]
  by_cases h1 : a = 1
  · subst h1
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    have hb0 : b ≠ 0 := by omega
    have hb1 : b ≠ 1 := by omega
    have c1 : D8 n [Hh n 0 b 0 1, Hh n 0 1 e f] [Hh n 0 b e f] :=
      e71 h8 hE (by omega) hb (by omega) (by omega) he hf (by omega) (by omega) hef
    have s1 : D8 n [Zx n b 1 b, Hh n 0 b 0 1, Hh n 0 1 e f, Zz n 1 g]
        [Zx n b 1 b, Hh n 0 b e f, Zz n 1 g] :=
      D8.seg [Zx n b 1 b] [Zz n 1 g] c1 (by simp) (by simp)
    have s2 : D8 n [Zx n b 1 b, Hh n 0 b e f, Zz n 1 g] [Hh n 0 1 e f, Zx n b 1 b, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_zxb1b h8 hE T hb hb0 hb1 hbe hbf) (by simp) (by simp)
    exact ((s1.trans s2).trans (D8.seg [Hh n 0 1 e f] []
      (tl_Xh1b h8 hb hg hb1 hg1 hbg) (by simp) (by simp))).symm
  · rw [if_neg h1]
    have s1 : D8 n [Xx n a b 0 1, Hh n 0 1 e f, Zz n 1 g]
        [Hh n 0 1 e f, Zx n 1 0 1, Xx n a b 0 1, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_xxab01 h8 hE T ha hb (by omega) h0 h1 hae haf (by omega)
        (by omega) hbe hbf) (by simp) (by simp)
    exact (s1.trans (D8.seg [Hh n 0 1 e f] []
      (tl_Xhab h8 ha hb hg (by omega) h0 h1 (by omega) (by omega) hg1 hag hbg)
      (by simp) (by simp))).symm

/-- `τ(H[0,1](-1)[1], X_[a,b])`. -/
theorem fs_Xhz {a b : ℕ} (hab : a < b) (hb : b < 2 ^ n) (hae : a ≠ e) (haf : a ≠ f)
    (hag : a ≠ g) (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g) :
    D8 n [Hh n 0 1 e f, Zz n 1 g, Zx n g a b] (tXn n false a b ++ [Hh n 0 1 e f]) := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  have ha : a < 2 ^ n := by omega
  unfold tXn
  by_cases h01 : a = 0 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h01
    simp only [and_self, if_true, Bool.false_eq_true, if_false, List.singleton_append]
    have s1 : D8 n [Hh n 0 1 e f, Zz n 1 g, Zx n g 0 1]
        [Hh n 0 1 e f, Zx n 1 0 1, Zx n 1 0 1, Zx n 0 0 1] :=
      (D8.seg [Hh n 0 1 e f] [] (tl_Xhz01 h8 hg (Ne.symm hag) hg1) (by simp) (by simp)).symm
    exact s1.trans (push_zx001 h8 hE T).symm
  rw [if_neg h01]
  by_cases h0 : a = 0
  · subst h0
    rw [if_pos rfl, if_pos rfl]
    have hb1 : b ≠ 1 := fun h => h01 ⟨rfl, h⟩
    have c1 : D8 n [Hh n b 1 0 1, Hh n 0 1 e f] [Hh n b 1 e f] :=
      e71 h8 hE hb (by omega) (by omega) (by omega) he hf hb1 (by omega) hef
    have s1 : D8 n [Xx n 0 1 0 b, Hh n b 1 0 1, Hh n 0 1 e f] [Xx n 0 1 0 b, Hh n b 1 e f] :=
      D8.seg [Xx n 0 1 0 b] [] c1 (by simp) (by simp)
    have s2 : D8 n [Hh n 0 1 e f, Zx n 1 0 1, Xx n 0 1 0 b]
        [Hh n 0 1 e f, Zz n 1 g, Zx n g 0 b] :=
      D8.seg [Hh n 0 1 e f] [] (tl_Xhz0b h8 hb hg (by omega) hb1 (Ne.symm hag) hg1 hbg)
        (by simp) (by simp)
    exact ((s1.trans (push_xx010b h8 hE T hb (by omega) hb1 hbe hbf)).trans s2).symm
  rw [if_neg h0]
  by_cases h1 : a = 1
  · subst h1
    rw [if_pos rfl, if_pos rfl]
    simp only [Bool.false_eq_true, if_false, List.singleton_append, List.cons_append]
    have hb0 : b ≠ 0 := by omega
    have hb1 : b ≠ 1 := by omega
    have c1 : D8 n [Hh n 0 b 0 1, Hh n 0 1 e f] [Hh n 0 b e f] :=
      e71 h8 hE (by omega) hb (by omega) (by omega) he hf (by omega) (by omega) hef
    have s1 : D8 n [Xx n 0 1 1 b, Hh n 0 b 0 1, Hh n 0 1 e f] [Xx n 0 1 1 b, Hh n 0 b e f] :=
      D8.seg [Xx n 0 1 1 b] [] c1 (by simp) (by simp)
    have s2 : D8 n [Hh n 0 1 e f, Zx n 1 0 1, Xx n 0 1 1 b]
        [Hh n 0 1 e f, Zz n 1 g, Zx n g 1 b] :=
      D8.seg [Hh n 0 1 e f] [] (tl_Xhz1b h8 hb hg hb0 hb1 hg1 hbg) (by simp) (by simp)
    exact ((s1.trans (push_xx011b h8 hE T hb hb0 hb1 hbe hbf)).trans s2).symm
  · rw [if_neg h1]
    have s2 : D8 n [Hh n 0 1 e f, Zx n 1 0 1, Xx n a b 0 1]
        [Hh n 0 1 e f, Zz n 1 g, Zx n g a b] :=
      D8.seg [Hh n 0 1 e f] []
        (tl_Xhzab h8 ha hb hg (by omega) h0 h1 (by omega) (by omega) hg1 hag hbg)
        (by simp) (by simp)
    exact ((push_xxab01 h8 hE T ha hb (by omega) h0 h1 hae haf (by omega) (by omega) hbe
      hbf).trans s2).symm

/-! ### `H_[a,b]` -/

omit T in
/-- `τ(ε, H_[a,b])`. -/
theorem fs_He {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (he : e < 2 ^ n)
    (hf : f < 2 ^ n) (hef : e ≠ f) : D8 n [Hh n a b e f] [Hh n a b 0 1, Hh n 0 1 e f] :=
  (e71 h8 hE ha hb (by omega) (by omega) he hf hab (by omega) hef).symm

/-- `τ(H[0,1], H_[a,b])`. -/
theorem fs_Hh {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (hae : a ≠ e)
    (haf : a ≠ f) (hbe : b ≠ e) (hbf : b ≠ f) :
    D8 n [Hh n 0 1 e f, Hh n a b e f] [Hh n 0 1 a b] := by
  obtain ⟨he, hf, -, hef, -, -, -, -, -, -, -⟩ := T
  exact (D8.seg [Hh n 0 1 e f] [] (e66 h8 hE ha hb he hf ⟨hab, hae, haf, hbe, hbf, hef⟩)
    (by simp) (by simp)).trans (e71 h8 hE (by omega) (by omega) he hf ha hb (by omega) hef hab)

/-- `τ((-1)[1], H_[a,b])`. -/
theorem fs_Hz {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (hae : a ≠ e)
    (haf : a ≠ f) (hag : a ≠ g) (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g) :
    D8 n [Zz n 1 g, Hh n a b e f] (w3n n a b ++ [Hh n 0 1 e f, Zz n 1 g]) := by
  have T' := T
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T'
  have c1 : D8 n [Hh n a b 0 1, Hh n 0 1 e f] [Hh n a b e f] :=
    e71 h8 hE ha hb (by omega) (by omega) he hf hab (by omega) hef
  unfold w3n
  by_cases h1 : a = 1 ∨ b = 1
  · rw [if_pos h1]
    have s1 : D8 n [Zx n b a b, Hh n a b 0 1, Hh n 0 1 e f, Zz n 1 g]
        [Zx n b a b, Hh n a b e f, Zz n 1 g] :=
      D8.seg [Zx n b a b] [Zz n 1 g] c1 (by simp) (by simp)
    have s2 : D8 n [Zx n b a b, Hh n a b e f, Zz n 1 g]
        [Hh n a b e f, Zx n b a b, Zx n b a b, Zx n b a b, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] (push_zxbab h8 hE T ha hb hab hae haf hbe hbf) (by simp) (by simp)
    have s3 : D8 n [Zz n 1 g, Hh n a b e f] [Hh n a b e f, Zx n a b a, Zz n 1 g] :=
      push_zz1g_in h8 hE T ha hb hab h1 hag hbg hae haf hbe hbf
    have s4 : D8 n [Hh n a b e f, Zx n a b a, Zz n 1 g]
        [Hh n a b e f, Zx n b a b, Zx n b a b, Zx n b a b, Zz n 1 g] :=
      D8.seg [Hh n a b e f] [Zz n 1 g] (tl_Hz h8 ha hb hab) (by simp) (by simp)
    exact (s3.trans s4).trans (s1.trans s2).symm
  · rw [if_neg h1]
    push Not at h1
    exact (push_zz1g_out h8 hE T ha hb hab h1.1 h1.2 hag hbg hae haf hbe hbf).trans
      (D8.seg [] [Zz n 1 g] c1 (by simp) (by simp)).symm

/-- `τ(H[0,1](-1)[1], H_[a,b])`. -/
theorem fs_Hhz {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (hae : a ≠ e)
    (haf : a ≠ f) (hag : a ≠ g) (hbe : b ≠ e) (hbf : b ≠ f) (hbg : b ≠ g) :
    D8 n [Hh n 0 1 e f, Zz n 1 g, Hh n a b e f] (w7n n a b ++ [Zz n 1 g]) := by
  have hh := fs_Hh h8 hE T ha hb hab hae haf hbe hbf
  unfold w7n
  by_cases h1 : a = 1 ∨ b = 1
  · rw [if_pos h1]
    have s1 : D8 n [Hh n 0 1 e f, Zz n 1 g, Hh n a b e f]
        [Hh n 0 1 e f, Hh n a b e f, Zx n a b a, Zz n 1 g] :=
      D8.seg [Hh n 0 1 e f] [] (push_zz1g_in h8 hE T ha hb hab h1 hag hbg hae haf hbe hbf)
        (by simp) (by simp)
    have s2 : D8 n [Hh n 0 1 e f, Hh n a b e f, Zx n a b a, Zz n 1 g]
        [Hh n 0 1 a b, Zx n a b a, Zz n 1 g] :=
      D8.seg [] [Zx n a b a, Zz n 1 g] hh (by simp) (by simp)
    exact (s1.trans s2).trans (D8.seg [Hh n 0 1 a b] [Zz n 1 g] (tl_Hhz h8 ha hb hab)
      (by simp) (by simp))
  · rw [if_neg h1]
    push Not at h1
    have s1 : D8 n [Hh n 0 1 e f, Zz n 1 g, Hh n a b e f]
        [Hh n 0 1 e f, Hh n a b e f, Zz n 1 g] :=
      D8.seg [Hh n 0 1 e f] []
        (push_zz1g_out h8 hE T ha hb hab h1.1 h1.2 hag hbg hae haf hbe hbf) (by simp) (by simp)
    have s2 : D8 n [Hh n 0 1 e f, Hh n a b e f, Zz n 1 g] [Hh n 0 1 a b, Zz n 1 g] :=
      D8.seg [] [Zz n 1 g] hh (by simp) (by simp)
    exact s1.trans s2

end Steps

end QCert.RealCliffordCH.Sec8
