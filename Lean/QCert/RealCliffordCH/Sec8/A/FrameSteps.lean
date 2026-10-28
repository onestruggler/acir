/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The frame: one step of the coset action

For three tags `e, f, g` (`e, f` away from `0, 1`, `g ≠ 1`; `FT`), the coset
representatives are written over `𝒫_N` with the tags as

* `T_ε = ε`, `T_{(-1)[1]} = (-1)_[1](-1)_[g]`, `T_{H[0,1]} = H_[0,1]H_[e,f]`,
  `T_{H[0,1](-1)[1]} = H_[0,1]H_[e,f] · (-1)_[1](-1)_[g]`,

and a generator `y` of `𝒢_N` away from the tags by its frame image `Φ(y)`
(`phiG`: `(-1)_[a] ↦ (-1)_[a](-1)_[g]`, `X_[a,b] ↦ (-1)_[g]X_[a,b]`,
`H_[a,b] ↦ H_[a,b]H_[e,f]`).  Each step of the coset action `τ` of
Definition A.2 is then the equation `T_c · Φ(y) ≈ τ(c, y)₁ · T_{τ(c, y)₂}`
of Figure 8.  This file proves those equations on natural-number indices,
case by case (the cases of `τ`), each by moving the Hadamard-free letters
past the letters `H_[a,b]H_[c,d]` (`push1`), reversing a pair (`flip1`),
contracting two letters (Equation (71)) and Corollary A.5.  Every case was
checked numerically first.
-/
import QCert.RealCliffordCH.Sec8.A.ItemATools
import QCert.RealCliffordCH.Sec8.A.ItemBPhi

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- Bounds of a list of `NL` letters. -/
macro "bdl" : tactic => `(tactic| (simp only [List.forall_mem_cons, NL.Bd, List.mem_nil_iff,
  false_implies, implies_true, and_true] <;> omega))

/-- Bounds of one `NL` letter. -/
macro "bd1" : tactic => `(tactic| (simp only [NL.Bd] <;> omega))

theorem negL_one (u : NL) (v : ℕ) : negL [u] v = u.neg v := by
  simp only [negL, permL, id]; cases u.neg v <;> rfl

theorem twL_one (u : NL) (a b : ℕ) :
    twL n [u] a b = if u.neg a = u.neg b then [] else [Zx n (u.perm a) (u.perm b) (u.perm a)] := by
  simp [twL, negL_one, permL]

/-- The inverse of `(-1)_[m]X_[c,d]`. -/
theorem inv_zx (m c d v : ℕ) :
    permL [NL.zx m c d, NL.zx (swN c d m) c d] v = v ∧
      negL [NL.zx m c d, NL.zx (swN c d m) c d] v = false := by
  refine ⟨by simp [permL, NL.perm, swN_swN], ?_⟩
  simp only [negL, permL, NL.neg, NL.perm, id, swN_swN]
  by_cases h : v = m
  · subst h; simp
  · have h' : swN c d v ≠ swN c d m := fun e => h (swN_inj c d e)
    simp [h, h']

/-- The inverse of `X_[a,b]X_[c,d]`. -/
theorem inv_xx (a b c d v : ℕ) :
    permL [NL.xx a b c d, NL.xx c d a b] v = v ∧ negL [NL.xx a b c d, NL.xx c d a b] v = false := by
  refine ⟨by simp [permL, NL.perm, swN_swN], ?_⟩
  simp [negL, permL, NL.neg]

/-- Moving one Hadamard-free letter with an inverse past `H_[a,b]H_[c,d]`. -/
theorem push1 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {u u' : NL} (hu : u.Bd n) (hu' : u'.Bd n)
    (pu : u.Pr) (pu' : u'.Pr) (hinv : ∀ v, permL [u, u'] v = v ∧ negL [u, u'] v = false)
    {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (h : Distinct4 a b c d) :
    D8 n [u.toPG n, Hh n a b c d]
      (Hh n (u.perm a) (u.perm b) (u.perm c) (u.perm d) :: (twL n [u] c d ++ twL n [u] a b ++
        [u.toPG n])) := by
  have k := push_hh h8 hE (P := [u]) (P' := [u']) (by simpa using hu) (by simpa using hu')
    (by simpa using pu) (by simpa using pu') (fun v _ => by simpa using hinv v) ha hb hc hd h
  simpa [permL] using k

/-- The tags of a frame. -/
structure FT (n e f g : ℕ) : Prop where
  he : e < 2 ^ n
  hf : f < 2 ^ n
  hg : g < 2 ^ n
  hef : e ≠ f
  heg : e ≠ g
  hfg : f ≠ g
  he0 : e ≠ 0
  he1 : e ≠ 1
  hf0 : f ≠ 0
  hf1 : f ≠ 1
  hg1 : g ≠ 1

section Steps

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : FT n e f g)
include h8 hE T

/-! ### Moving letters past `H_[0,1]H_[e,f]` and `H_[a,b]H_[e,f]` -/

/-- `(-1)_[a]X_[0,1]`, for `a ∉ {0, 1, e, f}`. -/
theorem push_zxa01 {a : ℕ} (ha : a < 2 ^ n) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hae : a ≠ e)
    (haf : a ≠ f) : D8 n [Zx n a 0 1, Hh n 0 1 e f] [Hh n 0 1 e f, Zx n 1 0 1, Zx n a 0 1] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .zx a 0 1) (u' := .zx a 0 1) (by bd1) (by bd1) (by simp [NL.Pr])
    (by simp [NL.Pr]) (fun v => by simpa [swN, ha0, ha1] using inv_zx a 0 1 v)
    (by omega : 0 < 2 ^ n) (by omega : 1 < 2 ^ n) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, if_pos, if_neg, he0, he1, hf0, hf1, ha0, ha1, hae, haf,
    Ne.symm hae, Ne.symm haf, Ne.symm ha0, Ne.symm ha1, zero_ne_one, one_ne_zero,
    not_false_eq_true, if_true, if_false, ite_true, ite_false, List.nil_append] at k
  have fl := flip1 h8 hE (a := 0) (b := 1) (by omega) (by omega) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  exact k.trans (D8.seg [] [Zx n a 0 1] fl (by simp [NL.toPG]) (by simp))

/-- `(-1)_[1](-1)_[0]`, which commutes with `H_[0,1]H_[e,f]`. -/
theorem push_zz10 : D8 n [Zz n 1 0, Hh n 0 1 e f] [Hh n 0 1 e f, Zz n 1 0] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .zz 1 0) (u' := .zz 1 0) (by bd1) (by bd1) trivial trivial
    (NL.inv_zz 1 0) (by omega : 0 < 2 ^ n) (by omega : 1 < 2 ^ n) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  rw [twL_one, twL_one] at k
  simpa [NL.perm, NL.neg, he0, he1, hf0, hf1, NL.toPG] using k

/-- `(-1)_[1]X_[0,1]`. -/
theorem push_zx101 :
    D8 n [Zx n 1 0 1, Hh n 0 1 e f] [Hh n 0 1 e f, Zx n 1 0 1, Zx n 1 0 1, Zx n 1 0 1] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .zx 1 0 1) (u' := .zx 0 0 1) (by bd1) (by bd1) (by simp [NL.Pr])
    (by simp [NL.Pr]) (fun v => by simpa [swN] using inv_zx 1 0 1 v)
    (by omega : 0 < 2 ^ n) (by omega : 1 < 2 ^ n) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, he0, he1, hf0, hf1, zero_ne_one, one_ne_zero,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append,
    Bool.false_eq_true, Bool.true_eq_false] at k
  have fl := flip1 h8 hE (a := 0) (b := 1) (by omega) (by omega) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  exact k.trans (D8.seg [] [Zx n 1 0 1, Zx n 1 0 1] fl (by simp [NL.toPG]) (by simp))

/-- `(-1)_[0]X_[0,1]`. -/
theorem push_zx001 :
    D8 n [Zx n 0 0 1, Hh n 0 1 e f] [Hh n 0 1 e f, Zx n 1 0 1, Zx n 1 0 1, Zx n 0 0 1] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .zx 0 0 1) (u' := .zx 1 0 1) (by bd1) (by bd1) (by simp [NL.Pr])
    (by simp [NL.Pr]) (fun v => by simpa [swN] using inv_zx 0 0 1 v)
    (by omega : 0 < 2 ^ n) (by omega : 1 < 2 ^ n) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, he0, he1, hf0, hf1, zero_ne_one, one_ne_zero,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append,
    Bool.false_eq_true, Bool.true_eq_false] at k
  have fl := flip1 h8 hE (a := 0) (b := 1) (by omega) (by omega) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  exact k.trans (D8.seg [] [Zx n 1 0 1, Zx n 0 0 1] fl (by simp [NL.toPG]) (by simp))

/-- `X_[0,1]X_[0,b]` moved past `H_[b,1]H_[e,f]`, for `b ∉ {0, 1, e, f}`. -/
theorem push_xx010b {b : ℕ} (hb : b < 2 ^ n) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbe : b ≠ e)
    (hbf : b ≠ f) :
    D8 n [Xx n 0 1 0 b, Hh n b 1 e f] [Hh n 0 1 e f, Zx n 1 0 1, Xx n 0 1 0 b] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .xx 0 1 0 b) (u' := .xx 0 b 0 1) (by bd1) (by bd1)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega) (inv_xx 0 1 0 b) hb (by omega : 1 < 2 ^ n)
    he hf ⟨hb1, hbe, hbf, by omega, by omega, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, he0, he1, hf0, hf1, hb0, hb1, hbe, hbf, Ne.symm hbe,
    Ne.symm hbf, Ne.symm hb0, Ne.symm hb1, zero_ne_one, one_ne_zero,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append] at k
  have fl := flip1 h8 hE (a := 0) (b := 1) (by omega) (by omega) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  exact k.trans (D8.seg [] [Xx n 0 1 0 b] fl (by simp [NL.toPG]) (by simp))

/-- `(-1)_[b]X_[1,b]` moved past `H_[0,b]H_[e,f]`, for `b ∉ {0, 1, e, f}`. -/
theorem push_zxb1b {b : ℕ} (hb : b < 2 ^ n) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbe : b ≠ e)
    (hbf : b ≠ f) : D8 n [Zx n b 1 b, Hh n 0 b e f] [Hh n 0 1 e f, Zx n b 1 b] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .zx b 1 b) (u' := .zx 1 1 b) (by bd1) (by bd1)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega)
    (fun v => by simpa [swN, hb1] using inv_zx b 1 b v) (by omega : 0 < 2 ^ n) hb he hf
    ⟨by omega, by omega, by omega, hbe, hbf, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, he0, he1, hf0, hf1, hb0, hb1, hbe, hbf, Ne.symm hbe,
    Ne.symm hbf, Ne.symm hb0, Ne.symm hb1, zero_ne_one, one_ne_zero,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append] at k
  simpa [NL.toPG] using k

/-- `X_[a,b]X_[0,1]` moved past `H_[0,1]H_[e,f]`, for `a, b ∉ {0, 1, e, f}`. -/
theorem push_xxab01 {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) (hae : a ≠ e) (haf : a ≠ f) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbe : b ≠ e)
    (hbf : b ≠ f) :
    D8 n [Xx n a b 0 1, Hh n 0 1 e f] [Hh n 0 1 e f, Zx n 1 0 1, Xx n a b 0 1] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .xx a b 0 1) (u' := .xx 0 1 a b) (by bd1) (by bd1)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega) (inv_xx a b 0 1)
    (by omega : 0 < 2 ^ n) (by omega : 1 < 2 ^ n) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, he0, he1, hf0, hf1, ha0, ha1, hae, haf, hb0, hb1, hbe, hbf,
    Ne.symm hae, Ne.symm haf, Ne.symm ha0, Ne.symm ha1, Ne.symm hbe, Ne.symm hbf, Ne.symm hb0,
    Ne.symm hb1, zero_ne_one, one_ne_zero,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append] at k
  have fl := flip1 h8 hE (a := 0) (b := 1) (by omega) (by omega) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  exact k.trans (D8.seg [] [Xx n a b 0 1] fl (by simp [NL.toPG]) (by simp))

/-- `X_[0,1]X_[1,b]` moved past `H_[0,b]H_[e,f]`, for `b ∉ {0, 1, e, f}`. -/
theorem push_xx011b {b : ℕ} (hb : b < 2 ^ n) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbe : b ≠ e)
    (hbf : b ≠ f) :
    D8 n [Xx n 0 1 1 b, Hh n 0 b e f] [Hh n 0 1 e f, Zx n 1 0 1, Xx n 0 1 1 b] := by
  obtain ⟨he, hf, -, hef, -, -, he0, he1, hf0, hf1, -⟩ := T
  have k := push1 h8 hE (u := .xx 0 1 1 b) (u' := .xx 1 b 0 1) (by bd1) (by bd1)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega) (inv_xx 0 1 1 b)
    (by omega : 0 < 2 ^ n) hb he hf ⟨by omega, by omega, by omega, hbe, hbf, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, he0, he1, hf0, hf1, hb0, hb1, hbe, hbf, Ne.symm hbe,
    Ne.symm hbf, Ne.symm hb0, Ne.symm hb1, zero_ne_one, one_ne_zero,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append] at k
  have fl := flip1 h8 hE (a := 0) (b := 1) (by omega) (by omega) he hf
    ⟨by omega, by omega, by omega, by omega, by omega, hef⟩
  exact k.trans (D8.seg [] [Xx n 0 1 1 b] fl (by simp [NL.toPG]) (by simp))

/-- `(-1)_[1](-1)_[g]` past `H_[a,b]H_[e,f]` with `1, g ∉ {a, b}`. -/
theorem push_zz1g_out {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hag : a ≠ g) (hbg : b ≠ g) (hae : a ≠ e) (haf : a ≠ f) (hbe : b ≠ e)
    (hbf : b ≠ f) : D8 n [Zz n 1 g, Hh n a b e f] [Hh n a b e f, Zz n 1 g] := by
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T
  have k := push1 h8 hE (u := .zz 1 g) (u' := .zz 1 g) (by bd1) (by bd1) trivial trivial
    (NL.inv_zz 1 g) ha hb he hf ⟨hab, hae, haf, hbe, hbf, hef⟩
  rw [twL_one, twL_one] at k
  simpa [NL.perm, NL.neg, ha1, hb1, hag, hbg, he1, hf1, heg, hfg, NL.toPG] using k

/-- `(-1)_[1](-1)_[g]` past `H_[a,b]H_[e,f]` with `1 ∈ {a, b}`, `g ∉ {a, b}`. -/
theorem push_zz1g_in {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b)
    (h1 : a = 1 ∨ b = 1) (hag : a ≠ g) (hbg : b ≠ g) (hae : a ≠ e) (haf : a ≠ f) (hbe : b ≠ e)
    (hbf : b ≠ f) : D8 n [Zz n 1 g, Hh n a b e f] [Hh n a b e f, Zx n a b a, Zz n 1 g] := by
  obtain ⟨he, hf, hg, hef, heg, hfg, he0, he1, hf0, hf1, hg1⟩ := T
  have k := push1 h8 hE (u := .zz 1 g) (u' := .zz 1 g) (by bd1) (by bd1) trivial trivial
    (NL.inv_zz 1 g) ha hb he hf ⟨hab, hae, haf, hbe, hbf, hef⟩
  rw [twL_one, twL_one] at k
  rcases h1 with rfl | rfl
  · simpa [NL.perm, NL.neg, Ne.symm hab, hab, hag, hbg, he1, hf1, heg, hfg, NL.toPG] using k
  · simpa [NL.perm, NL.neg, Ne.symm hab, hab, hag, hbg, he1, hf1, heg, hfg, NL.toPG] using k

/-- `(-1)_[b]X_[a,b]` past `H_[a,b]H_[e,f]`. -/
theorem push_zxbab {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) (hae : a ≠ e)
    (haf : a ≠ f) (hbe : b ≠ e) (hbf : b ≠ f) :
    D8 n [Zx n b a b, Hh n a b e f] [Hh n a b e f, Zx n b a b, Zx n b a b, Zx n b a b] := by
  obtain ⟨he, hf, -, hef, -, -, -, -, -, -, -⟩ := T
  have k := push1 h8 hE (u := .zx b a b) (u' := .zx a a b) (by bd1) (by bd1)
    (by simp [NL.Pr]; omega) (by simp [NL.Pr]; omega)
    (fun v => by simpa [swN, Ne.symm hab] using inv_zx b a b v) ha hb he hf ⟨hab, hae, haf, hbe, hbf, hef⟩
  rw [twL_one, twL_one] at k
  simp only [NL.perm, NL.neg, swN, hab, Ne.symm hab, hae, haf, hbe, hbf, Ne.symm hae,
    Ne.symm haf, Ne.symm hbe, Ne.symm hbf,
    if_true, if_false, ite_true, ite_false, not_false_eq_true, List.nil_append,
    Bool.false_eq_true, Bool.true_eq_false] at k
  have fl := flip1 h8 hE (a := a) (b := b) ha hb he hf ⟨hab, hae, haf, hbe, hbf, hef⟩
  exact k.trans (D8.seg [] [Zx n b a b, Zx n b a b] fl (by simp [NL.toPG]) (by simp))

end Steps

end QCert.RealCliffordCH.Sec8
