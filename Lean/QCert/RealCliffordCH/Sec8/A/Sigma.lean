/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-free derivations: signs and the letters `σ_j = (-1)_[j] X_[j,j+1]`

Derivations with the Hadamard-free equations of Figure 8 (`DH`):

* the sign letters `(-1)_[a](-1)_[b]` square to `ε` and commute (`zz_sq`,
  `zz_comm`);
* a sign letter passes `σ_j` from right to left, its indices renamed by the
  transposition of `j, j+1` (`sg_zz`), hence passes any word of `σ`s
  (`sgL_zz`);
* runs `σ_a σ_{a+1} ⋯ σ_{a+k-1}` (`run a k`): a `σ_j` far from a run
  commutes with it (`comm_below`, `comm_above`), and one inside it is shifted
  by one (`run_shift`, the braid relation (24) and (32)).
-/
import QCert.RealCliffordCH.Sec8.A.SPSound

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## Sign letters -/

theorem zz_sq {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : DH n [Zz n a b, Zz n a b] [] :=
  (DR.ctx [Zz n a b] [] (e21 n ha hb)).trans ((e22 n ha hb ha).trans (e20 n ha))

/-- `(-1)_[c](-1)_[d] ≈ (-1)_[p](-1)_[c] · (-1)_[p](-1)_[d]`. -/
theorem zz_split {p c d : ℕ} (hp : p < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) :
    DH n [Zz n c d] [Zz n p c, Zz n p d] :=
  (e22 n hc hp hd).symm.trans (DR.ctx [] [Zz n p d] (e21 n hc hp))

theorem g_comm {p x y : ℕ} (hp : p < 2 ^ n) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    DH n [Zz n p x, Zz n p y] [Zz n p y, Zz n p x] :=
  (DR.ctx [] [Zz n p y] (e21 n hp hx)).trans <| (e22 n hx hp hy).trans <|
    (e21 n hx hy).trans (zz_split hp hy hx)

theorem zz_comm {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) : DH n [Zz n a b, Zz n c d] [Zz n c d, Zz n a b] := by
  have h0 : (0 : ℕ) < 2 ^ n := Nat.two_pow_pos n
  exact (DR.append (zz_split h0 ha hb) (zz_split h0 hc hd)).trans <|
    (DR.ctx [Zz n 0 a] [Zz n 0 d] (g_comm h0 hb hc)).trans <|
    (DR.ctx [] [Zz n 0 b, Zz n 0 d] (g_comm h0 ha hc)).trans <|
    (DR.ctx [Zz n 0 c, Zz n 0 a] [] (g_comm h0 hb hd)).trans <|
    (DR.ctx [Zz n 0 c] [Zz n 0 b] (g_comm h0 ha hd)).trans <|
    DR.append (zz_split h0 hc hd).symm (zz_split h0 ha hb).symm

/-! ## Signs past `σ_a` -/

section Pass

variable {a : ℕ} (ha : a + 1 < 2 ^ n)
include ha

/-- Equation (31), from right to left. -/
theorem sg_zz_lo {c : ℕ} (hc : c < 2 ^ n) (h1 : c ≠ a) (h2 : c ≠ a + 1) :
    DH n [sg n a, Zz n a c] [Zz n (a + 1) c, sg n a] := (e31 n ha hc h1 h2).symm

theorem sg_zz_hi {c : ℕ} (hc : c < 2 ^ n) (h1 : c ≠ a) (h2 : c ≠ a + 1) :
    DH n [sg n a, Zz n (a + 1) c] [Zz n a c, sg n a] := by
  have ha' : a < 2 ^ n := by omega
  exact (DR.ctx [sg n a] [] (e22 n ha ha' hc).symm).trans <|
    (DR.ctx [sg n a] [Zz n a c] (e21 n ha ha')).trans <|
    (DR.ctx [sg n a] [Zz n a c] (e23 n ha)).trans <|
    (DR.ctx [sg n a, sg n a] [] (sg_zz_lo ha hc h1 h2)).trans <|
    (DR.ctx [] [Zz n (a + 1) c, sg n a] (e23 n ha).symm).trans <|
    DR.ctx [] [sg n a] (e22 n ha' ha hc)

/-- A sign `(-1)_[p](-1)_[x]` passes `σ_a`, `p ∉ {a, a+1}`. -/
theorem sg_zz_pivot {p x : ℕ} (hp : p < 2 ^ n) (hpa : p ≠ a) (hpa1 : p ≠ a + 1)
    (hx : x < 2 ^ n) :
    DH n [sg n a, Zz n p x] [Zz n p (swN a (a + 1) x), sg n a] := by
  have ha' : a < 2 ^ n := by omega
  by_cases h1 : x = a
  · subst h1
    rw [show swN x (x + 1) x = x + 1 by simp [swN]]
    exact (DR.ctx [sg n x] [] (e21 n hp ha')).trans <|
      (sg_zz_lo ha hp hpa hpa1).trans (DR.ctx [] [sg n x] (e21 n ha hp))
  by_cases h2 : x = a + 1
  · subst h2
    rw [show swN a (a + 1) (a + 1) = a by simp [swN]]
    exact (DR.ctx [sg n a] [] (e21 n hp ha)).trans <|
      (sg_zz_hi ha hp hpa hpa1).trans (DR.ctx [] [sg n a] (e21 n ha' hp))
  rw [show swN a (a + 1) x = x by simp [swN, h1, h2]]
  by_cases h3 : x = p
  · subst h3
    exact (DR.ctx [sg n a] [] (e20 n hp)).trans (DR.ctx [] [sg n a] (e20 n hp).symm)
  exact (DR.ctx [sg n a] [] (e22 n hp ha' hx).symm).trans <|
    (DR.ctx [] [Zz n a x] ((DR.ctx [sg n a] [] (e21 n hp ha')).trans <|
      (sg_zz_lo ha hp hpa hpa1).trans (DR.ctx [] [sg n a] (e21 n ha hp)))).trans <|
    (DR.ctx [Zz n p (a + 1)] [] (sg_zz_lo ha hx h1 h2)).trans <|
    DR.ctx [] [sg n a] (e22 n hp ha hx)

/-- A sign letter passes `σ_a`, its indices renamed by the transposition of
`a, a+1`. -/
theorem sg_zz {p c d : ℕ} (hp : p < 2 ^ n) (hpa : p ≠ a) (hpa1 : p ≠ a + 1) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) :
    DH n [sg n a, Zz n c d] [Zz n (swN a (a + 1) c) (swN a (a + 1) d), sg n a] := by
  have hs : ∀ x, x < 2 ^ n → swN a (a + 1) x < 2 ^ n := fun x hx => by
    unfold swN; split_ifs <;> omega
  exact (DR.ctx [sg n a] [] (zz_split hp hc hd)).trans <|
    (DR.ctx [] [Zz n p d] (sg_zz_pivot ha hp hpa hpa1 hc)).trans <|
    (DR.ctx [Zz n p (swN a (a + 1) c)] [] (sg_zz_pivot ha hp hpa hpa1 hd)).trans <|
    DR.ctx [] [sg n a] (zz_split hp (hs c hc) (hs d hd)).symm

end Pass

end QCert.RealCliffordCH.Sec8
