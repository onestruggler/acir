/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Toward hypothesis (b): the frame `Φ` and the images of Figure 6's relations

For three fresh indices `e, f, g` (`Tags`), `Φ` (`phiG`, `phiW`) writes a
generator of `𝒢_N` as a word over `𝒫_N` with the same action on the other
indices: `(-1)_[a] ↦ (-1)_[a](-1)_[g]`, `X_[a,b] ↦ (-1)_[g]X_[a,b]`,
`H_[a,b] ↦ H_[a,b]H_[e,f]` (the tags make the parities even).  Each relation
(a1)–(d2) of Hadamard-Π's Figure 6 whose indices avoid the tags has its two
images equal by Figure 8 (`img_a1`, …, `img_d2`), by Corollary A.5 for the
Hadamard-free ones, conjugation (`conj_hh`) for the mixed ones and
Equations (66), (71) for (b6).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBRen
import QCert.RealCliffordCH.Sec8.A.RS

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- The generators of Hadamard-Π. -/
abbrev HG (N : ℕ) := HadamardPi.Gen N

/-- The image of a generator. -/
def phiG (n e f g : ℕ) : HG (2 ^ n) → List (PG (2 ^ n))
  | .Z a => [Zz n a g]
  | .X a b _ => [Zx n g a b]
  | .H a b _ => [Hh n a b e f]

/-- The image of a word. -/
def phiW (n e f g : ℕ) (w : Word (HG (2 ^ n))) : List (PG (2 ^ n)) :=
  w.toList.flatMap (phiG n e f g)

theorem phiW_mul (e f g : ℕ) (w v : Word (HG (2 ^ n))) :
    phiW n e f g (w * v) = phiW n e f g w ++ phiW n e f g v := by
  simp [phiW, FreeMonoid.toList_mul]

theorem phiW_of (e f g : ℕ) (y : HG (2 ^ n)) :
    phiW n e f g (FreeMonoid.of y) = phiG n e f g y := by
  simp [phiW, FreeMonoid.toList_of]

theorem phiW_one (e f g : ℕ) : phiW n e f g 1 = [] := rfl

/-- The tags: three distinct indices. -/
structure Tags (n e f g : ℕ) : Prop where
  he : e < 2 ^ n
  hf : f < 2 ^ n
  hg : g < 2 ^ n
  hef : e ≠ f
  heg : e ≠ g
  hfg : f ≠ g

/-- An index below `2ⁿ` away from the tags. -/
def Av (n e f g x : ℕ) : Prop := x < 2 ^ n ∧ x ≠ e ∧ x ≠ f ∧ x ≠ g

/-! ## Helpers -/

/-- `H_[x,y]H_[e,f] · H_[z,w]H_[e,f] ≈ H_[x,y]H_[z,w]`. -/
theorem contract (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {x y z w e f : ℕ} (hx : x < 2 ^ n)
    (hy : y < 2 ^ n) (hz : z < 2 ^ n) (hw : w < 2 ^ n) (he : e < 2 ^ n) (hf : f < 2 ^ n)
    (hxy : x ≠ y) (hd : Distinct4 z w e f) :
    D8 n [Hh n x y e f, Hh n z w e f] [Hh n x y z w] :=
  (DR.left [Hh n x y e f] (e66 h8 hE hz hw he hf hd)).trans
    (e71 h8 hE hx hy he hf hz hw hxy hd.2.2.2.2.2 hd.1)

/-- From a conjugation to a commutation. -/
theorem push_of_conj {Pm P'm R : List (PG (2 ^ n))} {x : PG (2 ^ n)}
    (hc : D8 n (Pm ++ x :: P'm) R) (hcan : D8 n (P'm ++ Pm) []) :
    D8 n (Pm ++ [x]) (R ++ Pm) := by
  have k := DR.ctx (Pm ++ [x]) [] hcan
  exact (DR.rfl' (by simp)).trans (k.symm.trans ((DR.rfl' (by simp)).trans (DR.right Pm hc)))

/-! ## The images of (a1)–(d2) -/

section Img

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : Tags n e f g)
include h8 T

theorem img_a1 {a : ℕ} (ha : Av n e f g a) : D8 n [Zz n a g, Zz n a g] [] :=
  (zz_sq ha.1 T.hg).toD8

theorem img_a2 {a b : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hab : a ≠ b) :
    D8 n [Zx n g a b, Zx n g a b] [] := by
  have := A5v (n := n) (m := 3) (by omega) [a, b, g] rfl (by simp [hab, ha.2.2.2, hb.2.2.2])
    (by simp [ha.1, hb.1, T.hg]) [NL.zx 2 0 1, NL.zx 2 0 1] [] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_b1 {a b : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hab : a ≠ b) :
    D8 n [Zz n a g, Zz n b g] [Zz n b g, Zz n a g] := by
  have := A5v (n := n) (m := 3) (by omega) [a, b, g] rfl (by simp [hab, ha.2.2.2, hb.2.2.2])
    (by simp [ha.1, hb.1, T.hg]) [NL.zz 0 2, NL.zz 1 2] [NL.zz 1 2, NL.zz 0 2] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_b2 {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hc : Av n e f g c)
    (hbc : b ≠ c) (hab : a ≠ b) (hac : a ≠ c) :
    D8 n [Zz n a g, Zx n g b c] [Zx n g b c, Zz n a g] := by
  have := A5v (n := n) (m := 4) (by omega) [a, b, c, g] rfl
    (by simp [hab, hac, hbc, ha.2.2.2, hb.2.2.2, hc.2.2.2]) (by simp [ha.1, hb.1, hc.1, T.hg])
    [NL.zz 0 3, NL.zx 3 1 2] [NL.zx 3 1 2, NL.zz 0 3] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_b3 {a b c d : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hc : Av n e f g c)
    (hd : Av n e f g d) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    D8 n [Zx n g a b, Zx n g c d] [Zx n g c d, Zx n g a b] := by
  have := A5v (n := n) (m := 5) (by omega) [a, b, c, d, g] rfl
    (by simp [hab, hac, had, hbc, hbd, hcd, ha.2.2.2, hb.2.2.2, hc.2.2.2, hd.2.2.2])
    (by simp [ha.1, hb.1, hc.1, hd.1, T.hg])
    [NL.zx 4 0 1, NL.zx 4 2 3] [NL.zx 4 2 3, NL.zx 4 0 1] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_c1 {a b : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hab : a ≠ b) :
    D8 n [Zz n a g, Zx n g a b] [Zx n g a b, Zz n b g] := by
  have := A5v (n := n) (m := 3) (by omega) [a, b, g] rfl (by simp [hab, ha.2.2.2, hb.2.2.2])
    (by simp [ha.1, hb.1, T.hg]) [NL.zz 0 2, NL.zx 2 0 1] [NL.zx 2 0 1, NL.zz 1 2] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_c2 {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hc : Av n e f g c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    D8 n [Zx n g b c, Zx n g a b] [Zx n g a b, Zx n g a c] := by
  have := A5v (n := n) (m := 4) (by omega) [a, b, c, g] rfl
    (by simp [hab, hac, hbc, ha.2.2.2, hb.2.2.2, hc.2.2.2]) (by simp [ha.1, hb.1, hc.1, T.hg])
    [NL.zx 3 1 2, NL.zx 3 0 1] [NL.zx 3 0 1, NL.zx 3 0 2] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_c3 {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hc : Av n e f g c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    D8 n [Zx n g a c, Zx n g b c] [Zx n g b c, Zx n g a b] := by
  have := A5v (n := n) (m := 4) (by omega) [a, b, c, g] rfl
    (by simp [hab, hac, hbc, ha.2.2.2, hb.2.2.2, hc.2.2.2]) (by simp [ha.1, hb.1, hc.1, T.hg])
    [NL.zx 3 0 2, NL.zx 3 1 2] [NL.zx 3 1 2, NL.zx 3 0 1] (by decide)
  simpa [rv, NL.ren, NL.toPG] using this

theorem img_a3 (hE : E65 n) {a b : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hab : a ≠ b) :
    D8 n [Hh n a b e f, Hh n a b e f] [] :=
  hh_sq h8 hE ha.1 hb.1 T.he T.hf ⟨hab, ha.2.1, ha.2.2.1, hb.2.1, hb.2.2.1, T.hef⟩

theorem img_b6 (hE : E65 n) {a b c d : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hd : Av n e f g d) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    D8 n [Hh n a b e f, Hh n c d e f] [Hh n c d e f, Hh n a b e f] :=
  (contract h8 hE ha.1 hb.1 hc.1 hd.1 T.he T.hf hab
    ⟨hcd, hc.2.1, hc.2.2.1, hd.2.1, hd.2.2.1, T.hef⟩).trans <|
  (e66 h8 hE ha.1 hb.1 hc.1 hd.1 ⟨hab, hac, had, hbc, hbd, hcd⟩).trans
    (contract h8 hE hc.1 hd.1 ha.1 hb.1 T.he T.hf hcd
      ⟨hab, ha.2.1, ha.2.2.1, hb.2.1, hb.2.2.1, T.hef⟩).symm

/-- Conjugation by one sign pair `(-1)_[a](-1)_[g]`. -/
theorem conj_zzg (hE : E65 n) {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hbc : b ≠ c) :
    D8 n (Zz n a g :: Hh n b c e f :: [Zz n a g])
      (Hh n b c e f :: (twL n [NL.zz a g] e f ++ twL n [NL.zz a g] b c)) := by
  have k := conj_hh h8 hE (P := [NL.zz a g]) (P' := [NL.zz a g]) (by simp [NL.Bd, ha.1, T.hg])
    (by simp [NL.Bd, ha.1, T.hg]) (by simp [NL.Pr]) (by simp [NL.Pr])
    (fun v _ => NL.inv_zz a g v) hb.1 hc.1 T.he T.hf
    ⟨hbc, hb.2.1, hb.2.2.1, hc.2.1, hc.2.2.1, T.hef⟩
  simpa [permL, NL.perm, NL.toPG] using k

theorem img_b4 (hE : E65 n) {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hbc : b ≠ c) (hab : a ≠ b) (hac : a ≠ c) :
    D8 n [Zz n a g, Hh n b c e f] [Hh n b c e f, Zz n a g] := by
  have k := conj_zzg h8 T hE ha hb hc hbc
  have t1 : twL n [NL.zz a g] e f = [] := twL_agree (by
    simp [negL, permL, NL.neg, Ne.symm ha.2.1, Ne.symm ha.2.2.1, T.heg, T.hfg])
  have t2 : twL n [NL.zz a g] b c = [] := twL_agree (by
    simp [negL, permL, NL.neg, Ne.symm hab, Ne.symm hac, hb.2.2.2, hc.2.2.2])
  rw [t1, t2] at k
  exact push_of_conj (Pm := [Zz n a g]) (P'm := [Zz n a g]) k (zz_sq ha.1 T.hg).toD8

theorem img_d2 (hE : E65 n) {a b : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hab : a ≠ b) :
    D8 n [Zz n b g, Hh n a b e f] [Hh n a b e f, Zx n g a b] := by
  have k := conj_zzg h8 T hE hb ha hb hab
  have t1 : twL n [NL.zz b g] e f = [] := twL_agree (by
    simp [negL, permL, NL.neg, Ne.symm hb.2.1, Ne.symm hb.2.2.1, T.heg, T.hfg])
  have t2 : twL n [NL.zz b g] a b = [Zx n a b a] := by
    rw [twL_disagree (by simp [negL, permL, NL.neg, hab, ha.2.2.2, hb.2.2.2])]; rfl
  rw [t1, t2] at k
  have k2 := push_of_conj (Pm := [Zz n b g]) (P'm := [Zz n b g]) k (zz_sq hb.1 T.hg).toD8
  refine k2.trans ?_
  have := A5v (n := n) (m := 3) (by omega) [a, b, g] rfl (by simp [hab, ha.2.2.2, hb.2.2.2])
    (by simp [ha.1, hb.1, T.hg]) [NL.zx 0 1 0, NL.zz 1 2] [NL.zx 2 0 1] (by decide)
  exact DR.left [Hh n a b e f] (by simpa [rv, NL.ren, NL.toPG] using this)

/-- Conjugation by `(-1)_[g]X_[a,b]`, which renames `a` and `b` and signs only `g`. -/
theorem conj_zxg (hE : E65 n) {a b c d : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hd : Av n e f g d) (hab : a ≠ b) (hcd : c ≠ d) :
    D8 n (Zx n g a b :: Hh n c d e f :: [Zx n g a b])
      [Hh n (swN a b c) (swN a b d) e f] := by
  obtain ⟨ha, hae, haf, hag⟩ := ha; obtain ⟨hb, hbe, hbf, hbg⟩ := hb
  obtain ⟨hc, hce, hcf, hcg⟩ := hc; obtain ⟨hd, hde, hdf, hdg⟩ := hd
  have hg := T.hg; have he := T.he; have hf := T.hf
  have hinv : ∀ v < 2 ^ n, permL ([NL.zx g a b] ++ [NL.zx g a b]) v = v ∧
      negL ([NL.zx g a b] ++ [NL.zx g a b]) v = false := fun v _ => by
    have := inv_v (m := 3) [a, b, g] rfl (by simp [hab, hag, hbg]) [NL.zx 2 0 1, NL.zx 2 0 1] (by decide) v
    simpa [rv, NL.ren] using this
  have k := conj_hh h8 hE (P := [NL.zx g a b]) (P' := [NL.zx g a b])
    (by simp [NL.Bd, ha, hb, hg]) (by simp [NL.Bd, ha, hb, hg]) (by simp [NL.Pr, hab])
    (by simp [NL.Pr, hab]) hinv hc hd he hf ⟨hcd, hce, hcf, hde, hdf, T.hef⟩
  have pe : permL [NL.zx g a b] e = e := by simp [permL, NL.perm, swN, Ne.symm hae, Ne.symm hbe]
  have pf : permL [NL.zx g a b] f = f := by simp [permL, NL.perm, swN, Ne.symm haf, Ne.symm hbf]
  have sg : ∀ x, x ≠ g → swN a b x ≠ g := fun x hx => by
    unfold swN; split_ifs <;> first | exact hbg | exact hag | exact hx
  have ng : ∀ x, x ≠ g → negL [NL.zx g a b] x = false := fun x hx => by
    simp [negL, permL, NL.neg, sg x hx]
  rw [twL_agree (by rw [ng e T.heg, ng f T.hfg]), twL_agree (by rw [ng c hcg, ng d hdg]),
    pe, pf] at k
  simpa [permL, NL.perm, NL.toPG] using k

theorem img_b5 (hE : E65 n) {a b c d : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hd : Av n e f g d) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    D8 n [Zx n g a b, Hh n c d e f] [Hh n c d e f, Zx n g a b] := by
  have k := conj_zxg h8 T hE ha hb hc hd hab hcd
  rw [show swN a b c = c by simp [swN, Ne.symm hac, Ne.symm hbc],
    show swN a b d = d by simp [swN, Ne.symm had, Ne.symm hbd]] at k
  exact push_of_conj (Pm := [Zx n g a b]) (P'm := [Zx n g a b]) k (img_a2 h8 T ha hb hab)

theorem img_c4 (hE : E65 n) {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    D8 n [Hh n b c e f, Zx n g a b] [Zx n g a b, Hh n a c e f] := by
  have k := conj_zxg h8 T hE ha hb ha hc hab hac
  rw [show swN a b a = b by simp [swN],
    show swN a b c = c by simp [swN, Ne.symm hac, Ne.symm hbc]] at k
  exact (push_of_conj (Pm := [Zx n g a b]) (P'm := [Zx n g a b]) k (img_a2 h8 T ha hb hab)).symm

theorem img_c5 (hE : E65 n) {a b c : ℕ} (ha : Av n e f g a) (hb : Av n e f g b)
    (hc : Av n e f g c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    D8 n [Hh n a c e f, Zx n g b c] [Zx n g b c, Hh n a b e f] := by
  have k := conj_zxg h8 T hE hb hc ha hb hbc hab
  rw [show swN b c a = a by simp [swN, hab, hac],
    show swN b c b = c by simp [swN]] at k
  exact (push_of_conj (Pm := [Zx n g b c]) (P'm := [Zx n g b c]) k (img_a2 h8 T hb hc hbc)).symm

theorem img_d1 (hE : E65 n) {a b : ℕ} (ha : Av n e f g a) (hb : Av n e f g b) (hab : a ≠ b) :
    D8 n [Zz n a g, Zz n b g, Hh n a b e f] [Hh n a b e f, Zz n a g, Zz n b g] := by
  obtain ⟨ha, hae, haf, hag⟩ := ha; obtain ⟨hb, hbe, hbf, hbg⟩ := hb
  have hg := T.hg; have he := T.he; have hf := T.hf
  have hinv : ∀ v < 2 ^ n, permL ([NL.zz a g, NL.zz b g] ++ [NL.zz b g, NL.zz a g]) v = v ∧
      negL ([NL.zz a g, NL.zz b g] ++ [NL.zz b g, NL.zz a g]) v = false := fun v _ => by
    have := inv_v (m := 3) [a, b, g] rfl (by simp [hab, hag, hbg])
      [NL.zz 0 2, NL.zz 1 2, NL.zz 1 2, NL.zz 0 2] (by decide) v
    simpa [rv, NL.ren] using this
  have k := conj_hh h8 hE (P := [NL.zz a g, NL.zz b g]) (P' := [NL.zz b g, NL.zz a g])
    (by simp [NL.Bd, ha, hb, hg]) (by simp [NL.Bd, ha, hb, hg]) (by simp [NL.Pr])
    (by simp [NL.Pr]) hinv ha hb he hf ⟨hab, hae, haf, hbe, hbf, T.hef⟩
  rw [twL_agree (by simp [negL, permL, NL.neg, NL.perm, Ne.symm hae, Ne.symm hbe, Ne.symm haf,
      Ne.symm hbf, T.heg, T.hfg]),
    twL_agree (by simp [negL, permL, NL.neg, NL.perm, hab, Ne.symm hab, hag, hbg])] at k
  have hc : D8 n ([Zz n b g, Zz n a g] ++ [Zz n a g, Zz n b g]) [] := by
    have := A5v (n := n) (m := 3) (by omega) [a, b, g] rfl (by simp [hab, hag, hbg]) (by simp [ha, hb, hg])
      [NL.zz 1 2, NL.zz 0 2, NL.zz 0 2, NL.zz 1 2] [] (by decide)
    simpa [rv, NL.ren, NL.toPG] using this
  have := push_of_conj (Pm := [Zz n a g, Zz n b g]) (P'm := [Zz n b g, Zz n a g])
    (by simpa [permL, NL.perm, NL.toPG] using k) hc
  simpa using this

end Img

end QCert.RealCliffordCH.Sec8
