/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): the congruence, and the relations (a1)–(d2)

`GB n` is the congruence of Claim B of the Reidemeister–Schreier theorem
(`rsCon`): `w ∼ w'` when from every coset `τ**` reaches the same coset along
both words, with words equal by Figure 8.  Hypothesis (b) says that it
contains every relation of Figure 6.

Here: the parities of a word (`parL`), which decide the coset reached;
the existence of tags for a frame away from any four indices
(`exists_tags`); and, through `good_frame` and the images `img_*` of
`ItemBPhi.lean`, every relation (a1)–(d2) of Figure 6 in `GB n`
(`gb_a1`, …, `gb_d2`).
-/
import QCert.RealCliffordCH.Sec8.A.FrameRun
import QCert.RealCliffordCH.Sec8.A.ItemBPhi
import QCert.RealCliffordCH.Sec8.A.E65

namespace QCert.RealCliffordCH.Sec8

open QCert.HadamardPi (Fig6)

variable {n : ℕ}

variable (n) in
/-- The congruence of Claim B. -/
abbrev GB : Con (Word (HG (2 ^ n))) := rsCon (tauA n) (Fig8 n)

/-! ## Parities -/

/-- The sum of two parities. -/
def pxor (p q : Bool × Bool) : Bool × Bool := (xor p.1 q.1, xor p.2 q.2)

/-- The parities of a list of generators. -/
def parL {N : ℕ} (l : List (HG N)) : Bool × Bool :=
  l.foldl (fun p y => pxor p (gbits y)) (false, false)

theorem Cos.act_act (c : Cos) (p q : Bool × Bool) : (c.act p).act q = c.act (pxor p q) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  cases c <;> cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> rfl

theorem Cos.act_zero (c : Cos) : c.act (false, false) = c := by cases c <;> rfl

theorem foldl_act_gen {N : ℕ} (l : List (HG N)) (c : Cos) (p : Bool × Bool) :
    l.foldl (fun c y => c.act (gbits y)) (c.act p) =
      c.act (l.foldl (fun p y => pxor p (gbits y)) p) := by
  induction l generalizing p with
  | nil => rfl
  | cons y l ih => simp only [List.foldl_cons, Cos.act_act, ih]

theorem foldl_act {N : ℕ} (l : List (HG N)) (c : Cos) :
    l.foldl (fun c y => c.act (gbits y)) c = c.act (parL l) := by
  have := foldl_act_gen l c (false, false)
  rwa [Cos.act_zero] at this

/-- Same parities give the same coset from every coset. -/
theorem hpar_of {N : ℕ} {l l' : List (HG N)} (h : parL l = parL l') (c : Cos) :
    l.foldl (fun c y => c.act (gbits y)) c = l'.foldl (fun c y => c.act (gbits y)) c := by
  rw [foldl_act, foldl_act, h]

/-! ## Tags -/

theorem FT.tags {e f g : ℕ} (T : FT n e f g) : Tags n e f g :=
  ⟨T.he, T.hf, T.hg, T.hef, T.heg, T.hfg⟩

/-- Tags away from at most four indices. -/
theorem exists_tags (h8 : 8 ≤ 2 ^ n) (S : Finset ℕ) (hS : S.card ≤ 4) :
    ∃ e f g, FT n e f g ∧ e ∉ S ∧ f ∉ S ∧ g ∉ S := by
  obtain ⟨e, f, he, hf, hef, he', hf'⟩ := exists_fresh_pair (S ∪ {0, 1})
    ((Finset.card_union_le _ _).trans (by
      have : ({0, 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      omega))
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at he' hf'
  obtain ⟨g, hg, hg'⟩ : ∃ g, g < 8 ∧ g ∉ S ∪ {1, e, f} := by
    have h := Finset.card_le_card_sdiff_add_card (s := Finset.range 8) (t := S ∪ {1, e, f})
    have h2 : (S ∪ {1, e, f}).card ≤ 7 := (Finset.card_union_le _ _).trans (by
      have : ({1, e, f} : Finset ℕ).card ≤ 3 := Finset.card_le_three
      omega)
    rw [Finset.card_range] at h
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (show 0 < (Finset.range 8 \ (S ∪ {1, e, f})).card by omega)
    rw [Finset.mem_sdiff, Finset.mem_range] at hx
    exact ⟨x, hx.1, hx.2⟩
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hg'
  exact ⟨e, f, g, ⟨by omega, by omega, by omega, hef, Ne.symm hg'.2.2.1, Ne.symm hg'.2.2.2,
    he'.2.1, he'.2.2, hf'.2.1, hf'.2.2, hg'.2.1⟩, he'.1, hf'.1, hg'.1⟩

/-- Indices of a word inside `S`. -/
def InS {N : ℕ} (S : Finset ℕ) (w : Word (HG N)) : Prop := ∀ y ∈ w.toList, ∀ i ∈ gix y, i ∈ S

theorem InS.away {N : ℕ} {S : Finset ℕ} {w : Word (HG N)} (h : InS S w) {e f g : ℕ}
    (he : e ∉ S) (hf : f ∉ S) (hg : g ∉ S) : Away e f g w := fun y hy i hi =>
  ⟨fun h' => he (h' ▸ h y hy i hi), fun h' => hf (h' ▸ h y hy i hi),
    fun h' => hg (h' ▸ h y hy i hi)⟩

/-- A pair of words on at most four indices, with the same parities, whose frame images
are equal by Figure 8 for every choice of tags away from them, is in `GB`. -/
theorem gb_of (hn : 3 ≤ n) {w w' : Word (HG (2 ^ n))} (S : Finset ℕ) (hS : S.card ≤ 4)
    (hw : InS S w) (hw' : InS S w') (hpar : parL w.toList = parL w'.toList)
    (himg : ∀ e f g, FT n e f g → e ∉ S → f ∉ S → g ∉ S →
      D8 n (phiW n e f g w) (phiW n e f g w')) : GB n w w' := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨e, f, g, T, he, hf, hg⟩ := exists_tags h8 S hS
  exact good_frame h8 (e65 n hn) T (hw.away he hf hg) (hw'.away he hf hg) (hpar_of hpar)
    (himg e f g T he hf hg)

/-! ## The relations (a1)–(d2) -/

open QCert.HadamardPi

theorem h8_of (hn : 3 ≤ n) : 8 ≤ 2 ^ n :=
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem avS {S : Finset ℕ} {e f g : ℕ} {a : Fin (2 ^ n)} (haS : (a : ℕ) ∈ S) (he : e ∉ S)
    (hf : f ∉ S) (hg : g ∉ S) : Av n e f g a :=
  ⟨a.2, fun h => he (h ▸ haS), fun h => hf (h ▸ haS), fun h => hg (h ▸ haS)⟩

theorem fne {a b : Fin (2 ^ n)} (h : a ≠ b) : (a : ℕ) ≠ b := fun e => h (Fin.ext e)

theorem flt {a b : Fin (2 ^ n)} (h : a < b) : (a : ℕ) ≠ b := Nat.ne_of_lt h

/-- Simplification of the frame images. -/
macro "gb_simp" : tactic => `(tactic| simp only [phiW_mul, phiW_of, phiW_one, phiG,
  List.singleton_append, List.cons_append, List.nil_append, List.append_nil])

theorem InS.mul {N : ℕ} {S : Finset ℕ} {w v : Word (HG N)} (hw : InS S w) (hv : InS S v) :
    InS S (w * v) := by
  intro y hy i hi
  rw [FreeMonoid.toList_mul, List.mem_append] at hy
  rcases hy with hy | hy
  exacts [hw y hy i hi, hv y hy i hi]

theorem InS.one {N : ℕ} {S : Finset ℕ} : InS S (1 : Word (HG N)) := by
  intro y hy; simp at hy

theorem InS.ofZ {N : ℕ} {S : Finset ℕ} {a : Fin N} (ha : (a : ℕ) ∈ S) :
    InS S (FreeMonoid.of (Gen.Z a)) := by
  intro y hy i hi
  rw [FreeMonoid.toList_of, List.mem_singleton] at hy
  subst hy
  simp only [gix, List.mem_singleton] at hi
  subst hi; exact ha

theorem InS.ofX {N : ℕ} {S : Finset ℕ} {a b : Fin N} {h : a < b} (ha : (a : ℕ) ∈ S)
    (hb : (b : ℕ) ∈ S) : InS S (FreeMonoid.of (Gen.X a b h)) := by
  intro y hy i hi
  rw [FreeMonoid.toList_of, List.mem_singleton] at hy
  subst hy
  simp only [gix, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> assumption

theorem InS.ofH {N : ℕ} {S : Finset ℕ} {a b : Fin N} {h : a < b} (ha : (a : ℕ) ∈ S)
    (hb : (b : ℕ) ∈ S) : InS S (FreeMonoid.of (Gen.H a b h)) := by
  intro y hy i hi
  rw [FreeMonoid.toList_of, List.mem_singleton] at hy
  subst hy
  simp only [gix, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> assumption

theorem InS.ofList {N : ℕ} {S : Finset ℕ} {l : List (HG N)}
    (h : ∀ y ∈ l, InS S (FreeMonoid.of y)) : InS S (FreeMonoid.ofList l) := by
  intro y hy i hi
  rw [FreeMonoid.toList_ofList] at hy
  exact h y hy y (by simp) i hi

/-- The indices of a relation's words. -/
macro "gb_ins" : tactic => `(tactic|
  ((repeat'
      (first
        | refine InS.mul ?_ ?_
        | exact InS.one
        | refine InS.ofZ ?_
        | refine InS.ofX ?_ ?_
        | refine InS.ofH ?_ ?_)) <;> simp))

/-- The parities of a relation's words. -/
macro "gb_par" : tactic => `(tactic| simp [parL, gbits, pxor, FreeMonoid.toList_mul,
  FreeMonoid.toList_of])

section Small

variable (hn : 3 ≤ n)
include hn

theorem gb_a1 (a : Fin (2 ^ n)) : GB n (Z_[a] * Z_[a]) 1 := by
  refine gb_of hn {(a : ℕ)} (by simp) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_a1 (h8_of hn) T.tags (avS (by simp) he hf hg)

theorem gb_a2 {a b : Fin (2 ^ n)} (hab : a < b) : GB n (X_[a,b] * X_[a,b]) 1 := by
  refine gb_of hn {(a : ℕ), (b : ℕ)} (Finset.card_le_two.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_a2 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg) (flt hab)

theorem gb_a3 {a b : Fin (2 ^ n)} (hab : a < b) :
    GB n (H_[a,b] * H_[a,b]) (1) := by
  refine gb_of hn {(a : ℕ), (b : ℕ)} (Finset.card_le_two.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_a3 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab)

theorem gb_b1 {a b : Fin (2 ^ n)} (hab : a ≠ b) :
    GB n (Z_[a] * Z_[b]) (Z_[b] * Z_[a]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ)} (Finset.card_le_two.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_b1 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (fne hab)

theorem gb_b2 {a b c : Fin (2 ^ n)} (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
    GB n (Z_[a] * X_[b,c]) (X_[b,c] * Z_[a]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ)} (Finset.card_le_three.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_b2 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hbc) (fne hab) (fne hac)

theorem gb_b3 {a b c d : Fin (2 ^ n)} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    GB n (X_[a,b] * X_[c,d]) (X_[c,d] * X_[a,b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ)} (Finset.card_le_four) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_b3 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hcd) (fne hac) (fne had) (fne hbc) (fne hbd)

theorem gb_b4 {a b c : Fin (2 ^ n)} (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
    GB n (Z_[a] * H_[b,c]) (H_[b,c] * Z_[a]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ)} (Finset.card_le_three.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_b4 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hbc) (fne hab) (fne hac)

theorem gb_b5 {a b c d : Fin (2 ^ n)} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    GB n (X_[a,b] * H_[c,d]) (H_[c,d] * X_[a,b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ)} (Finset.card_le_four) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_b5 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hcd) (fne hac) (fne had) (fne hbc) (fne hbd)

theorem gb_b6 {a b c d : Fin (2 ^ n)} (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    GB n (H_[a,b] * H_[c,d]) (H_[c,d] * H_[a,b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ), (d : ℕ)} (Finset.card_le_four) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_b6 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hcd) (fne hac) (fne had) (fne hbc) (fne hbd)

theorem gb_c1 {a b : Fin (2 ^ n)} (hab : a < b) :
    GB n (Z_[a] * X_[a,b]) (X_[a,b] * Z_[b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ)} (Finset.card_le_two.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_c1 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab)

theorem gb_c2 {a b c : Fin (2 ^ n)} (hab : a < b) (hbc : b < c) :
    GB n (X_[b,c] * X_[a,b]) (X_[a,b] * FreeMonoid.of (Gen.X a c (hab.trans hbc))) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ)} (Finset.card_le_three.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_c2 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hbc) (flt (hab.trans hbc))

theorem gb_c3 {a b c : Fin (2 ^ n)} (hab : a < b) (hbc : b < c) :
    GB n (FreeMonoid.of (Gen.X a c (hab.trans hbc)) * X_[b,c]) (X_[b,c] * X_[a,b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ)} (Finset.card_le_three.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_c3 (h8_of hn) T.tags (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hbc) (flt (hab.trans hbc))

theorem gb_c4 {a b c : Fin (2 ^ n)} (hab : a < b) (hbc : b < c) :
    GB n (H_[b,c] * X_[a,b]) (X_[a,b] * FreeMonoid.of (Gen.H a c (hab.trans hbc))) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ)} (Finset.card_le_three.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_c4 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hbc) (flt (hab.trans hbc))

theorem gb_c5 {a b c : Fin (2 ^ n)} (hab : a < b) (hbc : b < c) :
    GB n (FreeMonoid.of (Gen.H a c (hab.trans hbc)) * X_[b,c]) (X_[b,c] * H_[a,b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ), (c : ℕ)} (Finset.card_le_three.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_c5 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab) (flt hbc) (flt (hab.trans hbc))

theorem gb_d1 {a b : Fin (2 ^ n)} (hab : a < b) :
    GB n (Z_[a] * Z_[b] * H_[a,b]) (H_[a,b] * Z_[a] * Z_[b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ)} (Finset.card_le_two.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_d1 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab)

theorem gb_d2 {a b : Fin (2 ^ n)} (hab : a < b) :
    GB n (Z_[b] * H_[a,b]) (H_[a,b] * X_[a,b]) := by
  refine gb_of hn {(a : ℕ), (b : ℕ)} (Finset.card_le_two.trans (by norm_num)) ?_ ?_ ?_ ?_
  · gb_ins
  · gb_ins
  · gb_par
  · intro e f g T he hf hg; gb_simp
    exact img_d2 (h8_of hn) T.tags (e65 n hn) (avS (by simp) he hf hg) (avS (by simp) he hf hg)
      (flt hab)

end Small

end QCert.RealCliffordCH.Sec8
