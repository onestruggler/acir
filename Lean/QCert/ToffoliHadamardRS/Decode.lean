/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the decoding

Translation of `Decode.agda`.  The generators of Li, Ross and Selinger at
`n = 8`, decoded as circuits over `Σ₁`, and the transport of their
relations.

Each generator is a circuit `b` conjugated by a Coxeter word: `(-1)_[a]` is
`m0` (that is `(-1)_[0]`) carried by a frame sending `0` to `a`, `X_[a,b]`
is `T 0` (that is `X_[0,1]`) carried by one sending `0, 1` to `a, b`, and
`K_[a,b,c,d]` is `NK` (`K_[0,1,2,3]`) carried by one sending `0, 1, 2, 3` to
`a, b, c, d`.  By the frame lemma of `Perm` the result depends only on where
the frame sends those states, since the `T i` above them commute with `b`
(Figure 7's (85)–(93), and the Coxeter relations).  So a word whose letters
are all carried by one frame `F` from a word `w₀` decodes to the conjugate
of `w₀`'s decoding by `F` (`Tr`, `tr_sound`), and a relation of Table 1
follows from one standard instance of it (`transport`).

The development is parameterised by the Coxeter relations for the circuits
`T d` (`cox`), which `Toffoli.Coxeter` derives from Figure 4.

States are natural numbers in the Coxeter words (`CoxeterFrames`); a frame
is valid (its letters below `7`) when its states are distinct and below `8`
(`frame_valid`), which every frame here is.
-/
import QCert.ToffoliHadamardRS.Perm
import QCert.ToffoliHadamardRS.Check
import QCert.ToffoliHadamardRS.Encoding
import QCert.LiRossSelinger.Units
import Mathlib.Tactic.IntervalCases

namespace QCert.ToffoliHadamardRS

open CoxeterFrames
open LiRossSelinger (Gen Table1)

/-- Distinctness of a few states, from order and distinctness hypotheses. -/
macro "nodup_tac" : tactic =>
  `(tactic| (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true, Fin.lt_def, ← Fin.val_inj] at *; omega))

/-! ## The decoding -/

/-- The decoding of a generator. -/
def dec : Gen 8 → Word G₁
  | .neg a => Fr m0 (frame [a.val])
  | .x a b _ => Fr (T 0) (frame [a.val, b.val])
  | .k a b c d _ _ _ => Fr NKw (frame [a.val, b.val, c.val, d.val])

/-- The decoding of words. -/
abbrev decW : Word (Gen 8) →* Word G₁ := FreeMonoid.lift dec

/-- Conjugation by a Coxeter word. -/
def Cj (F : CW) (w : Word G₁) : Word G₁ := Pc F * w * Pc (inv F)

/-- A frame of distinct states below `8` is a word of `S₈`. -/
theorem frame_valid8 {ts : List ℕ} (hd : ts.Nodup) (hb : ∀ t ∈ ts, t < 8) : Valid 7 (frame ts) :=
  frame_valid 7 ts hd hb

section

variable (cox : Coxeter R1plus)
include cox

/-! ## What the `T i` above a base circuit commute with -/

omit cox in
/-- (85)–(90): the `T i` with `i ≥ 1` commute with `(-1)_[0]`. -/
theorem comm_m0 : CommGeW R1plus T 1 m0 := by
  intro i h₁ h₂
  interval_cases i
  · exact Derivable.of (R1plus.fig7 Fig7.r85)
  · exact Derivable.of (R1plus.fig7 Fig7.r86)
  · exact Derivable.of (R1plus.fig7 Fig7.r87)
  · exact Derivable.of (R1plus.fig7 Fig7.r88)
  · exact Derivable.of (R1plus.fig7 Fig7.r89)
  · exact Derivable.of (R1plus.fig7 Fig7.r90)

omit cox in
/-- (91)–(93): the `T i` with `i ≥ 4` commute with `K_[0,1,2,3]`. -/
theorem comm_NK : CommGeW R1plus T 4 NKw := by
  intro i h₁ h₂
  interval_cases i
  · exact Derivable.of (R1plus.fig7 Fig7.r91)
  · exact Derivable.of (R1plus.fig7 Fig7.r92)
  · exact Derivable.of (R1plus.fig7 Fig7.r93)

/-- The Coxeter relations: the `T i` with `i ≥ 2` commute with `X_[0,1]`. -/
theorem comm_T0 : CommGeW R1plus T 2 (T 0) := fun i h₁ h₂ => (cox.far 0 i (by omega) h₂).symm

/-! ## Conjugation by a Coxeter word -/

theorem Cj_eps {F : CW} (hF : Valid 7 F) : Derivable R1plus (Cj F 1) 1 := by
  rw [Cj, mul_one]; exact Pc_inv cox hF

theorem Cj_mul {F : CW} (hF : Valid 7 F) (u v : Word G₁) :
    Derivable R1plus (Cj F u * Cj F v) (Cj F (u * v)) := by
  apply cl_eq.1
  have h := cl_eq.2 (Pc_inv' cox hF)
  rw [cl_mul, cl_one] at h
  simp only [Cj, cl_mul]
  calc cl R1plus (Pc F) * cl R1plus u * cl R1plus (Pc (inv F)) *
        (cl R1plus (Pc F) * cl R1plus v * cl R1plus (Pc (inv F)))
      = cl R1plus (Pc F) * cl R1plus u * (cl R1plus (Pc (inv F)) * cl R1plus (Pc F)) *
        cl R1plus v * cl R1plus (Pc (inv F)) := by simp only [mul_assoc]
    _ = _ := by rw [h, mul_one]; simp only [mul_assoc]

omit cox in
theorem Cj_cong (F : CW) {u v : Word G₁} (e : Derivable R1plus u v) :
    Derivable R1plus (Cj F u) (Cj F v) :=
  ((Derivable.refl _).mul e).mul (Derivable.refl _)

/-- A frame conjugating a circuit by itself twice. -/
theorem Fr_sq (b : Word G₁) (bb : Derivable R1plus (b * b) 1) {p : CW} (hp : Valid 7 p) :
    Derivable R1plus (Fr b p * Fr b p) 1 := by
  apply cl_eq.1
  have h := cl_eq.2 (Pc_inv' cox hp)
  have h' := cl_eq.2 (Pc_inv cox hp)
  have hb := cl_eq.2 bb
  rw [cl_mul, cl_one] at h h' hb
  simp only [Fr, CoxeterFrames.Fr, cl_mul, cl_one]
  calc cl R1plus (Pc p) * cl R1plus b * cl R1plus (Pc (inv p)) *
        (cl R1plus (Pc p) * cl R1plus b * cl R1plus (Pc (inv p)))
      = cl R1plus (Pc p) * cl R1plus b * (cl R1plus (Pc (inv p)) * cl R1plus (Pc p)) *
        cl R1plus b * cl R1plus (Pc (inv p)) := by simp only [mul_assoc]
    _ = cl R1plus (Pc p) * (cl R1plus b * cl R1plus b) * cl R1plus (Pc (inv p)) := by
        rw [h, mul_one]; simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, h']

/-- A Coxeter word passing a frame. -/
theorem Pc_Fr (b : Word G₁) {x : CW} (hx : Valid 7 x) (p : CW) :
    Derivable R1plus (Pc x * Fr b p) (Fr b (x ++ p) * Pc x) := by
  apply cl_eq.1
  have h := cl_eq.2 (Pc_inv' cox hx)
  rw [cl_mul, cl_one] at h
  simp only [Fr, CoxeterFrames.Fr, inv, List.reverse_append, CoxeterFrames.Pc_append, cl_mul]
  simp only [inv] at h
  calc cl R1plus (Pc x) * (cl R1plus (Pc p) * cl R1plus b * cl R1plus (Pc p.reverse))
      = cl R1plus (Pc x) * (cl R1plus (Pc p) * cl R1plus b * cl R1plus (Pc p.reverse)) *
        (cl R1plus (Pc x.reverse) * cl R1plus (Pc x)) := by rw [h, mul_one]
    _ = _ := by simp only [mul_assoc]

/-! ## Transport along a frame -/

omit cox in
/-- `u` is `u₀` with every state `x` replaced by `act F x`. -/
inductive Tr (F : CW) : Word (Gen 8) → Word (Gen 8) → Prop
  | trM {a i : Fin 8} : act F i.val = a.val → Tr F (FreeMonoid.of (.neg a)) (FreeMonoid.of (.neg i))
  | trX {a b i j : Fin 8} (p : a < b) (q : i < j) : act F i.val = a.val → act F j.val = b.val →
      Tr F (FreeMonoid.of (.x a b p)) (FreeMonoid.of (.x i j q))
  | trK {a b c d i₀ i₁ i₂ i₃ : Fin 8} (p : a < b) (q : b < c) (r : c < d)
      (p' : i₀ < i₁) (q' : i₁ < i₂) (r' : i₂ < i₃) :
      act F i₀.val = a.val → act F i₁.val = b.val → act F i₂.val = c.val → act F i₃.val = d.val →
      Tr F (FreeMonoid.of (.k a b c d p q r)) (FreeMonoid.of (.k i₀ i₁ i₂ i₃ p' q' r'))
  | trε : Tr F 1 1
  | trmul {u u₀ v v₀ : Word (Gen 8)} : Tr F u u₀ → Tr F v v₀ → Tr F (u * v) (u₀ * v₀)

/-- A frame on the states `as` is a frame on `is` conjugated by `F`, when `F`
sends `is` to `as`. -/
theorem fr_conj {F : CW} (hF : Valid 7 F) {j : ℕ} (hj : j ≤ 8) {b : Word G₁}
    (cb : CommGeW R1plus T j b) (as is : List ℕ) (ha : as.length = j) (hi : is.length = j)
    (hda : as.Nodup) (hdi : is.Nodup) (hba : ∀ t ∈ as, t < 8) (hbi : ∀ t ∈ is, t < 8)
    (e : is.map (act F) = as) :
    Derivable R1plus (Fr b (frame as)) (Cj F (Fr b (frame is))) := by
  have hc : Cj F (Fr b (frame is)) = Fr b (F ++ frame is) := CoxeterFrames.Fr_conj T b F (frame is)
  rw [hc]
  refine frame_eqW cox hj cb (frame_valid8 hda hba) (valid_append hF (frame_valid8 hdi hbi)) ?_
  intro x hx
  rw [act_append, frame_act as hda x (by omega), frame_act is hdi x (by omega)]
  simp only [← e, List.getElem_map]

theorem tr_sound {F : CW} (hF : Valid 7 F) {u u₀ : Word (Gen 8)} (t : Tr F u u₀) :
    Derivable R1plus (decW u) (Cj F (decW u₀)) := by
  induction t with
  | @trM a i e =>
    simp only [FreeMonoid.lift_eval_of, dec]
    exact fr_conj cox hF (by norm_num) comm_m0 [a.val] [i.val] rfl rfl (by simp) (by simp)
      (by simp) (by simp) (by simp [e])
  | @trX a b i j p q e₀ e₁ =>
    simp only [FreeMonoid.lift_eval_of, dec]
    exact fr_conj cox hF (by norm_num) (comm_T0 cox) [a.val, b.val] [i.val, j.val] rfl rfl
      (by nodup_tac) (by nodup_tac) (by simp) (by simp) (by simp [e₀, e₁])
  | @trK a b c d i₀ i₁ i₂ i₃ p q r p' q' r' e₀ e₁ e₂ e₃ =>
    simp only [FreeMonoid.lift_eval_of, dec]
    exact fr_conj cox hF (by norm_num) comm_NK [a.val, b.val, c.val, d.val]
      [i₀.val, i₁.val, i₂.val, i₃.val] rfl rfl (by nodup_tac) (by nodup_tac) (by simp) (by simp)
      (by simp [e₀, e₁, e₂, e₃])
  | trε => rw [map_one]; exact (Cj_eps cox hF).symm
  | trmul _ _ ih₁ ih₂ =>
    rw [map_mul, map_mul]
    exact (ih₁.mul ih₂).trans (Cj_mul cox hF _ _)

/-- A relation between words carried by one frame from a relation between
their standard instances. -/
theorem transport {F : CW} (hF : Valid 7 F) {l r l₀ r₀ : Word (Gen 8)} (tl : Tr F l l₀)
    (tr : Tr F r r₀) (e : Derivable R1plus (decW l₀) (decW r₀)) :
    Derivable R1plus (decW l) (decW r) :=
  (tr_sound cox hF tl).trans ((Cj_cong F e).trans (tr_sound cox hF tr).symm)

end

/-! ## The aliases of Figure 7 as frames -/

/-- `X_[a, a+1+d]` as a Coxeter word. -/
def xr (a : ℕ) : ℕ → CW
  | 0 => [a]
  | d + 1 => [a] ++ xr (a + 1) d ++ [a]

/-- `X_[a,b]` as a Coxeter word. -/
def xw (a b : ℕ) : CW :=
  match b - a with
  | 0 => []
  | d + 1 => xr a d

/-- `K_[a,b,c,d]`'s two Coxeter words. -/
def kq (a b c d : ℕ) : CW := xw 0 a ++ xw 1 b ++ xw 2 c ++ xw 3 d
def kq' (a b c d : ℕ) : CW := xw 3 d ++ xw 2 c ++ xw 1 b ++ xw 0 a

/-- The Coxeter word of a decoded `X_[a,b]`. -/
def xcw (a b : ℕ) : CW := frame [a, b] ++ [0] ++ inv (frame [a, b])

theorem Pc_xr (a d : ℕ) : CoxeterFrames.Pc (T (k := 1)) (xr a d) = TR a d := by
  induction d generalizing a with
  | zero => simp [xr, TR, CoxeterFrames.Pc]
  | succ d ih => simp only [xr, TR, CoxeterFrames.Pc_append, ih]; simp [CoxeterFrames.Pc]

theorem Pc_xw (a b : ℕ) : CoxeterFrames.Pc (T (k := 1)) (xw a b) = Xab a b := by
  unfold xw Xab
  cases b - a with
  | zero => rfl
  | succ d => exact Pc_xr a d

theorem dec_x (a b : Fin 8) (h : a < b) : dec (.x a b h) = Pc (xcw a.val b.val) := by
  simp [dec, xcw, Fr, CoxeterFrames.Fr, Pc, CoxeterFrames.Pc_append, mul_assoc]
  simp [CoxeterFrames.Pc]

section

variable (cox : Coxeter R1plus)
include cox

theorem alias1 (p q : CW) (hp : Valid 7 p) (hq : Valid 7 q) (h₁ : below 1 (act p) (act q) = true)
    (h₂ : below 8 (act (inv q)) (act q) = true) :
    Derivable R1plus (Fr m0 p) (Pc (k := 1) q * m0 * Pc (k := 1) q) :=
  (frame_eqW cox (by norm_num) comm_m0 hp hq (agree 1 _ _ h₁)).trans
    ((Derivable.refl _).mul (Pc_complete cox (valid_inv hq) hq (everywhere _ _ h₂)))

theorem alias4 (p q q' : CW) (hp : Valid 7 p) (hq : Valid 7 q) (hq' : Valid 7 q')
    (h₁ : below 4 (act p) (act q) = true) (h₂ : below 8 (act (inv q)) (act q') = true) :
    Derivable R1plus (Fr NKw p) (Pc (k := 1) q * NKw * Pc (k := 1) q') :=
  (frame_eqW cox (by norm_num) comm_NK hp hq (agree 4 _ _ h₁)).trans
    ((Derivable.refl _).mul (Pc_complete cox (valid_inv hq) hq' (everywhere _ _ h₂)))

theorem aliasX (p q : CW) (hp : Valid 7 p) (hq : Valid 7 q) (h : below 8 (act p) (act q) = true) :
    Derivable R1plus (Pc p) (Pc q) :=
  Pc_complete cox hp hq (everywhere _ _ h)

end

/-- The letters of the standard instances, and Figure 7's names for them. -/
inductive Std
  | m0s | m1s | m3s | m4s | x01 | x12 | x13 | x23 | x34 | x45 | x56 | x67 | x04
  | k0123 | k4567 | k1345 | k2345 | k0124

/-- The standard generators. -/
def std : Std → Gen 8
  | .m0s => mG 0
  | .m1s => mG 1
  | .m3s => mG 3
  | .m4s => mG 4
  | .x01 => xG 0 1
  | .x12 => xG 1 2
  | .x13 => xG 1 3
  | .x23 => xG 2 3
  | .x34 => xG 3 4
  | .x45 => xG 4 5
  | .x56 => xG 5 6
  | .x67 => xG 6 7
  | .x04 => xG 0 4
  | .k0123 => kG 0 1 2 3
  | .k4567 => kG 4 5 6 7
  | .k1345 => kG 1 3 4 5
  | .k2345 => kG 2 3 4 5
  | .k0124 => kG 0 1 2 4

/-- Figure 7's names for them. -/
def al : Std → Word G₁
  | .m0s => m0
  | .m1s => m 1
  | .m3s => m 3
  | .m4s => m 4
  | .x01 => T 0
  | .x12 => T 1
  | .x13 => Xab 1 3
  | .x23 => T 2
  | .x34 => T 3
  | .x45 => T 4
  | .x56 => T 5
  | .x67 => T 6
  | .x04 => Xab 0 4
  | .k0123 => NKw
  | .k4567 => Kq 4 5 6 7
  | .k1345 => Kq 1 3 4 5
  | .k2345 => Kq 2 3 4 5
  | .k0124 => Kq 0 1 2 4

/-- The standard instances as words. -/
abbrev stdW : Word Std →* Word (Gen 8) := FreeMonoid.map std

/-- Their aliases. -/
abbrev alW : Word Std →* Word G₁ := FreeMonoid.lift al

/-- An equation between equal words. -/
theorem deq {w v : Word G₁} (h : w = v) : Derivable R1plus w v := h ▸ Derivable.refl w

/-- The states of a frame, read off. -/
theorem fa (ts : List ℕ) (hd : ts.Nodup) (i : ℕ) {x : ℕ} (h : ts[i]? = some x) :
    act (frame ts) i = x := frame_act' ts hd i x h

section

variable (cox : Coxeter R1plus)
include cox

theorem al_ok : ∀ s : Std, Derivable R1plus (dec (std s)) (al s)
  | .m0s => deq (by simp [dec, std, mG, al, Fr, CoxeterFrames.Fr, show frame [0] = [] from rfl,
      inv, CoxeterFrames.Pc])
  | .m1s => (alias1 cox (frame [1]) (xw 0 1) (by decide) (by decide) (by decide) (by decide)).trans
      (deq (by simp only [Pc_xw]; rfl))
  | .m3s => (alias1 cox (frame [3]) (xw 0 3) (by decide) (by decide) (by decide) (by decide)).trans
      (deq (by simp only [Pc_xw]; rfl))
  | .m4s => (alias1 cox (frame [4]) (xw 0 4) (by decide) (by decide) (by decide) (by decide)).trans
      (deq (by simp only [Pc_xw]; rfl))
  | .x01 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 0 1) (xw 0 1) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 0 1))
  | .x12 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 1 2) (xw 1 2) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 1 2))
  | .x13 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 1 3) (xw 1 3) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 1 3))
  | .x23 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 2 3) (xw 2 3) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 2 3))
  | .x34 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 3 4) (xw 3 4) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 3 4))
  | .x45 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 4 5) (xw 4 5) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 4 5))
  | .x56 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 5 6) (xw 5 6) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 5 6))
  | .x67 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 6 7) (xw 6 7) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 6 7))
  | .x04 => by
    rw [std, xG, dec_x]
    exact (aliasX cox (xcw 0 4) (xw 0 4) (by decide) (by decide) (by decide)).trans (deq (Pc_xw 0 4))
  | .k0123 => deq (by simp [dec, std, kG, al, Fr, CoxeterFrames.Fr,
      show frame [0, 1, 2, 3] = [] from rfl, inv, CoxeterFrames.Pc])
  | .k4567 => (alias4 cox (frame [4, 5, 6, 7]) (kq 4 5 6 7) (kq' 4 5 6 7) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (deq (by simp only [kq, kq', CoxeterFrames.Pc_append, Pc_xw, al, Kq, mul_assoc]))
  | .k1345 => (alias4 cox (frame [1, 3, 4, 5]) (kq 1 3 4 5) (kq' 1 3 4 5) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (deq (by simp only [kq, kq', CoxeterFrames.Pc_append, Pc_xw, al, Kq, mul_assoc]))
  | .k2345 => (alias4 cox (frame [2, 3, 4, 5]) (kq 2 3 4 5) (kq' 2 3 4 5) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (deq (by simp only [kq, kq', CoxeterFrames.Pc_append, Pc_xw, al, Kq, mul_assoc]))
  | .k0124 => (alias4 cox (frame [0, 1, 2, 4]) (kq 0 1 2 4) (kq' 0 1 2 4) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (deq (by simp only [kq, kq', CoxeterFrames.Pc_append, Pc_xw, al, Kq, mul_assoc]))

theorem alW_ok (w : Word Std) : Derivable R1plus (decW (stdW w)) (alW w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of s w ih =>
    rw [map_mul, map_mul, map_mul, FreeMonoid.map_of, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]
    exact (al_ok cox s).mul ih

/-- A relation between standard instances, from one between their aliases
(the aliases computed by `simp`: their unfolding by `isDefEq` is slow). -/
theorem by_al (l r : Word Std) {wl wr : Word G₁} (e : Derivable R1plus wl wr)
    (hl : alW l = wl := by simp only [map_mul, FreeMonoid.lift_eval_of, al])
    (hr : alW r = wr := by simp only [map_mul, FreeMonoid.lift_eval_of, al]) :
    Derivable R1plus (decW (stdW l)) (decW (stdW r)) :=
  (alW_ok cox l).trans ((hl ▸ hr ▸ e).trans (alW_ok cox r).symm)

end

section

variable (cox : Coxeter R1plus)
include cox

/-! ## The relations of Table 1 -/

/-- An `X_[i,j]` conjugating a `K` frame. -/
theorem xk_base (x F₁ F₂ : CW) (hx : Valid 7 x) (h₁ : Valid 7 F₁) (h₂ : Valid 7 F₂)
    (h : below 4 (act (x ++ F₁)) (act F₂) = true) :
    Derivable R1plus (Pc x * Fr NKw F₁) (Fr NKw F₂ * Pc x) :=
  (Pc_Fr cox NKw hx F₁).trans
    ((frame_eqW cox (by norm_num) comm_NK (valid_append hx h₁) h₂ (agree 4 _ _ h)).mul
      (Derivable.refl _))

/-- The standard instance of (2d), from (95). -/
theorem base2d : Derivable R1plus (decW (Mw 0 * Mw 1)) (decW (Mw 1 * Mw 0)) :=
  transport cox (F := frame [0, 2, 3, 5, 1]) (by decide)
    (.trmul (.trM (i := ⟨0, by decide⟩) (by decide)) (.trM (i := ⟨4, by decide⟩) (by decide)))
    (.trmul (.trM (i := ⟨4, by decide⟩) (by decide)) (.trM (i := ⟨0, by decide⟩) (by decide)))
    (by_al cox (FreeMonoid.of .m0s * FreeMonoid.of .m4s) (FreeMonoid.of .m4s * FreeMonoid.of .m0s)
      (Derivable.of (R1plus.fig7 Fig7.r95)))

/-- The standard instances of (3a), (3b): permutations only. -/
theorem base3a : Derivable R1plus (decW (Xw 0 1 * Xw 0 2)) (decW (Xw 1 2 * Xw 0 1)) := by
  simp only [map_mul, FreeMonoid.lift_eval_of, xG, dec_x, ← CoxeterFrames.Pc_append]
  exact aliasX cox _ _ (by decide) (by decide) (by decide)

theorem base3b : Derivable R1plus (decW (Xw 1 2 * Xw 0 1)) (decW (Xw 0 2 * Xw 1 2)) := by
  simp only [map_mul, FreeMonoid.lift_eval_of, xG, dec_x, ← CoxeterFrames.Pc_append]
  exact aliasX cox _ _ (by decide) (by decide) (by decide)

/-- The standard instance of (3c), by (83)'s `T 0` squared. -/
theorem base3c : Derivable R1plus (decW (Xw 0 1 * Mw 1)) (decW (Mw 0 * Xw 0 1)) := by
  refine by_al cox (FreeMonoid.of .x01 * FreeMonoid.of .m1s) (FreeMonoid.of .m0s * FreeMonoid.of .x01)
    (wl := T 0 * m 1) (wr := m0 * T 0) ?_
  apply cl_eq.1
  have h := cl_eq.2 (cox.order 0 (by norm_num))
  rw [cl_mul, cl_one] at h
  have hm : m (k := 0) 1 = T 0 * m0 * T 0 := rfl
  rw [hm]
  simp only [cl_mul]
  rw [← mul_assoc, ← mul_assoc, h, one_mul]

/-- The standard instances of (3d)–(3g): an `X` renaming one index of a `K`. -/
theorem base3d : Derivable R1plus (decW (Xw 0 1 * Kw 0 2 3 4)) (decW (Kw 1 2 3 4 * Xw 0 1)) := by
  simp only [map_mul, FreeMonoid.lift_eval_of, xG, dec_x]
  exact xk_base cox (xcw 0 1) (frame [0, 2, 3, 4]) (frame [1, 2, 3, 4]) (by decide) (by decide) (by decide)
    (by decide)

theorem base3e : Derivable R1plus (decW (Xw 1 2 * Kw 0 1 3 4)) (decW (Kw 0 2 3 4 * Xw 1 2)) := by
  simp only [map_mul, FreeMonoid.lift_eval_of, xG, dec_x]
  exact xk_base cox (xcw 1 2) (frame [0, 1, 3, 4]) (frame [0, 2, 3, 4]) (by decide) (by decide) (by decide)
    (by decide)

theorem base3f : Derivable R1plus (decW (Xw 2 3 * Kw 0 1 2 4)) (decW (Kw 0 1 3 4 * Xw 2 3)) := by
  simp only [map_mul, FreeMonoid.lift_eval_of, xG, dec_x]
  exact xk_base cox (xcw 2 3) (frame [0, 1, 2, 4]) (frame [0, 1, 3, 4]) (by decide) (by decide) (by decide)
    (by decide)

theorem base3g : Derivable R1plus (decW (Xw 3 4 * Kw 0 1 2 3)) (decW (Kw 0 1 2 4 * Xw 3 4)) := by
  simp only [map_mul, FreeMonoid.lift_eval_of, xG, dec_x]
  exact xk_base cox (xcw 3 4) (frame [0, 1, 2, 3]) (frame [0, 1, 2, 4]) (by decide) (by decide) (by decide)
    (by decide)

/-- The standard instance of (6a): (101) of Figure 7, with (95) to put its
last two letters in order. -/
theorem base6a : Derivable R1plus
    (decW (Mw 0 * Mw 4 * Xw 0 4 * Kw 4 5 6 7 * Kw 0 1 2 3 * Xw 3 4 * Kw 0 1 2 3 * Kw 4 5 6 7 *
      Xw 0 4 * Mw 0 * Mw 4))
    (decW (Kw 4 5 6 7 * Kw 0 1 2 3 * Xw 3 4 * Kw 0 1 2 3 * Kw 4 5 6 7)) := by
  refine by_al cox (FreeMonoid.of .m0s * FreeMonoid.of .m4s * FreeMonoid.of .x04 * FreeMonoid.of .k4567 *
    FreeMonoid.of .k0123 * FreeMonoid.of .x34 * FreeMonoid.of .k0123 * FreeMonoid.of .k4567 *
    FreeMonoid.of .x04 * FreeMonoid.of .m0s * FreeMonoid.of .m4s)
    (FreeMonoid.of .k4567 * FreeMonoid.of .k0123 * FreeMonoid.of .x34 * FreeMonoid.of .k0123 *
    FreeMonoid.of .k4567)
    (wl := m0 * m 4 * Xab 0 4 * Kq 4 5 6 7 * NKw * T 3 * NKw * Kq 4 5 6 7 * Xab 0 4 * m0 * m 4)
    (wr := Ω) ?_ (by simp only [map_mul, FreeMonoid.lift_eval_of, al]) (by
      simp only [map_mul, FreeMonoid.lift_eval_of, al, Ω])
  set P := m0 * m 4 * Xab 0 4 * Kq 4 5 6 7 * NKw * T 3 * NKw * Kq 4 5 6 7 * Xab 0 4 with hP
  have e₁ : Derivable R1plus (P * m0 * m 4) (P * m 4 * m0) := by
    rw [mul_assoc P, mul_assoc P]; exact (Derivable.refl P).mul (Derivable.of (R1plus.fig7 Fig7.r95))
  have e₂ : P * m 4 * m0 = m0 * m 4 * Xab 0 4 * Ω * Xab 0 4 * m 4 * m0 := by
    rw [hP]; simp only [Ω, mul_assoc]
  exact e₁.trans (by rw [e₂]; exact Derivable.of (R1plus.fig7 Fig7.r101))

set_option maxHeartbeats 1000000 in
/-- The decoding respects the relations of Table 1.  Each letter of the
transport is given its standard states (`i := ⟨0, _⟩`, …), as in the Agda,
where left to unification they made Agda reduce the frame of symbolic
states. -/
theorem dec_ax {u v : Word (Gen 8)} (h : Table1 8 u v) : Derivable R1plus (decW u) (decW v) := by
  cases h with
  | r1a a b hab =>
    have hd : [a.val, b.val].Nodup := by nodup_tac
    simpa using Fr_sq cox (T 0) (cox.order 0 (by norm_num)) (frame_valid8 hd (by simp))
  | r1b a =>
    simpa using Fr_sq cox m0 (Derivable.of (R1plus.fig7 Fig7.r83)) (p := frame [a.val])
      (frame_valid8 (by simp) (by simp))
  | r1c a b c d hab hbc hcd =>
    have hd : [a.val, b.val, c.val, d.val].Nodup := by nodup_tac
    simpa using Fr_sq cox NKw (Derivable.of (R1plus.fig7 Fig7.r84)) (frame_valid8 hd (by simp))
  | r2a a b c d hab hcd h =>
    have hd : [a.val, b.val, c.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 0 1 * Xw 2 3)) (decW (Xw 2 3 * Xw 0 1)) := by_al cox (FreeMonoid.of .x01 * FreeMonoid.of .x23) (FreeMonoid.of .x23 * FreeMonoid.of .x01) (cox.far 0 2 (by norm_num) (by norm_num))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 0 1 * Xw 2 3) (r₀ := Xw 2 3 * Xw 0 1)
      (.trmul (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl))
        (.trX (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trX (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl)))
      e
  | r2b a b c hab h =>
    have hd : [c.val, a.val, b.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 1 2 * Mw 0)) (decW (Mw 0 * Xw 1 2)) := by_al cox (FreeMonoid.of .x12 * FreeMonoid.of .m0s) (FreeMonoid.of .m0s * FreeMonoid.of .x12) (Derivable.of (R1plus.fig7 Fig7.r85))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 1 2 * Mw 0) (r₀ := Mw 0 * Xw 1 2)
      (.trmul (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl))
        (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl)))
      (.trmul (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl))
        (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl)))
      e
  | r2c a b c d e f hab hcd hde hef h =>
    have hd : [c.val, d.val, e.val, f.val, a.val, b.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 4 5 * Kw 0 1 2 3)) (decW (Kw 0 1 2 3 * Xw 4 5)) := by_al cox (FreeMonoid.of .x45 * FreeMonoid.of .k0123) (FreeMonoid.of .k0123 * FreeMonoid.of .x45) (Derivable.of (R1plus.fig7 Fig7.r91))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 4 5 * Kw 0 1 2 3) (r₀ := Kw 0 1 2 3 * Xw 4 5)
      (.trmul (.trX (i := ⟨4, by decide⟩) (j := ⟨5, by decide⟩) _ (by decide) (fa _ hd 4 rfl) (fa _ hd 5 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trX (i := ⟨4, by decide⟩) (j := ⟨5, by decide⟩) _ (by decide) (fa _ hd 4 rfl) (fa _ hd 5 rfl)))
      e
  | r2d a b h =>
    have hd : [a.val, b.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Mw 0 * Mw 1)) (decW (Mw 1 * Mw 0)) := base2d cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Mw 0 * Mw 1) (r₀ := Mw 1 * Mw 0)
      (.trmul (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl))
        (.trM (i := ⟨1, by decide⟩) (fa _ hd 1 rfl)))
      (.trmul (.trM (i := ⟨1, by decide⟩) (fa _ hd 1 rfl))
        (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl)))
      e
  | r2e a b c d e hbc hcd hde h =>
    have hd : [b.val, c.val, d.val, e.val, a.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Mw 4 * Kw 0 1 2 3)) (decW (Kw 0 1 2 3 * Mw 4)) := by_al cox (FreeMonoid.of .m4s * FreeMonoid.of .k0123) (FreeMonoid.of .k0123 * FreeMonoid.of .m4s) (Derivable.of (R1plus.fig7 Fig7.r94))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Mw 4 * Kw 0 1 2 3) (r₀ := Kw 0 1 2 3 * Mw 4)
      (.trmul (.trM (i := ⟨4, by decide⟩) (fa _ hd 4 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trM (i := ⟨4, by decide⟩) (fa _ hd 4 rfl)))
      e
  | r2f a b c d e f g h hab hbc hcd hef hfg hgh hd =>
    have hd : [a.val, b.val, c.val, d.val, e.val, f.val, g.val, h.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Kw 0 1 2 3 * Kw 4 5 6 7)) (decW (Kw 4 5 6 7 * Kw 0 1 2 3)) := by_al cox (FreeMonoid.of .k0123 * FreeMonoid.of .k4567) (FreeMonoid.of .k4567 * FreeMonoid.of .k0123) (Derivable.of (R1plus.fig7 Fig7.r96))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Kw 0 1 2 3 * Kw 4 5 6 7) (r₀ := Kw 4 5 6 7 * Kw 0 1 2 3)
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trK (i₀ := ⟨4, by decide⟩) (i₁ := ⟨5, by decide⟩) (i₂ := ⟨6, by decide⟩) (i₃ := ⟨7, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 4 rfl) (fa _ hd 5 rfl) (fa _ hd 6 rfl) (fa _ hd 7 rfl)))
      (.trmul (.trK (i₀ := ⟨4, by decide⟩) (i₁ := ⟨5, by decide⟩) (i₂ := ⟨6, by decide⟩) (i₃ := ⟨7, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 4 rfl) (fa _ hd 5 rfl) (fa _ hd 6 rfl) (fa _ hd 7 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      e
  | r3a a a' b h₁ h₂ =>
    have hd : [a.val, a'.val, b.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 0 1 * Xw 0 2)) (decW (Xw 1 2 * Xw 0 1)) := base3a cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 0 1 * Xw 0 2) (r₀ := Xw 1 2 * Xw 0 1)
      (.trmul (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl))
        (.trX (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 2 rfl)))
      (.trmul (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl))
        (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl)))
      e
  | r3b a b b' h₁ h₂ =>
    have hd : [a.val, b.val, b'.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 1 2 * Xw 0 1)) (decW (Xw 0 2 * Xw 1 2)) := base3b cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 1 2 * Xw 0 1) (r₀ := Xw 0 2 * Xw 1 2)
      (.trmul (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl))
        (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl)))
      (.trmul (.trX (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 2 rfl))
        (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl)))
      e
  | r3c a b hab =>
    have hd : [a.val, b.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 0 1 * Mw 1)) (decW (Mw 0 * Xw 0 1)) := base3c cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 0 1 * Mw 1) (r₀ := Mw 0 * Xw 0 1)
      (.trmul (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl))
        (.trM (i := ⟨1, by decide⟩) (fa _ hd 1 rfl)))
      (.trmul (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl))
        (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl)))
      e
  | r3d a a' b c d h₁ h₂ hbc hcd =>
    have hd : [a.val, a'.val, b.val, c.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 0 1 * Kw 0 2 3 4)) (decW (Kw 1 2 3 4 * Xw 0 1)) := base3d cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 0 1 * Kw 0 2 3 4) (r₀ := Kw 1 2 3 4 * Xw 0 1)
      (.trmul (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨2, by decide⟩) (i₂ := ⟨3, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl)))
      (.trmul (.trK (i₀ := ⟨1, by decide⟩) (i₁ := ⟨2, by decide⟩) (i₂ := ⟨3, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl))
        (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl)))
      e
  | r3e a b b' c d hab h₁ h₂ hcd =>
    have hd : [a.val, b.val, b'.val, c.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 1 2 * Kw 0 1 3 4)) (decW (Kw 0 2 3 4 * Xw 1 2)) := base3e cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 1 2 * Kw 0 1 3 4) (r₀ := Kw 0 2 3 4 * Xw 1 2)
      (.trmul (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨3, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl)))
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨2, by decide⟩) (i₂ := ⟨3, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl))
        (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl)))
      e
  | r3f a b c c' d hab hbc h₁ h₂ =>
    have hd : [a.val, b.val, c.val, c'.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 2 3 * Kw 0 1 2 4)) (decW (Kw 0 1 3 4 * Xw 2 3)) := base3f cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 2 3 * Kw 0 1 2 4) (r₀ := Kw 0 1 3 4 * Xw 2 3)
      (.trmul (.trX (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 4 rfl)))
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨3, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl))
        (.trX (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      e
  | r3g a b c d d' hab hbc hcd h₁ =>
    have hd : [a.val, b.val, c.val, d.val, d'.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 3 4 * Kw 0 1 2 3)) (decW (Kw 0 1 2 4 * Xw 3 4)) := base3g cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 3 4 * Kw 0 1 2 3) (r₀ := Kw 0 1 2 4 * Xw 3 4)
      (.trmul (.trX (i := ⟨3, by decide⟩) (j := ⟨4, by decide⟩) _ (by decide) (fa _ hd 3 rfl) (fa _ hd 4 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 4 rfl))
        (.trX (i := ⟨3, by decide⟩) (j := ⟨4, by decide⟩) _ (by decide) (fa _ hd 3 rfl) (fa _ hd 4 rfl)))
      e
  | r4a a b c d hab hbc hcd =>
    have hd : [a.val, b.val, c.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 0 1 * Kw 0 1 2 3)) (decW (Kw 0 1 2 3 * Xw 1 3 * Mw 1 * Mw 3)) := by_al cox (FreeMonoid.of .x01 * FreeMonoid.of .k0123) (FreeMonoid.of .k0123 * FreeMonoid.of .x13 * FreeMonoid.of .m1s * FreeMonoid.of .m3s) (Derivable.of (R1plus.fig7 Fig7.r97))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 0 1 * Kw 0 1 2 3) (r₀ := Kw 0 1 2 3 * Xw 1 3 * Mw 1 * Mw 3)
      (.trmul (.trX (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 1 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trmul (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
              (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
            (.trX (i := ⟨1, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 3 rfl)))
          (.trM (i := ⟨1, by decide⟩) (fa _ hd 1 rfl)))
        (.trM (i := ⟨3, by decide⟩) (fa _ hd 3 rfl)))
      e
  | r4b a b c d hab hbc hcd =>
    have hd : [a.val, b.val, c.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 1 2 * Kw 0 1 2 3)) (decW (Mw 0 * Kw 0 1 2 3 * Mw 0 * Kw 0 1 2 3 * Mw 0)) := by_al cox (FreeMonoid.of .x12 * FreeMonoid.of .k0123) (FreeMonoid.of .m0s * FreeMonoid.of .k0123 * FreeMonoid.of .m0s * FreeMonoid.of .k0123 * FreeMonoid.of .m0s) (Derivable.of (R1plus.fig7 Fig7.r98))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 1 2 * Kw 0 1 2 3) (r₀ := Mw 0 * Kw 0 1 2 3 * Mw 0 * Kw 0 1 2 3 * Mw 0)
      (.trmul (.trX (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 2 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trmul (.trmul (.trmul (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl))
              (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
            (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl)))
          (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
            (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
        (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl)))
      e
  | r4c a b c d hab hbc hcd =>
    have hd : [a.val, b.val, c.val, d.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Xw 2 3 * Kw 0 1 2 3)) (decW (Kw 0 1 2 3 * Xw 1 3)) := by_al cox (FreeMonoid.of .x23 * FreeMonoid.of .k0123) (FreeMonoid.of .k0123 * FreeMonoid.of .x13) (Derivable.of (R1plus.fig7 Fig7.r99))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Xw 2 3 * Kw 0 1 2 3) (r₀ := Kw 0 1 2 3 * Xw 1 3)
      (.trmul (.trX (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trX (i := ⟨1, by decide⟩) (j := ⟨3, by decide⟩) _ (by decide) (fa _ hd 1 rfl) (fa _ hd 3 rfl)))
      e
  | r5a a b c d e f hab hbc hcd hde hef =>
    have hd : [a.val, b.val, c.val, d.val, e.val, f.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Kw 0 1 2 3 * Kw 1 3 4 5)) (decW (Kw 2 3 4 5 * Kw 0 1 2 4)) := by_al cox (FreeMonoid.of .k0123 * FreeMonoid.of .k1345) (FreeMonoid.of .k2345 * FreeMonoid.of .k0124) (Derivable.of (R1plus.fig7 Fig7.r100))
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Kw 0 1 2 3 * Kw 1 3 4 5) (r₀ := Kw 2 3 4 5 * Kw 0 1 2 4)
      (.trmul (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl))
        (.trK (i₀ := ⟨1, by decide⟩) (i₁ := ⟨3, by decide⟩) (i₂ := ⟨4, by decide⟩) (i₃ := ⟨5, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 1 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl) (fa _ hd 5 rfl)))
      (.trmul (.trK (i₀ := ⟨2, by decide⟩) (i₁ := ⟨3, by decide⟩) (i₂ := ⟨4, by decide⟩) (i₃ := ⟨5, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 2 rfl) (fa _ hd 3 rfl) (fa _ hd 4 rfl) (fa _ hd 5 rfl))
        (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨4, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 4 rfl)))
      e
  | r6a a b c d e f g h hab hbc hcd hde hef hfg hgh =>
    have hd : [a.val, b.val, c.val, d.val, e.val, f.val, g.val, h.val].Nodup := by nodup_tac
    have e : Derivable R1plus (decW (Mw 0 * Mw 4 * Xw 0 4 * Kw 4 5 6 7 * Kw 0 1 2 3 * Xw 3 4 * Kw 0 1 2 3 * Kw 4 5 6 7 * Xw 0 4 * Mw 0 * Mw 4)) (decW (Kw 4 5 6 7 * Kw 0 1 2 3 * Xw 3 4 * Kw 0 1 2 3 * Kw 4 5 6 7)) := base6a cox
    exact transport cox (frame_valid8 hd (by simp)) (l₀ := Mw 0 * Mw 4 * Xw 0 4 * Kw 4 5 6 7 * Kw 0 1 2 3 * Xw 3 4 * Kw 0 1 2 3 * Kw 4 5 6 7 * Xw 0 4 * Mw 0 * Mw 4) (r₀ := Kw 4 5 6 7 * Kw 0 1 2 3 * Xw 3 4 * Kw 0 1 2 3 * Kw 4 5 6 7)
      (.trmul (.trmul (.trmul (.trmul (.trmul (.trmul (.trmul (.trmul (.trmul (.trmul (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl))
                          (.trM (i := ⟨4, by decide⟩) (fa _ hd 4 rfl)))
                        (.trX (i := ⟨0, by decide⟩) (j := ⟨4, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 4 rfl)))
                      (.trK (i₀ := ⟨4, by decide⟩) (i₁ := ⟨5, by decide⟩) (i₂ := ⟨6, by decide⟩) (i₃ := ⟨7, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                        (fa _ hd 4 rfl) (fa _ hd 5 rfl) (fa _ hd 6 rfl) (fa _ hd 7 rfl)))
                    (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                      (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
                  (.trX (i := ⟨3, by decide⟩) (j := ⟨4, by decide⟩) _ (by decide) (fa _ hd 3 rfl) (fa _ hd 4 rfl)))
                (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                  (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
              (.trK (i₀ := ⟨4, by decide⟩) (i₁ := ⟨5, by decide⟩) (i₂ := ⟨6, by decide⟩) (i₃ := ⟨7, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                (fa _ hd 4 rfl) (fa _ hd 5 rfl) (fa _ hd 6 rfl) (fa _ hd 7 rfl)))
            (.trX (i := ⟨0, by decide⟩) (j := ⟨4, by decide⟩) _ (by decide) (fa _ hd 0 rfl) (fa _ hd 4 rfl)))
          (.trM (i := ⟨0, by decide⟩) (fa _ hd 0 rfl)))
        (.trM (i := ⟨4, by decide⟩) (fa _ hd 4 rfl)))
      (.trmul (.trmul (.trmul (.trmul (.trK (i₀ := ⟨4, by decide⟩) (i₁ := ⟨5, by decide⟩) (i₂ := ⟨6, by decide⟩) (i₃ := ⟨7, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                (fa _ hd 4 rfl) (fa _ hd 5 rfl) (fa _ hd 6 rfl) (fa _ hd 7 rfl))
              (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
                (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
            (.trX (i := ⟨3, by decide⟩) (j := ⟨4, by decide⟩) _ (by decide) (fa _ hd 3 rfl) (fa _ hd 4 rfl)))
          (.trK (i₀ := ⟨0, by decide⟩) (i₁ := ⟨1, by decide⟩) (i₂ := ⟨2, by decide⟩) (i₃ := ⟨3, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
            (fa _ hd 0 rfl) (fa _ hd 1 rfl) (fa _ hd 2 rfl) (fa _ hd 3 rfl)))
        (.trK (i₀ := ⟨4, by decide⟩) (i₁ := ⟨5, by decide⟩) (i₂ := ⟨6, by decide⟩) (i₃ := ⟨7, by decide⟩) _ _ _ (by decide) (by decide) (by decide)
          (fa _ hd 4 rfl) (fa _ hd 5 rfl) (fa _ hd 6 rfl) (fa _ hd 7 rfl)))
      e

/-- The decoding respects the congruence of Table 1. -/
theorem dec_cong {u v : Word (Gen 8)} (h : Derivable (Table1 8) u v) :
    Derivable R1plus (decW u) (decW v) :=
  derivable_map decW (fun _ _ r => dec_ax cox r) h

end

end QCert.ToffoliHadamardRS
