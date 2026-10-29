/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Rotations as boxes and multi-controlled `H` gates, at any wires

The paper's remark under (346)–(352) (page 234): by (333), (334) "together –
if there are white controls – with Equation (81) and maybe with Equation
(315) and/or (316)", every multi-controlled `(-1)ᵃ ZX` with any colours is a
product of boxes and multi-controlled `H` gates with a hole.  Here, for a
rotation with target `t` and a control of any colour on every other wire,
any box wire `b` and any hole `h` (`dec_at`): the rotation is
`HG · B · HG · B` (`ZX`) or `B · HG · B · HG` (`XZ`), `HG` the
multi-controlled `H` with its `H` on `t`, its box on `h`, `B` the box on
`b`, black on `t`, both with the rotation's colours elsewhere.

* `dec_canon`: at the canonical wires (`t, b, h = 0, 1, 2`), every colouring,
  from the black one ((333), (334)) by (81) on one wire at a time; the box
  wire `1` and the hole `2` by (315) and (316) (`x1_box`, `x2_hg`).
* `dec_at`: by the frame of the wires `t, b, h` (`E.frame`), which needs the
  naturality of rotations under swaps, (353) (`R347.mcSwapAll`).
* `comm_frame`, `frm_ctl`, `diff_frm`: an equation between two gates, moved
  by a frame, with the colours read through the frame.
-/
import QCert.RealCliffordCH.Sec8.D.N13.S353
import QCert.RealCliffordCH.Sec8.D.N13.E336

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-- (334) at one width, as `N13.eq334` states it. -/
abbrev H334 (n : ℕ) : Prop :=
  Derivable (theory n) (mc n .xz [0] (blackOn 1 n))
    (drawn [mc n .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 n)),
      mc n .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 n)),
      mc n .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 n)),
      mc n .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 n))])

/-- The four factors of a rotation: `ZX` for `a = false`, `XZ` for `a = true`. -/
def dw {N : ℕ} (a : Bool) (g b : Circ N) : List (Circ N) := if a then [b, g, b, g] else [g, b, g, b]

theorem dw_forall2 {N : ℕ} {R : Circ N → Circ N → Prop} (a : Bool) {g g' b b' : Circ N}
    (hg : R g g') (hb : R b b') : List.Forall₂ R (dw a g b) (dw a g' b') := by
  cases a <;> simp only [dw, Bool.false_eq_true, if_false, if_true] <;>
    exact List.Forall₂.cons (by assumption) (List.Forall₂.cons (by assumption)
      (List.Forall₂.cons (by assumption) (List.Forall₂.cons (by assumption) List.Forall₂.nil)))

theorem kindSp_sgn (a : Bool) : kindSp (Kind.sgnZX a) = 1 := by cases a <;> rfl

/-! ## Conjugation helpers -/

section Helpers

variable {N : ℕ}

/-- Conjugating the three factors of `a b c` by an involution. -/
theorem uconj3 {u : Circ N} (hu : Derivable (theory N) (u * u) 1) (a b c : Circ N) :
    Derivable (theory N) ((u * a * u) * (u * b * u) * (u * c * u)) (u * (a * b * c) * u) := by
  have e : (u * a * u) * (u * b * u) * (u * c * u) =
      u * a * (u * u) * b * (u * u) * c * u := by simp only [mul_assoc]
  rw [e]
  have k1 := dright u (dright c (dleft (u * a * (u * u) * b) hu))
  rw [mul_one] at k1
  refine k1.trans ?_
  have k2 := dright u (dright c (dright b (dleft (u * a) hu)))
  rw [mul_one] at k2
  refine k2.trans (der_of_eq ?_)
  simp only [mul_assoc]

/-- `a` fixed by `x`-conjugation, carried by an involution `u`. -/
theorem fix_conj {u x x' a a' : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (hx : Derivable (theory N) (u * x * u) x') (ha : Derivable (theory N) (u * a * u) a')
    (h : Derivable (theory N) (x * a * x) a) : Derivable (theory N) (x' * a' * x') a' :=
  (dmul (dmul hx.symm ha.symm) hx.symm).trans ((uconj3 hu x a x).trans ((dctx u u h).trans ha))

end Helpers

/-! ## `X` on the box wire and on the hole -/

/-- (316) for the multi-controlled `H` on the wires `0, 1` with coloured
controls: `X` on its hole passes it. -/
theorem x0_hole_hg (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (z : ℕ → Bool) :
    Derivable (theory N) (xAt N 0 * mc N .hg [0, 1] (colOn 2 N z) * xAt N 0)
      (mc N .hg [0, 1] (colOn 2 N z)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  have hc : ∀ i, (colOn 2 (k + 2) z i).isSome = true ↔ kindSp .hg ≤ i ∧ i < k + kindSp .hg := by
    intro i; simp only [colOn, kindSp]; split_ifs <;> simp <;> omega
  have hf := mc_full .hg k _ hc
  simp only [kindSp, canonC] at hf
  have e0 : ([0, 1] : List ℕ) = List.range 2 := rfl
  rw [e0, hf, colourW_eq]
  obtain ⟨hnd, hlt⟩ := whiteWires_ok (k + 2) (List.range 2) (colOn 2 (k + 2) z)
  set Wd := drawn ((whiteWires (k + 2) (List.range 2) (colOn 2 (k + 2) z)).map (xAt (k + 2)))
  have hD : HighW 2 Wd := N13.highW_drawn _ (fun a ha => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    rw [MS.mem_whiteWires] at hw
    have h2 := hw.2.2; simp [List.mem_range] at h2
    intro y hy; have := (xAt_wires _ w).2 y hy; omega)
  have hX : LowW 2 (xAt (k + 2) 0) :=
    N13.lowW_mono (xAt_wires (k + 2) 0).1 (by omega)
  have c1 : Derivable (theory (k + 2)) (Wd * xAt (k + 2) 0) (xAt (k + 2) 0 * Wd) :=
    comm_low_high _ _ hX hD
  have h316 := D.eq314 (k + 2) hN ih 1 le_rfl (by omega) x
  have e1 : atBot (k + 2) (x : Circ 1) = xAt (k + 2) 0 := (Net.pad_atBot1 (k + 1) x).symm
  have hb := mc_canon .hg k
  simp only [kindSp, canonC] at hb
  rw [e1, show (1 - 1 : ℕ) = 0 from rfl, show (1 + 1 : ℕ) = 2 from rfl, e0, hb] at h316
  rw [N13.drawn_two, N13.drawn_two] at h316
  have e : xAt (k + 2) 0 * (Wd * mch k * Wd) * xAt (k + 2) 0 =
      (xAt (k + 2) 0 * Wd) * mch k * (Wd * xAt (k + 2) 0) := by simp only [mul_assoc]
  rw [e]
  refine (dmul (dmul c1.symm (Derivable.refl _)) c1).trans ?_
  have e2 : Wd * xAt (k + 2) 0 * mch k * (xAt (k + 2) 0 * Wd) =
      Wd * (xAt (k + 2) 0 * mch k) * xAt (k + 2) 0 * Wd := by simp only [mul_assoc]
  rw [e2]
  refine (dright Wd (dright _ (dleft Wd h316.symm))).trans ?_
  have e3 : Wd * (mch k * xAt (k + 2) 0) * xAt (k + 2) 0 * Wd =
      Wd * mch k * (xAt (k + 2) 0 * xAt (k + 2) 0) * Wd := by simp only [mul_assoc]
  rw [e3]
  exact cancel_mid (D.xAt_inv (k + 2) 0 (by omega)) _ _

/-- (315) for the box of (333): `X` on its box wire `1` passes it. -/
theorem x1_box (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (z : ℕ → Bool) :
    Derivable (theory N) (xAt N 1 * mc N .box [1] (ctlOr (ctlAt 0 true) (colOn 2 N z)) * xAt N 1)
      (mc N .box [1] (ctlOr (ctlAt 0 true) (colOn 2 N z))) := by
  have hs := swsw N 0 (by omega)
  have hx : Derivable (theory N) (swAt N 0 * xAt N 0 * swAt N 0) (xAt N 1) := by
    have := x_conj N 0 0 (by omega)
    rwa [show Net.tau 0 0 = 1 by simp [Net.tau]] at this
  exact fix_conj hs hx (N13.swapAB N hN z true).1 (N13.x0_hole N hN ih z true)

/-- (316) for the multi-controlled `H` of (333): `X` on its hole `2` passes it. -/
theorem x2_hg (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (c₁ : Bool) (z : ℕ → Bool) :
    Derivable (theory N) (xAt N 2 * mc N .hg [2, 0] (ctlOr (ctlAt 1 c₁) (colOn 3 N z)) * xAt N 2)
      (mc N .hg [2, 0] (ctlOr (ctlAt 1 c₁) (colOn 3 N z))) := by
  set y : ℕ → Bool := fun j => if j = 2 then c₁ else z j
  have hs0 := swsw N 0 (by omega)
  have hs1 := swsw N 1 (by omega)
  have hx0 : Derivable (theory N) (swAt N 0 * xAt N 0 * swAt N 0) (xAt N 1) := by
    have := x_conj N 0 0 (by omega)
    rwa [show Net.tau 0 0 = 1 by simp [Net.tau]] at this
  have hx1 : Derivable (theory N) (swAt N 1 * xAt N 1 * swAt N 1) (xAt N 2) := by
    have := x_conj N 1 1 (by omega)
    rwa [show Net.tau 1 1 = 2 by simp [Net.tau]] at this
  have hR := N13.hgR (N := N) hN (colOn 2 N y) (by simp [colOn]) (by simp [colOn])
  have eR : mc N .hg [2, 0] ((colOn 2 N y ∘ Net.tau 0) ∘ Net.tau 1) =
      mc N .hg [2, 0] (ctlOr (ctlAt 1 c₁) (colOn 3 N z)) :=
    Net.mc_congr _ _ _ (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h3
      · subst h; simp [colOn, ctlOr, ctlAt, Net.tau]
      · subst h; simp [colOn, ctlOr, ctlAt, Net.tau, y, hi, show 2 < N by omega]
      · subst h; simp [colOn, ctlOr, ctlAt, Net.tau]
      · simp [Function.comp, Net.tau_of_gt (show 0 + 1 < i by omega),
          Net.tau_of_gt (show 1 + 1 < i by omega), colOn, ctlOr, ctlAt, y, hi,
          show i ≠ 2 by omega, show i ≠ 1 by omega, show 2 ≤ i by omega, show 3 ≤ i by omega])
  rw [eR] at hR
  have h0 := x0_hole_hg N hN ih y
  have k0 := fix_conj hs0 hx0 (Derivable.refl _) h0
  exact fix_conj hs1 hx1 hR k0

/-! ## The canonical decomposition, every colouring -/

/-- The multi-controlled `H` of (333) with the colours `z`. -/
abbrev HGz (N : ℕ) (z : ℕ → Bool) : Circ N := mc N .hg [2, 0] (ctlOr (ctlAt 1 (z 1)) (colOn 3 N z))

/-- The box of (333) with the colours `z`. -/
abbrev Bz (N : ℕ) (z : ℕ → Bool) : Circ N := mc N .box [1] (ctlOr (ctlAt 0 true) (colOn 2 N z))

section Ctl

open MergeAll

theorem ctl_congR {N : ℕ} {z z' : ℕ → Bool} (hzz : ∀ i, 1 ≤ i → i < N → i ≠ 0 → z i = z' i) :
    ∀ i < N, colOn 1 N z i = colOn 1 N z' i := by
  intro i hi; unfold colOn; split_ifs with h
  · rw [hzz i h.1 hi (by omega)]
  · rfl

theorem ctl_congH {N : ℕ} {z z' : ℕ → Bool} (hzz : ∀ i, 1 ≤ i → i < N → i ≠ 0 → z i = z' i) :
    ∀ i < N, ctlOr (ctlAt 1 (z 1)) (colOn 3 N z) i = ctlOr (ctlAt 1 (z' 1)) (colOn 3 N z') i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h | h
  · subst h; simp [ctlOr, ctlAt, colOn]
  · subst h; simp [ctlOr, ctlAt, colOn, hzz 1 le_rfl hi (by omega)]
  · subst h; simp [ctlOr, ctlAt, colOn]
  · simp [ctlOr, ctlAt, colOn, hzz i (by omega) hi (by omega), show i ≠ 1 by omega, h, hi]

theorem ctl_congB {N : ℕ} {z z' : ℕ → Bool} (hzz : ∀ i, 1 ≤ i → i < N → i ≠ 0 → z i = z' i) :
    ∀ i < N, ctlOr (ctlAt 0 true) (colOn 2 N z) i = ctlOr (ctlAt 0 true) (colOn 2 N z') i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
  · subst h; simp [ctlOr, ctlAt, colOn]
  · subst h; simp [ctlOr, ctlAt, colOn]
  · simp [ctlOr, ctlAt, colOn, hzz i (by omega) hi (by omega), show i ≠ 0 by omega, h, hi]

theorem ctl_flipR {N j : ℕ} (z : ℕ → Bool) (hj1 : 1 ≤ j) (hjN : j < N) :
    ∀ i < N, setCtl (colOn 1 N z) j (some (!z j)) i = colOn 1 N (flip1 z j) i := by
  intro i hi; unfold setCtl colOn flip1; split_ifs <;> (try simp_all) <;> omega

theorem ctl_flipH {N j : ℕ} (z : ℕ → Bool) (hj1 : 1 ≤ j) (hj2 : j ≠ 2) :
    ∀ i < N, setCtl (ctlOr (ctlAt 1 (z 1)) (colOn 3 N z)) j (some (!z j)) i =
      ctlOr (ctlAt 1 (flip1 z j 1)) (colOn 3 N (flip1 z j)) i := by
  intro i hi; unfold setCtl ctlOr ctlAt colOn flip1; split_ifs <;> (try simp_all) <;> omega

theorem ctl_flipH2 {N : ℕ} (z : ℕ → Bool) :
    ∀ i < N, ctlOr (ctlAt 1 (z 1)) (colOn 3 N z) i =
      ctlOr (ctlAt 1 (flip1 z 2 1)) (colOn 3 N (flip1 z 2)) i := by
  intro i hi; unfold ctlOr ctlAt colOn flip1; split_ifs <;> (try simp_all) <;> omega

theorem ctl_flipB {N j : ℕ} (z : ℕ → Bool) (hj2 : 2 ≤ j) :
    ∀ i < N, setCtl (ctlOr (ctlAt 0 true) (colOn 2 N z)) j (some (!z j)) i =
      ctlOr (ctlAt 0 true) (colOn 2 N (flip1 z j)) i := by
  intro i hi; unfold setCtl ctlOr ctlAt colOn flip1; split_ifs <;> (try simp_all) <;> omega

theorem ctl_flipB1 {N : ℕ} (z : ℕ → Bool) :
    ∀ i < N, ctlOr (ctlAt 0 true) (colOn 2 N z) i =
      ctlOr (ctlAt 0 true) (colOn 2 N (flip1 z 1)) i := by
  intro i hi; unfold ctlOr ctlAt colOn flip1; split_ifs <;> (try simp_all) <;> omega

end Ctl

/-- (81) as a conjugation. -/
theorem flip81 {N : ℕ} (K : Kind) (tg : List ℕ) (e e' : ℕ → Option Bool) (j : ℕ) (b : Bool)
    (hjN : j < N) (hjt : j ∉ tg) (hej : e j = some b)
    (he : ∀ i < N, setCtl e j (some !b) i = e' i) :
    Derivable (theory N) (xAt N j * mc N K tg e * xAt N j) (mc N K tg e') := by
  have h := D.eq81 N K tg e j b hjN hjt hej
  rw [show drawn [xAt N j, mc N K tg e, xAt N j] = xAt N j * mc N K tg e * xAt N j by
    simp [drawn, mul_assoc]] at h
  exact h.trans (der_of_eq (Net.mc_congr _ _ _ he))

theorem dec_canon {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (h333 : H333 N) (h334 : H334 N) (a : Bool) :
    ∀ z : ℕ → Bool, Derivable (theory N) (mc N (Kind.sgnZX a) [0] (colOn 1 N z))
      (drawn (dw a (HGz N z) (Bz N z))) := by
  refine MergeAll.colour_ind (N := N) (w := 0)
    (fun z => Derivable (theory N) (mc N (Kind.sgnZX a) [0] (colOn 1 N z))
      (drawn (dw a (HGz N z) (Bz N z)))) ?_ ?_ ?_
  · intro z z' hzz q
    have e1 : mc N (Kind.sgnZX a) [0] (colOn 1 N z) = mc N (Kind.sgnZX a) [0] (colOn 1 N z') :=
      Net.mc_congr _ _ _ (ctl_congR hzz)
    have e2 : HGz N z = HGz N z' := Net.mc_congr _ _ _ (ctl_congH hzz)
    have e3 : Bz N z = Bz N z' := Net.mc_congr _ _ _ (ctl_congB hzz)
    show Derivable (theory N) (mc N (Kind.sgnZX a) [0] (colOn 1 N z'))
      (drawn (dw a (HGz N z') (Bz N z')))
    rw [← e1, ← e2, ← e3]; exact q
  · intro z j hj1 hjN _ q
    have hx := D.xAt_inv N j hjN
    have fR : Derivable (theory N) (xAt N j * mc N (Kind.sgnZX a) [0] (colOn 1 N z) * xAt N j)
        (mc N (Kind.sgnZX a) [0] (colOn 1 N (MergeAll.flip1 z j))) :=
      flip81 _ [0] _ _ j (z j) hjN (by simp; omega) (by simp [colOn, hj1, hjN])
        (ctl_flipR z hj1 hjN)
    have fH : Derivable (theory N) (xAt N j * HGz N z * xAt N j) (HGz N (MergeAll.flip1 z j)) := by
      by_cases hj2 : j = 2
      · subst hj2
        exact (x2_hg N hN ih (z 1) z).trans (der_of_eq (Net.mc_congr _ _ _ (ctl_flipH2 z)))
      · refine flip81 _ [2, 0] _ _ j (z j) hjN (by simp; omega) ?_ (ctl_flipH z hj1 hj2)
        rcases (by omega : j = 1 ∨ 3 ≤ j) with h1 | h3
        · subst h1; simp [ctlOr, ctlAt]
        · simp [ctlOr, ctlAt, colOn, show j ≠ 1 by omega, h3, hjN]
    have fB : Derivable (theory N) (xAt N j * Bz N z * xAt N j) (Bz N (MergeAll.flip1 z j)) := by
      by_cases hj1' : j = 1
      · subst hj1'
        exact (x1_box N hN ih z).trans (der_of_eq (Net.mc_congr _ _ _ (ctl_flipB1 z)))
      · refine flip81 _ [1] _ _ j (z j) hjN (by simp; omega) ?_ (ctl_flipB z (by omega))
        simp [ctlOr, ctlAt, colOn, show j ≠ 0 by omega, show 2 ≤ j by omega, hjN]
    have k := via_conj hx (l := [mc N (Kind.sgnZX a) [0] (colOn 1 N z)]) (L := [_])
      (List.Forall₂.cons fR List.Forall₂.nil) (dw_forall2 a fH fB) (by rw [drawn_one']; exact q)
    rwa [drawn_one'] at k
  · have eR : mc N (Kind.sgnZX a) [0] (colOn 1 N fun _ => true) =
        mc N (Kind.sgnZX a) [0] (blackOn 1 N) :=
      Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
    have eH : HGz N (fun _ => true) = mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)) :=
      Net.mc_congr _ _ _ (fun i hi => by simp [ctlOr, ctlAt, colOn, blackOn])
    have eB : Bz N (fun _ => true) = mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)) :=
      Net.mc_congr _ _ _ (fun i hi => by simp [ctlOr, ctlAt, colOn, blackOn])
    show Derivable (theory N) (mc N (Kind.sgnZX a) [0] (colOn 1 N fun _ => true))
      (drawn (dw a (HGz N fun _ => true) (Bz N fun _ => true)))
    rw [eR, eH, eB]
    cases a
    · exact h333
    · exact h334

/-! ## Frames with colours read through the frame -/

section Frames

variable {N : ℕ}

/-- The colours of `d` read through the frame of the wires `ps`. -/
def rd (ps : List ℕ) (d : ℕ → Option Bool) : ℕ → Bool := fun j => (d (frm ps j)).getD false

/-- A canonical control function agrees with `d` through the frame. -/
theorem frm_ctl {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) (d e : ℕ → Option Bool)
    (hlow : ∀ j < ps.length, e j = d (ps.getD j 0))
    (hhigh : ∀ j, ps.length ≤ j → j < N → frm ps j ∉ ps → e j = some (rd ps d j))
    (hfull : ∀ i < N, i ∉ ps → d i ≠ none) : ∀ j < N, e j = d (frm ps j) := by
  intro j hj
  by_cases hjl : j < ps.length
  · rw [frm_getD hnd hps hjl]; exact hlow j hjl
  · obtain ⟨hm, hl⟩ := frm_out' hnd hps (by omega) hj
    rw [hhigh j (by omega) hj hm]
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hfull _ hl hm)
    simp [rd, hv]

/-- A difference of two colourings off the wires `ps`, read through the frame. -/
theorem diff_frm {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {d₁ d₂ : ℕ → Option Bool}
    {j₀ : ℕ} {u v : Bool} (h₁ : d₁ j₀ = some u) (h₂ : d₂ j₀ = some v) (huv : u ≠ v)
    (hj : j₀ ∉ ps) (hjN : j₀ < N) : DiffOn ps.length N (rd ps d₁) (rd ps d₂) := by
  refine ⟨pos (netOf ps) j₀, ?_, pos_lt _ (netOf_ok hnd hps) j₀ hjN, ?_⟩
  · by_contra hlt
    push Not at hlt
    have e := frm_getD hnd hps hlt
    rw [frm_pos] at e
    apply hj
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  · simp [rd, frm_pos, h₁, h₂, huv]

/-- A commutation of two gates, moved by the frame of the wires `ps`. -/
theorem comm_frame {P : Kind → Prop} (hsw : McSwapK N P) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) {K₁ K₂ : Kind} (hK₁ : P K₁) (hK₂ : P K₂)
    {tg₁ tg₂ tg₁' tg₂' : List ℕ} {e₁ e₂ d₁ d₂ : ℕ → Option Bool}
    (hl₁ : tg₁.length = kindSp K₁) (hn₁ : tg₁.Nodup) (ht₁ : ∀ t ∈ tg₁, t < N)
    (hm₁ : tg₁.map (frm ps) = tg₁')
    (hl₂ : tg₂.length = kindSp K₂) (hn₂ : tg₂.Nodup) (ht₂ : ∀ t ∈ tg₂, t < N)
    (hm₂ : tg₂.map (frm ps) = tg₂')
    (he₁ : ∀ j < N, e₁ j = d₁ (frm ps j)) (he₂ : ∀ j < N, e₂ j = d₂ (frm ps j))
    (h : D.Comm N (mc N K₁ tg₁ e₁) (mc N K₂ tg₂ e₂)) :
    D.Comm N (mc N K₁ tg₁' d₁) (mc N K₂ tg₂' d₂) := by
  have f₁ := frameAtK hsw hnd hps K₁ hK₁ tg₁ tg₁' d₁ e₁ hl₁ hn₁ ht₁ hm₁ he₁
  have f₂ := frameAtK hsw hnd hps K₂ hK₂ tg₂ tg₂' d₂ e₂ hl₂ hn₂ ht₂ hm₂ he₂
  exact via_frame hnd hps (List.Forall₂.cons f₁ (List.Forall₂.cons f₂ List.Forall₂.nil))
    (List.Forall₂.cons f₂ (List.Forall₂.cons f₁ List.Forall₂.nil)) h

end Frames

/-! ## The decomposition at any wires -/

/-- A rotation with target `t` and a control on every other wire, as boxes
on `b` and multi-controlled `H` gates with their hole on `h`. -/
theorem dec_at {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (hsw : E.McSwapAll N) (h333 : H333 N)
    (h334 : H334 N) (a : Bool) {t b h : ℕ} (ht : t < N) (hb : b < N) (hh : h < N) (htb : t ≠ b)
    (hth : t ≠ h) (hbh : b ≠ h) (c : ℕ → Option Bool) (hc : ∀ i < N, c i = none ↔ i = t) :
    Derivable (theory N) (mc N (Kind.sgnZX a) [t] c)
      (drawn (dw a (mc N .hg [h, t] (setCtl c h none))
        (mc N .box [b] (setCtl (setCtl c b none) t (some true))))) := by
  have hnd : [t, b, h].Nodup := by simp [htb, hth, hbh]
  have hps : ∀ p ∈ [t, b, h], p < N := by simp [ht, hb, hh]
  have f0 : frm [t, b, h] 0 = t := frm_getD hnd hps (by simp)
  have f1 : frm [t, b, h] 1 = b := frm_getD hnd hps (by simp)
  have f2 : frm [t, b, h] 2 = h := frm_getD hnd hps (by simp)
  have g0 : [t, b, h].getD 0 0 = t := rfl
  have g1 : [t, b, h].getD 1 0 = b := rfl
  have g2 : [t, b, h].getD 2 0 = h := rfl
  have hct : c t = none := (hc t ht).2 rfl
  obtain ⟨vb, hvb⟩ := Option.ne_none_iff_exists'.1 (fun e => htb ((hc b hb).1 e).symm)
  obtain ⟨vh, hvh⟩ := Option.ne_none_iff_exists'.1 (fun e => hth ((hc h hh).1 e).symm)
  have hdc := dec_canon hN ih h333 h334 a (rd [t, b, h] c)
  have hfull : ∀ (S : List ℕ), (∀ s ∈ S, s ∈ [t, b, h]) → ∀ (d : ℕ → Option Bool),
      (∀ i < N, i ∉ S → d i = c i) → ∀ i < N, i ∉ [t, b, h] → d i ≠ none := by
    intro S hS d hd i hi hni e
    have hiS : i ∉ S := fun m => hni (hS i m)
    rw [hd i hi hiS] at e
    exact hni (by rw [(hc i hi).1 e]; simp)
  have hlen : [t, b, h].length = 3 := rfl
  have low3 : ∀ j < [t, b, h].length, j = 0 ∨ j = 1 ∨ j = 2 := fun j hj => by
    rw [hlen] at hj; omega
  have high3 : ∀ j, [t, b, h].length ≤ j → 3 ≤ j := fun j hj => by rwa [hlen] at hj
  have rd1 : rd [t, b, h] c 1 = vb := by simp [rd, f1, hvb]
  have rd2 : rd [t, b, h] c 2 = vh := by simp [rd, f2, hvh]
  -- the rotation
  have fR := frameAtK (hsw.toK (fun _ => True)) hnd hps (Kind.sgnZX a) trivial [0] [t] c
    (colOn 1 N (rd [t, b, h] c)) (by rw [kindSp_sgn]; rfl) (by simp)
    (by intro u hu; simp at hu; omega) (by simp [f0])
    (frm_ctl hnd hps c _ (fun j hj => by
      rcases low3 j hj with rfl | rfl | rfl
      · simp [colOn, hct]
      · rw [g1, hvb]; simp [colOn, show 1 < N by omega, rd1]
      · rw [g2, hvh]; simp [colOn, show 2 < N by omega, rd2])
      (fun j hj hjN _ => by
        have := high3 j hj
        simp [colOn, show 1 ≤ j by omega, hjN])
      (hfull [] (by simp) c (fun _ _ _ => rfl)))
  -- the multi-controlled `H`
  have fH := frameAtK (mcSwapBH ih) hnd hps .hg (Or.inr rfl) [2, 0] [h, t] (setCtl c h none)
    (ctlOr (ctlAt 1 (rd [t, b, h] c 1)) (colOn 3 N (rd [t, b, h] c)))
    rfl (by simp) (by intro u hu; simp at hu; omega) (by simp [f0, f2])
    (frm_ctl hnd hps _ _ (fun j hj => by
      rcases low3 j hj with rfl | rfl | rfl
      · simp [ctlOr, ctlAt, colOn, setCtl, hth, hct]
      · simp [ctlOr, ctlAt, colOn, setCtl, hbh, hvb, rd1]
      · simp [ctlOr, ctlAt, colOn, setCtl])
      (fun j hj hjN hm => by
        have hj3 := high3 j hj
        have hfh : frm [t, b, h] j ≠ h := fun e => hm (by simp [e])
        simp [ctlOr, ctlAt, colOn, rd, setCtl, hfh, show j ≠ 1 by omega, hj3, hjN])
      (hfull [h] (by simp) _ (fun i _ hi => by
        simp only [setCtl]; rw [if_neg (by simpa using hi)])))
  -- the box
  have fB := frameAtK (mcSwapBH ih) hnd hps .box (Or.inl rfl) [1] [b]
    (setCtl (setCtl c b none) t (some true)) (ctlOr (ctlAt 0 true) (colOn 2 N (rd [t, b, h] c)))
    rfl (by simp) (by intro u hu; simp at hu; omega) (by simp [f1])
    (frm_ctl hnd hps _ _ (fun j hj => by
      rcases low3 j hj with rfl | rfl | rfl
      · simp [ctlOr, ctlAt, colOn, setCtl]
      · simp [ctlOr, ctlAt, colOn, setCtl, Ne.symm htb]
      · simp [ctlOr, ctlAt, colOn, setCtl, Ne.symm hth, Ne.symm hbh, hvh, rd2,
          show 2 < N by omega])
      (fun j hj hjN hm => by
        have hj3 := high3 j hj
        have hft : frm [t, b, h] j ≠ t := fun e => hm (by simp [e])
        have hfb : frm [t, b, h] j ≠ b := fun e => hm (by simp [e])
        simp [ctlOr, ctlAt, colOn, rd, setCtl, hft, hfb, show j ≠ 0 by omega,
          show 2 ≤ j by omega, hjN])
      (hfull [t, b] (by simp) _ (fun i _ hi => by
        simp only [setCtl]
        rw [if_neg (fun e => hi (by simp [e])), if_neg (fun e => hi (by simp [e]))])))
  have k := via_frame hnd hps (l := [mc N (Kind.sgnZX a) [0] (colOn 1 N (rd [t, b, h] c))])
    (L := [_]) (List.Forall₂.cons fR List.Forall₂.nil) (dw_forall2 a fH fB)
    (by rw [drawn_one']; exact hdc)
  rwa [drawn_one'] at k

end QCert.RealCliffordCH.Sec8.D.N13.R347
