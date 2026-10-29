/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (342) and (344) from six wires on: assembly

See `E344s` for the method.  Here: the first gate as `P ⊗ P` around the
pieces of (339)'s box (`expH`), the second gate's pieces conjugated by `Q`
(`expQ`, with `Q` = `P ⊗ P` for (344), `P ⊗ P` and the swap of the wires
`0, 1` for (342)), the two remainders ((338), resp. (337), on their
merges), the pairs (`pairsQ`), and the reduction of the interface to the
frame (`comm344_ge6`, `comm342_ge6`).

No window is decided here; the only decisions are two-wire checks of the
conjugating words.  Memory (2026-10-29): 27 s, peak 0.40 GB anonymous.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E344s

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8 Sep

/-- The colours of the first gate in the frame (wires `2, …`). -/
def xH (c₁ : Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 2 then true else if i = 3 then c₁ else x i

/-- Pointwise equality of control functions on the wires `0, …, 4` and above. -/
macro "ctl_case4x" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ i = 4 ∨ 5 ≤ i) with h | h | h | h | h | h5 <;> (try subst h) <;>
  simp only [colOn, ctlOr, ctlAt, yH, yS, xE, xF, zS, xA, xA4, yB, yB3, xH, ctlX, setCtl,
    Net.tau, Function.comp] <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | (simp [List.lookup]; done) | omega))

/-! ## The first gate -/

theorem bA_xH (m : ℕ) (x : ℕ → Bool) (c₁ : Bool) :
    bA (m + 6) (xH c₁ x) true = mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ true x)) :=
  mc_congr _ _ _ (by ctl_case4x)

/-- The first gate: `P ⊗ P` around the pieces of the box of (339). -/
theorem expH (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ : Bool) :
    Derivable (theory (m + 6)) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xH c₁ x)))
      ((pp : Circ (m + 6)) * drawn (piecesA m x c₁ true) * pp) := by
  have h : Derivable (theory (m + 6)) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xH c₁ x)))
      ((pp : Circ (m + 6)) * bA (m + 6) (xH c₁ x) true * pp) := hg0_box4 (m + 2) (xH c₁ x)
  exact h.trans (dctx _ _ ((der_of_eq (bA_xH m x c₁)).trans (expA9 m ih x c₁ true)))

/-! ## The second gate -/

/-- The pieces of the second gate, conjugated by `Q`. -/
abbrev piecesQ (m : ℕ) (y : ℕ → Bool) (c : Bool) (qL qL' : List Lt) : List (Circ (m + 6)) :=
  (piecesB m y c).map (fun b => wc 4 (m + 6) qL' * b * wc 4 (m + 6) qL)

theorem expQ (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c : Bool) (qL qL' : List Lt)
    (h1 : Derivable (theory (m + 6)) (wc 4 (m + 6) qL * wc 4 (m + 6) qL') 1)
    (h2 : Derivable (theory (m + 6)) (wc 4 (m + 6) qL' * wc 4 (m + 6) qL) 1) :
    Derivable (theory (m + 6)) (wc 4 (m + 6) qL' * BE (m + 6) c y * wc 4 (m + 6) qL)
      (drawn (piecesQ m y c qL qL')) :=
  (dright _ (dleft _ (expB9 m ih y c))).trans (conj_drawn h1 h2 _)

/-! ## The two remainders -/

theorem pp6_inv (m : ℕ) (ih : IH (m + 6)) :
    Derivable (theory (m + 6)) ((pp : Circ (m + 6)) * pp) 1 := pp_inv (m + 3) ih

/-- `Comm a (P⊗P · b · P⊗P)` from `Comm (P⊗P · a · P⊗P) b`. -/
theorem comm_pp {m : ℕ} (ih : IH (m + 6)) {a b : Circ (m + 6)}
    (h : Comm (m + 6) ((pp : Circ (m + 6)) * a * pp) b) : Comm (m + 6) a (pp * b * pp) :=
  Comm.congr (pp_pp_conj (m := m + 1) ih a) (Derivable.refl _) (Comm.conj h (pp6_inv m ih))

/-- The remainder of the first gate between `P ⊗ P`: two multi-controlled `H`. -/
theorem splitH (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ : Bool) :
    Derivable (theory (m + 6)) ((pp : Circ (m + 6)) * cX 5 (m + 6) x (Ar c₁ true) * pp)
      (drawn [mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xA4 c₁ x true)),
        mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xA4 c₁ x false))]) := by
  have hp := pp6_inv m ih
  refine (dright _ (dleft _ (splitA m ih x c₁ true))).trans ((conj_drawn hp hp _).trans ?_)
  simp only [List.map_cons, List.map_nil]
  have e : ∀ b, Derivable (theory (m + 6)) ((pp : Circ (m + 6)) * aM m x c₁ true b * pp)
      (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xA4 c₁ x b))) := fun b =>
    (show Derivable (theory (m + 6)) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xA4 c₁ x b)))
      ((pp : Circ (m + 6)) * bA (m + 6) (xA4 c₁ x b) true * pp) from
      hg0_box4 (m + 2) (xA4 c₁ x b)).symm
  exact drawn2_congr (e true) (e false)

theorem diff_rem (y x : ℕ → Bool) (c₁ b b' : Bool) (m : ℕ) :
    DiffOn 2 (m + 6) (yB3 y b') (xA4 c₁ x b) :=
  ⟨2, le_rfl, by omega, by simp [yB3, xA4]⟩

theorem colOn2_tau0 (N : ℕ) (z : ℕ → Bool) (i : ℕ) :
    colOn 2 N z (Net.tau 0 i) = colOn 2 N z i := by
  unfold Net.tau
  split_ifs with h1 h2
  · subst h1; simp [colOn]
  · subst h2; simp [colOn]
  · rfl

/-- The swap of the wires `0, 1` on a multi-controlled `H` coloured from wire `2`. -/
theorem hg_s0 (m : ℕ) (ih : IH (m + 6)) (z : ℕ → Bool) :
    Derivable (theory (m + 6))
      (swAt (m + 6) 0 * mc (m + 6) .hg [1, 0] (colOn 2 (m + 6) z) * swAt (m + 6) 0)
      (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) z)) :=
  swBH ih 0 (by omega) .hg (Or.inr rfl) [1, 0] [0, 1] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (fun i _ => colOn2_tau0 _ z i)

theorem bM_s0 (m : ℕ) (y : ℕ → Bool) (c₂ q : Bool) :
    Derivable (theory (m + 6)) (swAt (m + 6) 0 *
      mc (m + 6) .box [0] (ctlOr (ctlAt 1 c₂) (colOn 2 (m + 6) (yB3 y q))) * swAt (m + 6) 0)
      (bM m y c₂ q) :=
  mc_s0 (m + 6) (by omega) _ 0 (by omega) _ _ (by decide) (fun i _ => by
    simp only [ctlOr, colOn2_tau0]
    congr 1
    simp only [ctlAt, Net.tau]
    split_ifs <;> first | rfl | omega)

theorem Yt1_s0 (m : ℕ) (y : ℕ → Bool) (c₂ : Bool) :
    Derivable (theory (m + 6)) (Yt (m + 6) 1 c₂ y)
      (swAt (m + 6) 0 * boxN (m + 6) y c₂ false * swAt (m + 6) 0) :=
  (mc_s0 (m + 6) (by omega) .box 0 (by omega) _ _ (by decide) (by ctl_case4x)).symm

theorem k44 (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ p q : Bool) :
    Comm (m + 6) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xA4 c₁ x p))) (bM m y c₂ q) := by
  have c0 := comm338d_ge5 (m + 6) (by omega) ih (yB3 y q) (xA4 c₁ x p)
    (diff_rem y x c₁ p q m) c₂
  exact Derivable.symm (Comm.congr (bM_s0 m y c₂ q) (hg_s0 m ih (xA4 c₁ x p))
    (Comm.conj c0 (swsw (m + 6) 0 (by omega))))

/-- (344): the two remainders. -/
theorem commRem44 (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ true)) ((pp : Circ (m + 6)) * Yt (m + 6) 1 c₂ y * pp) := by
  refine comm_pp ih ?_
  refine Comm.congr (splitH m ih x c₁).symm ((Yt1_s0 m y c₂).trans (splitB m ih y c₂)).symm
    (comm_drawn _ _ ?_)
  intro a ha b hb
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact k44 m ih x y c₁ c₂ _ _

/-- (342): the two remainders. -/
theorem commRem42 (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ true)) ((pp : Circ (m + 6)) * Yt (m + 6) 0 c₂ y * pp) := by
  refine comm_pp ih ?_
  have eY : Yt (m + 6) 0 c₂ y = mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) (yB c₂ y)) 3 none) :=
    mc_congr _ _ _ (by ctl_case4x)
  have e : ∀ b, mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) (yB c₂ y)) 3 (some b)) =
      bA (m + 6) (yB3 y b) c₂ := fun b => mc_congr _ _ _ (by ctl_case4x)
  have hY : Derivable (theory (m + 6)) (Yt (m + 6) 0 c₂ y)
      (drawn [bA (m + 6) (yB3 y true) c₂, bA (m + 6) (yB3 y false) c₂]) := by
    rw [eY, ← e true, ← e false]
    exact merge2 m ih (yB c₂ y) 3 (by omega) (by omega)
  refine Comm.congr (splitH m ih x c₁).symm hY.symm (comm_drawn _ _ ?_)
  intro a ha b hb
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
  have k : ∀ p q : Bool, Comm (m + 6) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xA4 c₁ x p)))
      (bA (m + 6) (yB3 y q) c₂) := fun p q =>
    Derivable.symm (comm337_ge5 (m + 6) (by omega) ih (yB3 y q) (xA4 c₁ x p)
      (diff_rem y x c₁ p q m) c₂)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact k _ _

/-! ## The pairs -/

theorem pairsQ {qL qL' : List Lt} (hq : QOK qL qL') (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool)
    (c₁ c₂ : Bool) (t : ℕ) (ht : t ≤ 1)
    (hrem : Derivable (theory (m + 6))
      (wc 4 (m + 6) qL' * (swAt (m + 6) 0 * boxN (m + 6) y c₂ false * swAt (m + 6) 0) *
        wc 4 (m + 6) qL) ((pp : Circ (m + 6)) * Yt (m + 6) t c₂ y * pp))
    (hRR : Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ true)) ((pp : Circ (m + 6)) * Yt (m + 6) t c₂ y * pp)) :
    ∀ a ∈ piecesA m x c₁ true, ∀ b ∈ piecesQ m y c₂ qL qL', Comm (m + 6) a b := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha'
  obtain ⟨b1, hb1, rfl⟩ := List.mem_map.1 hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb1
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb'
  have hR : Derivable (theory (m + 6))
      (wc 4 (m + 6) qL' * (wc 4 (m + 6) uL' * cX 4 (m + 6) (zS c₂ y) (P3' c₂ false) *
        wc 4 (m + 6) uL) * wc 4 (m + 6) qL) ((pp : Circ (m + 6)) * Yt (m + 6) t c₂ y * pp) :=
    (dctx _ _ (remB' m ih y c₂)).trans hrem
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']
    exact commRR_qc hq m ih hr hr'
  · rw [rots_cX hr]
    exact Comm.congr (Derivable.refl _) hR.symm (commRpp m ih y c₂ t ht hr)
  · rw [rots_cX hr']
    exact Comm.congr (remA m ih x c₁ true).symm (Derivable.refl _) (commArR_qc hq m ih x c₁ true hr')
  · exact Comm.congr (remA m ih x c₁ true).symm hR.symm hRR

/-- The pair in the frame, from the pieces. -/
theorem commFrame {qL qL' : List Lt} (hq : QOK qL qL') (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool)
    (c₁ c₂ : Bool) (t : ℕ) (ht : t ≤ 1)
    (h1 : Derivable (theory (m + 6)) (wc 4 (m + 6) qL * wc 4 (m + 6) qL') 1)
    (h2 : Derivable (theory (m + 6)) (wc 4 (m + 6) qL' * wc 4 (m + 6) qL) 1)
    (hrem : Derivable (theory (m + 6))
      (wc 4 (m + 6) qL' * (swAt (m + 6) 0 * boxN (m + 6) y c₂ false * swAt (m + 6) 0) *
        wc 4 (m + 6) qL) ((pp : Circ (m + 6)) * Yt (m + 6) t c₂ y * pp))
    (hRR : Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ true)) ((pp : Circ (m + 6)) * Yt (m + 6) t c₂ y * pp))
    (B : Circ (m + 6))
    (hB : Derivable (theory (m + 6)) ((pp : Circ (m + 6)) * B * pp)
      (wc 4 (m + 6) qL' * BE (m + 6) c₂ y * wc 4 (m + 6) qL)) :
    Comm (m + 6) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xH c₁ x))) B := by
  have hc : Comm (m + 6) (drawn (piecesA m x c₁ true)) (drawn (piecesQ m y c₂ qL qL')) :=
    comm_drawn _ _ (pairsQ hq m ih x y c₁ c₂ t ht hrem hRR)
  have hc' := Comm.congr (Derivable.refl _) (hB.trans (expQ m ih y c₂ qL qL' h1 h2)).symm hc
  have k := Comm.conj hc' (pp6_inv m ih)
  exact Comm.congr (expH m ih x c₁).symm (pp_pp_conj (m := m + 1) ih B) k

/-! ## (344) in the frame -/

theorem q44 : QOK N13.ppL N13.ppL where
  loc := by decide
  rt := by decide
  rt' := by decide
  on := by decide +kernel
  off := by decide +kernel

theorem comm344E (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm (m + 6) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xH c₁ x))) (BE (m + 6) c₂ y) := by
  have hp := pp6_inv m ih
  rw [← wc_ppL6] at hp
  refine commFrame q44 m ih x y c₁ c₂ 1 le_rfl hp hp ?_ (commRem44 m ih x y c₁ c₂) _ ?_
  · rw [wc_ppL6]
    exact dctx _ _ (mc_s0 (m + 6) (by omega) _ 0 (by omega) _ _ (by decide) (by ctl_case4x))
  · exact der_of_eq (by rw [wc_ppL6])

/-! ## (342) in the frame -/

theorem q42 : QOK (N13.ppL ++ [.s (.S 0)]) ([.s (.S 0)] ++ N13.ppL) where
  loc := by decide
  rt := by decide
  rt' := by decide
  on := by decide +kernel
  off := by decide +kernel

theorem wc_q42 (m : ℕ) : wc 4 (m + 6) (N13.ppL ++ [.s (.S 0)]) = swAt (m + 6) 0 * pp := by
  rw [wc_append, wc_one', circ_S, wc_ppL6]

theorem wc_q42' (m : ℕ) : wc 4 (m + 6) ([.s (.S 0)] ++ N13.ppL) = pp * swAt (m + 6) 0 := by
  rw [wc_append, wc_one', circ_S, wc_ppL6]

/-- The second gate of (342) in the frame: box on wire `0`, `H` on wire `3`. -/
abbrev BE' (N : ℕ) (c₂ : Bool) (y : ℕ → Bool) : Circ N :=
  mc N .hg [0, 3] (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 2 false) (colOn 4 N y)))

theorem comm342E (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm (m + 6) (mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xH c₁ x))) (BE' (m + 6) c₂ y) := by
  have hp := pp6_inv m ih
  have hs := swsw (m + 6) 0 (by omega)
  have i1 : Derivable (theory (m + 6))
      (wc 4 (m + 6) (N13.ppL ++ [.s (.S 0)]) * wc 4 (m + 6) ([.s (.S 0)] ++ N13.ppL)) 1 := by
    rw [wc_q42, wc_q42']
    have e : swAt (m + 6) 0 * pp * (pp * swAt (m + 6) 0) =
        swAt (m + 6) 0 * ((pp : Circ (m + 6)) * pp) * swAt (m + 6) 0 := by simp only [mul_assoc]
    rw [e]
    exact (dctx _ _ hp).trans (by simpa only [mul_one] using hs)
  have i2 : Derivable (theory (m + 6))
      (wc 4 (m + 6) ([.s (.S 0)] ++ N13.ppL) * wc 4 (m + 6) (N13.ppL ++ [.s (.S 0)])) 1 := by
    rw [wc_q42, wc_q42']
    have e : (pp : Circ (m + 6)) * swAt (m + 6) 0 * (swAt (m + 6) 0 * pp) =
        pp * (swAt (m + 6) 0 * swAt (m + 6) 0) * pp := by simp only [mul_assoc]
    rw [e]
    exact (dctx _ _ hs).trans (by simpa only [mul_one] using hp)
  have hrem : Derivable (theory (m + 6))
      (wc 4 (m + 6) ([.s (.S 0)] ++ N13.ppL) *
        (swAt (m + 6) 0 * boxN (m + 6) y c₂ false * swAt (m + 6) 0) *
        wc 4 (m + 6) (N13.ppL ++ [.s (.S 0)])) ((pp : Circ (m + 6)) * Yt (m + 6) 0 c₂ y * pp) := by
    rw [wc_q42, wc_q42']
    have e : (pp : Circ (m + 6)) * swAt (m + 6) 0 *
        (swAt (m + 6) 0 * boxN (m + 6) y c₂ false * swAt (m + 6) 0) * (swAt (m + 6) 0 * pp) =
        pp * ((swAt (m + 6) 0 * swAt (m + 6) 0) * boxN (m + 6) y c₂ false *
          (swAt (m + 6) 0 * swAt (m + 6) 0)) * pp := by simp only [mul_assoc]
    rw [e]
    refine dctx _ _ ((dmul (dmul hs (Derivable.refl _)) hs).trans ?_)
    simp only [one_mul, mul_one]
    exact Derivable.refl _
  have hB : Derivable (theory (m + 6)) ((pp : Circ (m + 6)) * BE' (m + 6) c₂ y * pp)
      (wc 4 (m + 6) ([.s (.S 0)] ++ N13.ppL) * BE (m + 6) c₂ y *
        wc 4 (m + 6) (N13.ppL ++ [.s (.S 0)])) := by
    rw [wc_q42, wc_q42']
    have t0 := swBH ih 0 (by omega) .hg (Or.inr rfl) [1, 3] [0, 3]
      (ctlOr (ctlAt 0 c₂) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y)))
      (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) rfl (by decide)
      (by intro t ht; simp at ht; omega) rfl (by ctl_case4x)
    have e : (pp : Circ (m + 6)) * swAt (m + 6) 0 * BE (m + 6) c₂ y * (swAt (m + 6) 0 * pp) =
        pp * (swAt (m + 6) 0 * BE (m + 6) c₂ y * swAt (m + 6) 0) * pp := by simp only [mul_assoc]
    rw [e]
    exact dctx _ _ t0.symm
  exact commFrame q42 m ih x y c₁ c₂ 0 (by omega) i1 i2 hrem (commRem42 m ih x y c₁ c₂) _ hB

/-! ## Back to the interface -/

abbrev cA44 (N : ℕ) (x : ℕ → Bool) (c₁ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 2 c₁) (colOn 3 N x)
abbrev cB44 (N : ℕ) (y : ℕ → Bool) (c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 0 c₂) (colOn 3 N y)
abbrev cB42 (N : ℕ) (y : ℕ → Bool) (c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 1 c₂) (colOn 3 N y)

theorem frameA (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ : Bool) (hx : x 3 = true) :
    Derivable (theory (m + 6)) (swAt (m + 6) 2 * mc (m + 6) .hg [0, 1] (colOn 2 (m + 6) (xH c₁ x)) *
      swAt (m + 6) 2) (mc (m + 6) .hg [0, 1] (cA44 (m + 6) x c₁)) :=
  swBH ih 2 (by omega) .hg (Or.inr rfl) [0, 1] [0, 1] _ _ rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cA44, colOn, ctlOr, ctlAt, xH, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))

/-- (344) when the colourings are black, resp. white, on wire `3`. -/
theorem comm344_core (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ : Bool)
    (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 6) (mc (m + 6) .hg [0, 1] (cA44 (m + 6) x c₁))
      (mc (m + 6) .hg [1, 2] (cB44 (m + 6) y c₂)) := by
  have hB := swBH ih 2 (by omega) .hg (Or.inr rfl) [1, 3] [1, 2]
    (ctlOr (ctlAt 0 c₂) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) (cB44 (m + 6) y c₂) rfl
    (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cB44, colOn, ctlOr, ctlAt, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  exact comm_flip (comm344E m ih x y c₁ c₂) (swsw (m + 6) 2 (by omega)) (frameA m ih x c₁ hx) hB

/-- (342) when the colourings are black, resp. white, on wire `3`. -/
theorem comm342_core (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ : Bool)
    (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 6) (mc (m + 6) .hg [0, 1] (cA44 (m + 6) x c₁))
      (mc (m + 6) .hg [0, 2] (cB42 (m + 6) y c₂)) := by
  have hB := swBH ih 2 (by omega) .hg (Or.inr rfl) [0, 3] [0, 2]
    (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) (cB42 (m + 6) y c₂) rfl
    (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cB42, colOn, ctlOr, ctlAt, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  exact comm_flip (comm342E m ih x y c₁ c₂) (swsw (m + 6) 2 (by omega)) (frameA m ih x c₁ hx) hB

/-- Relabeling a multi-controlled `H` on the wires `0, 1, 2` by a swap of
two of its controls above wire `2`. -/
theorem hg_tau (m : ℕ) (ih : IH (m + 6)) (tg : List ℕ) (htg : tg.length = 2) (hnd : tg.Nodup)
    (ht : ∀ t ∈ tg, t < 3) (u : ℕ) (hu : u < 3) (hut : u ∉ tg) (z : ℕ → Bool) (c : Bool) (j : ℕ)
    (hj : 3 ≤ j) (hjN : j + 2 ≤ m + 6) :
    Derivable (theory (m + 6))
      (swAt (m + 6) j * mc (m + 6) .hg tg (ctlOr (ctlAt u c) (colOn 3 (m + 6) (z ∘ Net.tau j))) *
        swAt (m + 6) j) (mc (m + 6) .hg tg (ctlOr (ctlAt u c) (colOn 3 (m + 6) z))) :=
  swBH ih j hjN .hg (Or.inr rfl) tg tg _ _ htg hnd (fun t h => by have := ht t h; omega)
    ((List.map_congr_left (g := id) fun t h => by
      show Net.tau j t = t
      exact Net.tau_of_lt (by have := ht t h; omega)).trans (List.map_id tg))
    (fun i hi => by
      simp only [ctlOr, ctlAt_tau (show u < j by omega), colOn_tau hj hjN z hi])

/-- `X` on wire `3` exchanges the colour there. -/
theorem hg_flip (m : ℕ) (tg : List ℕ) (ht : ∀ t ∈ tg, t < 3) (u : ℕ) (hu : u < 3) (z : ℕ → Bool)
    (c : Bool) :
    Derivable (theory (m + 6))
      (xAt (m + 6) 3 * mc (m + 6) .hg tg (ctlOr (ctlAt u c) (colOn 3 (m + 6) (flipAt 3 z))) *
        xAt (m + 6) 3) (mc (m + 6) .hg tg (ctlOr (ctlAt u c) (colOn 3 (m + 6) z))) := by
  have e := eq81 (m + 6) .hg tg (ctlOr (ctlAt u c) (colOn 3 (m + 6) (flipAt 3 z))) 3
    (flipAt 3 z 3) (by omega) (fun h => by have := ht 3 h; omega)
    (by simp [ctlOr, ctlAt, colOn, show (3 : ℕ) ≠ u by omega])
  rw [show drawn [xAt (m + 6) 3, mc (m + 6) .hg tg (ctlOr (ctlAt u c) (colOn 3 (m + 6) (flipAt 3 z))),
      xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .hg tg (ctlOr (ctlAt u c)
        (colOn 3 (m + 6) (flipAt 3 z))) * xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
  refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
  have := colOn_flip (lo := 3) (N := m + 6) (by omega) z i
  simp only [setCtl, ctlOr, ctlAt] at this ⊢
  split_ifs at this ⊢ <;> simp_all

/-- (344) from six wires on. -/
theorem comm344_ge6 (N : ℕ) (hN : 6 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 6 := ⟨N - 6, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 6) (mc (m + 6) .hg [0, 1] (cA44 (m + 6) x c₁))
    (mc (m + 6) .hg [1, 2] (cB44 (m + 6) y c₂))) ?_ ?_
    (fun x y hx hy => comm344_core m ih x y c₁ c₂ hx hy) x y hxy
  · intro x y j hj hjN h
    exact Comm.congr (hg_tau m ih [0, 1] rfl (by decide) (by decide) 2 (by omega) (by decide) x c₁ j
      hj hjN) (hg_tau m ih [1, 2] rfl (by decide) (by decide) 0 (by omega) (by decide) y c₂ j hj hjN)
      (Comm.conj h (swsw _ j hjN))
  · intro x y h
    exact comm_flip h (xAt_inv (m + 6) 3 (by omega))
      (hg_flip m [0, 1] (by decide) 2 (by omega) x c₁) (hg_flip m [1, 2] (by decide) 0 (by omega) y c₂)

/-- (342) from six wires on. -/
theorem comm342_ge6 (N : ℕ) (hN : 6 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [0, 2] (ctlOr (ctlAt 1 c₂) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 6 := ⟨N - 6, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 6) (mc (m + 6) .hg [0, 1] (cA44 (m + 6) x c₁))
    (mc (m + 6) .hg [0, 2] (cB42 (m + 6) y c₂))) ?_ ?_
    (fun x y hx hy => comm342_core m ih x y c₁ c₂ hx hy) x y hxy
  · intro x y j hj hjN h
    exact Comm.congr (hg_tau m ih [0, 1] rfl (by decide) (by decide) 2 (by omega) (by decide) x c₁ j
      hj hjN) (hg_tau m ih [0, 2] rfl (by decide) (by decide) 1 (by omega) (by decide) y c₂ j hj hjN)
      (Comm.conj h (swsw _ j hjN))
  · intro x y h
    exact comm_flip h (xAt_inv (m + 6) 3 (by omega))
      (hg_flip m [0, 1] (by decide) 2 (by omega) x c₁) (hg_flip m [0, 2] (by decide) 1 (by omega) y c₂)

end QCert.RealCliffordCH.Sec8.D.N13
