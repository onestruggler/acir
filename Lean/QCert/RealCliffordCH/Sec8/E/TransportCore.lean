/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: moving equations of multi-controlled gates to any wires (core)

The equations of Appendix D are stated at a canonical position (box wire
`0`, …).  The paper uses them on any wires, the network being irrelevant
in a PROP; here a swap network `μ` conjugates (`Net.placedBy N μ`) every
multi-controlled gate into another one (`placedBy_mc`), its wire `q` going
to `pos μ.reverse q`, so an equation between products of such gates moves
along any network (`placedBy_drawn`, `placedBy_cong`).

* `McSwapAll N`: naturality of `mc` for one swap, at any wires.  `Net.mc_swap`
  is the case where the two wires are not both controls; the other case
  needs (307), (313), (353) and is supplied by package (v).  Every lemma
  that moves gates across controls takes it as a hypothesis.
* `frame`: with `μ` the network of `placeG` for the wires `ps` and
  `π = pos μ.reverse` (so `π i = ps[i]`), `placedBy μ (mc K tg (c ∘ π))` is
  `mc K (tg.map π) c`: the canonical statement at the colouring `c ∘ π`
  gives the statement on the wires `ps`.
* `recolour`: `X` on several control wires on both sides exchanges their
  colours (Equation (81), iterated).
-/
import QCert.RealCliffordCH.Sec8.E.Letters
import QCert.RealCliffordCH.Sec8.Net
import QCert.RealCliffordCH.Sec8.D.N8
import QCert.RealCliffordCH.Sec8.Fast

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-- Naturality of `mc` for one swap, at any wires (`Net.mc_swap` and the
case of two controls). -/
abbrev McSwapAll (N : ℕ) : Prop :=
  ∀ j, j + 2 ≤ N → ∀ (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool),
    tg.length = kindSp K → tg.Nodup → (∀ t ∈ tg, t < N) →
      Derivable (theory N) (drawn [swAt N j, mc N K tg c, swAt N j])
        (mc N K (tg.map (Net.tau j)) (c ∘ Net.tau j))

/-- Naturality of `mc` for one swap, for the kinds satisfying `P`. -/
abbrev McSwapK (N : ℕ) (P : Kind → Prop) : Prop :=
  ∀ j, j + 2 ≤ N → ∀ (K : Kind), P K → ∀ (tg : List ℕ) (c : ℕ → Option Bool),
    tg.length = kindSp K → tg.Nodup → (∀ t ∈ tg, t < N) →
      Derivable (theory N) (drawn [swAt N j, mc N K tg c, swAt N j])
        (mc N K (tg.map (Net.tau j)) (c ∘ Net.tau j))

theorem McSwapAll.toK {N : ℕ} (h : McSwapAll N) (P : Kind → Prop) : McSwapK N P :=
  fun j hj K _ tg c => h j hj K tg c

/-- The symmetry (353) of the canonical `ZX`/`XZ` gates at every width up to `N`. -/
abbrev Sym353 (N : ℕ) : Prop :=
  ∀ k, k + 1 ≤ N → 3 ≤ k + 1 → ∀ (a : Bool) (j : ℕ), 1 ≤ j → j + 2 ≤ k + 1 →
    Derivable (theory (k + 1))
      (drawn [mc (k + 1) (Kind.sgnZX a) [0] (blackOn 1 (k + 1)), swAt (k + 1) j])
      (drawn [swAt (k + 1) j, mc (k + 1) (Kind.sgnZX a) [0] (blackOn 1 (k + 1))])

theorem ctrl_count {N : ℕ} {K : Kind} {tg : List ℕ} {c : ℕ → Option Bool}
    (htg : tg.length = kindSp K) (hnd : tg.Nodup) (htN : ∀ t ∈ tg, t < N) :
    (ctrlWires N tg c).length + kindSp K ≤ N := by
  have h1 := MS.nodup_length_le (ctrlWires_nodup N tg c hnd) (a := 0) (b := N) (by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact ⟨Nat.zero_le _, htN x h⟩
    · exact ⟨Nat.zero_le _, (MS.mem_ctrlWires.1 h).1⟩)
  simp only [List.length_append, htg] at h1
  omega

/-- Naturality of the box and the multi-controlled `H` for one swap, from
completeness below `N` and the symmetries (307), (313). -/
theorem mcSwapBH {N : ℕ} (ih : IH N) : McSwapK N (fun K => K = .box ∨ K = .hg) := by
  intro j hj K hK tg c htg hnd htN
  apply mc_swap_sym N j hj K tg c htg hnd htN
  have hk := ctrl_count (c := c) htg hnd htN
  set k := (ctrlWires N tg c).length
  rcases hK with rfl | rfl
  · exact canonSym_box k fun u hu1 hu2 =>
      D.eq307 (k + 1) (by omega) (ih.mono (by simp [kindSp] at hk; omega)) u hu1 hu2
  · exact canonSym_hg k fun u hu1 hu2 =>
      D.eq313 (k + 2) (by omega) (ih.mono (by simp [kindSp] at hk; omega)) u hu1 hu2

/-- Naturality of `mc` for one swap at any wires, from completeness below `N`,
the symmetries (307), (313) of the canonical gates and (353) (Net's
`mc_swap_sym`). -/
theorem mcSwapOf {N : ℕ} (ih : IH N) (h353 : Sym353 N) : McSwapAll N := by
  intro j hj K tg c htg hnd htN
  have hk := ctrl_count (c := c) htg hnd htN
  cases K with
  | box => exact mcSwapBH ih j hj .box (Or.inl rfl) tg c htg hnd htN
  | hg => exact mcSwapBH ih j hj .hg (Or.inr rfl) tg c htg hnd htN
  | zx =>
    apply mc_swap_sym N j hj _ tg c htg hnd htN
    set k := (ctrlWires N tg c).length
    by_cases hk2 : 2 ≤ k
    · exact canonSym_zx k false fun u hu1 hu2 =>
        h353 k (by simp [kindSp] at hk; omega) (by omega) false u hu1 hu2
    · intro u hu1 hu2; simp [kindSp] at hu1 hu2; omega
  | xz =>
    apply mc_swap_sym N j hj _ tg c htg hnd htN
    set k := (ctrlWires N tg c).length
    by_cases hk2 : 2 ≤ k
    · exact canonSym_zx k true fun u hu1 hu2 =>
        h353 k (by simp [kindSp] at hk; omega) (by omega) true u hu1 hu2
    · intro u hu1 hu2; simp [kindSp] at hu1 hu2; omega

section Placed

variable {N : ℕ}

theorem placedBy_cons (j : ℕ) (μ : List ℕ) (A : Circ N) :
    placedBy N (j :: μ) A = drawn [swAt N j, placedBy N μ A, swAt N j] := by
  rw [placedBy, placedBy, List.reverse_cons, swW_append, swW_cons, swW_cons, swW_nil, one_mul]
  simp [drawn, mul_assoc]

theorem placedBy_nil (A : Circ N) : placedBy N [] A = A := by
  simp [placedBy, swW_nil]

theorem placedBy_cong (μ : List ℕ) {A B : Circ N} (h : Derivable (theory N) A B) :
    Derivable (theory N) (placedBy N μ A) (placedBy N μ B) := by
  unfold placedBy
  exact dright _ (dleft _ h)

theorem swW_cancel {μ : List ℕ} (hμ : Ok N μ) : Derivable (theory N) (swW N μ * swW N μ.reverse) 1 := by
  have h := (SwEq.cancel μ.reverse (fun x hx => hμ x (List.mem_reverse.1 hx))).der
  rw [List.reverse_reverse, swW_append] at h
  simpa using h

theorem placedBy_mul {μ : List ℕ} (hμ : Ok N μ) (A B : Circ N) :
    Derivable (theory N) (placedBy N μ (A * B)) (placedBy N μ A * placedBy N μ B) := by
  unfold placedBy
  have e : swW N μ.reverse * A * swW N μ * (swW N μ.reverse * B * swW N μ) =
      swW N μ.reverse * A * (swW N μ * swW N μ.reverse) * B * swW N μ := by
    simp only [mul_assoc]
  rw [e]
  have := dright (swW N μ) (dright B (dleft (swW N μ.reverse * A) (swW_cancel hμ)))
  simp only [mul_one] at this
  simpa only [mul_assoc] using this.symm

theorem placedBy_one {μ : List ℕ} (hμ : Ok N μ) : Derivable (theory N) (placedBy N μ 1) 1 := by
  unfold placedBy
  have h := (SwEq.cancel μ hμ).der
  rw [swW_append] at h
  simpa [mul_one, swW_nil] using h

theorem placedBy_drawn {μ : List ℕ} (hμ : Ok N μ) :
    ∀ l : List (Circ N), Derivable (theory N) (placedBy N μ (drawn l)) (drawn (l.map (placedBy N μ)))
  | [] => by simpa [drawn] using placedBy_one hμ
  | a :: l => by
    rw [drawn_cons, List.map_cons, drawn_cons]
    exact (placedBy_mul hμ _ _).trans (dright _ (placedBy_drawn hμ l))

theorem placedBy_inv {μ : List ℕ} (hμ : Ok N μ) (A : Circ N) :
    Derivable (theory N) (placedBy N μ.reverse (placedBy N μ A)) A := by
  unfold placedBy
  rw [List.reverse_reverse]
  have e : swW N μ * (swW N μ.reverse * A * swW N μ) * swW N μ.reverse =
      (swW N μ * swW N μ.reverse) * A * (swW N μ * swW N μ.reverse) := by simp only [mul_assoc]
  rw [e]
  have := dmul (dright A (swW_cancel hμ)) (swW_cancel hμ)
  simpa using this

/-- A swap network conjugates a multi-controlled gate into another one. -/
theorem placedBy_mcK {P : Kind → Prop} (hsw : McSwapK N P) :
    ∀ (μ : List ℕ), Ok N μ → ∀ (K : Kind), P K → ∀ (tg : List ℕ) (c : ℕ → Option Bool),
      tg.length = kindSp K → tg.Nodup → (∀ t ∈ tg, t < N) →
        Derivable (theory N) (placedBy N μ (mc N K tg c))
          (mc N K (tg.map (pos μ.reverse)) (c ∘ pos μ))
  | [], _, K, _, tg, c, _, _, _ => by
    rw [placedBy_nil]
    have e1 : tg.map (pos ([] : List ℕ).reverse) = tg := by
      conv_rhs => rw [← List.map_id tg]
      rfl
    have e2 : c ∘ pos [] = c := by funext q; rfl
    rw [e1, e2]
  | j :: μ, hμ, K, hK, tg, c, hl, hnd, hlt => by
    have hμ' : Ok N μ := fun x hx => hμ x (by simp [hx])
    have hj : j + 2 ≤ N := hμ j (by simp)
    rw [placedBy_cons]
    have ih := placedBy_mcK hsw μ hμ' K hK tg c hl hnd hlt
    refine (dleft _ (dright _ ih)).trans ?_
    · have := hsw j hj K hK (tg.map (pos μ.reverse)) (c ∘ pos μ) (by simpa using hl)
        (hnd.map (pos_injective _)) (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
          exact pos_lt _ (fun x hx => hμ' x (List.mem_reverse.1 hx)) u (hlt u hu))
      have e1 : (tg.map (pos μ.reverse)).map (Net.tau j) = tg.map (pos (j :: μ).reverse) := by
        simp [List.map_map, Function.comp_def, pos_append]
      have e2 : (c ∘ pos μ) ∘ Net.tau j = c ∘ pos (j :: μ) := by
        funext q; simp [pos_cons]
      rw [e1, e2] at this
      simpa [drawn, mul_assoc] using this

/-- A swap network conjugates a multi-controlled gate into another one. -/
theorem placedBy_mc (hsw : McSwapAll N) (μ : List ℕ) (hμ : Ok N μ) (K : Kind) (tg : List ℕ)
    (c : ℕ → Option Bool) (hl : tg.length = kindSp K) (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < N) :
    Derivable (theory N) (placedBy N μ (mc N K tg c))
      (mc N K (tg.map (pos μ.reverse)) (c ∘ pos μ)) :=
  placedBy_mcK (hsw.toK (fun _ => True)) μ hμ K trivial tg c hl hnd hlt

end Placed

/-! ## Frames -/

section Frame

variable {N : ℕ}

/-- The network of `placeG` for the wires `ps`. -/
def netOf (ps : List ℕ) : List ℕ := netK ps ps.length

/-- The wire of the original circuit that the network for `ps` carries to
wire `i`. -/
def frm (ps : List ℕ) (i : ℕ) : ℕ := pos (netOf ps).reverse i

theorem netOf_ok {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) : Ok N (netOf ps) :=
  (netK_spec hnd hps ps.length le_rfl).1

theorem frm_getD {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {i : ℕ}
    (hi : i < ps.length) : frm ps i = ps.getD i 0 := by
  have := (netK_pos_iff hnd hps hi).2 rfl
  unfold frm netOf
  conv_lhs => rw [← this]
  exact pos_reverse _ _

theorem frm_lt {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {q : ℕ} (hq : q < N) :
    frm ps q < N :=
  pos_lt _ (fun x hx => netOf_ok hnd hps x (List.mem_reverse.1 hx)) q hq

theorem frm_injective (ps : List ℕ) : Function.Injective (frm ps) := pos_injective _

theorem pos_frm (ps : List ℕ) (q : ℕ) : pos (netOf ps) (frm ps q) = q := pos_reverse' _ q

/-- The canonical statement at the colouring `c ∘ frm ps` gives the statement
on the wires `ps`. -/
theorem frameK {P : Kind → Prop} (hsw : McSwapK N P) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (K : Kind) (hK : P K) (tg : List ℕ) (c : ℕ → Option Bool) (hl : tg.length = kindSp K)
    (htnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg (c ∘ frm ps)))
      (mc N K (tg.map (frm ps)) c) := by
  have := placedBy_mcK hsw (netOf ps) (netOf_ok hnd hps) K hK tg (c ∘ frm ps) hl htnd htN
  have e : (c ∘ frm ps) ∘ pos (netOf ps) = c := by
    funext q; simp only [Function.comp, frm, pos_reverse]
  have e2 : tg.map (pos (netOf ps).reverse) = tg.map (frm ps) := rfl
  rw [e, e2] at this
  exact this

/-- The canonical statement at the colouring `c ∘ frm ps` gives the statement
on the wires `ps`. -/
theorem frame (hsw : McSwapAll N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (hl : tg.length = kindSp K) (htnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg (c ∘ frm ps)))
      (mc N K (tg.map (frm ps)) c) :=
  frameK (hsw.toK (fun _ => True)) hnd hps K trivial tg c hl htnd htN

/-- An equation between products of gates on canonical positions, conjugated
by a network. -/
theorem frame_eq {μ : List ℕ} (hμ : Ok N μ) {l r : List (Circ N)}
    (h : Derivable (theory N) (drawn l) (drawn r)) :
    Derivable (theory N) (drawn (l.map (placedBy N μ))) (drawn (r.map (placedBy N μ))) :=
  ((placedBy_drawn hμ l).symm.trans (placedBy_cong μ h)).trans (placedBy_drawn hμ r)

end Frame

/-! ## Colours -/

/-- `c` with the colours on the wires `ws` exchanged. -/
def flipOn (ws : List ℕ) (c : ℕ → Option Bool) : ℕ → Option Bool :=
  fun j => if j ∈ ws then (c j).map not else c j

/-- Equation (81) on several control wires: `X` on the wires `ws` (nested)
on both sides of a multi-controlled gate exchanges their colours. -/
theorem recolour {N : ℕ} (K : Kind) (tg : List ℕ) :
    ∀ (ws : List ℕ) (c : ℕ → Option Bool), ws.Nodup → (∀ j ∈ ws, j < N ∧ j ∉ tg ∧ (c j).isSome) →
      Derivable (theory N) (drawn (ws.map (xAt N) ++ [mc N K tg c] ++ (ws.map (xAt N)).reverse))
        (mc N K tg (flipOn ws c))
  | [], c, _, _ => by
    have h1 : flipOn [] c = c := by funext j; simp [flipOn]
    have h2 : drawn (([] : List ℕ).map (xAt N) ++ [mc N K tg c] ++ (([] : List ℕ).map (xAt N)).reverse)
        = mc N K tg c := by simp [drawn]
    rw [h1, h2]
  | w :: ws, c, hnd, hw => by
    have hnd' := (List.nodup_cons.1 hnd)
    have ih := recolour K tg ws c hnd'.2 (fun j hj => hw j (by simp [hj]))
    obtain ⟨hwN, hwt, hws⟩ := hw w (by simp)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hws
    have hfb : flipOn ws c w = some b := by simp [flipOn, hnd'.1, hb]
    have h81 := D.eq81 N K tg (flipOn ws c) w b hwN hwt hfb
    have e : drawn ((w :: ws).map (xAt N) ++ [mc N K tg c] ++ ((w :: ws).map (xAt N)).reverse) =
        drawn [xAt N w, drawn (ws.map (xAt N) ++ [mc N K tg c] ++ (ws.map (xAt N)).reverse),
          xAt N w] := by
      simp [drawn, mul_assoc]
    rw [e]
    refine (dleft _ (dright _ ih)).trans ?_
    have e2 : setCtl (flipOn ws c) w (some !b) = flipOn (w :: ws) c := by
      funext j
      by_cases hj : j = w
      · subst hj; simp [setCtl, flipOn, hb]
      · simp [setCtl, flipOn, hj]
    rw [← e2]
    simpa [drawn, mul_assoc] using h81

/-! ## (309) with idle wires -/

theorem setCtl_liftW {c : ℕ → Option Bool} {w q : ℕ} (hwq : w ≠ q) (v : Option Bool) :
    setCtl c w v ∘ liftW q = setCtl (c ∘ liftW q) (dropW q w) v := by
  funext j
  simp only [Function.comp, setCtl, liftW, dropW]
  split_ifs <;> first | rfl | omega

/-- (309) on two wires: the box on wire `0` controlled by wire `1` in both
colours is the box with no control. -/
theorem merge2 (ih2 : CompleteAt 2) (c : ℕ → Option Bool) (hc : c 0 = none) (b : Bool) :
    Derivable (theory 2) (drawn [mc 2 .box [0] (setCtl c 1 (some b)), mc 2 .box [0] (setCtl c 1 (some !b))])
      (mc 2 .box [0] (setCtl c 1 none)) := by
  have e : ∀ v, mc 2 .box [0] (setCtl c 1 v) = mc 2 .box [0] (fun j => if j = 1 then v else none) := by
    intro v
    apply Net.mc_congr
    intro i hi
    rcases i with _ | _ | i
    · simp [setCtl, hc]
    · simp [setCtl]
    · omega
  rw [e, e, e]
  cases b
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))

/-- One step of the induction: (309) with idle wires on `N' + 1` wires, given it
on `N'` wires.  With an idle wire other than the merged one, it is moved to
the top; otherwise every wire is a control and this is (309). -/
theorem merge_step {N' : ℕ} (hN : 3 ≤ N' + 1) (ih : IH (N' + 1))
    (down : ∀ c' : ℕ → Option Bool, c' 0 = none → ∀ w', 1 ≤ w' → w' < N' → ∀ b : Bool,
      Derivable (theory N')
        (drawn [mc N' .box [0] (setCtl c' w' (some b)), mc N' .box [0] (setCtl c' w' (some !b))])
        (mc N' .box [0] (setCtl c' w' none)))
    (c : ℕ → Option Bool) (hc : c 0 = none) (w : ℕ) (hw1 : 1 ≤ w) (hw2 : w < N' + 1) (b : Bool) :
    Derivable (theory (N' + 1))
      (drawn [mc (N' + 1) .box [0] (setCtl c w (some b)),
        mc (N' + 1) .box [0] (setCtl c w (some !b))])
      (mc (N' + 1) .box [0] (setCtl c w none)) := by
  by_cases hq : ∃ q, 1 ≤ q ∧ q < N' + 1 ∧ q ≠ w ∧ c q = none
  · obtain ⟨q, hq1, hq2, hqw, hcq⟩ := hq
    have hA : ∀ v, ToTop N' q (mc (N' + 1) .box [0] (setCtl c w v))
        (mc N' .box [0] (setCtl (c ∘ liftW q) (dropW q w) v)) := by
      intro v
      have := ToTop.mc (M := N') (q := q) (by omega) .box [0] (setCtl c w v) rfl (by simp)
        (by simp) (by simp; omega) (by simp [setCtl, hqw, hcq])
      have e0 : [0].map (dropW q) = [0] := by simp [dropW]
      rwa [setCtl_liftW (Ne.symm hqw), e0] at this
    have hc' : (c ∘ liftW q) 0 = none := by simp [liftW, show 0 < q by omega, hc]
    have hw' : 1 ≤ dropW q w ∧ dropW q w < N' := by simp only [dropW]; split_ifs <;> omega
    exact liftIdle (ToTop.ofList (List.Forall₂.cons (hA _) (List.Forall₂.cons (hA _)
      List.Forall₂.nil))) (hA none) (down (c ∘ liftW q) hc' (dropW q w) hw'.1 hw'.2 b)
  · push Not at hq
    set x : ℕ → Bool := fun j => (c j).getD false
    have e : ∀ v, mc (N' + 1) .box [0] (setCtl c w v) =
        mc (N' + 1) .box [0] (setCtl (colOn 1 (N' + 1) x) w v) := by
      intro v
      apply Net.mc_congr
      intro i hi
      by_cases hiw : i = w
      · simp [setCtl, hiw]
      · by_cases hi0 : i = 0
        · subst hi0; simp [setCtl, hiw, hc, colOn]
        · have hci := hq i (by omega) hi hiw
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hci
          simp [setCtl, hiw, colOn, hy, x, show 1 ≤ i by omega, hi]
    rw [e, e, e]
    exact D.eq309 (N' + 1) hN ih x w hw1 hw2 b

/-- (309) at the box wire `0` for any controls (some wires may be idle). -/
theorem mergeC : ∀ (M : ℕ), IH (M + 3) → ∀ (c : ℕ → Option Bool), c 0 = none →
    ∀ w, 1 ≤ w → w < M + 3 → ∀ b : Bool,
      Derivable (theory (M + 3))
        (drawn [mc (M + 3) .box [0] (setCtl c w (some b)), mc (M + 3) .box [0] (setCtl c w (some !b))])
        (mc (M + 3) .box [0] (setCtl c w none)) := by
  intro M
  induction M with
  | zero =>
    intro ih
    exact merge_step (N' := 2) (by omega) ih fun c' hc' w' h1 h2 b => by
      obtain rfl : w' = 1 := by omega
      exact merge2 (ih 2 (by omega)) c' hc' b
  | succ M ihM =>
    intro ih
    exact merge_step (N' := M + 3) (by omega) ih (ihM (ih.mono (by omega)))

/-! ## Drawn products -/

theorem drawn_forall2 {N : ℕ} : ∀ {l l' : List (Circ N)},
    List.Forall₂ (fun A B => Derivable (theory N) A B) l l' →
      Derivable (theory N) (drawn l) (drawn l')
  | [], [], _ => Derivable.refl _
  | _ :: _, _ :: _, List.Forall₂.cons h hl => by
    rw [drawn_cons, drawn_cons]; exact dmul (drawn_forall2 hl) h

theorem drawn_map_congr {N : ℕ} {α : Type*} (l : List α) {f g : α → Circ N}
    (h : ∀ a ∈ l, Derivable (theory N) (f a) (g a)) :
    Derivable (theory N) (drawn (l.map f)) (drawn (l.map g)) := by
  apply drawn_forall2
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem drawn_flatMap {N : ℕ} {α : Type*} (l : List α) (g : α → List (Circ N)) :
    drawn (l.flatMap g) = drawn (l.map fun a => drawn (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, SE.drawn_append, ih, List.map_cons, drawn_cons]

theorem range_double {β : Type*} (K : ℕ) (f : ℕ → β) :
    (List.range (2 * K)).map f = (List.range K).flatMap fun i => [f (2 * i), f (2 * i + 1)] := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append,
      List.map_append, ih, List.range_succ, List.flatMap_append]
    simp

/-- An equation between gates at canonical positions, moved by the frame of
the wires `ps`: each factor is identified with a moved canonical one. -/
theorem via_frame {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    {l r L R : List (Circ N)}
    (hl : List.Forall₂ (fun A B => Derivable (theory N) (placedBy N (netOf ps) A) B) l L)
    (hr : List.Forall₂ (fun A B => Derivable (theory N) (placedBy N (netOf ps) A) B) r R)
    (h : Derivable (theory N) (drawn l) (drawn r)) : Derivable (theory N) (drawn L) (drawn R) := by
  have h' := frame_eq (netOf_ok hnd hps) h
  have m : ∀ {l L : List (Circ N)},
      List.Forall₂ (fun A B => Derivable (theory N) (placedBy N (netOf ps) A) B) l L →
      Derivable (theory N) (drawn (l.map (placedBy N (netOf ps)))) (drawn L) := by
    intro l L hl
    apply drawn_forall2
    induction hl with
    | nil => exact List.Forall₂.nil
    | cons h _ ih => exact List.Forall₂.cons h ih
  exact ((m hl).symm.trans h').trans (m hr)

/-! ## (309) at any box wire -/

theorem frm_pos (ps : List ℕ) (q : ℕ) : frm ps (pos (netOf ps) q) = q := pos_reverse _ q

theorem setCtl_frm (ps : List ℕ) (c : ℕ → Option Bool) (w : ℕ) (v : Option Bool) :
    setCtl c w v ∘ frm ps = setCtl (c ∘ frm ps) (pos (netOf ps) w) v := by
  funext j
  simp only [Function.comp, setCtl]
  have : frm ps j = w ↔ j = pos (netOf ps) w := by
    constructor
    · rintro rfl; exact (pos_frm ps j).symm
    · rintro rfl; exact frm_pos ps w
  by_cases h : j = pos (netOf ps) w
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun e => h (this.1 e)), if_neg h]


/-! ## Colourings of a list of wires -/

/-- The controls `base` with the bits of `i` on the wires `ws` (the first wire
the least significant bit). -/
def bitsOn : List ℕ → ℕ → (ℕ → Option Bool) → ℕ → Option Bool
  | [], _, base => base
  | w :: ws, i, base => setCtl (bitsOn ws (i / 2) base) w (some (decide (i % 2 = 1)))

/-- The controls `base` with the wires `ws` idle. -/
def idleOn : List ℕ → (ℕ → Option Bool) → ℕ → Option Bool
  | [], base => base
  | w :: ws, base => idleOn ws (setCtl base w none)

theorem bitsOn_of_not_mem : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) (j : ℕ), j ∉ ws →
    bitsOn ws i base j = base j
  | [], _, _, _, _ => rfl
  | w :: ws, i, base, j, hj => by
    have hjw : j ≠ w := fun e => hj (by simp [e])
    simp only [bitsOn, setCtl, hjw, if_false]
    exact bitsOn_of_not_mem ws _ base j (fun h => hj (by simp [h]))

theorem setCtl_bitsOn : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) (w : ℕ) (v : Option Bool),
    w ∉ ws → setCtl (bitsOn ws i base) w v = bitsOn ws i (setCtl base w v)
  | [], _, _, _, _, _ => rfl
  | u :: ws, i, base, w, v, hw => by
    have hwu : w ≠ u := fun e => hw (by simp [e])
    simp only [bitsOn]
    rw [← setCtl_bitsOn ws (i / 2) base w v (fun h => hw (by simp [h]))]
    funext j
    simp only [setCtl]
    by_cases h1 : j = w <;> by_cases h2 : j = u <;> simp_all

end QCert.RealCliffordCH.Sec8.E
