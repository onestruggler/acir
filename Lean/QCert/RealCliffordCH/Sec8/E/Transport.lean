/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: moving equations of multi-controlled gates to any wires

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
import QCert.RealCliffordCH.Sec8.D.N15

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-- Naturality of `mc` for one swap, at any wires (`Net.mc_swap` and the
case of two controls). -/
abbrev McSwapAll (N : ℕ) : Prop :=
  ∀ j, j + 2 ≤ N → ∀ (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool),
    tg.length = kindSp K → tg.Nodup → (∀ t ∈ tg, t < N) →
      Derivable (theory N) (drawn [swAt N j, mc N K tg c, swAt N j])
        (mc N K (tg.map (Net.tau j)) (c ∘ Net.tau j))

/-- Naturality of `mc` for one swap at any wires, from completeness below `N`
and the symmetries (307), (313), (353) of the canonical gates (Net's
`mc_swap_sym`; at a width below `N` they are the same equations there). -/
theorem mcSwapAll {N : ℕ} (ih : IH N) : McSwapAll N := by
  intro j hj K tg c htg hnd htN
  apply mc_swap_sym N j hj K tg c htg hnd htN
  have hk : (ctrlWires N tg c).length + kindSp K ≤ N := by
    have h1 := MS.nodup_length_le (ctrlWires_nodup N tg c hnd) (a := 0) (b := N) (by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact ⟨Nat.zero_le _, htN x h⟩
      · exact ⟨Nat.zero_le _, (MS.mem_ctrlWires.1 h).1⟩)
    simp only [List.length_append, htg] at h1
    omega
  set k := (ctrlWires N tg c).length
  cases K with
  | box =>
    exact canonSym_box k fun u hu1 hu2 =>
      D.eq307 (k + 1) (by omega) (ih.mono (by simp [kindSp] at hk; omega)) u hu1 hu2
  | hg =>
    exact canonSym_hg k fun u hu1 hu2 =>
      D.eq313 (k + 2) (by omega) (ih.mono (by simp [kindSp] at hk; omega)) u hu1 hu2
  | zx =>
    exact canonSym_zx k false fun u hu1 hu2 =>
      D.eq353 (k + 1) (by omega) (ih.mono (by simp [kindSp] at hk; omega)) false u hu1 hu2
  | xz =>
    exact canonSym_zx k true fun u hu1 hu2 =>
      D.eq353 (k + 1) (by omega) (ih.mono (by simp [kindSp] at hk; omega)) true u hu1 hu2

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
theorem placedBy_mc (hsw : McSwapAll N) :
    ∀ (μ : List ℕ), Ok N μ → ∀ (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool),
      tg.length = kindSp K → tg.Nodup → (∀ t ∈ tg, t < N) →
        Derivable (theory N) (placedBy N μ (mc N K tg c))
          (mc N K (tg.map (pos μ.reverse)) (c ∘ pos μ))
  | [], _, K, tg, c, _, _, _ => by
    rw [placedBy_nil]
    have e1 : tg.map (pos ([] : List ℕ).reverse) = tg := by
      conv_rhs => rw [← List.map_id tg]
      rfl
    have e2 : c ∘ pos [] = c := by funext q; rfl
    rw [e1, e2]
  | j :: μ, hμ, K, tg, c, hl, hnd, hlt => by
    have hμ' : Ok N μ := fun x hx => hμ x (by simp [hx])
    have hj : j + 2 ≤ N := hμ j (by simp)
    rw [placedBy_cons]
    have ih := placedBy_mc hsw μ hμ' K tg c hl hnd hlt
    refine (dleft _ (dright _ ih)).trans ?_
    · have := hsw j hj K (tg.map (pos μ.reverse)) (c ∘ pos μ) (by simpa using hl)
        (hnd.map (pos_injective _)) (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
          exact pos_lt _ (fun x hx => hμ' x (List.mem_reverse.1 hx)) u (hlt u hu))
      have e1 : (tg.map (pos μ.reverse)).map (Net.tau j) = tg.map (pos (j :: μ).reverse) := by
        simp [List.map_map, Function.comp_def, pos_append]
      have e2 : (c ∘ pos μ) ∘ Net.tau j = c ∘ pos (j :: μ) := by
        funext q; simp [pos_cons]
      rw [e1, e2] at this
      simpa [drawn, mul_assoc] using this

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
theorem frame (hsw : McSwapAll N) {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (hl : tg.length = kindSp K) (htnd : tg.Nodup)
    (htN : ∀ t ∈ tg, t < N) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg (c ∘ frm ps)))
      (mc N K (tg.map (frm ps)) c) := by
  have := placedBy_mc hsw (netOf ps) (netOf_ok hnd hps) K tg (c ∘ frm ps) hl htnd htN
  have e : (c ∘ frm ps) ∘ pos (netOf ps) = c := by
    funext q; simp only [Function.comp, frm, pos_reverse]
  have e2 : tg.map (pos (netOf ps).reverse) = tg.map (frm ps) := rfl
  rw [e, e2] at this
  exact this

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

end QCert.RealCliffordCH.Sec8.E
