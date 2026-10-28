/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (309) and (311): coloured boxes

At a fixed width `N`, from the black statements (299), (301), (302) and
(307) at width `N` (module parameters of the section):

* `colour_red`: (81) on several wires at once: a gate with white controls on
  the wires `ws` is the gate with those controls black, between `X` gates on
  `ws`;
* (301), (302) at every control wire `w` (`merge301`, `merge302`): carried
  from the wire `2` by the swaps of the wires `w, w + 1`, which fix the box
  ((307)) and move the white or idle control (`Net.mc_swap_sym`, `mc_swap`);
* (309) (`eq309_of`) and (311) (`eq311_of`): by `colour_red`, the paper's
  proof.
-/
import QCert.RealCliffordCH.Sec8.D.N8.I307

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

/-- The `X` gates on the wires `ws`. -/
abbrev Xs (N : ℕ) (ws : List ℕ) : Circ N := drawn (ws.map (xAt N))

theorem xs_cons_comm (N j : ℕ) (ws : List ℕ) :
    Derivable (theory N) (xAt N j * Xs N ws) (Xs N ws * xAt N j) := by
  have h := D.drawn_xs_perm (N := N) (List.perm_append_singleton j ws).symm
  rw [List.map_cons, D.drawn_cons', List.map_append, D.drawn_append', List.map_singleton,
    show drawn [xAt N j] = xAt N j by simp [drawn]] at h
  exact h.symm

theorem xs_sq (N : ℕ) : ∀ (ws : List ℕ), (∀ j ∈ ws, j < N) →
    Derivable (theory N) (Xs N ws * Xs N ws) 1
  | [], _ => by simp [Xs, drawn]; exact Derivable.refl _
  | j :: ws, h => by
    have ih := xs_sq N ws (fun i hi => h i (by simp [hi]))
    have hx := D.xx N j (h j (by simp))
    simp only [Xs, List.map_cons, D.drawn_cons'] at ih ⊢
    have e : drawn (ws.map (xAt N)) * xAt N j * (drawn (ws.map (xAt N)) * xAt N j) =
        drawn (ws.map (xAt N)) * (xAt N j * drawn (ws.map (xAt N))) * xAt N j := by
      simp only [mul_assoc]
    rw [e]
    refine (dright _ (dleft _ (xs_cons_comm N j ws))).trans ?_
    have e2 : drawn (ws.map (xAt N)) * (drawn (ws.map (xAt N)) * xAt N j) * xAt N j =
        (drawn (ws.map (xAt N)) * drawn (ws.map (xAt N))) * (xAt N j * xAt N j) := by
      simp only [mul_assoc]
    rw [e2]
    simpa using dmul ih hx

/-- (81) on the wires `ws`. -/
theorem colour_red (N : ℕ) (K : Kind) (tg : List ℕ) :
    ∀ (ws : List ℕ) (c : ℕ → Option Bool), ws.Nodup →
      (∀ j ∈ ws, j < N ∧ j ∉ tg ∧ c j = some false) →
      Derivable (theory N) (mc N K tg c)
        (Xs N ws * mc N K tg (fun i => if i ∈ ws then some true else c i) * Xs N ws)
  | [], c, _, _ => by
    simp only [Xs, List.map_nil, drawn, List.reverse_nil, List.prod_nil, one_mul, mul_one,
      List.not_mem_nil, if_false]
    exact Derivable.refl _
  | j :: ws, c, hnd, h => by
    obtain ⟨hjN, hjt, hcj⟩ := h j (by simp)
    have hjws : j ∉ ws := (List.nodup_cons.1 hnd).1
    set c₁ := setCtl c j (some true)
    have h81 := D.eq81' N K tg c j false hjN hjt hcj
    have hxx := D.xx N j hjN
    have h1 : Derivable (theory N) (mc N K tg c) (xAt N j * mc N K tg c₁ * xAt N j) := by
      have e : drawn [xAt N j, mc N K tg c, xAt N j] = xAt N j * mc N K tg c * xAt N j := by
        simp [drawn, mul_assoc]
      rw [e] at h81
      have h2 := dctx (xAt N j) (xAt N j) h81
      have e2 : xAt N j * (xAt N j * mc N K tg c * xAt N j) * xAt N j =
          (xAt N j * xAt N j) * mc N K tg c * (xAt N j * xAt N j) := by simp only [mul_assoc]
      rw [e2] at h2
      have h3 := dmul (dmul hxx (Derivable.refl (mc N K tg c))) hxx
      simp only [one_mul, mul_one] at h3
      exact h3.symm.trans h2
    have ih := colour_red N K tg ws c₁ (List.nodup_cons.1 hnd).2 (fun i hi => by
      obtain ⟨a, b', c'⟩ := h i (by simp [hi])
      refine ⟨a, b', ?_⟩
      have : i ≠ j := fun e => hjws (e ▸ hi)
      simp [c₁, setCtl, this, c'])
    have hc : (fun i => if i ∈ ws then some true else c₁ i) =
        (fun i => if i ∈ j :: ws then some true else c i) := by
      funext i
      by_cases hi : i ∈ ws
      · simp [hi]
      · by_cases hij : i = j
        · subst hij; simp [c₁, setCtl, hi]
        · simp [c₁, setCtl, hi, hij]
    rw [hc] at ih
    refine h1.trans ((dright (xAt N j) (dleft (xAt N j) ih)).trans ?_)
    simp only [Xs, List.map_cons, D.drawn_cons']
    have e : xAt N j * (drawn (ws.map (xAt N)) * mc N K tg (fun i => if i ∈ j :: ws then some true
        else c i) * drawn (ws.map (xAt N))) * xAt N j =
        (xAt N j * drawn (ws.map (xAt N))) * (mc N K tg (fun i => if i ∈ j :: ws then some true
          else c i) * (drawn (ws.map (xAt N)) * xAt N j)) := by simp only [mul_assoc]
    rw [e]
    refine (dright _ (xs_cons_comm N j ws)).trans ?_
    simp only [mul_assoc]
    exact Derivable.refl _

/-! ## Boxes with all controls black but one -/

/-- The box on wire `0` with all other wires black, except `w` set to `v`. -/
abbrev Bv (N w : ℕ) (v : Option Bool) : Circ N := mc N .box [0] (setCtl (blackOn 1 N) w v)

theorem Bv_true (N w : ℕ) (hw : 1 ≤ w) : Bv N w (some true) = BxI N :=
  mc_congr _ _ _ (fun i hi => by
    simp only [setCtl, blackOn]
    split_ifs <;> first | rfl | omega)

theorem ctrlWires_Bv (N w : ℕ) (hw : 1 ≤ w) (hwN : w < N) (b : Bool) :
    (ctrlWires N [0] (setCtl (blackOn 1 N) w (some b))).length = N - 1 := by
  have e : ctrlWires N [0] (setCtl (blackOn 1 N) w (some b)) = List.range' 1 (N - 1) := by
    unfold ctrlWires
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [List.range_eq_range', show n + 1 - 1 = n by omega]
    show List.filter _ (List.range' 0 (n + 1)) = _
    rw [List.range'_succ, List.filter_cons]
    simp only [setCtl, blackOn, show (0 : ℕ) ≠ w by omega, if_false, show ¬ (1 ≤ 0 ∧ 0 < n + 1) by
      omega, Option.isSome_none, Bool.false_and, Bool.false_eq_true]
    refine List.filter_eq_self.2 (fun j hj => ?_)
    rw [List.mem_range'_1] at hj
    by_cases h : j = w
    · simp [h]; omega
    · simp [h, show 1 ≤ j ∧ j < n + 1 by omega]; omega
  rw [e, List.length_range']

section Merge

variable {N : ℕ} (hN : 3 ≤ N)
  (h307 : ∀ j, 1 ≤ j → j + 2 ≤ N →
    Derivable (theory N) (drawn [BxI N, swAt N j]) (drawn [swAt N j, BxI N]))

include hN h307 in
theorem canonSym_N : CanonSym .box (N - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simpa using canonSym_box k h307

include hN h307 in
/-- The swap of the wires `w, w + 1` moves a white control from `w` to `w + 1`. -/
theorem conj_Bv (w : ℕ) (hw : 1 ≤ w) (hwN : w + 2 ≤ N) (b : Bool) :
    Derivable (theory N) (swAt N w * Bv N w (some b) * swAt N w) (Bv N (w + 1) (some b)) := by
  have h := mc_swap_sym N w hwN .box [0] (setCtl (blackOn 1 N) w (some b)) rfl (by simp)
    (by simp; omega) (by rw [ctrlWires_Bv N w hw (by omega) b]; exact canonSym_N hN h307)
  have e1 : [0].map (Net.tau w) = [0] := by rw [List.map_singleton, Net.tau_of_lt (by omega)]
  rw [e1] at h
  refine (der_of_eq (by simp [drawn, mul_assoc])).trans (h.trans (der_of_eq (mc_congr _ _ _ ?_)))
  intro i hi
  simp only [Function.comp_apply, Net.tau, setCtl, blackOn]
  split_ifs <;> first | rfl | omega

/-- The swap of the wires `w, w + 1` moves an idle wire from `w` to `w + 1`. -/
theorem conj_Bn (w : ℕ) (hw : 1 ≤ w) (hwN : w + 2 ≤ N) :
    Derivable (theory N) (swAt N w * Bv N w none * swAt N w) (Bv N (w + 1) none) := by
  have h := mc_swap N w hwN .box [0] (setCtl (blackOn 1 N) w none) rfl (by simp) (by simp; omega)
    (by
      intro ⟨h1, _⟩
      simp only [ctrlWires, List.mem_filter, setCtl, if_true, Option.isSome_none,
        Bool.false_and, Bool.false_eq_true, and_false] at h1)
  have e1 : [0].map (Net.tau w) = [0] := by rw [List.map_singleton, Net.tau_of_lt (by omega)]
  rw [e1] at h
  refine (der_of_eq (by simp [drawn, mul_assoc])).trans (h.trans (der_of_eq (mc_congr _ _ _ ?_)))
  intro i hi
  simp only [Function.comp_apply, Net.tau, setCtl, blackOn]
  split_ifs <;> first | rfl | omega

/-- Carrying an equation `drawn [A, B] ≈ C` along a conjugation by an involution. -/
theorem conj3 {S A B C A' B' C' : Circ N} (hS : Derivable (theory N) (S * S) 1)
    (hA : Derivable (theory N) (S * A * S) A') (hB : Derivable (theory N) (S * B * S) B')
    (hC : Derivable (theory N) (S * C * S) C') (h : Derivable (theory N) (drawn [A, B]) C) :
    Derivable (theory N) (drawn [A', B']) C' := by
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one] at h ⊢
  refine (dmul hB hA).symm.trans ?_
  have e : S * B * S * (S * A * S) = S * B * (S * S) * A * S := by simp only [mul_assoc]
  rw [e]
  have h1 := dright S (dright A (dleft (S * B) hS))
  rw [mul_one] at h1
  refine h1.trans ?_
  have e2 : S * B * A * S = S * (B * A) * S := by simp only [mul_assoc]
  rw [e2]
  exact (dctx S S h).trans hC

theorem conj_symm {S A A' : Circ N} (hS : Derivable (theory N) (S * S) 1)
    (h : Derivable (theory N) (S * A * S) A') : Derivable (theory N) (S * A' * S) A := by
  have h1 := dctx S S h.symm
  have e : S * (S * A * S) * S = (S * S) * A * (S * S) := by simp only [mul_assoc]
  rw [e] at h1
  have h2 := dmul (dmul hS (Derivable.refl A)) hS
  simp only [one_mul, mul_one] at h2
  exact h1.trans h2

include hN h307 in
theorem conj_Bx (w : ℕ) (hw : 1 ≤ w) (hwN : w + 2 ≤ N) :
    Derivable (theory N) (swAt N w * BxI N * swAt N w) (BxI N) := by
  have h := h307 w hw hwN
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one] at h
  have h1 := dright (swAt N w) h
  have e : BxI N * swAt N w * swAt N w = BxI N * (swAt N w * swAt N w) := by simp only [mul_assoc]
  rw [e] at h1
  have h2 := dleft (BxI N) (swsw N w hwN)
  rw [mul_one] at h2
  exact h1.trans h2

include hN h307 in
/-- (301) and (302) at every control wire, from the wire `2`. -/
theorem merge_at (b : Bool)
    (h2 : Derivable (theory N) (drawn (if b then [BxI N, Bv N 2 (some false)]
      else [Bv N 2 (some false), BxI N])) (Bv N 2 none)) :
    ∀ w, 1 ≤ w → w < N → Derivable (theory N) (drawn (if b then [BxI N, Bv N w (some false)]
      else [Bv N w (some false), BxI N])) (Bv N w none) := by
  have up : ∀ d, 2 + d < N → Derivable (theory N) (drawn (if b then [BxI N, Bv N (2 + d) (some false)]
      else [Bv N (2 + d) (some false), BxI N])) (Bv N (2 + d) none) := by
    intro d
    induction d with
    | zero => intro _; exact h2
    | succ d ihd =>
      intro hd
      have ih := ihd (by omega)
      have hS := swsw N (2 + d) (by omega)
      have cB := conj_Bx hN h307 (2 + d) (by omega) (by omega)
      have cF := conj_Bv hN h307 (2 + d) (by omega) (by omega) false
      have cN := conj_Bn (N := N) (2 + d) (by omega) (by omega)
      cases b
      · exact conj3 hS cF cB cN ih
      · exact conj3 hS cB cF cN ih
  intro w hw hwN
  rcases (by omega : w = 1 ∨ 2 ≤ w) with rfl | h2w
  · have hS := swsw N 1 (by omega)
    have cB := conj_Bx hN h307 1 (by omega) (by omega)
    have cF := conj_symm hS (conj_Bv hN h307 1 (by omega) (by omega) false)
    have cN := conj_symm hS (conj_Bn (N := N) 1 (by omega) (by omega))
    cases b
    · exact conj3 hS cF cB cN h2
    · exact conj3 hS cB cF cN h2
  · obtain ⟨d, rfl⟩ : ∃ d, w = 2 + d := ⟨w - 2, by omega⟩
    exact up d hwN

end Merge


/-! ## (309) and (311) -/

theorem drawn2 {N : ℕ} (a b : Circ N) : drawn [a, b] = b * a := by simp [drawn]

/-- A product of two gates, each between the same `X` gates. -/
theorem xs_mul {N : ℕ} (ws : List ℕ) (hws : ∀ j ∈ ws, j < N) (A B : Circ N) :
    Derivable (theory N) (drawn [Xs N ws * A * Xs N ws, Xs N ws * B * Xs N ws])
      (Xs N ws * drawn [A, B] * Xs N ws) := by
  rw [drawn2, drawn2]
  have e : Xs N ws * B * Xs N ws * (Xs N ws * A * Xs N ws) =
      Xs N ws * B * (Xs N ws * Xs N ws) * A * Xs N ws := by simp only [mul_assoc]
  rw [e]
  have h := dright (Xs N ws) (dright A (dleft (Xs N ws * B) (xs_sq N ws hws)))
  rw [mul_one] at h
  refine h.trans ?_
  simp only [mul_assoc]; exact Derivable.refl _

theorem colour_box (N : ℕ) (c c' : ℕ → Option Bool) (ws : List ℕ) (hnd : ws.Nodup)
    (hws : ∀ j ∈ ws, j < N ∧ j ∉ [0] ∧ c j = some false)
    (hc : ∀ i < N, (if i ∈ ws then some true else c i) = c' i) :
    Derivable (theory N) (mc N .box [0] c) (Xs N ws * mc N .box [0] c' * Xs N ws) :=
  (colour_red N .box [0] ws c hnd hws).trans (der_of_eq (by rw [mc_congr _ _ _ hc]))

/-- (311) at width `N`, from (299) at width `N`. -/
theorem eq311_of {N : ℕ} (h299 : Derivable (theory N) (drawn [BxI N, BxI N]) 1)
    (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .box [0] (colOn 1 N x), mc N .box [0] (colOn 1 N x)]) 1 := by
  set ws := (List.range N).filter (fun j => decide (1 ≤ j) && !x j)
  have hwsN : ∀ j ∈ ws, j < N := fun j hj => by
    simp only [ws, List.mem_filter, List.mem_range] at hj; exact hj.1
  have h := colour_box N (colOn 1 N x) (blackOn 1 N) ws ((List.nodup_range).filter _)
    (fun j hj => by
      simp only [ws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at hj
      refine ⟨hj.1, by simp; omega, by simp [colOn, hj.2.1, hj.1, hj.2.2]⟩)
    (fun i hi => by
      by_cases hm : i ∈ ws
      · rw [if_pos hm]
        have hm' := hm
        simp only [ws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hm'
        simp [hi, blackOn, hm'.2.1]
      · rw [if_neg hm]
        simp only [ws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', not_and] at hm
        simp only [colOn, blackOn]
        by_cases h1 : 1 ≤ i
        · have := hm hi h1
          simp [h1, hi]
          cases hx : x i <;> simp_all
        · simp [h1])
  rw [drawn2]
  refine (dmul h h).trans ?_
  have h2 := xs_mul ws hwsN (BxI N) (BxI N)
  rw [drawn2, drawn2] at h2
  rw [drawn2] at h299
  refine h2.trans ?_
  have h3 := dright (Xs N ws) (dleft (Xs N ws) h299)
  rw [mul_one] at h3
  exact h3.trans (xs_sq N ws hwsN)

/-- (309) at width `N`, from (301), (302) and (307) at width `N`. -/
theorem eq309_of {N : ℕ} (hN : 3 ≤ N)
    (h307 : ∀ j, 1 ≤ j → j + 2 ≤ N →
      Derivable (theory N) (drawn [BxI N, swAt N j]) (drawn [swAt N j, BxI N]))
    (h301 : Derivable (theory N) (drawn [BxI N, Bv N 2 (some false)]) (Bv N 2 none))
    (h302 : Derivable (theory N) (drawn [Bv N 2 (some false), BxI N]) (Bv N 2 none))
    (x : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w) (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N .box [0] (setCtl (colOn 1 N x) w (some b)),
        mc N .box [0] (setCtl (colOn 1 N x) w (some !b))])
      (mc N .box [0] (setCtl (colOn 1 N x) w none)) := by
  set ws := (List.range N).filter (fun j => decide (1 ≤ j) && decide (j ≠ w) && !x j)
  have hwsN : ∀ j ∈ ws, j < N := fun j hj => by
    simp only [ws, List.mem_filter, List.mem_range] at hj; exact hj.1
  have red : ∀ v : Option Bool, Derivable (theory N) (mc N .box [0] (setCtl (colOn 1 N x) w v))
      (Xs N ws * Bv N w v * Xs N ws) := by
    intro v
    refine colour_box N _ _ ws ((List.nodup_range).filter _) (fun j hj => ?_) (fun i hi => ?_)
    · simp only [ws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at hj
      refine ⟨hj.1, by simp; omega, by simp [setCtl, colOn, hj.2.1.2, hj.2.1.1, hj.1, hj.2.2]⟩
    · by_cases hiw : i = w
      · subst hiw
        have : i ∉ ws := by simp [ws]
        simp [this, setCtl]
      · by_cases hm : i ∈ ws
        · rw [if_pos hm]
          have hm' := hm
          simp only [ws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hm'
          simp [hi, blackOn, setCtl, hiw, hm'.2.1.1]
        · rw [if_neg hm]
          simp only [ws, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', not_and] at hm
          simp only [setCtl, colOn, blackOn, if_neg hiw]
          by_cases h1 : 1 ≤ i
          · have := hm hi ⟨h1, hiw⟩
            simp [h1, hi]
            cases hx : x i <;> simp_all
          · simp [h1]
  have black : Derivable (theory N) (drawn [Bv N w (some b), Bv N w (some !b)]) (Bv N w none) := by
    cases b
    · have h := merge_at hN h307 false h302 w hw hwN
      simp only [Bool.false_eq_true, if_false] at h
      rw [show (!false) = true from rfl, Bv_true N w hw]
      exact h
    · have h := merge_at hN h307 true h301 w hw hwN
      simp only [if_true] at h
      rw [show (!true) = false from rfl, Bv_true N w hw]
      exact h
  have e1 : drawn [mc N .box [0] (setCtl (colOn 1 N x) w (some b)),
      mc N .box [0] (setCtl (colOn 1 N x) w (some !b))] =
      mc N .box [0] (setCtl (colOn 1 N x) w (some !b)) *
        mc N .box [0] (setCtl (colOn 1 N x) w (some b)) := by simp [drawn]
  rw [e1]
  refine (dmul (red _) (red _)).trans ?_
  have h2 := xs_mul ws hwsN (Bv N w (some b)) (Bv N w (some !b))
  rw [drawn2, drawn2] at h2
  rw [drawn2] at black
  exact h2.trans ((dright _ (dleft _ black)).trans (red none).symm)

end QCert.RealCliffordCH.Sec8.D.N8
