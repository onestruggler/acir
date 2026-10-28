/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Stage 2 of the stabiliser chain, and completeness at every width

Toward Theorem 4.4.  Stage 2 acts on the words of tokens of the stabiliser
of `Z₀` (stage 1), through the points `(1, i) :: y` that `X₀` reaches.
Its Schreier condition (`Good2`) holds for every such token on `n + 1 ≥ 3`
wires, from the stage-1 condition on `n` wires and the local facts
(S2a)-(S2g) (`good2_tok`).  The end (`words_trivial_succ`): a word acting
trivially is, by stage 1, a word of tokens of the stabiliser of `Z₀`, by
stage 2 a word of tokens of the stabiliser of `Z₀` and `X₀`, that is, a
word on wire `0` times a word above it (`split_K2`); each acts trivially
on its own wires, so both are trivial by completeness on one and on `n`
wires (`k2_trivial`).  By induction on the width the rules are complete
on every number of wires (`complete_all`).
-/
import QCert.QutritClifford.Stage1

namespace QCert.QutritClifford

/-- **The Schreier condition of stage 2** for a word on `n` wires. -/
def Good2 (n : ℕ) (w : List Lt) : Prop :=
  ∀ (i : Fin 3) (y : Pt), y.length + 1 = n → ∃ i' y', ptRun w ((1, i) :: y) = (1, i') :: y' ∧
    ∃ ts, K2 n ts ∧ E n (tau ((1, i) :: y) ++ w) (kw ts ++ tau ((1, i') :: y'))

theorem Good2.nil (n : ℕ) : Good2 n [] :=
  fun i y _ => ⟨i, y, rfl, [], K2.nil n, by simpa using E.refl _⟩

theorem Good2.append {n : ℕ} {a b : List Lt} (ha : Good2 n a) (hb : Good2 n b) :
    Good2 n (a ++ b) := by
  intro i y hy
  obtain ⟨i1, y1, hp1, t1, h1, e1⟩ := ha i y hy
  have hy1 : y1.length + 1 = n := by
    have := length_ptRun a ((1, i) :: y)
    rw [hp1] at this; simp at this; omega
  obtain ⟨i2, y2, hp2, t2, h2, e2⟩ := hb i1 y1 hy1
  refine ⟨i2, y2, by rw [ptRun_append, hp1, hp2], t1 ++ t2, h1.append h2, ?_⟩
  have h3 : E n (tau ((1, i) :: y) ++ a ++ b) (kw t1 ++ (tau ((1, i1) :: y1) ++ b)) := by
    simpa [List.append_assoc] using e1.append (E.refl b)
  have h4 := h3.trans ((E.refl (kw t1)).append e2)
  simpa [List.append_assoc, kw_append] using h4

theorem ptRun_sw0_one : ∀ s < 3, ∀ i : Fin 3, ptRun (sw0 s).word [(1, i)] = [(1, snext (sw0 s) i)] := by
  decide

theorem sw0_onW0 : ∀ s < 3, (sw0 s).word.all onW0 = true := by decide

section Step

variable {n : ℕ} (hn : 2 ≤ n) (hc : Complete 2)
include hn hc

/-- A word of tokens of the second stabiliser passes `Q`. -/
theorem q_pass (i : Fin 3) : ∀ ts : List Tok, K2 (n + 1) ts →
    ∃ ts', K2 (n + 1) ts' ∧ E (n + 1) (Qw i ++ kw ts) (kw ts' ++ Qw i)
  | [], _ => ⟨[], K2.nil _, by simpa [kw] using E.refl _⟩
  | t :: ts, h => by
    obtain ⟨ts1, h1, e1⟩ := q_pass i ts (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have ht := h t List.mem_cons_self
    have h3 : 3 ≤ n + 1 := by omega
    obtain ⟨k, hk, ek⟩ : ∃ k, K2 (n + 1) k ∧ E (n + 1) (Qw i ++ t.word) (kw k ++ Qw i) := by
      have one : ∀ j < 2, t = tw0 j →
          ∃ k, K2 (n + 1) k ∧ E (n + 1) (Qw i ++ t.word) (kw k ++ Qw i) := by
        intro j hj ht'
        have hok := ok_S2e i j hj
        refine ⟨(eS2e i j).2, (K2_of_entOk hok).mono (by omega), ?_⟩
        rw [ht']
        exact E.of3 h3 (of_entOk hc hok)
          (fits_append (fits_mono (fits_Qw i) (by omega)) (fits_mono (fits_tw0 j hj) (by omega)))
          (fits_append (K2_of_entOk hok).fits (fits_mono (fits_Qw i) (by omega)))
      cases t with
      | X0 => exact one 0 (by omega) rfl
      | Z0 => exact one 1 (by omega) rfl
      | S0 => simp [Tok.isK2] at ht
      | C0 => simp [Tok.isK2] at ht
      | top x =>
        have hlo : 1 ≤ x.lo := by simpa [Tok.isK2] using ht.1
        have hx : x.hi < n + 1 := ht.2 x (by simp [Tok.word])
        refine ⟨[.top x], K2_top hlo hx, ?_⟩
        exact E_comm _ _ (fun a ha b hb => by
          simp only [Tok.word, List.mem_singleton] at hb
          subst hb; exact disj_of_lt (by rw [Qw_hi i a ha]; omega))
    refine ⟨k ++ ts1, hk.append h1, ?_⟩
    rw [kw_cons, ← List.append_assoc]
    refine (ek.append (E.refl _)).trans ?_
    rw [List.append_assoc, kw_append, List.append_assoc]
    exact (E.refl _).append e1

/-- A word of tokens of the first stabiliser, one wire up, passes `Q ⨾ CZ`. -/
theorem qc_pass (i : Fin 3) : ∀ ts : List Tok, K1 n ts →
    ∃ ts', K2 (n + 1) ts' ∧ E (n + 1) (Qw i ++ [.C 0] ++ (kw ts).map Lt.up) (kw ts' ++ (Qw i ++ [.C 0]))
  | [], _ => ⟨[], K2.nil _, by simpa [kw] using E.refl _⟩
  | t :: ts, h => by
    obtain ⟨ts1, h1, e1⟩ := qc_pass i ts (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have ht := h t List.mem_cons_self
    have h3 : 3 ≤ n + 1 := by omega
    obtain ⟨k, hk, ek⟩ : ∃ k, K2 (n + 1) k ∧
        E (n + 1) (Qw i ++ [.C 0] ++ t.word.map Lt.up) (kw k ++ (Qw i ++ [.C 0])) := by
      -- through `CZ` by (S2c) or (S2d), then through `Q`
      have via : ∀ (k0 : List Tok) (c : List Lt), K2 3 k0 → E (n + 1) ([.C 0] ++ c) (kw k0 ++ [.C 0]) →
          t.word.map Lt.up = c →
          ∃ k, K2 (n + 1) k ∧ E (n + 1) (Qw i ++ [.C 0] ++ t.word.map Lt.up) (kw k ++ (Qw i ++ [.C 0])) := by
        intro k0 c hk0 e0 hw
        obtain ⟨k1, hk1, e1'⟩ := q_pass hn hc i k0 (hk0.mono (by omega))
        refine ⟨k1, hk1, ?_⟩
        rw [hw, List.append_assoc]
        refine ((E.refl (Qw i)).append e0).trans ?_
        rw [← List.append_assoc]
        refine (e1'.append (E.refl _)).trans ?_
        rw [List.append_assoc]
      have one : ∀ c < 3, t.word.map Lt.up = cw1 c →
          ∃ k, K2 (n + 1) k ∧ E (n + 1) (Qw i ++ [.C 0] ++ t.word.map Lt.up) (kw k ++ (Qw i ++ [.C 0])) := by
        intro c hc3 hw
        have hok := ok_S2c c hc3
        exact via _ _ (K2_of_entOk hok) (E.of3 h3 (of_entOk hc hok)
          (fits_append (by decide) (fits_mono (fits_cw1 c hc3) (by omega)))
          (fits_append (K2_of_entOk hok).fits (by decide))) hw
      cases t with
      | S0 => exact one 0 (by omega) rfl
      | X0 => exact one 1 (by omega) rfl
      | Z0 => exact one 2 (by omega) rfl
      | C0 =>
        have hok := ok_S2d
        exact via _ _ (K2_of_entOk hok) (E.of3 h3 (of_entOk hc hok) (by decide)
          (fits_append (K2_of_entOk hok).fits (by decide))) rfl
      | top x =>
        have hlo : 1 ≤ x.lo := by simpa [Tok.isK1] using ht.1
        have hx : x.hi < n := ht.2 x (by simp [Tok.word])
        refine ⟨[.top x.up], K2_top (by simp only [Lt.lo_up]; omega)
          (by simp only [Lt.hi_up]; omega), ?_⟩
        refine E_comm _ _ (fun a ha b hb => ?_)
        simp only [Tok.word, List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        refine disj_of_lt ?_
        rcases List.mem_append.1 ha with ha | ha
        · have := Qw_hi i a ha; simp only [Lt.lo_up]; omega
        · rw [List.mem_singleton.1 ha]; simp only [Lt.hi, Lt.lo_up]; omega
    refine ⟨k ++ ts1, hk.append h1, ?_⟩
    have h3 : E (n + 1) (Qw i ++ [.C 0] ++ (kw (t :: ts)).map Lt.up)
        (kw k ++ (Qw i ++ [.C 0] ++ (kw ts).map Lt.up)) := by
      rw [kw_cons, List.map_append]
      simpa [List.append_assoc] using ek.append (E.refl ((kw ts).map Lt.up))
    have h4 := h3.trans ((E.refl (kw k)).append e1)
    simpa [List.append_assoc, kw_append] using h4

/-- `S`, `X`, `Z` on wire `0`. -/
theorem s2_bot (s : ℕ) (hs : s < 3) : Good2 (n + 1) (sw0 s).word := by
  intro i y hy
  obtain ⟨p', h1, h2⟩ := ptRun_w0 (sw0 s).word (sw0_onW0 s hs) (1, i) y
  rw [ptRun_sw0_one s hs i] at h1
  simp only [List.cons.injEq, and_true] at h1
  refine ⟨snext (sw0 s) i, y, by rw [h2, ← h1], ?_⟩
  have h3 : 3 ≤ n + 1 := by omega
  cases hzy : isZ y with
  | true =>
    have hok := ok_S2a i s hs
    refine ⟨(eS2a i s).2, (K2_of_entOk hok).mono (by omega), ?_⟩
    simp only [tau, hzy, if_true, List.append_nil]
    exact E.of3 h3 (of_entOk hc hok)
      (fits_append (fits_mono (fits_Qw i) (by omega)) (fits_mono (fits_sw0 s hs) (by omega)))
      (fits_append (K2_of_entOk hok).fits (fits_mono (fits_Qw _) (by omega)))
  | false =>
    have hok := ok_S2b i s hs
    refine ⟨(eS2b i s).2, (K2_of_entOk hok).mono (by omega), ?_⟩
    simp only [tau, hzy, Bool.false_eq_true, if_false]
    have c1 : E (n + 1) ((sigma y).map Lt.up ++ (sw0 s).word) ((sw0 s).word ++ (sigma y).map Lt.up) :=
      E_comm _ _ (fun a ha b hb => (Bool.or_comm _ _).trans
        (disj_of_lt (by rw [sw0_hi s hs b hb]; exact lo_of_mem_up ha)))
    have c2 := E.of3 h3 (of_entOk hc hok)
      (fits_append (fits_append (fits_mono (fits_Qw i) (by omega)) (by decide))
        (fits_mono (fits_sw0 s hs) (by omega)))
      (fits_append (K2_of_entOk hok).fits (fits_append (fits_mono (fits_Qw _) (by omega)) (by decide)))
    have e1 : Qw i ++ .C 0 :: (sigma y).map Lt.up ++ (sw0 s).word =
        Qw i ++ [.C 0] ++ ((sigma y).map Lt.up ++ (sw0 s).word) := by simp
    have e2 : Qw (snext (sw0 s) i) ++ .C 0 :: (sigma y).map Lt.up =
        Qw (snext (sw0 s) i) ++ [.C 0] ++ (sigma y).map Lt.up := by simp
    rw [e1, e2]
    refine ((E.refl _).append c1).trans ?_
    rw [← List.append_assoc]
    refine (c2.append (E.refl _)).trans ?_
    rw [List.append_assoc]

/-- `CZ` on wires `0, 1`. -/
theorem s2_C0 : Good2 (n + 1) [.C 0] := by
  intro i y hy
  obtain ⟨q, rest, rfl, hr⟩ := length_pos (n := n - 1) (by omega : y.length = n - 1 + 1)
  refine ⟨i + q.1, (q.1, q.2 + 1) :: rest, rfl, ?_⟩
  have h3 : 3 ≤ n + 1 := by omega
  cases hzq : isZ (q :: rest) with
  | true =>
    have hq : q = (0, 0) ∧ isZ rest = true := by
      simp only [isZ_cons, Bool.and_eq_true, beq_iff_eq] at hzq; exact hzq
    obtain ⟨rfl, hzr⟩ := hq
    refine ⟨[], K2.nil _, ?_⟩
    have h01 : isZ ((0, 0 + 1) :: rest) = false := by simp [isZ_cons]
    have hs : sigma ((0, 0 + 1) :: rest) = [] := by simp [sigma, hzr, alpha]
    simp only [tau, hzq, if_true, List.append_nil, h01, Bool.false_eq_true, if_false, hs,
      List.map_nil, add_zero, kw_nil, List.nil_append]
    exact E.refl _
  | false =>
    cases hzr : isZ rest with
    | true =>
      have hq := isZ_cons_false hzq hzr
      have hok := ok_S2f i q hq
      refine ⟨(eS2f i q).2, (K2_of_entOk hok).mono (by omega), ?_⟩
      have e1 : tau ((1, i) :: q :: rest) ++ [.C 0] = Qw i ++ [.C 0] ++ (alpha q).map Lt.up ++ [.C 0] := by
        simp [tau, hzq, sigma, hzr]
      have e2 : tau ((1, i + q.1) :: (q.1, q.2 + 1) :: rest) =
          if (q.1, q.2 + 1) = (0, 0) then Qw (i + q.1)
          else Qw (i + q.1) ++ [.C 0] ++ (alpha (q.1, q.2 + 1)).map Lt.up := by
        by_cases h0 : (q.1, q.2 + 1) = (0, 0)
        · rw [if_pos h0]
          have : isZ ((q.1, q.2 + 1) :: rest) = true := by simp only [isZ_cons, h0, hzr]; rfl
          simp only [tau, this, if_true, List.append_nil]
        · rw [if_neg h0]
          have : isZ ((q.1, q.2 + 1) :: rest) = false := by simp [isZ_cons, h0]
          simp [tau, this, sigma, hzr]
      rw [e1, e2]
      exact E.of3 h3 (of_entOk hc hok)
        (fits_append (fits_append (fits_append (fits_mono (fits_Qw i) (by omega)) (by decide))
          (fits_up_le (fits_alpha q) (by omega))) (by decide))
        (fits_append (K2_of_entOk hok).fits (by
          split
          · exact fits_mono (fits_Qw _) (by omega)
          · exact fits_append (fits_append (fits_mono (fits_Qw _) (by omega)) (by decide))
              (fits_up_le (fits_alpha _) (by omega))))
    | false =>
      have hok := ok_S2g i q
      refine ⟨(eS2g i q).2, (K2_of_entOk hok).mono (by omega), ?_⟩
      have hq' : isZ ((q.1, q.2 + 1) :: rest) = false := by simp [isZ_cons, hzr]
      have e1 : tau ((1, i) :: q :: rest) ++ [.C 0] =
          Qw i ++ [.C 0] ++ (Gam q).map Lt.up ++ (((sigma rest).map Lt.up).map Lt.up ++ [.C 0]) := by
        simp [tau, hzq, sigma, hzr]
      have e2 : tau ((1, i + q.1) :: (q.1, q.2 + 1) :: rest) =
          Qw (i + q.1) ++ [.C 0] ++ (Gam (q.1, q.2 + 1)).map Lt.up ++
            ((sigma rest).map Lt.up).map Lt.up := by
        simp [tau, hq', sigma, hzr]
      rw [e1, e2]
      have c1 : E (n + 1) (((sigma rest).map Lt.up).map Lt.up ++ [.C 0])
          ([.C 0] ++ ((sigma rest).map Lt.up).map Lt.up) :=
        E_comm _ _ (fun a ha b hb => (Bool.or_comm _ _).trans (disj_of_lt (by
          rw [List.mem_singleton.1 hb]; have := lo_of_mem_up_up ha; simp [Lt.hi]; omega)))
      have c2 := E.of3 h3 (of_entOk hc hok)
        (fits_append (fits_append (fits_append (fits_mono (fits_Qw i) (by omega)) (by decide))
          (fits_up_le (fits_Gam q) (by omega))) (by decide))
        (fits_append (K2_of_entOk hok).fits (fits_append (fits_append
          (fits_mono (fits_Qw _) (by omega)) (by decide)) (fits_up_le (fits_Gam _) (by omega))))
      refine ((E.refl _).append c1).trans ?_
      rw [← List.append_assoc]
      refine (c2.append (E.refl _)).trans ?_
      rw [List.append_assoc]

/-- A letter above wire `0`. -/
theorem s2_top (h1 : S1 n) (x : Lt) (hlo : 1 ≤ x.lo) (hx : x.hi < n + 1) : Good2 (n + 1) [x] := by
  intro i y hy
  refine ⟨i, ptAct x.down y, by simp only [ptRun_cons, ptRun_nil, ptAct_top x hlo], ?_⟩
  cases hzy : isZ y with
  | true =>
    refine ⟨[.top x], K2_top hlo hx, ?_⟩
    simp only [tau, hzy, isZ_ptAct, if_true, List.append_nil, kw, List.flatMap_cons,
      List.flatMap_nil, Tok.word]
    exact E_comm _ _ (fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; exact disj_of_lt (by rw [Qw_hi i a ha]; omega))
  | false =>
    obtain ⟨ts', hts', hE⟩ := h1 x.down (by cases x <;> simp_all [Lt.hi, Lt.lo, Lt.down] <;> omega)
      y (by omega) hzy
    obtain ⟨ts'', hts'', hE2⟩ := qc_pass hn hc i ts' hts'
    refine ⟨ts'', hts'', ?_⟩
    simp only [tau, hzy, isZ_ptAct, Bool.false_eq_true, if_false]
    have e1 : Qw i ++ .C 0 :: (sigma y).map Lt.up ++ [x] =
        Qw i ++ [.C 0] ++ (sigma y ++ [x.down]).map Lt.up := by
      simp [List.map_append, Lt.up_down x hlo]
    have e2 : Qw i ++ .C 0 :: (sigma (ptAct x.down y)).map Lt.up =
        Qw i ++ [.C 0] ++ (sigma (ptAct x.down y)).map Lt.up := by simp
    rw [e1, e2]
    refine ((E.refl _).append hE.up).trans ?_
    rw [List.map_append, ← List.append_assoc]
    refine (hE2.append (E.refl _)).trans ?_
    simp only [List.append_assoc]
    exact E.refl _

/-- Every token of the first stabiliser satisfies the condition. -/
theorem good2_tok (h1 : S1 n) (t : Tok) (ht : t.isK1 = true ∧ Fits (n + 1) t.word) :
    Good2 (n + 1) t.word := by
  cases t with
  | S0 => exact s2_bot hn hc 0 (by omega)
  | X0 => exact s2_bot hn hc 1 (by omega)
  | Z0 => exact s2_bot hn hc 2 (by omega)
  | C0 => exact s2_C0 hn hc
  | top x =>
    exact s2_top hn hc h1 x (by simpa [Tok.isK1] using ht.1) (ht.2 x (by simp [Tok.word]))

theorem good2_kw (h1 : S1 n) : ∀ ts : List Tok, K1 (n + 1) ts → Good2 (n + 1) (kw ts)
  | [], _ => Good2.nil _
  | t :: ts, h => by
    rw [kw_cons]
    exact (good2_tok hn hc h1 t (h t List.mem_cons_self)).append
      (good2_kw h1 ts (fun u hu => h u (List.mem_cons_of_mem _ hu)))

end Step

/-! ### Stage 1 for words -/

theorem good1_all {n : ℕ} (h1 : S1 n) : ∀ l : List Lt, Fits n l → Good1 n l
  | [], _ => Good1.nil _
  | x :: l, h => by
    have := (Good1.single (h1 x (h x List.mem_cons_self))).append
      (good1_all h1 l (fun y hy => h y (List.mem_cons_of_mem _ hy)))
    simpa using this

/-! ### The end -/

/-- A word of tokens of the second stabiliser is a word on wire `0` followed
by a word above it. -/
theorem split_K2 {N : ℕ} : ∀ ts : List Tok, K2 N ts →
    ∃ b u : List Lt, Fits 1 b ∧ (∀ x ∈ u, 1 ≤ x.lo) ∧ Fits N u ∧ E N (kw ts) (b ++ u)
  | [], _ => by
    refine ⟨[], [], ?_, ?_, ?_, ?_⟩
    · intro x hx; simp at hx
    · intro x hx; simp at hx
    · intro x hx; simp at hx
    · simpa [kw] using E.refl _
  | t :: ts, h => by
    obtain ⟨b, u, hb, hu, hfu, e⟩ := split_K2 ts (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have ht := h t List.mem_cons_self
    rw [kw_cons]
    have e1 : E N (t.word ++ kw ts) (t.word ++ (b ++ u)) := (E.refl _).append e
    cases t with
    | X0 =>
      refine ⟨X0w ++ b, u, fits_append (by decide) hb, hu, hfu, ?_⟩
      simpa [List.append_assoc] using e1
    | Z0 =>
      refine ⟨Z0w ++ b, u, fits_append (by decide) hb, hu, hfu, ?_⟩
      simpa [List.append_assoc] using e1
    | S0 => simp [Tok.isK2] at ht
    | C0 => simp [Tok.isK2] at ht
    | top x =>
      have hlo : 1 ≤ x.lo := by simpa [Tok.isK2] using ht.1
      have hx : x.hi < N := ht.2 x (by simp [Tok.word])
      refine ⟨b, x :: u, hb, fun y hy => ?_, fun y hy => ?_, ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        exacts [hlo, hu y hy]
      · rcases List.mem_cons.1 hy with rfl | hy
        exacts [hx, hfu y hy]
      · refine e1.trans ?_
        have c : E N ([x] ++ b) (b ++ [x]) := E_comm _ _ (fun a ha c hc => by
          rw [List.mem_singleton.1 ha]
          have := hb c hc
          exact (Bool.or_comm _ _).trans (disj_of_lt (by omega)))
        have := c.append (E.refl u)
        simpa [Tok.word, List.append_assoc] using this

theorem xat1' : PD.Xat (0 : Fin 1) = ⟨0, ![1], ![0]⟩ := by decide
theorem zat1' : PD.Zat (0 : Fin 1) = ⟨0, ![0], ![1]⟩ := by decide

/-- A word on wire `0` followed by a word above it, acting trivially, is
derivably trivial, given completeness on one and on `n` wires. -/
theorem k2_trivial {n : ℕ} (hc1 : Complete 1) (hcn : Complete n) {b u : List Lt} (hb : Fits 1 b)
    (hu : ∀ x ∈ u, 1 ≤ x.lo) (h : actC (n + 1) (cw (n + 1) (b ++ u)) = 1) : E (n + 1) (b ++ u) [] := by
  have hcb : cw (n + 1) b = bot (cw 1 b) := cw_pad n b hb
  have hcu : cw (n + 1) u = top (cw n (u.map Lt.down)) := cw_hi n u (by
    simp only [List.all_eq_true, hi1, decide_eq_true_eq]; exact hu)
  -- the wire-0 part
  have hb1 : ∀ a0 b0 : Fin 3, actC 1 (cw 1 b) ⟨0, ![a0], ![b0]⟩ = ⟨0, ![a0], ![b0]⟩ := by
    intro a0 b0
    have e := congrFun h ((PD.sc 0 : PD n).cons a0 b0)
    rw [cw_append, map_mul] at e
    change actC (n + 1) (cw (n + 1) u) (actC (n + 1) (cw (n + 1) b) ((PD.sc 0 : PD n).cons a0 b0)) =
      (PD.sc 0 : PD n).cons a0 b0 at e
    rw [hcb, actC_bot (cw 1 b) a0 b0 (PD.sc 0) rfl, PD.scale_cons, hcu, actC_top, actC_scale,
      actC_sc] at e
    obtain ⟨ha, hb', hs⟩ := PD.cons_inj e
    have hc0 := congrArg PD.c hs
    simp only [PD.scale, PD.sc, add_zero] at hc0
    apply PD.ext hc0
    · funext j; rw [Subsingleton.elim j 0]; exact ha
    · funext j; rw [Subsingleton.elim j 0]; exact hb'
  have eb : E 1 b [] := by
    refine pcomplete hc1 (actC_eq_of_gens (fun j => ?_) (fun j => ?_))
    · rw [Subsingleton.elim j 0, xat1', hb1]; rfl
    · rw [Subsingleton.elim j 0, zat1', hb1]; rfl
  have eb' : E (n + 1) b [] := E.pad n eb hb (fun _ h => nomatch h)
  -- the part above
  have hu1 : actC (n + 1) (cw (n + 1) u) = 1 := by
    have := actC_eq_of_E (eb'.append (E.refl u))
    rw [h] at this
    simpa using this.symm
  have hun : actC n (cw n (u.map Lt.down)) = actC n (cw n []) := by
    funext Q
    have e := congrFun hu1 (Q.cons 0 0)
    rw [hcu, actC_top] at e
    exact (PD.cons_inj e).2.2
  have eu : E n (u.map Lt.down) [] := pcomplete hcn hun
  have eu' : E (n + 1) u [] := by
    have := eu.up
    rwa [List.map_map, List.map_congr_left (l := u) (f := Lt.up ∘ Lt.down) (g := id)
      (fun x hx => Lt.up_down x (hu x hx)), List.map_id, List.map_nil] at this
  simpa using eb'.append eu'

/-- The point `Z₀` and the point `X₀` on `n + 1` wires. -/
def zpt (n : ℕ) : Pt := (0, 1) :: List.replicate n (0, 0)
def xpt (n : ℕ) : Pt := (1, 0) :: List.replicate n (0, 0)

theorem isZ_replicate (n : ℕ) : isZ (List.replicate n ((0, 0) : Fin 3 × Fin 3)) = true := by
  simp [isZ]

/-- **The end**: on `n + 1 ≥ 3` wires every word acting trivially is
derivably trivial up to a phase. -/
theorem words_trivial_succ {n : ℕ} (hn : 2 ≤ n) (hc1 : Complete 1) (hc2 : Complete 2)
    (hcn : Complete n) (h1 : S1 n) : WordsTrivial (n + 1) := by
  intro l hl htr
  have h1' := s1_succ hn hc2 h1
  -- stage 1
  obtain ⟨ts, hts, e1⟩ := good1_all h1' l hl (zpt n) (by simp [zpt]) (by simp [zpt, isZ_cons])
  rw [ptRun_triv htr hl (zpt n) (by simp [zpt])] at e1
  have hsz : sigma (zpt n) = [] := by simp [zpt, sigma, isZ_replicate, alpha]
  rw [hsz, List.nil_append, List.append_nil] at e1
  -- stage 2
  obtain ⟨i', y', hpt, ts2, hts2, e2⟩ := good2_kw hn hc2 h1 ts hts 0 (List.replicate n (0, 0))
    (by simp)
  have hx : ptRun (kw ts) (xpt n) = xpt n := by
    rw [← ptRun_eq_of_E e1 hl hts.fits (xpt n) (by simp [xpt])]
    exact ptRun_triv htr hl (xpt n) (by simp [xpt])
  simp only [xpt] at hx
  have hx' : (1, i') :: y' = ((1, 0) : Fin 3 × Fin 3) :: List.replicate n (0, 0) := by
    rw [← hpt]; exact hx
  rw [hx'] at e2
  have htz : tau ((1, 0) :: List.replicate n (0, 0)) = [] := by
    simp [tau, isZ_replicate, Qw]
  rw [htz, List.nil_append, List.append_nil] at e2
  -- the second stabiliser
  have e3 := e1.trans e2
  obtain ⟨b, u, hb, hu, hfu, e4⟩ := split_K2 ts2 hts2
  have htr' : actC (n + 1) (cw (n + 1) (b ++ u)) = 1 := by
    rw [← actC_eq_of_E (e3.trans e4)]; exact htr
  exact (e3.trans e4).trans (k2_trivial hc1 hcn hb hu htr')

/-- Completeness and the stage-1 condition on every width from two. -/
theorem complete_s1 : ∀ n, 2 ≤ n → Complete n ∧ S1 n
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => ⟨complete_two, s1_two⟩
  | n + 3, _ => by
    obtain ⟨hc, h1⟩ := complete_s1 (n + 2) (by omega)
    exact ⟨complete_of_words (words_trivial_succ (by omega) complete_one complete_two hc h1),
      s1_succ (by omega) complete_two h1⟩

/-- **Completeness at every width.** -/
theorem complete_all : ∀ n, Complete n
  | 0 => complete_zero
  | 1 => complete_one
  | n + 2 => (complete_s1 (n + 2) (by omega)).1

end QCert.QutritClifford
