/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Stage 1 of the stabiliser chain

Toward Theorem 4.4.  The Schreier condition of stage 1 on `n` wires
(`S1 n`): for every letter `x` and every point `y ≠ 1`,
`sigma y ⨾ x = k ⨾ sigma (x·y)` up to a phase, with `k` a word of tokens
of the stabiliser of `Z₀`.  On two wires it is decided from completeness
there (`s1_two`, with the K-words of `S12Data.lean`); on `n + 1 ≥ 3`
wires it follows from the condition on `n` wires and the local facts
(`s1_succ`):

* a letter above wire `0` acts on the section of the rest of the point,
  by the condition one wire down, and the K-word it leaves passes `Gam`
  (`gam_pass`, by (S1c), (S1d));
* `H` and `S` on wire `0` pass `alpha` or `Gam` ((S1a), (S1b));
* the swap `W0` of wires `0, 1` is treated as a whole ((S1e)-(S1g)), and
  `CZ` on wires `0, 1` is the word `W1 ⨾ W0 ⨾ CZ₁₂ ⨾ W0 ⨾ W1` (S1h).
-/
import QCert.QutritClifford.Facts
import QCert.QutritClifford.S12Data
import QCert.QutritClifford.Cert2

namespace QCert.QutritClifford

/-! ### Words on disjoint wires, and facts on three wires -/

/-- Words on disjoint wires commute. -/
theorem E_comm {k : ℕ} : ∀ (u v : List Lt), (∀ a ∈ u, ∀ b ∈ v, Lt.disj a b = true) →
    E k (u ++ v) (v ++ u)
  | u, [], _ => by rw [List.append_nil, List.nil_append]
  | u, x :: v, h => by
    have h1 : E k (u ++ [x]) (x :: u) := E.move_left x u (fun a ha => h a ha x List.mem_cons_self)
    have h2 := E_comm (k := k) u v (fun a ha b hb => h a ha b (List.mem_cons_of_mem _ hb))
    have e1 : E k (u ++ x :: v) (x :: u ++ v) := by
      have := h1.append (E.refl v)
      simpa [List.append_assoc] using this
    exact e1.trans ((E.refl [x]).append h2)

theorem disj_of_lt {a b : Lt} (h : a.hi < b.lo) : Lt.disj a b = true := by
  simp [Lt.disj, h]

theorem lo_of_mem_up {l : List Lt} {x : Lt} (h : x ∈ l.map Lt.up) : 1 ≤ x.lo := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
  simp

theorem lo_of_mem_up_up {l : List Lt} {x : Lt} (h : x ∈ (l.map Lt.up).map Lt.up) : 2 ≤ x.lo := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  have := lo_of_mem_up hy
  simp; omega

/-- A fact on three wires holds on the bottom three of `n ≥ 3` wires. -/
theorem E.of3 {n : ℕ} (hn : 3 ≤ n) {l r : List Lt} (h : E 3 l r) (hl : Fits 3 l) (hr : Fits 3 r) :
    E n l r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact E.pad m h hl hr

theorem fits_alpha : ∀ p : Fin 3 × Fin 3, Fits 1 (alpha p) := by decide
theorem fits_Gam : ∀ p : Fin 3 × Fin 3, Fits 2 (Gam p) := by decide
theorem fits_Qw : ∀ i : Fin 3, Fits 1 (Qw i) := by decide
theorem fits_W0 : Fits 2 W0 := by decide
theorem fits_W1 : Fits 3 W1 := by decide
theorem fits_cw1 : ∀ c < 3, Fits 2 (cw1 c) := by decide
theorem fits_sw0 : ∀ s < 3, Fits 1 (sw0 s).word := by decide
theorem fits_tw0 : ∀ t < 2, Fits 1 (tw0 t).word := by decide

theorem fits_up_le {k k' : ℕ} {l : List Lt} (h : Fits k l) (hk : k + 1 ≤ k') :
    Fits k' (l.map Lt.up) := fits_mono (fits_up h) hk

theorem fits_sigma : ∀ y : Pt, Fits y.length (sigma y)
  | [] => fun _ h => nomatch h
  | p :: y => by
    simp only [sigma]
    split
    · exact fits_mono (fits_alpha p) (by simp)
    · rename_i hz
      have hy : 1 ≤ y.length := by
        cases y with
        | nil => simp [isZ] at hz
        | cons _ _ => simp
      exact fits_append (fits_mono (fits_Gam p) (by simp; omega)) (fits_up (fits_sigma y))

theorem fits_tau : ∀ y : Pt, 1 ≤ y.length → Fits y.length (tau y)
  | [], h => by simp at h
  | p :: y, _ => by
    simp only [tau]
    split
    · simpa using fits_mono (fits_Qw p.2) (by simp)
    · rename_i hz
      have hy : 1 ≤ y.length := by
        cases y with
        | nil => simp [isZ] at hz
        | cons _ _ => simp
      refine fits_append (fits_mono (fits_Qw p.2) (by simp)) ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp [Lt.hi]; omega
      · exact fits_up (fits_sigma y) x hx

theorem alpha_hi : ∀ p : Fin 3 × Fin 3, ∀ x ∈ alpha p, x.hi = 0 := by decide
theorem Gam_hi : ∀ p : Fin 3 × Fin 3, ∀ x ∈ Gam p, x.hi ≤ 1 := by decide
theorem Qw_hi : ∀ i : Fin 3, ∀ x ∈ Qw i, x.hi = 0 := by decide
theorem W0_hi : ∀ x ∈ W0, x.hi ≤ 1 := by decide
theorem sw0_hi : ∀ s < 3, ∀ x ∈ (sw0 s).word, x.hi = 0 := by decide

theorem K1_top {n : ℕ} {x : Lt} (hlo : 1 ≤ x.lo) (hx : x.hi < n) : K1 n [.top x] := by
  intro t ht
  rw [List.mem_singleton.1 ht]
  exact ⟨by simpa [Tok.isK1] using hlo, fun y hy => by rw [List.mem_singleton.1 hy]; exact hx⟩

theorem K2_top {n : ℕ} {x : Lt} (hlo : 1 ≤ x.lo) (hx : x.hi < n) : K2 n [.top x] := by
  intro t ht
  rw [List.mem_singleton.1 ht]
  exact ⟨by simpa [Tok.isK2] using hlo, fun y hy => by rw [List.mem_singleton.1 hy]; exact hx⟩

theorem isZ_cons_false {p : Fin 3 × Fin 3} {y : Pt} (h : isZ (p :: y) = false) (hy : isZ y = true) :
    p ≠ (0, 0) := by
  intro hp; simp [isZ_cons, hp, hy] at h

theorem ptAct_top (x : Lt) (hlo : 1 ≤ x.lo) (p : Fin 3 × Fin 3) (y : Pt) :
    ptAct x (p :: y) = p :: ptAct x.down y := by
  conv_lhs => rw [← Lt.up_down x hlo]
  exact ptAct_up _ _ _

theorem length_pos {y : Pt} {n : ℕ} (h : y.length = n + 1) : ∃ p y', y = p :: y' ∧ y'.length = n := by
  cases y with
  | nil => simp at h
  | cons p y' => exact ⟨p, y', rfl, by simpa using h⟩

/-! ### The condition -/

/-- **The Schreier condition of stage 1** on `n` wires. -/
def S1 (n : ℕ) : Prop :=
  ∀ x : Lt, x.hi < n → ∀ y : Pt, y.length = n → isZ y = false →
    ∃ ts, K1 n ts ∧ E n (sigma y ++ [x]) (kw ts ++ sigma (ptAct x y))

/-- The condition for a word. -/
def Good1 (n : ℕ) (w : List Lt) : Prop :=
  ∀ y : Pt, y.length = n → isZ y = false →
    ∃ ts, K1 n ts ∧ E n (sigma y ++ w) (kw ts ++ sigma (ptRun w y))

theorem Good1.nil (n : ℕ) : Good1 n [] := fun _ _ _ => ⟨[], K1.nil n, by simpa using E.refl _⟩

theorem Good1.append {n : ℕ} {a b : List Lt} (ha : Good1 n a) (hb : Good1 n b) : Good1 n (a ++ b) := by
  intro y hy hz
  obtain ⟨t1, h1, e1⟩ := ha y hy hz
  obtain ⟨t2, h2, e2⟩ := hb (ptRun a y) (by rw [length_ptRun, hy]) (by rw [isZ_ptRun, hz])
  refine ⟨t1 ++ t2, h1.append h2, ?_⟩
  have h3 : E n (sigma y ++ a ++ b) (kw t1 ++ (sigma (ptRun a y) ++ b)) := by
    simpa [List.append_assoc] using e1.append (E.refl b)
  have h4 := h3.trans ((E.refl (kw t1)).append e2)
  simpa [List.append_assoc, ptRun_append, kw_append] using h4

theorem Good1.single {n : ℕ} {x : Lt} (h : ∀ y : Pt, y.length = n → isZ y = false →
    ∃ ts, K1 n ts ∧ E n (sigma y ++ [x]) (kw ts ++ sigma (ptAct x y))) : Good1 n [x] := h

/-! ### On two wires -/

/-- The letters on two wires, by index. -/
def let2 : ℕ → Lt
  | 0 => .H 0
  | 1 => .S 0
  | 2 => .H 1
  | 3 => .S 1
  | _ => .C 0

/-- The K-word of the condition on two wires. -/
def kS12 (i : ℕ) (p q : Fin 3 × Fin 3) : List Tok := k12.getD (81 * i + 9 * pidx p + pidx q) []

/-- The check of the condition on two wires. -/
def chk12 (i : ℕ) (p q : Fin 3 × Fin 3) : Bool :=
  let l := sigma [p, q] ++ [let2 i]
  let r := kw (kS12 i p q) ++ sigma (ptAct (let2 i) [p, q])
  K1b 2 (kS12 i p q) && l.all in2 && r.all in2 && same2 l r

theorem chk12_ok : ∀ i < 5, ∀ p q : Fin 3 × Fin 3, isZ [p, q] = false → chk12 i p q = true := by
  decide +kernel

theorem let2_of {x : Lt} (h : x.hi < 2) : ∃ i < 5, let2 i = x := by
  rcases x with j | j | j <;> simp only [Lt.hi] at h
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    exacts [⟨0, by omega, rfl⟩, ⟨2, by omega, rfl⟩]
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    exacts [⟨1, by omega, rfl⟩, ⟨3, by omega, rfl⟩]
  · obtain rfl : j = 0 := by omega
    exact ⟨4, by omega, rfl⟩

/-- **Stage 1 on two wires**, from completeness there. -/
theorem s1_two : S1 2 := by
  intro x hx y hy hz
  obtain ⟨i, hi, rfl⟩ := let2_of hx
  obtain ⟨p, q, rfl⟩ : ∃ p q, y = [p, q] := by
    match y, hy with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  have h := chk12_ok i hi p q hz
  simp only [chk12, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hk, hl⟩, hr⟩, hs⟩ := h
  exact ⟨kS12 i p q, K1_of_b hk, pcomplete complete_two (same2_sound hl hr hs)⟩

theorem ptRun_W0_pair : ∀ p q : Fin 3 × Fin 3, ptRun W0 [p, q] = [q, p] := by decide

theorem ptRun_W0 (p q : Fin 3 × Fin 3) (y : Pt) : ptRun W0 (p :: q :: y) = q :: p :: y := by
  obtain ⟨p', q', h1, h2⟩ := ptRun_w01 W0 (by decide) p q y
  rw [ptRun_W0_pair] at h1
  simp only [List.cons.injEq, and_true] at h1
  rw [h2, ← h1.1, ← h1.2]

/-! ### The step -/

section Step

variable {n : ℕ} (hn : 2 ≤ n) (hc : Complete 2)
include hn hc

/-- A K-word one wire up passes `Gam`. -/
theorem gam_pass (p : Fin 3 × Fin 3) : ∀ ts : List Tok, K1 n ts →
    ∃ ts', K1 (n + 1) ts' ∧ E (n + 1) (Gam p ++ (kw ts).map Lt.up) (kw ts' ++ Gam p)
  | [], _ => ⟨[], K1.nil _, by simpa [kw] using E.refl _⟩
  | t :: ts, h => by
    obtain ⟨ts1, h1, e1⟩ := gam_pass p ts (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have ht := h t List.mem_cons_self
    have h3 : 3 ≤ n + 1 := by omega
    obtain ⟨k, hk, ek⟩ : ∃ k, K1 (n + 1) k ∧
        E (n + 1) (Gam p ++ t.word.map Lt.up) (kw k ++ Gam p) := by
      have one : ∀ c < 3, t.word.map Lt.up = cw1 c →
          ∃ k, K1 (n + 1) k ∧ E (n + 1) (Gam p ++ t.word.map Lt.up) (kw k ++ Gam p) := by
        intro c hc3 hw
        have hok := ok_S1c p c hc3
        refine ⟨(eS1c p c).2, (K1_of_entOk hok).mono (by omega), ?_⟩
        rw [hw]
        exact E.of3 h3 (of_entOk hc hok)
          (fits_append (fits_mono (fits_Gam p) (by omega)) (fits_mono (fits_cw1 c hc3) (by omega)))
          (fits_append (K1_of_entOk hok).fits (fits_mono (fits_Gam p) (by omega)))
      cases t with
      | S0 => exact one 0 (by omega) rfl
      | X0 => exact one 1 (by omega) rfl
      | Z0 => exact one 2 (by omega) rfl
      | C0 =>
        have hok := ok_S1d p
        refine ⟨(eS1d p).2, (K1_of_entOk hok).mono (by omega), ?_⟩
        exact E.of3 h3 (of_entOk hc hok)
          (fits_append (fits_mono (fits_Gam p) (by omega)) (by decide))
          (fits_append (K1_of_entOk hok).fits (fits_mono (fits_Gam p) (by omega)))
      | top x =>
        have hlo : 1 ≤ x.lo := by simpa [Tok.isK1] using ht.1
        have hx : x.hi < n := ht.2 x (by simp [Tok.word])
        refine ⟨[.top x.up], K1_top (by simp only [Lt.lo_up]; omega) (by simp only [Lt.hi_up]; omega), ?_⟩
        exact E_comm _ _ (fun a ha b hb => by
          have := Gam_hi p a ha
          simp only [Tok.word, List.map_cons, List.map_nil, List.mem_singleton] at hb
          subst hb; exact disj_of_lt (by simp; omega))
    refine ⟨k ++ ts1, hk.append h1, ?_⟩
    rw [kw_cons, List.map_append, ← List.append_assoc]
    refine (ek.append (E.refl _)).trans ?_
    rw [List.append_assoc, kw_append, List.append_assoc]
    exact (E.refl _).append e1

/-- A letter above wire `0`. -/
theorem s1_top (h1 : S1 n) (x : Lt) (hlo : 1 ≤ x.lo) (hx : x.hi < n + 1) : Good1 (n + 1) [x] := by
  intro y hy hz
  obtain ⟨p, y', rfl, hy'⟩ := length_pos hy
  simp only [ptRun_cons, ptRun_nil, ptAct_top x hlo]
  cases hzy : isZ y' with
  | true =>
    refine ⟨[.top x], K1_top hlo hx, ?_⟩
    simp only [sigma, hzy, isZ_ptAct, if_true, kw, List.flatMap_cons, List.flatMap_nil,
      Tok.word, List.append_nil]
    exact E_comm _ _ (fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; exact disj_of_lt (by rw [alpha_hi p a ha]; omega))
  | false =>
    obtain ⟨ts', hts', hE⟩ := h1 x.down (by cases x <;> simp_all [Lt.hi, Lt.lo, Lt.down] <;> omega)
      y' hy' hzy
    obtain ⟨ts'', hts'', hE2⟩ := gam_pass hn hc p ts' hts'
    refine ⟨ts'', hts'', ?_⟩
    simp only [sigma, hzy, isZ_ptAct, Bool.false_eq_true, if_false]
    have e1 : Gam p ++ (sigma y').map Lt.up ++ [x] = Gam p ++ (sigma y' ++ [x.down]).map Lt.up := by
      simp [List.map_append, Lt.up_down x hlo]
    rw [e1]
    refine ((E.refl (Gam p)).append hE.up).trans ?_
    rw [List.map_append, ← List.append_assoc]
    refine (hE2.append (E.refl _)).trans ?_
    rw [List.append_assoc]

/-- `H` and `S` on wire `0`. -/
theorem s1_bot (g : ℕ) (hg : g < 2) : Good1 (n + 1) [xw0 g] := by
  intro y hy hz
  obtain ⟨p, y', rfl, hy'⟩ := length_pos hy
  have hact : ptAct (xw0 g) (p :: y') = pt1 (xw0 g) p :: y' := by
    rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl <;> rfl
  simp only [ptRun_cons, ptRun_nil, hact]
  have h3 : 3 ≤ n + 1 := by omega
  have hxw : ∀ g < 2, Fits 1 [xw0 g] := by decide
  have hxhi : ∀ g < 2, (xw0 g).hi = 0 := by decide
  cases hzy : isZ y' with
  | true =>
    have hp := isZ_cons_false hz hzy
    have hok := ok_S1a p hp g hg
    refine ⟨(eS1a p g).2, (K1_of_entOk hok).mono (by omega), ?_⟩
    simp only [sigma, hzy, if_true]
    exact E.of3 h3 (of_entOk hc hok)
      (fits_append (fits_mono (fits_alpha p) (by omega)) (fits_mono (hxw g hg) (by omega)))
      (fits_append (K1_of_entOk hok).fits (fits_mono (fits_alpha _) (by omega)))
  | false =>
    have hok := ok_S1b p g hg
    refine ⟨(eS1b p g).2, (K1_of_entOk hok).mono (by omega), ?_⟩
    simp only [sigma, hzy, Bool.false_eq_true, if_false]
    have c1 : E (n + 1) ((sigma y').map Lt.up ++ [xw0 g]) ([xw0 g] ++ (sigma y').map Lt.up) :=
      E_comm _ _ (fun a ha b hb => by
        rw [List.mem_singleton.1 hb]
        exact (Bool.or_comm _ _).trans (disj_of_lt (by rw [hxhi g hg]; exact lo_of_mem_up ha)))
    have c2 := E.of3 h3 (of_entOk hc hok)
      (fits_append (fits_mono (fits_Gam p) (by omega)) (fits_mono (hxw g hg) (by omega)))
      (fits_append (K1_of_entOk hok).fits (fits_mono (fits_Gam _) (by omega)))
    rw [List.append_assoc]
    refine ((E.refl (Gam p)).append c1).trans ?_
    rw [← List.append_assoc]
    refine (c2.append (E.refl _)).trans ?_
    rw [List.append_assoc]

/-- The swap of wires `0, 1`. -/
theorem s1_W0 : Good1 (n + 1) W0 := by
  intro y hy hz
  obtain ⟨p, y', rfl, hy'⟩ := length_pos hy
  obtain ⟨q, rest, rfl, hr⟩ := length_pos (n := n - 1) (by rw [hy']; omega)
  rw [ptRun_W0]
  have h3 : 3 ≤ n + 1 := by omega
  cases hzq : isZ (q :: rest) with
  | true =>
    have hp := isZ_cons_false hz hzq
    have hq : q = (0, 0) ∧ isZ rest = true := by
      simp only [isZ_cons, Bool.and_eq_true, beq_iff_eq] at hzq; exact hzq
    have hok := ok_S1e p hp
    refine ⟨(eS1e p).2, (K1_of_entOk hok).mono (by omega), ?_⟩
    have hpr : isZ (p :: rest) = false := by simp [isZ_cons, hp]
    have e1 : sigma (p :: q :: rest) = alpha p := by simp only [sigma, hzq, if_true]
    have e2 : sigma (q :: p :: rest) = W0 ++ (alpha p).map Lt.up := by
      rw [hq.1]
      simp only [sigma, hpr, Bool.false_eq_true, if_false, hq.2, Gam, if_pos]
    rw [e1, e2]
    exact E.of3 h3 (of_entOk hc hok)
      (fits_append (fits_mono (fits_alpha p) (by omega)) (fits_mono fits_W0 (by omega)))
      (fits_append (K1_of_entOk hok).fits (fits_append (fits_mono fits_W0 (by omega))
        (fits_up_le (fits_alpha p) (by omega))))
  | false =>
    cases hzr : isZ rest with
    | true =>
      have hq := isZ_cons_false hzq hzr
      have hok := ok_S1f p q hq
      refine ⟨(eS1f p q).2, (K1_of_entOk hok).mono (by omega), ?_⟩
      have e1 : sigma (p :: q :: rest) = Gam p ++ (alpha q).map Lt.up := by
        simp only [sigma, hzq, hzr, Bool.false_eq_true, if_false, if_true]
      have e2 : sigma (q :: p :: rest) = if p = (0, 0) then alpha q else Gam q ++ (alpha p).map Lt.up := by
        by_cases hp0 : p = (0, 0)
        · have : isZ (p :: rest) = true := by simp [isZ_cons, hp0, hzr]
          rw [if_pos hp0]
          simp only [sigma, this, if_true]
        · have : isZ (p :: rest) = false := by simp [isZ_cons, hp0]
          rw [if_neg hp0]
          simp only [sigma, this, Bool.false_eq_true, if_false, hzr, if_true]
      rw [e1, e2]
      exact E.of3 h3 (of_entOk hc hok)
        (fits_append (fits_append (fits_mono (fits_Gam p) (by omega))
          (fits_up_le (fits_alpha q) (by omega))) (fits_mono fits_W0 (by omega)))
        (fits_append (K1_of_entOk hok).fits (by
          split
          · exact fits_mono (fits_alpha q) (by omega)
          · exact fits_append (fits_mono (fits_Gam q) (by omega)) (fits_up_le (fits_alpha p) (by omega))))
    | false =>
      have hok := ok_S1g p q
      refine ⟨(eS1g p q).2, (K1_of_entOk hok).mono (by omega), ?_⟩
      have hpr : isZ (p :: rest) = false := by simp [isZ_cons, hzr]
      have e1 : sigma (p :: q :: rest) =
          Gam p ++ (Gam q).map Lt.up ++ ((sigma rest).map Lt.up).map Lt.up := by
        simp only [sigma, hzq, hzr, Bool.false_eq_true, if_false, List.map_append, List.append_assoc]
      have e2 : sigma (q :: p :: rest) =
          Gam q ++ (Gam p).map Lt.up ++ ((sigma rest).map Lt.up).map Lt.up := by
        simp only [sigma, hpr, hzr, Bool.false_eq_true, if_false, List.map_append, List.append_assoc]
      rw [e1, e2]
      have c1 : E (n + 1) (((sigma rest).map Lt.up).map Lt.up ++ W0)
          (W0 ++ ((sigma rest).map Lt.up).map Lt.up) :=
        E_comm _ _ (fun a ha b hb => (Bool.or_comm _ _).trans
          (disj_of_lt (by have := W0_hi b hb; have := lo_of_mem_up_up ha; omega)))
      have c2 := E.of3 h3 (of_entOk hc hok)
        (fits_append (fits_append (fits_mono (fits_Gam p) (by omega))
          (fits_up_le (fits_Gam q) (by omega))) (fits_mono fits_W0 (by omega)))
        (fits_append (K1_of_entOk hok).fits (fits_append (fits_mono (fits_Gam q) (by omega))
          (fits_up_le (fits_Gam p) (by omega))))
      rw [List.append_assoc]
      refine ((E.refl (Gam p ++ (Gam q).map Lt.up)).append c1).trans ?_
      rw [← List.append_assoc]
      refine (c2.append (E.refl _)).trans ?_
      simp only [List.append_assoc]
      exact E.refl _

/-- A word of letters above wire `0`. -/
theorem s1_tops (h1 : S1 n) : ∀ w : List Lt, (∀ x ∈ w, 1 ≤ x.lo ∧ x.hi < n + 1) → Good1 (n + 1) w
  | [], _ => Good1.nil _
  | x :: w, h => by
    have := (s1_top hn hc h1 x (h x List.mem_cons_self).1 (h x List.mem_cons_self).2).append
      (s1_tops h1 w (fun y hy => h y (List.mem_cons_of_mem _ hy)))
    simpa using this

/-- `CZ` on wires `0, 1`, through (S1h). -/
theorem s1_C0 (h1 : S1 n) : Good1 (n + 1) [.C 0] := by
  have h3 : 3 ≤ n + 1 := by omega
  have hok := ok_S1h
  have hfr : Fits 3 (W1 ++ W0 ++ [.C 1] ++ W0 ++ W1) := by decide
  have eh : E (n + 1) [.C 0] (W1 ++ W0 ++ [.C 1] ++ W0 ++ W1) := by
    have := E.of3 h3 (of_entOk hc hok) (by decide) (fits_append (K1_of_entOk hok).fits hfr)
    have hk : kw (ent fS1h 0).2 = [] := by decide
    rwa [hk, List.nil_append] at this
  have hW1 : ∀ x ∈ W1, 1 ≤ x.lo ∧ x.hi < n + 1 := by
    intro x hx
    have : 1 ≤ x.lo ∧ x.hi < 3 := by revert x; decide
    omega
  have hg : Good1 (n + 1) (W1 ++ W0 ++ [.C 1] ++ W0 ++ W1) :=
    ((((s1_tops hn hc h1 W1 hW1).append (s1_W0 hn hc)).append
      (s1_top hn hc h1 (.C 1) (by decide) (by simp [Lt.hi]; omega))).append (s1_W0 hn hc)).append
      (s1_tops hn hc h1 W1 hW1)
  intro y hy hz
  obtain ⟨ts, hts, e⟩ := hg y hy hz
  refine ⟨ts, hts, ?_⟩
  rw [ptRun_eq_of_E eh (fits_mono (by decide : Fits 2 [.C 0]) (by omega)) (fits_mono hfr h3) y hy]
  exact ((E.refl (sigma y)).append eh).trans e

/-- **The step of stage 1**: the condition on `n + 1 ≥ 3` wires, from the
condition on `n` wires and completeness on two. -/
theorem s1_succ (h1 : S1 n) : S1 (n + 1) := by
  intro x hx y hy hz
  by_cases hlo : 1 ≤ x.lo
  · obtain ⟨ts, h, e⟩ := s1_top hn hc h1 x hlo hx y hy hz
    exact ⟨ts, h, by simpa using e⟩
  · rcases x with j | j | j <;> simp only [Lt.lo] at hlo
    · obtain rfl : j = 0 := by omega
      obtain ⟨ts, h, e⟩ := s1_bot hn hc 0 (by omega) y hy hz
      exact ⟨ts, h, by simpa using e⟩
    · obtain rfl : j = 0 := by omega
      obtain ⟨ts, h, e⟩ := s1_bot hn hc 1 (by omega) y hy hz
      exact ⟨ts, h, by simpa using e⟩
    · obtain rfl : j = 0 := by omega
      obtain ⟨ts, h, e⟩ := s1_C0 hn hc h1 y hy hz
      exact ⟨ts, h, by simpa using e⟩

end Step

end QCert.QutritClifford
