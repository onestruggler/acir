/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of placed and multi-controlled gates at every width

The operators of the circuits of `MC` on `N` wires, `N` arbitrary, entry by
entry over ℚ(√2) (`opsQ.eval`; `sem_of_eval` carries an identity to the real
semantics).  States are read wire by wire through `bit` (`0` beyond the
width), and an operator acting on the wires `ws` of `N` wires (its wire `i`
on `ws[i]`), the others unchanged, is `onW N ws G`.

* `eval_place1`, `eval_place2`, `eval_atBot`: single gates and circuits at
  the bottom are `onW`.
* A swap is the permutation of states exchanging two wires (`eval_swAt`), so
  conjugating by a swap network permutes the wires of the inner operator
  (`eval_conjNet`), and `placeG N g ps` is `g` on the wires `ps`
  (`eval_placeG`).  The combinatorial content is that the network `netL N ps`
  brings `ps[i]` to wire `i` (`sig_netPos`).
* The canonical gates of Definition 2.4 (`box k`, `zx k`, `xz k`, `mch k`)
  apply their one-control gate when all their controls are `1`
  (`eval_canon`), by induction on the number of controls as in
  `Soundness.eval_box`.
* `X` on both sides of a gate exchanges the colour of a control
  (`eval_colourW`), and the multi-controlled gate `mc N K tg c` is `Λ_c(U)`:
  `U` on the wires `tg` when the controls match `c`, the identity otherwise
  (`eval_mc`); with all the controls above wire `k` it is block diagonal in
  the top wires (`eval_mc_blk`), which reduces identities at every width to
  identities on `k` wires.
-/
import QCert.RealCliffordCH.Sec8.MC
import QCert.RealCliffordCH.Sim
import QCert.RealCliffordCH.EvalLemmas

namespace QCert.RealCliffordCH.Sec8.MS

open Matrix Circuit Sim

/-! ## Bits of states and operators on given wires -/

/-- The value of wire `j` of a state, `0` beyond the width. -/
def bit {N : ℕ} (s : State 2 N) (j : ℕ) : Fin 2 := if h : j < N then s ⟨j, h⟩ else 0

theorem bit_lt {N : ℕ} (s : State 2 N) {j : ℕ} (h : j < N) : bit s j = s ⟨j, h⟩ := dif_pos h

theorem bit_ge {N : ℕ} (s : State 2 N) {j : ℕ} (h : N ≤ j) : bit s j = 0 := dif_neg (by omega)

@[simp] theorem bit_fin {N : ℕ} (s : State 2 N) (j : Fin N) : bit s j = s j := dif_pos j.isLt

theorem state_ext {N : ℕ} {s t : State 2 N} (h : ∀ j < N, bit s j = bit t j) : s = t := by
  funext j; have := h j j.isLt; rwa [bit_fin, bit_fin] at this

/-- The wires `ws` of a state, as a state of `a` wires. -/
def rd {N a : ℕ} (ws : List ℕ) (s : State 2 N) : State 2 a := fun i => bit s (ws.getD i 0)

/-- `G` on the wires `ws` of `N` wires (its wire `i` on `ws[i]`), the other
wires unchanged. -/
def onW (N : ℕ) (ws : List ℕ) {a : ℕ} (G : Op Q 2 a) : Op Q 2 N := fun s t =>
  if ∀ j < N, j ∉ ws → bit s j = bit t j then G (rd ws s) (rd ws t) else 0

/-- The state of the top `n` of `n + 1` wires. -/
def tl {n : ℕ} (s : State 2 (n + 1)) : State 2 n := fun j => bit s (j + 1)

theorem bit_tl {n : ℕ} (s : State 2 (n + 1)) (j : ℕ) : bit (tl s) j = bit s (j + 1) := by
  by_cases h : j < n
  · rw [bit_lt _ h]; rfl
  · rw [bit_ge _ (by omega), bit_ge _ (by omega)]

/-- The entries of a circuit moved up one wire. -/
theorem eval_shift_apply {n : ℕ} (w : Circ n) (s t : State 2 (n + 1)) :
    opsQ.eval (n + 1) (shift w) s t =
      if bit s 0 = bit t 0 then opsQ.eval n w (tl s) (tl t) else 0 := by
  rw [eval_shift, onTop_apply]
  have e1 : ∀ u : State 2 (n + 1), (split 2 n 1 u).2 = tl u := by
    intro u; funext j; simp only [split, Equiv.coe_fn_mk, tl]
    rw [bit_lt _ (by omega)]; congr 1; ext; simp; omega
  have e2 : (split 2 n 1 s).1 = (split 2 n 1 t).1 ↔ bit s 0 = bit t 0 := by
    rw [bit_lt _ (by omega), bit_lt _ (by omega)]
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; fin_cases i; exact h
  rw [e1, e1]
  by_cases h : bit s 0 = bit t 0
  · rw [if_pos (e2.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e2.1 h')), if_neg h]

/-- `onW` moved up one wire. -/
theorem onTop_onW {n : ℕ} (ws : List ℕ) {a : ℕ} (ha : ws.length = a) (G : Op Q 2 a)
    (s t : State 2 (n + 1)) :
    (if bit s 0 = bit t 0 then onW n ws G (tl s) (tl t) else 0) =
      onW (n + 1) (ws.map (· + 1)) G s t := by
  have hrd : ∀ u : State 2 (n + 1), (rd ws (tl u) : State 2 a) = rd (ws.map (· + 1)) u := by
    intro u; funext i
    have hi : (i : ℕ) < ws.length := by omega
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some, bit_tl]
  simp only [onW, hrd]
  by_cases h0 : bit s 0 = bit t 0
  · rw [if_pos h0]
    congr 1
    apply propext
    constructor
    · intro H j hj hjw
      rcases j with _ | j
      · exact h0
      · rw [← bit_tl, ← bit_tl]
        exact H j (by omega) (fun hm => hjw (List.mem_map.2 ⟨j, hm, rfl⟩))
    · intro H j hj hjw
      rw [bit_tl, bit_tl]
      exact H (j + 1) (by omega) (fun hm => by
        obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
        exact hjw (by rw [show j = i by omega]; exact hi))
  · rw [if_neg h0, if_neg]
    intro H; exact h0 (H 0 (by omega) (by simp))

/-- The entries of a circuit with idle wires on top. -/
theorem eval_pad_apply (m : ℕ) {k : ℕ} (w : Circ k) (s t : State 2 (m + k)) :
    opsQ.eval (m + k) (Circuit.pad m w) s t =
      if ∀ j < m + k, k ≤ j → bit s j = bit t j then opsQ.eval k w (rd (List.range k) s)
        (rd (List.range k) t) else 0 := by
  rw [eval_pad, onBottom_apply']
  have hrd : ∀ u : State 2 (m + k), (fun i : Fin k => u ⟨i, by omega⟩) = rd (List.range k) u := by
    intro u; funext i
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_range i.isLt, Option.getD_some]
    rw [bit_lt _ (by omega)]
  rw [hrd, hrd]
  congr 1
  apply propext
  constructor
  · intro H j hj hk; rw [bit_lt _ hj, bit_lt _ hj]; exact H j hj hk
  · intro H j hj hk; have := H j hj hk; rwa [bit_lt _ hj, bit_lt _ hj] at this

theorem onW_range_pad (m k : ℕ) {a : ℕ} (G : Op Q 2 a) (s t : State 2 (m + k)) :
    (if ∀ j < m + k, k ≤ j → bit s j = bit t j then G (rd (List.range k) s)
        (rd (List.range k) t) else 0) = onW (m + k) (List.range k) G s t := by
  simp only [onW, List.mem_range, not_lt]

/-! ## Single gates on given wires -/

theorem eval_place1 : ∀ (N j : ℕ) (w : Circ 1), j < N →
    opsQ.eval N (place1 N j w) = onW N [j] (opsQ.eval 1 w)
  | k + 1, 0, w, _ => by
    funext s t
    show opsQ.eval (k + 1) (Circuit.pad k w) s t = _
    rw [eval_pad_apply, onW_range_pad]
    rfl
  | N + 1, j + 1, w, h => by
    funext s t
    show opsQ.eval (N + 1) (shift (place1 N j w)) s t = _
    rw [eval_shift_apply, eval_place1 N j w (by omega), onTop_onW [j] rfl]
    rfl
  | 0, _, _, h => absurd h (by omega)

theorem eval_place2 : ∀ (N j : ℕ) (w : Circ 2), j + 2 ≤ N →
    opsQ.eval N (place2 N j w) = onW N [j, j + 1] (opsQ.eval 2 w)
  | k + 2, 0, w, _ => by
    funext s t
    show opsQ.eval (k + 2) (Circuit.pad k w) s t = _
    rw [eval_pad_apply, onW_range_pad]
    rfl
  | N + 1, j + 1, w, h => by
    funext s t
    show opsQ.eval (N + 1) (shift (place2 N j w)) s t = _
    rw [eval_shift_apply, eval_place2 N j w (by omega), onTop_onW [j, j + 1] rfl]
    rfl
  | 0, _, _, h => absurd h (by omega)
  | 1, 0, _, h => absurd h (by omega)

/-! ## Swaps and permutations of states -/

/-- The transposition of `a` and `a + 1`. -/
def tau (a x : ℕ) : ℕ := if x = a then a + 1 else if x = a + 1 then a else x

theorem tau_tau (a x : ℕ) : tau a (tau a x) = x := by
  unfold tau; split_ifs <;> omega

theorem tau_lt {N a x : ℕ} (ha : a + 2 ≤ N) (hx : x < N) : tau a x < N := by
  unfold tau; split_ifs <;> omega

theorem tau_inj (a : ℕ) {x y : ℕ} (h : tau a x = tau a y) : x = y := by
  rw [← tau_tau a x, h, tau_tau]

/-- A state with its wires permuted: wire `i` gets the value of wire `σ i`. -/
def permSt {N : ℕ} (σ : ℕ → ℕ) (t : State 2 N) : State 2 N := fun i => bit t (σ i)

theorem bit_permSt {N : ℕ} (σ : ℕ → ℕ) (t : State 2 N) {j : ℕ} (hj : j < N) :
    bit (permSt σ t) j = bit t (σ j) := by
  rw [bit_lt _ hj]; rfl

/-- The operator of a map of basis states. -/
def pOp {N : ℕ} (φ : State 2 N → State 2 N) : Op Q 2 N := fun s t => if s = φ t then 1 else 0

/-- Conjugation by the operator of an involution of the basis states. -/
theorem pOp_conj {N : ℕ} (φ ψ : State 2 N → State 2 N) (hφ : ∀ u, φ (φ u) = u) (A : Op Q 2 N)
    (s t : State 2 N) : (pOp φ * A * pOp ψ) s t = A (φ s) (ψ t) := by
  rw [mul_apply, Finset.sum_eq_single (ψ t)]
  · rw [mul_apply, Finset.sum_eq_single (φ s)]
    · simp [pOp, hφ]
    · intro v _ hv
      have : ¬ s = φ v := fun e => hv (by rw [e, hφ])
      simp [pOp, this]
    · simp
  · intro u _ hu; simp [pOp, hu]
  · simp

theorem pOp_mul {N : ℕ} (φ ψ : State 2 N → State 2 N) (hφ : ∀ u, φ (φ u) = u) :
    pOp φ * pOp ψ = pOp (φ ∘ ψ) := by
  funext s t
  have := pOp_conj φ ψ hφ 1 s t
  rw [mul_one] at this
  rw [this]
  simp only [pOp, one_apply, Function.comp_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [← h, hφ]
  · intro h; rw [h, hφ]

/-- The swap of Equation (8) exchanges the two wires. -/
theorem eval_swap : opsQ.eval 2 (swap : Circ 2) =
    fun u v => if u 0 = v 1 ∧ u 1 = v 0 then (1 : Q) else 0 :=
  eval_eq_of_checkM (by decide +kernel)

theorem rd_two {N : ℕ} (j : ℕ) (u : State 2 N) :
    (rd [j, j + 1] u : State 2 2) 0 = bit u j ∧ (rd [j, j + 1] u : State 2 2) 1 = bit u (j + 1) :=
  ⟨rfl, rfl⟩

theorem eval_swAt {N a : ℕ} (ha : a + 2 ≤ N) :
    opsQ.eval N (swAt N a) = pOp (permSt (tau a)) := by
  funext s t
  rw [swAt, eval_place2 N a _ ha, eval_swap]
  simp only [onW, pOp]
  have key : s = permSt (tau a) t ↔
      ((∀ j < N, j ∉ [a, a + 1] → bit s j = bit t j) ∧
        bit s a = bit t (a + 1) ∧ bit s (a + 1) = bit t a) := by
    constructor
    · rintro rfl
      refine ⟨fun j hj hm => ?_, ?_, ?_⟩
      · rw [bit_permSt _ _ hj]; congr 1; unfold tau
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        rw [if_neg hm.1, if_neg hm.2]
      · rw [bit_permSt _ _ (by omega)]; unfold tau; rw [if_pos rfl]
      · rw [bit_permSt _ _ (by omega)]; unfold tau; rw [if_neg (by omega), if_pos rfl]
    · rintro ⟨h1, h2, h3⟩
      apply state_ext
      intro j hj
      rw [bit_permSt _ _ hj]
      unfold tau
      split_ifs with e1 e2
      · rw [e1]; exact h2
      · rw [e2]; exact h3
      · exact h1 j hj (by simp; omega)
  by_cases h1 : ∀ j < N, j ∉ [a, a + 1] → bit s j = bit t j
  · rw [if_pos h1]
    by_cases h2 : bit s a = bit t (a + 1) ∧ bit s (a + 1) = bit t a
    · rw [if_pos (key.2 ⟨h1, h2⟩)]
      rw [if_pos]; exact h2
    · rw [if_neg (fun e => h2 (key.1 e).2)]
      rw [if_neg]; exact h2
  · rw [if_neg h1, if_neg (fun e => h1 (key.1 e).1)]

theorem permSt_tau_tau {N a : ℕ} (ha : a + 2 ≤ N) (u : State 2 N) :
    permSt (tau a) (permSt (tau a) u) = u := by
  apply state_ext; intro j hj
  rw [bit_permSt _ _ hj, bit_permSt _ _ (tau_lt ha hj), tau_tau]

/-! ## Swap networks -/

/-- The map of wires of a list of swap positions, in drawn order: wire `i`
after the network carries what wire `sig l i` carried before. -/
def sig : List ℕ → ℕ → ℕ
  | [], x => x
  | a :: l, x => tau a (sig l x)

theorem sig_append (l₁ l₂ : List ℕ) (x : ℕ) : sig (l₁ ++ l₂) x = sig l₁ (sig l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, sig, ih]

theorem sig_lt {N : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a + 2 ≤ N) → ∀ {x : ℕ}, x < N → sig l x < N
  | [], _, _, hx => hx
  | a :: l, hl, _, hx => tau_lt (hl a (by simp)) (sig_lt (fun b hb => hl b (by simp [hb])) hx)

theorem sig_inj : ∀ (l : List ℕ) {x y : ℕ}, sig l x = sig l y → x = y
  | [], _, _, h => h
  | a :: l, _, _, h => sig_inj l (tau_inj a h)

theorem drawn_conj {N : ℕ} (x : Circ N) (m : List (Circ N)) :
    drawn (x :: m ++ [x]) = x * drawn m * x := by
  simp [drawn, List.prod_append, mul_assoc]

/-- Conjugating by a swap network permutes the wires of the operator inside. -/
theorem eval_conjNet {N : ℕ} : ∀ (l : List ℕ), (∀ a ∈ l, a + 2 ≤ N) → ∀ (w : Circ N)
    (s t : State 2 N),
    opsQ.eval N (drawn (l.map (swAt N) ++ [w] ++ (l.map (swAt N)).reverse)) s t =
      opsQ.eval N w (permSt (sig l) s) (permSt (sig l) t)
  | [], _, w, s, t => by
    simp only [List.map_nil, List.nil_append, List.reverse_nil, List.append_nil]
    have : drawn [w] = w := by simp [drawn]
    have hid : ∀ u : State 2 N, permSt (sig []) u = u := by
      intro u; apply state_ext; intro j hj; rw [bit_permSt _ _ hj]; rfl
    rw [this, hid, hid]
  | a :: l, hl, w, s, t => by
    have ha : a + 2 ≤ N := hl a (by simp)
    have hl' : ∀ b ∈ l, b + 2 ≤ N := fun b hb => hl b (by simp [hb])
    have e : (a :: l).map (swAt N) ++ [w] ++ ((a :: l).map (swAt N)).reverse =
        swAt N a :: (l.map (swAt N) ++ [w] ++ (l.map (swAt N)).reverse) ++ [swAt N a] := by
      simp
    rw [e, drawn_conj, map_mul, map_mul, eval_swAt ha,
      pOp_conj _ _ (permSt_tau_tau ha), eval_conjNet l hl' w]
    have hc : ∀ u : State 2 N, permSt (sig l) (permSt (tau a) u) = permSt (sig (a :: l)) u := by
      intro u; apply state_ext; intro j hj
      rw [bit_permSt _ _ hj, bit_permSt _ _ hj, bit_permSt _ _ (sig_lt hl' hj)]; rfl
    rw [hc, hc]

/-! ## Where `netL` brings the wires -/

/-- The swap positions of `moveDown N p i`. -/
def mvPos (p i : ℕ) : List ℕ := (List.range (p - i)).reverse.map (i + ·)

/-- The swap positions of `netL N ps`. -/
def netPos (ps : List ℕ) : List ℕ :=
  (List.range ps.length).flatMap fun i => mvPos (curPos ps i (ps.getD i 0)) i

theorem netL_eq (N : ℕ) (ps : List ℕ) : netL N ps = (netPos ps).map (swAt N) := by
  simp [netL, netPos, mvPos, moveDown, List.map_flatMap, Function.comp_def]

theorem sig_mvPos (i : ℕ) : ∀ (d x : ℕ), sig (mvPos (i + d) i) x =
    if x = i then i + d else if i < x ∧ x ≤ i + d then x - 1 else x
  | 0, x => by
    simp only [mvPos, Nat.add_sub_cancel_left, List.range_zero, List.reverse_nil, List.map_nil, sig]
    split_ifs <;> omega
  | d + 1, x => by
    have e : mvPos (i + (d + 1)) i = (i + d) :: mvPos (i + d) i := by
      simp [mvPos, List.range_succ, Nat.add_sub_cancel_left]
    rw [e, sig, sig_mvPos i d x]
    unfold tau
    split_ifs <;> omega

/-- A nodup list of numbers in `[a, b)` has at most `b - a` elements. -/
theorem nodup_length_le {l : List ℕ} (hl : l.Nodup) {a b : ℕ} (h : ∀ x ∈ l, a ≤ x ∧ x < b) :
    l.length ≤ b - a := by
  rw [← List.toFinset_card_of_nodup hl, ← Nat.card_Ico a b]
  exact Finset.card_le_card fun x hx => Finset.mem_Ico.2 (h x (List.mem_toFinset.1 hx))

section CurPos

variable {ps : List ℕ}

theorem curPos_def (i q : ℕ) :
    curPos ps i q = q + ((ps.take i).filter fun p => decide (q < p)).length := rfl

theorem curPos_ge (hnd : ps.Nodup) {i q : ℕ} (hi : i ≤ ps.length) (hq : q ∉ ps.take i) :
    i ≤ curPos ps i q := by
  have hT : (ps.take i).Nodup := (List.take_sublist i ps).nodup hnd
  have hlen : (ps.take i).length = i := by simp; omega
  have e := List.length_eq_length_filter_add (l := ps.take i) (fun p => decide (q < p))
  have hb : ((ps.take i).filter fun p => !decide (q < p)).length ≤ q - 0 := by
    apply nodup_length_le (hT.filter _)
    intro x hx
    rw [List.mem_filter] at hx
    have : x ≠ q := fun e => hq (e ▸ hx.1)
    simp at hx; omega
  rw [curPos_def]; omega

theorem curPos_lt (hnd : ps.Nodup) {i q q' : ℕ} (hq : q ∉ ps.take i) (hq' : q' ∉ ps.take i)
    (h : q < q') : curPos ps i q < curPos ps i q' := by
  have hT : (ps.take i).Nodup := (List.take_sublist i ps).nodup hnd
  set T := ps.take i
  have e := List.length_eq_length_filter_add (l := T.filter fun p => decide (q < p))
    (fun p => decide (q' < p))
  have e1 : ((T.filter fun p => decide (q < p)).filter fun p => decide (q' < p)) =
      T.filter fun p => decide (q' < p) := by
    rw [List.filter_filter]; apply List.filter_congr; intro x _
    by_cases hx : q' < x
    · simp [hx, show q < x by omega]
    · simp [hx]
  have hb : ((T.filter fun p => decide (q < p)).filter fun p => !decide (q' < p)).length ≤
      q' - (q + 1) := by
    apply nodup_length_le ((hT.filter _).filter _)
    intro x hx
    simp only [List.mem_filter, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      at hx
    have : x ≠ q' := fun e => hq' (e ▸ hx.1.1)
    omega
  rw [curPos_def, curPos_def]
  show q + (T.filter fun p => decide (q < p)).length < q' + (T.filter fun p => decide (q' < p)).length
  rw [← e1]; omega

theorem curPos_le (hnd : ps.Nodup) {N : ℕ} (hlt : ∀ p ∈ ps, p < N) {i q : ℕ} (hqN : q < N) :
    curPos ps i q ≤ N - 1 := by
  have hT : (ps.take i).Nodup := (List.take_sublist i ps).nodup hnd
  have hb : ((ps.take i).filter fun p => decide (q < p)).length ≤ N - (q + 1) := by
    apply nodup_length_le (hT.filter _)
    intro x hx
    rw [List.mem_filter] at hx
    have := hlt x (List.mem_of_mem_take hx.1)
    simp at hx; omega
  rw [curPos_def]; omega

theorem curPos_succ {i : ℕ} (hi : i < ps.length) (q : ℕ) :
    curPos ps (i + 1) q = curPos ps i q + if q < ps[i] then 1 else 0 := by
  rw [curPos_def, curPos_def, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h] <;> omega

end CurPos

/-- The swaps up to the `i`-th step of `netL`. -/
def netUpTo (ps : List ℕ) (i : ℕ) : List ℕ :=
  (List.range i).flatMap fun j => mvPos (curPos ps j (ps.getD j 0)) j

theorem netUpTo_succ (ps : List ℕ) (i : ℕ) :
    netUpTo ps (i + 1) = netUpTo ps i ++ mvPos (curPos ps i (ps.getD i 0)) i := by
  simp [netUpTo, List.range_succ, List.flatMap_append]

theorem sig_netUpTo {ps : List ℕ} (hnd : ps.Nodup) : ∀ i, i ≤ ps.length →
    (∀ j < i, sig (netUpTo ps i) j = ps.getD j 0) ∧
      (∀ q, q ∉ ps.take i → sig (netUpTo ps i) (curPos ps i q) = q)
  | 0, _ => ⟨fun j hj => absurd hj (by omega), fun q _ => by simp [netUpTo, sig, curPos_def]⟩
  | i + 1, hi => by
    obtain ⟨ha, hb⟩ := sig_netUpTo hnd i (by omega)
    have hi' : i < ps.length := by omega
    have hgd : ps.getD i 0 = ps[i] := by simp [List.getD_eq_getElem?_getD, hi']
    have hpi : ps[i] ∉ ps.take i := by
      intro hm
      obtain ⟨k, hk, e⟩ := List.getElem_of_mem hm
      simp only [List.length_take] at hk
      rw [List.getElem_take] at e
      have := (List.Nodup.getElem_inj_iff hnd).1 e
      omega
    set p := curPos ps i ps[i] with hp
    have hpge : i ≤ p := curPos_ge hnd (by omega) hpi
    have hsig : ∀ x, sig (mvPos p i) x =
        if x = i then p else if i < x ∧ x ≤ p then x - 1 else x := by
      intro x
      have := sig_mvPos i (p - i) x
      rwa [Nat.add_sub_cancel' hpge] at this
    rw [netUpTo_succ, hgd]
    refine ⟨fun j hj => ?_, fun q hq => ?_⟩
    · rw [sig_append, hsig]
      by_cases hji : j = i
      · subst hji; rw [if_pos rfl, hp, hb _ hpi, hgd]
      · rw [if_neg hji, if_neg (by omega)]; exact ha j (by omega)
    · have hq1 : q ∉ ps.take i := fun h => hq (List.take_subset_take_left _ (by omega) h)
      have hq2 : q ≠ ps[i] := by
        intro e; apply hq; rw [e]
        have hlt : i < (ps.take (i + 1)).length := by simp; omega
        have := List.getElem_mem hlt
        rwa [List.getElem_take] at this
      have hc := curPos_ge hnd (by omega : i ≤ ps.length) hq1
      rw [curPos_succ hi', sig_append, hsig]
      rcases Nat.lt_or_gt_of_ne hq2 with hlt | hgt
      · have := curPos_lt hnd hq1 hpi hlt
        rw [if_pos hlt, if_neg (show curPos ps i q + 1 ≠ i by omega),
          if_pos (show i < curPos ps i q + 1 ∧ curPos ps i q + 1 ≤ p by omega), Nat.add_sub_cancel]
        exact hb q hq1
      · have := curPos_lt hnd hpi hq1 hgt
        rw [if_neg (show ¬ q < ps[i] by omega), add_zero, if_neg (show curPos ps i q ≠ i by omega),
          if_neg (show ¬ (i < curPos ps i q ∧ curPos ps i q ≤ p) by omega)]
        exact hb q hq1

/-- `netL N ps` brings wire `ps[i]` to wire `i`. -/
theorem sig_netPos {ps : List ℕ} (hnd : ps.Nodup) {j : ℕ} (hj : j < ps.length) :
    sig (netPos ps) j = ps.getD j 0 :=
  (sig_netUpTo hnd ps.length le_rfl).1 j hj

/-- The other wires go above, in order. -/
theorem sig_netPos_curPos {ps : List ℕ} (hnd : ps.Nodup) {q : ℕ} (hq : q ∉ ps) :
    sig (netPos ps) (curPos ps ps.length q) = q :=
  (sig_netUpTo hnd ps.length le_rfl).2 q (by rwa [List.take_length])

theorem netPos_bound {ps : List ℕ} (hnd : ps.Nodup) {N : ℕ} (hlt : ∀ p ∈ ps, p < N) :
    ∀ a ∈ netPos ps, a + 2 ≤ N := by
  intro a ha
  simp only [netPos, List.mem_flatMap, List.mem_range, mvPos, List.mem_map, List.mem_reverse]
    at ha
  obtain ⟨i, hi, d, hd, rfl⟩ := ha
  have hgd : ps.getD i 0 = ps[i] := by simp [List.getD_eq_getElem?_getD, hi]
  rw [hgd] at hd
  have := curPos_le hnd hlt (i := i) (hlt _ (List.getElem_mem hi))
  omega

/-! ## Circuits at the bottom and placed circuits -/

theorem bit_re {a b : ℕ} (h : a = b) (u : State 2 a) (j : ℕ) :
    bit (fun i : Fin b => bit u i) j = bit u j := by
  subst h
  by_cases hj : j < a
  · rw [bit_lt _ hj, bit_lt _ hj]
  · rw [bit_ge _ (by omega), bit_ge _ (by omega)]

theorem eval_heq_apply {a b : ℕ} (h : a = b) {w : Circ a} {w' : Circ b} (hw : HEq w w')
    (s t : State 2 b) :
    opsQ.eval b w' s t = opsQ.eval a w (fun i => bit s i) (fun i => bit t i) := by
  subst h; cases hw
  have e : ∀ u : State 2 a, (fun i : Fin a => bit u i) = u := fun u => by funext i; exact bit_fin u i
  rw [e, e]

theorem onW_range_self {n : ℕ} (G : Op Q 2 n) : onW n (List.range n) G = G := by
  funext s t
  have e : ∀ u : State 2 n, (rd (List.range n) u : State 2 n) = u := by
    intro u; funext i
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_range i.isLt, Option.getD_some, bit_fin]
  simp only [onW, e]
  rw [if_pos (fun j hj hm => absurd (List.mem_range.2 hj) hm)]

theorem eval_padTop {n : ℕ} (w : Circ n) :
    opsQ.eval (n + 1) (padTop w) = onW (n + 1) (List.range n) (opsQ.eval n w) := by
  funext s t
  rw [eval_heq_apply (Nat.add_comm 1 n) (pad_one_heq w), eval_pad_apply]
  have hrd : ∀ u : State 2 (n + 1),
      (rd (List.range n) (fun i : Fin (1 + n) => bit u i) : State 2 n) = rd (List.range n) u := by
    intro u; funext i; simp only [rd, bit_re (Nat.add_comm 1 n).symm]
  simp only [hrd, onW, bit_re (Nat.add_comm 1 n).symm, List.mem_range, not_lt]
  congr 1
  apply propext
  constructor
  · intro H j hj hk; exact H j (by omega) hk
  · intro H j hj hk; exact H j (by omega) hk

theorem onW_range_nest {n m : ℕ} (hm : m ≤ n) (G : Op Q 2 m) :
    onW (n + 1) (List.range n) (onW n (List.range m) G) = onW (n + 1) (List.range m) G := by
  funext s t
  have hb : ∀ (u : State 2 (n + 1)) j, j < n → bit (rd (List.range n) u : State 2 n) j = bit u j := by
    intro u j hj
    rw [bit_lt _ hj]
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_range hj, Option.getD_some]
  have hrd : ∀ u : State 2 (n + 1),
      (rd (List.range m) (rd (List.range n) u : State 2 n) : State 2 m) = rd (List.range m) u := by
    intro u; funext i
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_range i.isLt, Option.getD_some]
    exact hb u i (by omega)
  simp only [onW, hrd, List.mem_range, not_lt]
  by_cases h1 : ∀ j < n + 1, n ≤ j → bit s j = bit t j
  · rw [if_pos h1]
    congr 1
    apply propext
    constructor
    · intro H j hj hk
      by_cases hjn : j < n
      · have := H j hjn hk; rwa [hb s j hjn, hb t j hjn] at this
      · exact h1 j hj (by omega)
    · intro H j hj hk
      rw [hb s j hj, hb t j hj]; exact H j (by omega) hk
  · rw [if_neg h1, if_neg]
    intro H; exact h1 fun j hj hk => H j hj (by omega)

/-- A circuit at the bottom of wider ones. -/
theorem eval_atBot : ∀ (N : ℕ) {m : ℕ} (g : Circ m), m ≤ N →
    opsQ.eval N (atBot N g) = onW N (List.range m) (opsQ.eval m g)
  | N, m, g, hm => by
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rw [atBot_self, onW_range_self]
    · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [atBot_succ N' g (by omega), eval_padTop, eval_atBot N' g (by omega),
        onW_range_nest (by omega)]

/-- `placeG N g ps` is `g` on the wires `ps`. -/
theorem eval_placeG {N m : ℕ} (g : Circ m) {ps : List ℕ} (hnd : ps.Nodup)
    (hlt : ∀ p ∈ ps, p < N) (hlen : ps.length = m) :
    opsQ.eval N (placeG N g ps) = onW N ps (opsQ.eval m g) := by
  have hmN : m ≤ N := by
    rw [← hlen]
    have := nodup_length_le hnd (a := 0) (b := N) (fun x hx => ⟨Nat.zero_le _, hlt x hx⟩)
    omega
  have hb := netPos_bound hnd hlt
  funext s t
  unfold placeG
  rw [netL_eq, eval_conjNet _ hb, eval_atBot N g hmN]
  have hrd : ∀ u : State 2 N,
      (rd (List.range m) (permSt (sig (netPos ps)) u) : State 2 m) = rd ps u := by
    intro u; funext i
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_range i.isLt, Option.getD_some]
    rw [bit_permSt _ _ (by omega), sig_netPos hnd (by omega)]
    simp [List.getD_eq_getElem?_getD]
  simp only [onW, hrd, List.mem_range, not_lt]
  congr 1
  apply propext
  constructor
  · intro H j hj hjp
    have hc1 := curPos_ge hnd (i := ps.length) le_rfl (by rwa [List.take_length])
    have hc2 := curPos_le hnd hlt (i := ps.length) hj
    have := H (curPos ps ps.length j) (by omega) (by omega)
    rwa [bit_permSt _ _ (by omega), bit_permSt _ _ (by omega), sig_netPos_curPos hnd hjp] at this
  · intro H j hj hk
    rw [bit_permSt _ _ hj, bit_permSt _ _ hj]
    apply H _ (sig_lt hb hj)
    intro hm
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
    have e2 := sig_netPos hnd hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, e] at e2
    have := sig_inj _ e2.symm
    omega


/-! ## The canonical multi-controlled gates -/

/-- The number of special wires of a kind (box wire; target; box wire and
`H` wire). -/
def _root_.QCert.RealCliffordCH.Sec8.Kind.ar : Kind → ℕ
  | .hg => 2
  | _ => 1

/-- The canonical gate of kind `K` with `k` controls (Definition 2.4). -/
def _root_.QCert.RealCliffordCH.Sec8.Kind.canon : (K : Kind) → (k : ℕ) → Circ (k + K.ar)
  | .box, k => box k
  | .zx, k => zx k
  | .xz, k => xz k
  | .hg, k => mch k

theorem canonAt_eq (N : ℕ) (K : Kind) (k : ℕ) (ps : List ℕ) :
    canonAt N K k ps = placeG N (K.canon k) ps := by
  cases K <;> rfl

/-- `U` on the bottom `a` of `k + a` wires when the top `k` wires are all `1`,
the identity otherwise. -/
def cOp (k a : ℕ) (U : Op Q 2 a) : Op Q 2 (k + a) := fun u v =>
  if ∀ j < k + a, a ≤ j → bit u j = bit v j then
    (if ∀ j < k + a, a ≤ j → bit v j = 1 then U else 1) (rd (List.range a) u) (rd (List.range a) v)
  else 0

theorem split_fst_rd {k a : ℕ} (u : State 2 (k + a)) :
    (split 2 k a u).1 = rd (List.range a) u := by
  funext i
  simp only [split, Equiv.coe_fn_mk, rd, List.getD_eq_getElem?_getD, List.getElem?_range i.isLt,
    Option.getD_some]
  rw [bit_lt _ (by omega)]

theorem split_snd_bit {k a : ℕ} (u : State 2 (k + a)) (j : Fin k) :
    (split 2 k a u).2 j = bit u (a + j) := by
  rw [bit_lt _ (by omega)]; rfl

theorem cOp_eq_blk (k a : ℕ) (U : Op Q 2 a) :
    cOp k a U = blk (m := k) (k := a) fun h => if ∀ j, h j = 1 then U else 1 := by
  funext u v
  simp only [cOp, blk, split_fst_rd]
  have e1 : (split 2 k a u).2 = (split 2 k a v).2 ↔ ∀ j < k + a, a ≤ j → bit u j = bit v j := by
    constructor
    · intro h j hj hk
      have := congrFun h ⟨j - a, by omega⟩
      rwa [split_snd_bit, split_snd_bit, show a + (j - a) = j by omega] at this
    · intro h; funext j; rw [split_snd_bit, split_snd_bit]; exact h _ (by omega) (by omega)
  by_cases h1 : ∀ j < k + a, a ≤ j → bit u j = bit v j
  · rw [if_pos h1, if_pos (e1.2 h1)]
    have e2 : (∀ j, (split 2 k a u).2 j = 1) ↔ ∀ j < k + a, a ≤ j → bit v j = 1 := by
      constructor
      · intro h j hj hk
        have := h ⟨j - a, by omega⟩
        rwa [split_snd_bit, show a + (j - a) = j by omega, h1 j hj hk] at this
      · intro h j; rw [split_snd_bit, h1 _ (by omega) (by omega)]; exact h _ (by omega) (by omega)
    by_cases h2 : ∀ j < k + a, a ≤ j → bit v j = 1
    · rw [if_pos h2, if_pos (e2.2 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (e2.1 h))]
  · rw [if_neg h1, if_neg (fun h => h1 (e1.1 h))]

theorem cOp_zero1 (U : Op Q 2 1) : cOp 0 1 U = U := by
  funext u v
  have e : ∀ w : State 2 (0 + 1), (rd (List.range 1) w : State 2 1) = w := by
    intro w; funext i; fin_cases i; rfl
  simp only [cOp, e]
  rw [if_pos (fun j hj hk => absurd hj (by omega)), if_pos (fun j hj hk => absurd hj (by omega))]

theorem cOp_zero2 (U : Op Q 2 2) : cOp 0 2 U = U := by
  funext u v
  have e : ∀ w : State 2 (0 + 2), (rd (List.range 2) w : State 2 2) = w := by
    intro w; funext i; fin_cases i <;> rfl
  simp only [cOp, e]
  rw [if_pos (fun j hj hk => absurd hj (by omega)), if_pos (fun j hj hk => absurd hj (by omega))]

theorem eval_box_all : ∀ k, opsQ.eval (k + 1) (box k) = boxOp k
  | 0 => eval_eq_of_checkM (by decide +kernel)
  | 1 => eval_eq_of_checkM (by decide +kernel)
  | k + 2 => eval_box k

theorem eval_box_blk1 (k : ℕ) :
    opsQ.eval (k + 1) (box k) =
      blk (m := k) (k := 1) fun h => if ∀ j, h j = 1 then opsQ.eval 1 (box 0) else 1 := by
  rw [eval_box_all, eval_box_all, boxOp, diagonal_eq_blk (m := k) (k := 1)]
  congr 1; funext h
  have key : ∀ l : State 2 1, (∀ i : Fin k, (split 2 k 1).symm (l, h) i.succ = 1) ↔ ∀ j, h j = 1 := by
    intro l
    simp only [split_symm_apply, Fin.val_succ]
    constructor
    · intro H j; have := H j; rw [dif_neg (by omega)] at this; convert this using 2
    · intro H i; rw [dif_neg (by omega)]; convert H i using 2
  by_cases hh : ∀ j, h j = 1
  · rw [if_pos hh, boxOp]; congr 1; funext l
    rw [if_pos ((key l).2 hh), if_pos (fun i => i.elim0)]
  · rw [if_neg hh, ← diagonal_one]; congr 1; funext l
    rw [if_neg (fun H => hh ((key l).1 H))]

theorem eval_box_blk2 (k : ℕ) :
    opsQ.eval (k + 2) (box (k + 1)) =
      blk (m := k) (k := 2) fun h => if ∀ j, h j = 1 then opsQ.eval 2 (box 1) else 1 := by
  rw [eval_box_all (k + 1), eval_box_all 1, boxOp, diagonal_eq_blk (m := k) (k := 2)]
  congr 1; funext h
  have key : ∀ l : State 2 2, (∀ i : Fin (k + 1), (split 2 k 2).symm (l, h) i.succ = 1) ↔
      (l 1 = 1 ∧ ∀ j, h j = 1) := by
    intro l
    simp only [split_symm_apply, Fin.val_succ]
    constructor
    · intro H
      refine ⟨?_, fun j => ?_⟩
      · have := H 0; simpa using this
      · have := H j.succ; simp only [Fin.val_succ] at this
        rw [dif_neg (by omega)] at this; convert this using 2
    · rintro ⟨hl, hh⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hl
      · simp only [Fin.val_succ]; rw [dif_neg (by omega)]; convert hh j using 2
  by_cases hh : ∀ j, h j = 1
  · rw [if_pos hh, boxOp]; congr 1; funext l
    have k1 : (∀ i : Fin 1, l i.succ = 1) ↔ l 1 = 1 := by
      constructor
      · intro H; exact H 0
      · intro H i; fin_cases i; exact H
    by_cases hl : l 1 = 1
    · rw [if_pos ((key l).2 ⟨hl, hh⟩), if_pos (k1.2 hl)]
    · rw [if_neg (fun H => hl ((key l).1 H).1), if_neg (fun H => hl (k1.1 H))]
  · rw [if_neg hh, ← diagonal_one]; congr 1; funext l
    rw [if_neg (fun H => hh ((key l).1 H).2)]

theorem eval_bot2 (k : ℕ) (w : Circ 2) :
    opsQ.eval (k + 2) (Circuit.pad k w) = blk (m := k) (k := 2) fun _ => opsQ.eval 2 w := by
  rw [eval_pad, onBottom_eq_blk]

theorem pad_ch (k : ℕ) : Circuit.pad k (ch : Circ 2) = (ch : Circ (k + 2)) := rfl
theorem pad_swap (k : ℕ) : Circuit.pad k (swap : Circ 2) = (swap : Circ (k + 2)) := rfl
theorem pad_pp (k : ℕ) : Circuit.pad k (pp : Circ 2) = (pp : Circ (k + 2)) := rfl

theorem sw_sw : opsQ.eval 2 (swap : Circ 2) * opsQ.eval 2 (swap : Circ 2) = 1 := by
  have := eval_eq_of_check (n := 2) (w := drawn [swap, swap]) (w' := drawn []) (by decide +kernel)
  simpa [drawn] using this

theorem ch_ch : opsQ.eval 2 (ch : Circ 2) * opsQ.eval 2 (ch : Circ 2) = 1 := by
  have := eval_eq_of_check (n := 2) (w := drawn [ch, ch]) (w' := drawn []) (by decide +kernel)
  simpa [drawn] using this

theorem pp_pp : opsQ.eval 2 (pp : Circ 2) * opsQ.eval 2 (pp : Circ 2) = 1 := by
  have := eval_eq_of_check (n := 2) (w := drawn [pp, pp]) (w' := drawn []) (by decide +kernel)
  simpa [drawn] using this

theorem pp_box_pp : opsQ.eval 2 (pp : Circ 2) * opsQ.eval 2 (box 1) * opsQ.eval 2 (pp : Circ 2) =
    opsQ.eval 2 (mch 0) := by
  have := eval_eq_of_check (n := 2) (w := drawn [pp, box 1, pp]) (w' := mch 0) (by decide +kernel)
  simpa [drawn, mul_assoc] using this

theorem eval_zx_blk (k : ℕ) :
    opsQ.eval (k + 2) (zx (k + 1)) =
      blk (m := k) (k := 2) fun h => if ∀ j, h j = 1 then opsQ.eval 2 (zx 1) else 1 := by
  have hz : zx (k + 1) = drawn [ch, conj swap (box (k + 1)), ch, conj swap (box (k + 1))] := rfl
  have hz1 : zx 1 = drawn [ch, conj swap (box 1), ch, conj swap (box 1)] := rfl
  rw [hz, hz1]
  simp only [conj, drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, map_mul]
  rw [← pad_ch, ← pad_swap, eval_bot2, eval_bot2, eval_box_blk2]
  simp only [blk_mul]
  congr 1; funext h
  split_ifs
  · rfl
  · simp only [mul_one, ← mul_assoc, sw_sw, one_mul, ch_ch]

theorem eval_xz_blk (k : ℕ) :
    opsQ.eval (k + 2) (xz (k + 1)) =
      blk (m := k) (k := 2) fun h => if ∀ j, h j = 1 then opsQ.eval 2 (xz 1) else 1 := by
  have hz : xz (k + 1) = drawn [conj swap (box (k + 1)), ch, conj swap (box (k + 1)), ch] := rfl
  have hz1 : xz 1 = drawn [conj swap (box 1), ch, conj swap (box 1), ch] := rfl
  rw [hz, hz1]
  simp only [conj, drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, map_mul]
  rw [← pad_ch, ← pad_swap, eval_bot2, eval_bot2, eval_box_blk2]
  simp only [blk_mul]
  congr 1; funext h
  split_ifs
  · rfl
  · simp only [mul_one, ← mul_assoc, sw_sw, one_mul, ch_ch]

theorem eval_mch_blk (k : ℕ) :
    opsQ.eval (k + 2 + 2) (mch (k + 2)) =
      blk (m := k + 2) (k := 2) fun h => if ∀ j, h j = 1 then opsQ.eval 2 (mch 0) else 1 := by
  have hm : mch (k + 2) = drawn [pp, box (k + 3), pp] := rfl
  rw [hm]
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, map_mul]
  rw [← pad_pp (k + 2), eval_bot2, eval_box_blk2 (k + 2)]
  simp only [blk_mul]
  congr 1; funext h
  split_ifs
  · rw [← pp_box_pp, mul_assoc]
  · rw [one_mul, pp_pp]

/-- `cOp` with one control more, read two wires at a time. -/
theorem cOp_nest1 (k : ℕ) (U : Op Q 2 1) :
    (blk (m := k) (k := 2) fun h => if ∀ j, h j = 1 then cOp 1 1 U else 1) = cOp (k + 1) 1 U := by
  rw [← cOp_eq_blk]
  funext u v
  have r1 : List.range 1 = [0] := rfl
  have r2 : List.range 2 = [0, 1] := rfl
  have hA : (∀ j < k + 1 + 1, 1 ≤ j → bit u j = bit v j) ↔
      (bit u 1 = bit v 1 ∧ ∀ j < k + 2, 2 ≤ j → bit u j = bit v j) := by
    constructor
    · intro H; exact ⟨H 1 (by omega) le_rfl, fun j hj hk => H j hj (by omega)⟩
    · rintro ⟨h1, h2⟩ j hj hk
      rcases Nat.lt_or_ge j 2 with h | h
      · obtain rfl : j = 1 := by omega
        exact h1
      · exact h2 j hj h
  have hC : (∀ j < k + 1 + 1, 1 ≤ j → bit v j = 1) ↔
      (bit v 1 = 1 ∧ ∀ j < k + 2, 2 ≤ j → bit v j = 1) := by
    constructor
    · intro H; exact ⟨H 1 (by omega) le_rfl, fun j hj hk => H j hj (by omega)⟩
    · rintro ⟨h1, h2⟩ j hj hk
      rcases Nat.lt_or_ge j 2 with h | h
      · obtain rfl : j = 1 := by omega
        exact h1
      · exact h2 j hj h
  have hA1 : ∀ x y : State 2 (k + 2), (∀ j < 1 + 1, 1 ≤ j →
      bit (rd [0, 1] x : State 2 2) j = bit (rd [0, 1] y : State 2 2) j) ↔ bit x 1 = bit y 1 := by
    intro x y
    constructor
    · intro H; exact H 1 (by omega) le_rfl
    · intro H j hj hk; obtain rfl : j = 1 := by omega
      exact H
  have hC1 : ∀ y : State 2 (k + 2), (∀ j < 1 + 1, 1 ≤ j → bit (rd [0, 1] y : State 2 2) j = 1) ↔
      bit y 1 = 1 := by
    intro y
    constructor
    · intro H; exact H 1 (by omega) le_rfl
    · intro H j hj hk; obtain rfl : j = 1 := by omega
      exact H
  have hrr : ∀ x : State 2 (k + 2), (rd [0] (rd [0, 1] x : State 2 2) : State 2 1) = rd [0] x := by
    intro x; funext i; fin_cases i; rfl
  have hr2 : ∀ x y : State 2 (k + 2), (rd [0, 1] x : State 2 2) = rd [0, 1] y ↔
      (bit x 0 = bit y 0 ∧ bit x 1 = bit y 1) := by
    intro x y
    constructor
    · intro e; exact ⟨congrFun e 0, congrFun e 1⟩
    · rintro ⟨e0, e1⟩; funext i; fin_cases i
      · exact e0
      · exact e1
  have hr1 : ∀ x y : State 2 (k + 2), (rd [0] x : State 2 1) = rd [0] y ↔ bit x 0 = bit y 0 := by
    intro x y
    constructor
    · intro e; exact congrFun e 0
    · intro e; funext i; fin_cases i; exact e
  have ia : ∀ {n : ℕ} (C : Prop) [Decidable C] (A B : Op Q 2 n) (x y : State 2 n),
      (if C then A else B) x y = if C then A x y else B x y := by
    intros; split_ifs <;> rfl
  simp only [cOp, r1, r2, ia, one_apply, hA, hC, hA1, hC1, hrr, hr2, hr1]
  rcases fin2_cases (bit u 1) with b1 | b1 <;> rcases fin2_cases (bit v 1) with b2 | b2 <;>
    rcases fin2_cases (bit u 0) with b3 | b3 <;> rcases fin2_cases (bit v 0) with b4 | b4 <;>
    by_cases a2 : ∀ j < k + 2, 2 ≤ j → bit u j = bit v j <;>
    by_cases c2 : ∀ j < k + 2, 2 ≤ j → bit v j = 1 <;> simp [a2, c2, b1, b2, b3, b4]

theorem eval_zx1 : opsQ.eval 2 (zx 1) = cOp 1 1 (opsQ.eval 1 (zx 0)) :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_xz1 : opsQ.eval 2 (xz 1) = cOp 1 1 (opsQ.eval 1 (xz 0)) :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_mch1 : opsQ.eval 3 (mch 1) = cOp 1 2 (opsQ.eval 2 (mch 0)) :=
  eval_eq_of_checkM (by decide +kernel)

/-- The gate of a kind without controls: `-1`, `ZX`, `XZ`, and `H` on wire `1`
of two wires. -/
def _root_.QCert.RealCliffordCH.Sec8.Kind.U : (K : Kind) → Op Q 2 K.ar
  | .box => opsQ.eval 1 (box 0)
  | .zx => opsQ.eval 1 (zx 0)
  | .xz => opsQ.eval 1 (xz 0)
  | .hg => opsQ.eval 2 (mch 0)

/-- The canonical gates of Definition 2.4 apply their gate without controls
when all their controls are `1`. -/
theorem eval_canon : ∀ (K : Kind) (k : ℕ),
    opsQ.eval (k + K.ar) (K.canon k) = cOp k K.ar K.U
  | .box, k => by
    show opsQ.eval (k + 1) (box k) = cOp k 1 (opsQ.eval 1 (box 0))
    rw [eval_box_blk1, cOp_eq_blk]
  | .zx, 0 => (cOp_zero1 _).symm
  | .zx, k + 1 => by
    show opsQ.eval (k + 2) (zx (k + 1)) = cOp (k + 1) 1 (opsQ.eval 1 (zx 0))
    rw [eval_zx_blk, eval_zx1, cOp_nest1]
  | .xz, 0 => (cOp_zero1 _).symm
  | .xz, k + 1 => by
    show opsQ.eval (k + 2) (xz (k + 1)) = cOp (k + 1) 1 (opsQ.eval 1 (xz 0))
    rw [eval_xz_blk, eval_xz1, cOp_nest1]
  | .hg, 0 => (cOp_zero2 _).symm
  | .hg, 1 => eval_mch1
  | .hg, k + 2 => by
    show opsQ.eval (k + 2 + 2) (mch (k + 2)) = cOp (k + 2) 2 (opsQ.eval 2 (mch 0))
    rw [eval_mch_blk, cOp_eq_blk]


/-! ## Placed canonical gates -/

theorem bit_rd {N a : ℕ} (ws : List ℕ) (s : State 2 N) {j : ℕ} (hj : j < a) :
    bit (rd ws s : State 2 a) j = bit s (ws.getD j 0) := by
  rw [bit_lt _ hj]; rfl

theorem getD_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- A canonical gate placed with its special wires on `tg` and its controls on
`cs`: `U` on `tg` when the wires `cs` are all `1`. -/
theorem onW_cOp {N k a : ℕ} {tg cs : List ℕ} (hnd : (tg ++ cs).Nodup)
    (hlt : ∀ p ∈ tg ++ cs, p < N) (ha : tg.length = a) (hk : cs.length = k) (U : Op Q 2 a)
    (s t : State 2 N) :
    onW N (tg ++ cs) (cOp k a U) s t =
      if ∀ j < N, j ∉ tg → bit s j = bit t j then
        (if ∀ j ∈ cs, bit t j = 1 then U else 1) (rd tg s) (rd tg t)
      else 0 := by
  have hdis : ∀ x ∈ cs, x ∉ tg := fun x hx ht =>
    (List.disjoint_of_nodup_append hnd) ht hx
  have hgd : ∀ j, a ≤ j → (tg ++ cs).getD j 0 = cs.getD (j - a) 0 := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), ha]
  have hrd : ∀ u : State 2 N,
      (rd (List.range a) (rd (tg ++ cs) u : State 2 (k + a)) : State 2 a) = rd tg u := by
    intro u; funext i
    simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_range i.isLt, Option.getD_some]
    rw [bit_lt _ (by omega)]
    show bit u ((tg ++ cs).getD i 0) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  simp only [onW, cOp, hrd]
  have eA : ((∀ j < N, j ∉ tg ++ cs → bit s j = bit t j) ∧
      ∀ j < k + a, a ≤ j → bit (rd (tg ++ cs) s : State 2 (k + a)) j =
        bit (rd (tg ++ cs) t : State 2 (k + a)) j) ↔ ∀ j < N, j ∉ tg → bit s j = bit t j := by
    constructor
    · rintro ⟨h1, h2⟩ j hj hjt
      by_cases hjc : j ∈ cs
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hjc
        have := h2 (a + i) (by omega) (by omega)
        rwa [bit_rd _ _ (by omega), bit_rd _ _ (by omega), hgd _ (by omega),
          show a + i - a = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some] at this
      · exact h1 j hj (fun hm => (List.mem_append.1 hm).elim hjt hjc)
    · intro H
      refine ⟨fun j hj hm => H j hj (fun h => hm (List.mem_append_left _ h)), ?_⟩
      intro j hj ha'
      rw [bit_rd _ _ hj, bit_rd _ _ hj, hgd _ ha']
      have hm : cs.getD (j - a) 0 ∈ cs := getD_mem (by omega)
      exact H _ (hlt _ (List.mem_append_right _ hm)) (hdis _ hm)
  have eC : (∀ j < k + a, a ≤ j → bit (rd (tg ++ cs) t : State 2 (k + a)) j = 1) ↔
      ∀ j ∈ cs, bit t j = 1 := by
    constructor
    · intro H j hjc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hjc
      have := H (a + i) (by omega) (by omega)
      rwa [bit_rd _ _ (by omega), hgd _ (by omega), show a + i - a = i by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    · intro H j hj ha'
      rw [bit_rd _ _ hj, hgd _ ha']
      exact H _ (getD_mem (by omega))
  by_cases h1 : ∀ j < N, j ∉ tg ++ cs → bit s j = bit t j
  · rw [if_pos h1]
    by_cases h2 : ∀ j < k + a, a ≤ j → bit (rd (tg ++ cs) s : State 2 (k + a)) j =
        bit (rd (tg ++ cs) t : State 2 (k + a)) j
    · rw [if_pos h2, if_pos (eA.1 ⟨h1, h2⟩)]
      by_cases h3 : ∀ j ∈ cs, bit t j = 1
      · rw [if_pos (eC.2 h3), if_pos h3]
      · rw [if_neg (fun h => h3 (eC.1 h)), if_neg h3]
    · rw [if_neg h2, if_neg (fun H => h2 (eA.2 H).2)]
  · rw [if_neg h1, if_neg (fun H => h1 (eA.2 H).1)]

/-! ## Colours -/

/-- `0 ↔ 1`. -/
def nb (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

theorem nb_nb (b : Fin 2) : nb (nb b) = b := by
  rcases fin2_cases b with rfl | rfl <;> rfl

/-- A state with the wires `ws` negated. -/
def flipSt {N : ℕ} (ws : List ℕ) (t : State 2 N) : State 2 N :=
  fun i => if (i : ℕ) ∈ ws then nb (t i) else t i

theorem bit_flipSt {N : ℕ} (ws : List ℕ) (t : State 2 N) {j : ℕ} (hj : j < N) :
    bit (flipSt ws t) j = if j ∈ ws then nb (bit t j) else bit t j := by
  rw [bit_lt _ hj, bit_lt _ hj]; rfl

theorem flipSt_flipSt {N : ℕ} (ws : List ℕ) (t : State 2 N) : flipSt ws (flipSt ws t) = t := by
  funext i; simp only [flipSt]; split_ifs <;> simp [nb_nb]

theorem eval_x1 : opsQ.eval 1 (x : Circ 1) = fun u v => if u 0 = nb (v 0) then (1 : Q) else 0 :=
  eval_eq_of_checkM (by decide +kernel)

theorem eval_xAt {N j : ℕ} (hj : j < N) : opsQ.eval N (xAt N j) = pOp (flipSt [j]) := by
  funext s t
  rw [xAt, eval_place1 N j _ hj, eval_x1]
  simp only [onW, pOp]
  have key : s = flipSt [j] t ↔ ((∀ i < N, i ∉ [j] → bit s i = bit t i) ∧ bit s j = nb (bit t j)) := by
    constructor
    · rintro rfl
      refine ⟨fun i hi hm => ?_, ?_⟩
      · rw [bit_flipSt _ _ hi, if_neg hm]
      · rw [bit_flipSt _ _ hj, if_pos (by simp)]
    · rintro ⟨h1, h2⟩
      apply state_ext; intro i hi
      rw [bit_flipSt _ _ hi]
      split_ifs with hm
      · rw [List.mem_singleton] at hm; subst hm; exact h2
      · exact h1 i hi hm
  by_cases h1 : ∀ i < N, i ∉ [j] → bit s i = bit t i
  · rw [if_pos h1]
    by_cases h2 : bit s j = nb (bit t j)
    · rw [if_pos (key.2 ⟨h1, h2⟩), if_pos]; exact h2
    · rw [if_neg (fun e => h2 (key.1 e).2), if_neg]; exact h2
  · rw [if_neg h1, if_neg (fun e => h1 (key.1 e).1)]

theorem eval_xs {N : ℕ} : ∀ (ws : List ℕ), ws.Nodup → (∀ j ∈ ws, j < N) →
    opsQ.eval N (drawn (ws.map (xAt N))) = pOp (flipSt ws)
  | [], _, _ => by
    funext s t
    have : flipSt ([] : List ℕ) t = t := by funext i; simp [flipSt]
    simp only [List.map_nil, drawn, List.reverse_nil, List.prod_nil, map_one, pOp, this, one_apply]
  | a :: l, hnd, hlt => by
    have hal : a ∉ l := (List.nodup_cons.1 hnd).1
    have e : drawn ((a :: l).map (xAt N)) = drawn (l.map (xAt N)) * xAt N a := by
      simp [drawn, List.prod_append]
    rw [e, map_mul, eval_xs l (List.nodup_cons.1 hnd).2 (fun j hj => hlt j (by simp [hj])),
      eval_xAt (hlt a (by simp)), pOp_mul _ _ (flipSt_flipSt l)]
    congr 1
    funext t i
    simp only [Function.comp_apply, flipSt, List.mem_cons]
    by_cases h1 : (i : ℕ) = a
    · have : (i : ℕ) ∉ l := h1 ▸ hal
      simp [h1, hal]
    · by_cases h2 : (i : ℕ) ∈ l <;> simp [h1, h2]

/-- `X` on the wires `ws` on both sides of a gate. -/
theorem eval_colourW {N : ℕ} {ws : List ℕ} (hnd : ws.Nodup) (hlt : ∀ j ∈ ws, j < N)
    (g : Circ N) (s t : State 2 N) :
    opsQ.eval N (colourW N ws g) s t = opsQ.eval N g (flipSt ws s) (flipSt ws t) := by
  have e : colourW N ws g = drawn (ws.map (xAt N)) * g * drawn (ws.map (xAt N)) := by
    simp [colourW, drawn, List.prod_append, mul_assoc]
  rw [e, map_mul, map_mul, eval_xs ws hnd hlt, pOp_conj _ _ (flipSt_flipSt ws)]

/-! ## The multi-controlled gates -/

/-- The wires of `t` outside `tg` match the controls `c`. -/
def Match (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) (t : State 2 N) : Prop :=
  ∀ j < N, j ∉ tg → ∀ b, c j = some b → bit t j = if b then 1 else 0

instance (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) (t : State 2 N) :
    Decidable (Match N tg c t) := by
  unfold Match; infer_instance

/-- `Λ_c(U)`: `U` on the wires `tg` when the other wires match the controls
`c`, the identity otherwise. -/
def lamOp (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) {a : ℕ} (U : Op Q 2 a) : Op Q 2 N :=
  fun s t =>
    if ∀ j < N, j ∉ tg → bit s j = bit t j then
      (if Match N tg c t then U else 1) (rd tg s) (rd tg t)
    else 0

theorem mem_ctrlWires {N : ℕ} {tg : List ℕ} {c : ℕ → Option Bool} {j : ℕ} :
    j ∈ ctrlWires N tg c ↔ j < N ∧ (c j).isSome ∧ j ∉ tg := by
  simp [ctrlWires, List.mem_filter, List.mem_range]

theorem mem_whiteWires {N : ℕ} {tg : List ℕ} {c : ℕ → Option Bool} {j : ℕ} :
    j ∈ whiteWires N tg c ↔ j < N ∧ c j = some false ∧ j ∉ tg := by
  simp [whiteWires, List.mem_filter, List.mem_range]

/-- The multi-controlled gate `mc N K tg c` is `Λ_c(U_K)`. -/
theorem eval_mc {N : ℕ} {K : Kind} {tg : List ℕ} (c : ℕ → Option Bool) (hnd : tg.Nodup)
    (hlt : ∀ j ∈ tg, j < N) (ha : tg.length = K.ar) :
    opsQ.eval N (mc N K tg c) = lamOp N tg c K.U := by
  set cs := ctrlWires N tg c with hcs
  set W := whiteWires N tg c with hW
  have hcsnd : cs.Nodup := (List.nodup_range).filter _
  have hWnd : W.Nodup := (List.nodup_range).filter _
  have hnd2 : (tg ++ cs).Nodup := by
    rw [List.nodup_append]
    exact ⟨hnd, hcsnd, fun x hx y hy e => (mem_ctrlWires.1 (e ▸ hy)).2.2 hx⟩
  have hlt2 : ∀ p ∈ tg ++ cs, p < N := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hlt p h
    · exact (mem_ctrlWires.1 h).1
  have hWlt : ∀ j ∈ W, j < N := fun j hj => (mem_whiteWires.1 hj).1
  funext s t
  unfold mc
  rw [eval_colourW hWnd hWlt, canonAt_eq,
    eval_placeG _ hnd2 hlt2 (by rw [List.length_append, ha, hcs, Nat.add_comm]), eval_canon,
    onW_cOp hnd2 hlt2 ha rfl]
  simp only [lamOp]
  have hrd : ∀ u : State 2 N, (rd tg (flipSt W u) : State 2 K.ar) = rd tg u := by
    intro u; funext i
    simp only [rd]
    have hi : tg.getD i 0 ∈ tg := getD_mem (by omega)
    rw [bit_flipSt _ _ (hlt _ hi), if_neg (fun h => (mem_whiteWires.1 h).2.2 hi)]
  rw [hrd, hrd]
  have eA : (∀ j < N, j ∉ tg → bit (flipSt W s) j = bit (flipSt W t) j) ↔
      ∀ j < N, j ∉ tg → bit s j = bit t j := by
    refine forall_congr' fun j => imp_congr_right fun hj => imp_congr_right fun _ => ?_
    rw [bit_flipSt _ _ hj, bit_flipSt _ _ hj]
    split_ifs
    · constructor
      · intro e; rw [← nb_nb (bit s j), e, nb_nb]
      · intro e; rw [e]
    · exact Iff.rfl
  have eC : (∀ j ∈ cs, bit (flipSt W t) j = 1) ↔ Match N tg c t := by
    constructor
    · intro H j hj hjt b hb
      have hm : j ∈ cs := mem_ctrlWires.2 ⟨hj, by rw [hb]; rfl, hjt⟩
      have := H j hm
      rw [bit_flipSt _ _ hj] at this
      cases b
      · rw [if_pos (mem_whiteWires.2 ⟨hj, hb, hjt⟩)] at this
        rcases fin2_cases (bit t j) with h | h
        · exact h
        · rw [h] at this; exact absurd this (by decide)
      · rw [if_neg (fun h => by rw [(mem_whiteWires.1 h).2.1] at hb; cases hb)] at this
        exact this
    · intro H j hj
      obtain ⟨hjN, hsome, hjt⟩ := mem_ctrlWires.1 hj
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
      have := H j hjN hjt b hb
      rw [bit_flipSt _ _ hjN]
      cases b
      · rw [if_pos (mem_whiteWires.2 ⟨hjN, hb, hjt⟩), this]; rfl
      · rw [if_neg (fun h => by rw [(mem_whiteWires.1 h).2.1] at hb; cases hb), this]; rfl
  by_cases h1 : ∀ j < N, j ∉ tg → bit s j = bit t j
  · rw [if_pos (eA.2 h1), if_pos h1]
    by_cases h2 : Match N tg c t
    · rw [if_pos (eC.2 h2), if_pos h2]
    · rw [if_neg (fun h => h2 (eC.1 h)), if_neg h2]
  · rw [if_neg (fun h => h1 (eA.1 h)), if_neg h1]


/-! ## Block diagonal in the wires above the bottom `k` -/

theorem bit_rd_range {N k : ℕ} (u : State 2 N) {j : ℕ} (hj : j < k) :
    bit (rd (List.range k) u : State 2 k) j = bit u j := by
  rw [bit_rd _ _ hj, List.getD_eq_getElem?_getD, List.getElem?_range hj, Option.getD_some]

theorem rd_rd_range {N k a : ℕ} {ws : List ℕ} (hws : ∀ j ∈ ws, j < k) (ha : ws.length = a)
    (u : State 2 N) : (rd ws (rd (List.range k) u : State 2 k) : State 2 a) = rd ws u := by
  funext i
  simp only [rd]
  exact bit_rd_range u (hws _ (getD_mem (by omega)))

theorem split_snd_eq_iff {m k : ℕ} (s t : State 2 (m + k)) :
    (split 2 m k s).2 = (split 2 m k t).2 ↔ ∀ j < m + k, k ≤ j → bit s j = bit t j := by
  constructor
  · intro h j hj hk
    have := congrFun h ⟨j - k, by omega⟩
    rwa [split_snd_bit, split_snd_bit, show k + (j - k) = j by omega] at this
  · intro h; funext j; rw [split_snd_bit, split_snd_bit]; exact h _ (by omega) (by omega)

/-- An operator on wires below `k` is block diagonal above `k`. -/
theorem onW_blk {m k a : ℕ} {ws : List ℕ} (hws : ∀ j ∈ ws, j < k) (ha : ws.length = a)
    (G : Op Q 2 a) : onW (m + k) ws G = blk (m := m) (k := k) fun _ => onW k ws G := by
  funext s t
  simp only [blk, split_fst_rd, onW, rd_rd_range hws ha]
  by_cases h1 : ∀ j < m + k, k ≤ j → bit s j = bit t j
  · rw [if_pos ((split_snd_eq_iff s t).2 h1)]
    have e : (∀ j < m + k, j ∉ ws → bit s j = bit t j) ↔
        ∀ j < k, j ∉ ws → bit (rd (List.range k) s : State 2 k) j =
          bit (rd (List.range k) t : State 2 k) j := by
      constructor
      · intro H j hj hjw; rw [bit_rd_range _ hj, bit_rd_range _ hj]; exact H j (by omega) hjw
      · intro H j hj hjw
        by_cases hjk : j < k
        · have := H j hjk hjw; rwa [bit_rd_range _ hjk, bit_rd_range _ hjk] at this
        · exact h1 j hj (by omega)
    by_cases h2 : ∀ j < m + k, j ∉ ws → bit s j = bit t j
    · rw [if_pos h2, if_pos (e.1 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (e.2 h))]
  · rw [if_neg (fun h => h1 ((split_snd_eq_iff s t).1 h)), if_neg]
    intro H; exact h1 fun j hj hk => H j hj (fun hm => by have := hws j hm; omega)

/-- The controls above `k` match the top wires `h`. -/
def TopMatch (k : ℕ) (c : ℕ → Option Bool) {m : ℕ} (h : State 2 m) : Prop :=
  ∀ j : Fin m, ∀ b, c (k + j) = some b → h j = if b then 1 else 0

instance (k : ℕ) (c : ℕ → Option Bool) {m : ℕ} (h : State 2 m) : Decidable (TopMatch k c h) := by
  unfold TopMatch; infer_instance

/-- `Λ_c(U)` with its special wires below `k` is block diagonal above `k`: on
the blocks where the top wires match the controls there, it is `Λ_c(U)` on
`k` wires. -/
theorem lamOp_blk {m k a : ℕ} {tg : List ℕ} (htg : ∀ j ∈ tg, j < k) (ha : tg.length = a)
    (c : ℕ → Option Bool) (U : Op Q 2 a) :
    lamOp (m + k) tg c U =
      blk (m := m) (k := k) fun h => if TopMatch k c h then lamOp k tg c U else 1 := by
  funext s t
  have ia : ∀ (C : Prop) [Decidable C] (A B : Op Q 2 k) (x y : State 2 k),
      (if C then A else B) x y = if C then A x y else B x y := by
    intros; split_ifs <;> rfl
  have ia' : ∀ (C : Prop) [Decidable C] (A B : Op Q 2 a) (x y : State 2 a),
      (if C then A else B) x y = if C then A x y else B x y := by
    intros; split_ifs <;> rfl
  simp only [blk, split_fst_rd, lamOp, rd_rd_range htg ha, ia, ia', one_apply]
  have hTop : ∀ u : State 2 (m + k),
      TopMatch k c (split 2 m k u).2 ↔ ∀ j < m + k, k ≤ j → ∀ b, c j = some b →
        bit u j = if b then 1 else 0 := by
    intro u
    constructor
    · intro H j hj hk b hb
      have := H ⟨j - k, by omega⟩ b (by simpa [show k + (j - k) = j by omega] using hb)
      rwa [split_snd_bit, show k + (j - k) = j by omega] at this
    · intro H j b hb; rw [split_snd_bit]; exact H _ (by omega) (by omega) b hb
  have hM : Match (m + k) tg c t ↔ (Match k tg c (rd (List.range k) t : State 2 k) ∧
      ∀ j < m + k, k ≤ j → ∀ b, c j = some b → bit t j = if b then 1 else 0) := by
    constructor
    · intro H
      refine ⟨fun j hj hjt b hb => ?_, fun j hj hk b hb => H j hj (fun hm => by
        have := htg j hm; omega) b hb⟩
      rw [bit_rd_range _ hj]; exact H j (by omega) hjt b hb
    · rintro ⟨H1, H2⟩ j hj hjt b hb
      by_cases hjk : j < k
      · have := H1 j hjk hjt b hb; rwa [bit_rd_range _ hjk] at this
      · exact H2 j hj (by omega) b hb
  have hloc : ∀ x y : State 2 (m + k), (∀ j < m + k, k ≤ j → bit x j = bit y j) →
      ((∀ j < m + k, j ∉ tg → bit x j = bit y j) ↔
        ∀ j < k, j ∉ tg → bit (rd (List.range k) x : State 2 k) j =
          bit (rd (List.range k) y : State 2 k) j) := by
    intro x y h1
    constructor
    · intro H j hj hjw; rw [bit_rd_range _ hj, bit_rd_range _ hj]; exact H j (by omega) hjw
    · intro H j hj hjw
      by_cases hjk : j < k
      · have := H j hjk hjw; rwa [bit_rd_range _ hjk, bit_rd_range _ hjk] at this
      · exact h1 j hj (by omega)
  have hsame : ∀ x y : State 2 (m + k),
      (rd (List.range k) x : State 2 k) = rd (List.range k) y ↔
        ((∀ j < k, j ∉ tg → bit (rd (List.range k) x : State 2 k) j =
          bit (rd (List.range k) y : State 2 k) j) ∧ (rd tg x : State 2 a) = rd tg y) := by
    intro x y
    constructor
    · intro e
      refine ⟨fun j _ _ => by rw [e], ?_⟩
      rw [← rd_rd_range htg ha x, ← rd_rd_range htg ha y, e]
    · rintro ⟨H, e⟩
      apply state_ext; intro j hj
      by_cases hjt : j ∈ tg
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hjt
        have := congrFun e ⟨i, by omega⟩
        simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some] at this
        rw [bit_rd_range _ hj, bit_rd_range _ hj]; exact this
      · exact H j hj hjt
  by_cases h1 : ∀ j < m + k, k ≤ j → bit s j = bit t j
  · rw [if_pos ((split_snd_eq_iff s t).2 h1)]
    simp only [hTop s, hM]
    have hct : (∀ j < m + k, k ≤ j → ∀ b, c j = some b → bit s j = if b then 1 else 0) ↔
        (∀ j < m + k, k ≤ j → ∀ b, c j = some b → bit t j = if b then 1 else 0) := by
      constructor
      · intro H j hj hk b hb; rw [← h1 j hj hk]; exact H j hj hk b hb
      · intro H j hj hk b hb; rw [h1 j hj hk]; exact H j hj hk b hb
    simp only [hct]
    by_cases h2 : ∀ j < m + k, j ∉ tg → bit s j = bit t j
    · rw [if_pos h2, if_pos ((hloc s t h1).1 h2)]
      by_cases h3 : ∀ j < m + k, k ≤ j → ∀ b, c j = some b → bit t j = if b then 1 else 0
      · rw [if_pos h3]; simp only [and_iff_left h3]
      · rw [if_neg h3, if_neg (fun h => h3 h.2)]
        by_cases h4 : (rd tg s : State 2 a) = rd tg t
        · rw [if_pos h4, if_pos ((hsame s t).2 ⟨(hloc s t h1).1 h2, h4⟩)]
        · rw [if_neg h4, if_neg (fun e => h4 ((hsame s t).1 e).2)]
    · rw [if_neg h2]
      by_cases h3 : ∀ j < m + k, k ≤ j → ∀ b, c j = some b → bit t j = if b then 1 else 0
      · rw [if_pos h3, if_neg (fun h => h2 ((hloc s t h1).2 h))]
      · rw [if_neg h3, if_neg (fun e => h2 ((hloc s t h1).2 ((hsame s t).1 e).1))]
  · rw [if_neg (fun h => h1 ((split_snd_eq_iff s t).1 h)), if_neg]
    intro H; exact h1 fun j hj hk => H j hj (fun hm => by have := htg j hm; omega)

/-- **The bulk form.**  A multi-controlled gate whose special wires are below
`k`, on `m + k` wires: on the blocks of the top `m` wires that match its
controls there, the same gate on `k` wires; the identity elsewhere. -/
theorem eval_mc_blk {m k : ℕ} {K : Kind} {tg : List ℕ} (c : ℕ → Option Bool) (hnd : tg.Nodup)
    (htg : ∀ j ∈ tg, j < k) (ha : tg.length = K.ar) :
    opsQ.eval (m + k) (mc (m + k) K tg c) =
      blk (m := m) (k := k) fun h => if TopMatch k c h then opsQ.eval k (mc k K tg c) else 1 := by
  rw [eval_mc c hnd (fun j hj => by have := htg j hj; omega) ha, eval_mc c hnd htg ha,
    lamOp_blk htg ha]

/-- A circuit on the bottom `k` wires is block diagonal above `k`. -/
theorem eval_pad_blk (m : ℕ) {k : ℕ} (w : Circ k) :
    opsQ.eval (m + k) (Circuit.pad m w) = blk (m := m) (k := k) fun _ => opsQ.eval k w := by
  rw [eval_pad, onBottom_eq_blk]

theorem eval_place1_blk {m k j : ℕ} (hj : j < k) (w : Circ 1) :
    opsQ.eval (m + k) (place1 (m + k) j w) =
      blk (m := m) (k := k) fun _ => opsQ.eval k (place1 k j w) := by
  rw [eval_place1 _ _ _ (by omega), eval_place1 _ _ _ hj,
    onW_blk (fun i hi => by rw [List.mem_singleton] at hi; omega) rfl]

theorem eval_place2_blk {m k j : ℕ} (hj : j + 2 ≤ k) (w : Circ 2) :
    opsQ.eval (m + k) (place2 (m + k) j w) =
      blk (m := m) (k := k) fun _ => opsQ.eval k (place2 k j w) := by
  rw [eval_place2 _ _ _ (by omega), eval_place2 _ _ _ hj,
    onW_blk (fun i hi => by simp at hi; omega) rfl]

theorem eval_placeG_blk {m k a : ℕ} (g : Circ a) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < k) (hlen : ps.length = a) :
    opsQ.eval (m + k) (placeG (m + k) g ps) =
      blk (m := m) (k := k) fun _ => opsQ.eval k (placeG k g ps) := by
  rw [eval_placeG g hnd (fun p hp => by have := hps p hp; omega) hlen, eval_placeG g hnd hps hlen,
    onW_blk hps hlen]

end QCert.RealCliffordCH.Sec8.MS
