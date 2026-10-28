/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemmas D.12–D.13: the kit

Tools for the commutations of Appendix D.7 (package (v) of `PLAN.md`).

* `Comm N a b`: the two gates commute; closed under derivable equality
  (`Comm.congr`), products (`comm_drawn`), inverses (`Comm.inv`) and
  conjugation (`Comm.conj`).
* The engine `SymEngine` reads multi-controlled letters with the bulk (the
  wires above the local ones) all black.  `wcX K N x l` reads them with the
  bulk coloured by `x`, and `colour_wc` carries a derivation between words
  to their coloured versions: conjugating by `X` on the white bulk wires
  colours the letters with bulk controls (`mc_colour`) and passes the
  others, which stay on the local wires (`lowW_mcL`, `lowW_lt`).
* Helpers on `X` gates and involutions (moved here from `N13.lean`).
-/
import QCert.RealCliffordCH.Sec8.D.N8.Anchors
import QCert.RealCliffordCH.Sec8.D.N8

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

/-- Two gates commute. -/
abbrev Comm (N : ℕ) (g₁ g₂ : Circ N) : Prop := Derivable (theory N) (drawn [g₁, g₂]) (drawn [g₂, g₁])

/-! ## Helpers -/

section Helpers

open Eng Net

/-- `X X = 1` on one wire, in letters ((1), (2)). -/
theorem xxL : Derivable (theory 1) (circW 1 [.H 0, .Z 0, .H 0, .H 0, .Z 0, .H 0]) (circW 1 []) := by
  have hT : AllD 1 [([.H 0, .H 0], []), ([.Z 0, .Z 0], [])] := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · have h := derivable_rule Rule.e1 0
      simpa [circW, drawn, map_mul, L.circ, place1] using h
    · have h := derivable_rule Rule.e2 0
      simpa [circW, drawn, map_mul, L.circ, place1] using h
  exact check_pure (N := 0) hT (ss := [.rw 2 0 false, .rw 1 1 false, .rw 0 0 false]) (by decide)
    (by decide)

/-- `X` is an involution, on any wire. -/
theorem xAt_inv (N q : ℕ) (hq : q < N) : Derivable (theory N) (xAt N q * xAt N q) 1 := by
  have h := lift_word (K := 1) (by decide) xxL q N (by omega)
  rw [xAt_eq]
  simpa [circW, drawn, mul_assoc, Nat.add_comm] using h

/-- A row of `X` gates on distinct wires is an involution. -/
theorem xs_inv (N : ℕ) (ws : List ℕ) (hnd : ws.Nodup) (hws : ∀ w ∈ ws, w < N) :
    Derivable (theory N) (drawn (ws.map (xAt N)) * drawn (ws.map (xAt N))) 1 := by
  have hp := xs_perm (N := N) (List.reverse_perm ws).symm hnd
  refine (dleft _ hp).trans ?_
  clear hp
  induction ws with
  | nil => simpa [drawn] using Derivable.refl (Γ := theory N) 1
  | cons w ws ih =>
    rw [List.map_cons, Net.drawn_cons, List.reverse_cons, List.map_append, List.map_singleton]
    have e : drawn (List.map (xAt N) ws.reverse ++ [xAt N w]) =
        xAt N w * drawn (ws.reverse.map (xAt N)) := by
      simp [drawn]
    rw [e]
    have e2 : drawn (ws.map (xAt N)) * xAt N w * (xAt N w * drawn (ws.reverse.map (xAt N))) =
        drawn (ws.map (xAt N)) * (xAt N w * xAt N w) * drawn (ws.reverse.map (xAt N)) := by
      simp only [mul_assoc]
    rw [e2]
    have h1 := dright (drawn (ws.reverse.map (xAt N))) (dleft (drawn (ws.map (xAt N)))
      (xAt_inv N w (hws w (by simp))))
    rw [mul_one] at h1
    exact h1.trans (ih (List.nodup_cons.1 hnd).2 (fun v hv => hws v (by simp [hv])))

/-- Two gates with the same colours: the colours cancel between them. -/
theorem colourW_mul (N : ℕ) (ws : List ℕ) (hnd : ws.Nodup) (hws : ∀ w ∈ ws, w < N)
    (A B : Circ N) :
    Derivable (theory N) (colourW N ws A * colourW N ws B) (colourW N ws (A * B)) := by
  rw [colourW_eq, colourW_eq, colourW_eq]
  have e : drawn (ws.map (xAt N)) * A * drawn (ws.map (xAt N)) *
      (drawn (ws.map (xAt N)) * B * drawn (ws.map (xAt N))) =
      drawn (ws.map (xAt N)) * A * (drawn (ws.map (xAt N)) * drawn (ws.map (xAt N))) * B *
        drawn (ws.map (xAt N)) := by simp only [mul_assoc]
  rw [e]
  have h := dright (drawn (ws.map (xAt N))) (dright B (dleft (drawn (ws.map (xAt N)) * A)
    (xs_inv N ws hnd hws)))
  rw [mul_one] at h
  simpa only [mul_assoc] using h

/-- Cancelling an involution in the middle of a word. -/
theorem cancel_mid {N : ℕ} {v : Circ N} (hv : Derivable (theory N) (v * v) 1) (a b : Circ N) :
    Derivable (theory N) (a * (v * v) * b) (a * b) := by
  have := dright b (dleft a hv)
  simpa only [mul_one] using this

/-- `u v u v` and `v u v u` are inverse when `u`, `v` are involutions. -/
theorem palin {N : ℕ} {u v : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (hv : Derivable (theory N) (v * v) 1) :
    Derivable (theory N) (u * v * u * v * (v * u * v * u)) 1 := by
  have e1 : u * v * u * v * (v * u * v * u) = (u * v * u) * (v * v) * (u * v * u) := by
    simp only [mul_assoc]
  rw [e1]; refine (cancel_mid hv _ _).trans ?_
  have e2 : u * v * u * (u * v * u) = (u * v) * (u * u) * (v * u) := by simp only [mul_assoc]
  rw [e2]; refine (cancel_mid hu _ _).trans ?_
  have e3 : u * v * (v * u) = u * (v * v) * u := by simp only [mul_assoc]
  rw [e3]; refine (cancel_mid hv _ _).trans ?_
  exact hu

theorem swap_inv (m : ℕ) : Derivable (theory (m + 2)) ((swap : Circ (m + 2)) * swap) 1 := by
  have h := derivable_rule Rule.g m
  simpa [drawn, map_mul] using h

theorem ch_inv (m : ℕ) : Derivable (theory (m + 2)) ((ch : Circ (m + 2)) * ch) 1 := by
  have h := derivable_rule Rule.e5 m
  simpa [drawn, map_mul] using h

/-- The control wires of a gate with a control on every non-special wire. -/
theorem ctrlWires_full (k s : ℕ) (c : ℕ → Option Bool)
    (hc : ∀ i, (c i).isSome = true ↔ s ≤ i ∧ i < k + s) :
    ctrlWires (k + s) (List.range s) c = List.range' s k := by
  refine eq_of_lt_mem ((List.pairwise_lt_range).filter _) List.pairwise_lt_range' (fun i => ?_)
  simp only [ctrlWires, List.mem_filter, List.mem_range, List.mem_range'_1, Bool.and_eq_true,
    Bool.not_eq_true', hc]
  constructor
  · rintro ⟨_, h1, _⟩; omega
  · intro h
    refine ⟨by omega, by omega, ?_⟩
    have : ¬ (List.range s).contains i = true := by
      rw [List.contains_iff_mem, List.mem_range]; omega
    simpa using this

/-- A gate with a control on every non-special wire is the coloured
canonical gate. -/
theorem mc_full (K : Kind) (k : ℕ) (c : ℕ → Option Bool)
    (hc : ∀ i, (c i).isSome = true ↔ kindSp K ≤ i ∧ i < k + kindSp K) :
    mc (k + kindSp K) K (List.range (kindSp K)) c =
      colourW (k + kindSp K) (whiteWires (k + kindSp K) (List.range (kindSp K)) c)
        (canonC K k) := by
  have hps : List.range (kindSp K) ++ List.range' (kindSp K) k = List.range (k + kindSp K) := by
    have h1 := @List.range'_append_1 0 (kindSp K) k
    rw [Nat.zero_add] at h1
    rw [List.range_eq_range', List.range_eq_range', h1, Nat.add_comm]
  simp only [mc, ctrlWires_full k _ c hc, List.length_range', hps, canonAt_eq, placeG_id]

theorem whiteWires_ok (N : ℕ) (tg : List ℕ) (c : ℕ → Option Bool) :
    (whiteWires N tg c).Nodup ∧ ∀ w ∈ whiteWires N tg c, w < N :=
  ⟨whiteWires_nodup N tg c, fun w hw => by
    simp only [whiteWires, List.mem_filter, List.mem_range] at hw; exact hw.1⟩

end Helpers

namespace N13

open Eng SE Net

/-! ## Commuting gates -/

section Comm

variable {N : ℕ}

theorem drawn_two (a b : Circ N) : drawn [a, b] = b * a := by simp [drawn]

theorem Comm.congr {a a' b b' : Circ N} (ha : Derivable (theory N) a a')
    (hb : Derivable (theory N) b b') (h : Comm N a b) : Comm N a' b' := by
  unfold Comm at *
  rw [drawn_two, drawn_two] at *
  exact (dmul hb.symm ha.symm).trans (h.trans (dmul ha hb))

theorem Comm.mul_left {a b c : Circ N} (ha : Comm N a c) (hb : Comm N b c) :
    Comm N (a * b) c := by
  unfold Comm at *
  rw [drawn_two, drawn_two] at *
  have h1 : Derivable (theory N) (c * (a * b)) (a * (c * b)) := by
    rw [← mul_assoc, show a * (c * b) = (a * c) * b by rw [mul_assoc]]
    exact dright b ha
  refine h1.trans ?_
  rw [mul_assoc]; exact dleft a hb

theorem comm_one (c : Circ N) : Comm N 1 c := by
  unfold Comm; rw [drawn_two, drawn_two, mul_one, one_mul]

theorem comm_drawn_left {c : Circ N} : ∀ (l : List (Circ N)), (∀ a ∈ l, Comm N a c) →
    Comm N (drawn l) c
  | [], _ => by simpa [drawn] using comm_one c
  | a :: l, h => by
    rw [Net.drawn_cons]
    exact Comm.mul_left (comm_drawn_left l (fun b hb => h b (by simp [hb]))) (h a (by simp))

/-- Two products commute when their factors do. -/
theorem comm_drawn (l₁ l₂ : List (Circ N)) (h : ∀ a ∈ l₁, ∀ b ∈ l₂, Comm N a b) :
    Comm N (drawn l₁) (drawn l₂) :=
  comm_drawn_left l₁ fun a ha => (comm_drawn_left l₂ fun b hb => (h a ha b hb).symm).symm

/-- A gate commuting with `a` commutes with an inverse of `a` (Lemma B.5). -/
theorem Comm.inv {a a' b : Circ N} (h : Comm N a b) (h1 : Derivable (theory N) (a * a') 1)
    (h2 : Derivable (theory N) (a' * a) 1) : Comm N a' b := by
  unfold Comm at *
  rw [drawn_two, drawn_two] at *
  have e1 : Derivable (theory N) (b * a') (a' * (a * b) * a') := by
    have := dright (b * a') h2.symm
    rw [one_mul] at this
    have e : a' * a * (b * a') = a' * (a * b) * a' := by simp only [mul_assoc]
    rwa [e] at this
  refine e1.trans ?_
  have e2 : Derivable (theory N) (a' * (a * b) * a') (a' * (b * a) * a') := dright _ (dleft _ h.symm)
  refine e2.trans ?_
  have e3 : a' * (b * a) * a' = a' * b * (a * a') := by simp only [mul_assoc]
  rw [e3]
  have := dleft (a' * b) h1
  rwa [mul_one] at this

/-- Conjugation preserves commutation. -/
theorem Comm.conj {a b u v : Circ N} (h : Comm N a b) (hvu : Derivable (theory N) (v * u) 1) :
    Comm N (u * a * v) (u * b * v) := by
  unfold Comm at *
  rw [drawn_two, drawn_two] at *
  have e1 : u * b * v * (u * a * v) = u * b * (v * u) * a * v := by simp only [mul_assoc]
  have e2 : u * a * v * (u * b * v) = u * a * (v * u) * b * v := by simp only [mul_assoc]
  rw [e1, e2]
  have k1 : Derivable (theory N) (u * b * (v * u) * a * v) (u * (b * a) * v) := by
    have := dright v (dright a (dleft (u * b) hvu))
    simpa only [mul_one, mul_assoc] using this
  have k2 : Derivable (theory N) (u * a * (v * u) * b * v) (u * (a * b) * v) := by
    have := dright v (dright b (dleft (u * a) hvu))
    simpa only [mul_one, mul_assoc] using this
  exact k1.trans ((dctx u v h).trans k2.symm)

end Comm

/-! ## Words and gates -/

theorem wc_two (K N : ℕ) (x y : Lt) : wc K N [x, y] = drawn [x.circ K N, y.circ K N] := rfl

theorem wc_one' (K N : ℕ) (x : Lt) : wc K N [x] = x.circ K N := by simp [wc, drawn]

/-- A run of two letters exchanged is a commutation. -/
theorem comm_of_wc {K N : ℕ} {x y : Lt} (h : Derivable (theory N) (wc K N [x, y]) (wc K N [y, x])) :
    Comm N (x.circ K N) (y.circ K N) := h

theorem all_two {P : Lt → Prop} {x y : Lt} (hx : P x) (hy : P y) : ∀ g ∈ [x, y], P g := by
  intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl <;> assumption

/-- `X` on wire `q`, as three letters. -/
def xL (q : ℕ) : List Lt := [.s (.H q), .s (.Z q), .s (.H q)]

theorem wc_xconj (K N q : ℕ) (g : Lt) :
    wc K N (xL q ++ [g] ++ xL q) = xAt N q * g.circ K N * xAt N q := by
  simp [wc, xL, drawn, xAt_eq, circW, mul_assoc, Lt.circ]

theorem wc_xconj2 (K N q : ℕ) (g h : Lt) :
    wc K N (xL q ++ [g, h] ++ xL q) = xAt N q * (h.circ K N * g.circ K N) * xAt N q := by
  simp [wc, xL, drawn, xAt_eq, circW, mul_assoc, Lt.circ]

/-- Conjugating a commutation by an involution `u`. -/
theorem comm_flip {N : ℕ} {a b a' b' u : Circ N} (h : Comm N a b)
    (hu : Derivable (theory N) (u * u) 1) (ha : Derivable (theory N) (u * a * u) a')
    (hb : Derivable (theory N) (u * b * u) b') : Comm N a' b' :=
  Comm.congr ha hb (Comm.conj h hu)

/-- Pointwise equality of control functions: the wires `0, …, 5` one by one,
the others by `omega`. -/
macro "ctl_tac" : tactic => `(tactic| (intro i hi; rcases i with _ | _ | _ | _ | _ | _ | i <;>
  (simp only [ctl, ctlX, ctlOr, ctlAt, blackOn, colOn, setCtl]) <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | simp_all | omega))

/-! ## The local wires stay below -/

theorem lowW_mono {n m m' : ℕ} {u : Circ n} (h : LowW m u) (hm : m ≤ m') : LowW m' u :=
  fun g hg => le_trans (h g hg) hm

theorem lowW_padTop' {M m : ℕ} {X : Circ M} (h : LowW m X) : LowW m (padTop X) := by
  intro g hg
  simp only [padTop, FreeMonoid.toList_map, List.mem_map] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  rw [gHi_padTop]; exact h y hy

theorem lowW_self {M : ℕ} (X : Circ M) : LowW M X := fun g _ => gHi_le g

/-- A multi-controlled letter without bulk controls stays on the local wires. -/
theorem lowW_mcL {K : ℕ} (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool))
    (hx : (Lt.g Kd tg cs false).ok K = true) :
    ∀ N, K ≤ N → LowW K (mc N Kd tg (ctl K cs false)) := by
  simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
  obtain ⟨⟨hnd, hlt⟩, ha⟩ := hx
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact lowW_self _
  | succ M hM ih =>
    rw [mc_top M Kd tg _ (by rw [← kindSp_eq]; exact ha) hnd
      (fun t ht => by have := hlt t ht; simp at this; omega)
      (by simp [ctl, show ¬ M < K by omega])]
    exact lowW_padTop' ih

/-- A letter without bulk controls stays on the local wires. -/
theorem lowW_lt {K : ℕ} (x : Lt) (hx : x.ok K = true) (hb : ∀ Kd tg cs, x ≠ .g Kd tg cs true) :
    ∀ N, K ≤ N → LowW K (x.circ K N) := by
  intro N hN
  cases x with
  | s l =>
    simp only [Lt.ok, decide_eq_true_eq] at hx
    exact lowW_mono (lowW_letter N l) hx
  | g Kd tg cs b =>
    cases b
    · exact lowW_mcL Kd tg cs hx N hN
    · exact absurd rfl (hb Kd tg cs)

/-- A multi-controlled gate without controls above `k` is at the bottom. -/
theorem mc_atBot {k : ℕ} (Kd : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (htg : tg.length = kindSp Kd)
    (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < k) (hc : ∀ j, k ≤ j → c j = none) :
    ∀ N, k ≤ N → mc N Kd tg c = atBot N (mc k Kd tg c) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [atBot_self]
  | succ M hM ih =>
    rw [mc_top M Kd tg c htg hnd (fun t ht => by have := hlt t ht; omega) (hc M hM), ih,
      atBot_succ M _ (by omega)]

/-! ## Colouring the bulk -/

/-- The controls of a multi-controlled letter with the bulk coloured by `x`. -/
def ctlX (K : ℕ) (cs : List (ℕ × Bool)) (x : ℕ → Bool) : ℕ → Option Bool :=
  fun j => if j < K then cs.lookup j else some (x j)

/-- A letter read with the bulk coloured by `x`. -/
def cX (K N : ℕ) (x : ℕ → Bool) : Lt → Circ N
  | .s l => l.circ N
  | .g Kd tg cs b => if b then mc N Kd tg (ctlX K cs x) else mc N Kd tg (ctl K cs false)

/-- A word read with the bulk coloured by `x`. -/
def wcX (K N : ℕ) (x : ℕ → Bool) (l : List Lt) : Circ N := drawn (l.map (cX K N x))

/-- `X` on the wires `ws`, all controls of colour black, colours them white. -/
theorem mc_colour (N : ℕ) (Kd : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (ws : List ℕ)
    (hnd : ws.Nodup) (hws : ∀ j ∈ ws, j < N ∧ j ∉ tg ∧ c j = some true) :
    Derivable (theory N) (colourW N ws (mc N Kd tg c))
      (mc N Kd tg (fun j => if j ∈ ws then some false else c j)) := by
  set c' : ℕ → Option Bool := fun j => if j ∈ ws then some false else c j
  have hctl : ctrlWires N tg c' = ctrlWires N tg c := by
    unfold ctrlWires
    refine List.filter_congr (fun j _ => ?_)
    by_cases h : j ∈ ws
    · simp only [c', if_pos h, (hws j h).2.2]; rfl
    · simp only [c', if_neg h]
  have hW : (whiteWires N tg c').Perm (whiteWires N tg c ++ ws) := by
    refine (List.perm_ext_iff_of_nodup (whiteWires_nodup N tg c') ?_).2 (fun j => ?_)
    · refine List.nodup_append.2 ⟨whiteWires_nodup N tg c, hnd, fun a ha b hb hab => ?_⟩
      subst hab
      rw [MS.mem_whiteWires] at ha
      rw [(hws a hb).2.2] at ha
      exact absurd ha.2.1 (by simp)
    · rw [List.mem_append, MS.mem_whiteWires, MS.mem_whiteWires]
      by_cases h : j ∈ ws
      · simp [c', h, (hws j h).1, (hws j h).2.1]
      · simp only [c', if_neg h, h, or_false]
  set G := canonAt N Kd (ctrlWires N tg c).length (tg ++ ctrlWires N tg c)
  have hmc : mc N Kd tg c = colourW N (whiteWires N tg c) G := rfl
  have hmc' : mc N Kd tg c' = colourW N (whiteWires N tg c') G := by
    show colourW N (whiteWires N tg c')
      (canonAt N Kd (ctrlWires N tg c').length (tg ++ ctrlWires N tg c')) = _
    rw [hctl]
  rw [hmc, hmc', colourW_eq, colourW_eq, colourW_eq]
  have hndW' := whiteWires_nodup N tg c'
  have hp := xs_perm (N := N) hW hndW'
  rw [List.map_append, drawn_append] at hp
  set Dw := drawn ((whiteWires N tg c).map (xAt N))
  set Ds := drawn (ws.map (xAt N))
  -- `Ds * Dw` and `Dw * Ds` agree
  have hndWs : (whiteWires N tg c ++ ws).Nodup := hW.nodup_iff.1 hndW'
  have hsw : Derivable (theory N) (Dw * Ds) (Ds * Dw) := by
    have h := xs_perm (N := N) (List.perm_append_comm (l₁ := whiteWires N tg c) (l₂ := ws)) hndWs
    rw [List.map_append, drawn_append, List.map_append, drawn_append] at h
    exact h.symm
  have e : Ds * (Dw * G * Dw) * Ds = Ds * Dw * G * (Dw * Ds) := by simp only [mul_assoc]
  rw [e]
  exact (dmul (Derivable.refl _) hsw).trans (dmul (dright _ hp.symm) hp.symm)

/-- The white bulk wires of `x` on `N` wires, local width `K`. -/
def whiteBulk (K N : ℕ) (x : ℕ → Bool) : List ℕ := (List.range N).filter fun j => K ≤ j && !x j

theorem whiteBulk_nodup (K N : ℕ) (x : ℕ → Bool) : (whiteBulk K N x).Nodup :=
  (List.nodup_range).filter _

theorem mem_whiteBulk {K N : ℕ} {x : ℕ → Bool} {j : ℕ} :
    j ∈ whiteBulk K N x ↔ j < N ∧ K ≤ j ∧ x j = false := by
  simp [whiteBulk, List.mem_filter, List.mem_range]

theorem highW_drawn {n m : ℕ} : ∀ (l : List (Circ n)), (∀ a ∈ l, HighW m a) → HighW m (drawn l)
  | [], _ => by intro g hg; simp [drawn] at hg
  | a :: l, h => by
    rw [Net.drawn_cons]
    exact highW_mul (highW_drawn l (fun b hb => h b (by simp [hb]))) (h a (by simp))

/-- One letter, conjugated by `X` on the white bulk wires, is its coloured
version. -/
theorem letter_colour {K N : ℕ} (hKN : K ≤ N) (x : ℕ → Bool) (g : Lt) (hg : g.ok K = true) :
    Derivable (theory N) (colourW N (whiteBulk K N x) (g.circ K N)) (cX K N x g) := by
  have hnd := whiteBulk_nodup K N x
  have hlt : ∀ w ∈ whiteBulk K N x, w < N := fun w hw => (mem_whiteBulk.1 hw).1
  set D := drawn ((whiteBulk K N x).map (xAt N))
  have high : HighW K D := highW_drawn _ (fun a ha => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    intro y hy
    have := (xAt_wires N w).2 y hy
    have := (mem_whiteBulk.1 hw).2.1
    omega)
  have pass : ∀ u : Circ N, LowW K u → Derivable (theory N) (colourW N (whiteBulk K N x) u) u := by
    intro u hu
    rw [colourW_eq]
    have h1 : Derivable (theory N) (D * u * D) (u * (D * D)) := by
      have := dright D (comm_low_high u D hu high); rwa [mul_assoc u] at this
    refine h1.trans ?_
    have := dleft u (xs_inv N _ hnd hlt)
    rwa [mul_one] at this
  cases g with
  | s l =>
    simp only [Lt.ok, decide_eq_true_eq] at hg
    exact pass _ (lowW_mono (lowW_letter N l) hg)
  | g Kd tg cs b =>
    cases b
    · exact pass _ (lowW_mcL Kd tg cs hg N hKN)
    · have hg' := hg
      simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hg'
      obtain ⟨⟨_, htg⟩, _⟩ := hg'
      have h := mc_colour N Kd tg (ctl K cs true) (whiteBulk K N x) hnd (fun j hj => by
        obtain ⟨h1, h2, _⟩ := mem_whiteBulk.1 hj
        refine ⟨h1, fun ht => ?_, by simp [ctl, show ¬ j < K by omega]⟩
        have := htg j ht; simp at this; omega)
      refine h.trans (der_of_eq (mc_congr N Kd tg (fun i hi => ?_)))
      simp only [ctlX, ctl, mem_whiteBulk]
      by_cases hik : i < K
      · simp [hik, show ¬ K ≤ i by omega]
      · simp only [hik, if_false, if_true]
        by_cases hx : x i
        · simp [hx]
        · simp [hx, hi, show K ≤ i by omega]

/-- A derivation between words, with the bulk coloured by `x`. -/
theorem colour_wc {K N : ℕ} (hKN : K ≤ N) (x : ℕ → Bool) {l r : List Lt}
    (hl : ∀ g ∈ l, g.ok K = true) (hr : ∀ g ∈ r, g.ok K = true)
    (d : Derivable (theory N) (wc K N l) (wc K N r)) :
    Derivable (theory N) (wcX K N x l) (wcX K N x r) := by
  have hnd := whiteBulk_nodup K N x
  have hlt : ∀ w ∈ whiteBulk K N x, w < N := fun w hw => (mem_whiteBulk.1 hw).1
  set D := drawn ((whiteBulk K N x).map (xAt N))
  have hDD := xs_inv N _ hnd hlt
  have word : ∀ l : List Lt, (∀ g ∈ l, g.ok K = true) →
      Derivable (theory N) (D * wc K N l * D) (wcX K N x l) := by
    intro l hl
    induction l with
    | nil =>
      simp only [wc, wcX, List.map_nil, drawn, List.reverse_nil, List.prod_nil, mul_one]
      exact hDD
    | cons g l ih =>
      rw [wc_cons]
      simp only [wcX, List.map_cons, Net.drawn_cons]
      refine (conj_mul hDD).trans (dmul (ih (fun y hy => hl y (by simp [hy]))) ?_)
      have := letter_colour hKN x g (hl g (by simp))
      rwa [colourW_eq] at this
  exact (word l hl).symm.trans ((dctx D D d).trans (word r hr))

end N13

end QCert.RealCliffordCH.Sec8.D
