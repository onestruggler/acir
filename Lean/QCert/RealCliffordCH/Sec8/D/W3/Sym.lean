/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symmetries of token equations (packages (i)–(iii))

Equations between words of `WEng` tokens are carried to other placements
without new derivations:

* `relabel`: an equation conjugated by a swap network, token by token —
  every token relabelled through the transpositions (`rlS`): a placed word
  (`Net.placeG_swap`), a multi-controlled gate (`Net.mc_swap`, and
  `Net.mc_swap_sym` when two controls are exchanged, given the symmetry
  `CanonSym` of the canonical gate), a letter through its placed form
  (`toP`, `Net.place1_placeG`, `Net.place2_placeG`);
* `x81`: `X` on a control on both sides of a multi-controlled gate exchanges
  its colour (Equation (81), `D.eq81'`), with `X` written as a placed token;
* `swq`: a token conjugated by one swap is its relabelled form.

Each is stated for table entries of `WEng` (`rel_entry`, `x81_entry`,
`swq_entry`), the side conditions decided by a Boolean.  `canonSym_small`
gives `CanonSym` below the full width from completeness (Lemma 5.1).
-/
import QCert.RealCliffordCH.Sec8.D.WEng
import QCert.RealCliffordCH.Sec8.D.Colour

namespace QCert.RealCliffordCH.Sec8.WS

open Circuit Eng Net WE

/-! ## Letters as placed tokens -/

/-- A letter as a placed token. -/
def toP : L → Tk
  | .H j => .p 1 [.H 0] [j]
  | .Z j => .p 1 [.Z 0] [j]
  | .C j => .p 2 [.C 0] [j, j + 1]
  | .K j => .p 2 [.K 0] [j, j + 1]
  | .S j => .p 2 [.S 0] [j, j + 1]

theorem circW1 (g : Circ 1) (l : L) (hl : l.circ 1 = place1 1 0 g) : circW 1 [l] = g := by
  simp only [circW, drawn, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.prod_cons, List.prod_nil, mul_one, hl]
  exact pad_zero1 g

theorem circW2 (g : Circ 2) (l : L) (hl : l.circ 2 = place2 2 0 g) : circW 2 [l] = g := by
  simp only [circW, drawn, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.prod_cons, List.prod_nil, mul_one, hl]
  exact pad_zero2 g

theorem toP_sound {N : ℕ} (l : L) (hl : l.lo + l.wd ≤ N) :
    Derivable (theory N) (l.circ N) ((toP l).circ N) := by
  cases l with
  | H j =>
    show Derivable (theory N) (place1 N j h) (placeG N (circW 1 [L.H 0]) [j])
    rw [circW1 h (L.H 0) rfl]
    exact place1_placeG h N j (by simp [L.lo, L.wd] at hl; omega)
  | Z j =>
    show Derivable (theory N) (place1 N j z) (placeG N (circW 1 [L.Z 0]) [j])
    rw [circW1 z (L.Z 0) rfl]
    exact place1_placeG z N j (by simp [L.lo, L.wd] at hl; omega)
  | C j =>
    show Derivable (theory N) (place2 N j cz) (placeG N (circW 2 [L.C 0]) [j, j + 1])
    rw [circW2 cz (L.C 0) rfl]
    exact place2_placeG cz N j (by simp [L.lo, L.wd] at hl; omega)
  | K j =>
    show Derivable (theory N) (place2 N j ch) (placeG N (circW 2 [L.K 0]) [j, j + 1])
    rw [circW2 ch (L.K 0) rfl]
    exact place2_placeG ch N j (by simp [L.lo, L.wd] at hl; omega)
  | S j =>
    show Derivable (theory N) (place2 N j swap) (placeG N (circW 2 [L.S 0]) [j, j + 1])
    rw [circW2 swap (L.S 0) rfl]
    exact place2_placeG swap N j (by simp [L.lo, L.wd] at hl; omega)

/-! ## Relabelling by one adjacent transposition -/

/-- The token conjugated by the swap of wires `j, j + 1`. -/
def rl1 (j : ℕ) : Tk → Tk
  | .s l => match toP l with
    | .p m w ps => .p m w (ps.map (Net.tau j))
    | t => t
  | .g Kd tg cs => .g Kd (tg.map (Net.tau j)) (cs.map fun p => (Net.tau j p.1, p.2))
  | .p m w ps => .p m w (ps.map (Net.tau j))

/-- The swap of wires `j, j + 1` exchanges two controls of the gate. -/
def bothCtl (N j : ℕ) (tg : List ℕ) (cs : List (ℕ × Bool)) : Bool :=
  decide (j ∈ ctrlWires N tg (SE.ctl N cs false)) &&
    decide (j + 1 ∈ ctrlWires N tg (SE.ctl N cs false))

/-- The side conditions of `rl1`: the symmetries `avail` of the canonical
gates are used when two controls are exchanged. -/
def rlOK (N j : ℕ) (avail : Kind → ℕ → Bool) : Tk → Bool
  | .g Kd tg cs => decide (j + 2 ≤ N) && (Tk.g Kd tg cs).ok N &&
      (!(bothCtl N j tg cs) || avail Kd (ctrlWires N tg (SE.ctl N cs false)).length)
  | t => decide (j + 2 ≤ N) && t.ok N

theorem lookup_map_inj {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ (cs : List (ℕ × Bool)) (x : ℕ),
      (cs.map fun p => (f p.1, p.2)).lookup (f x) = cs.lookup x
  | [], _ => rfl
  | (a, b) :: cs, x => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases h : x = a
    · subst h; simp
    · have : (f x == f a) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => h (hf e)
      have h2 : (x == a) = false := by simp [h]
      rw [this, h2]
      exact lookup_map_inj hf cs x

theorem tau_inj (j : ℕ) : Function.Injective (Net.tau j) := fun a b h => by
  have := congrArg (Net.tau j) h; rwa [Net.tau_tau, Net.tau_tau] at this

theorem ctl_rl1 {N j : ℕ} (hj : j + 2 ≤ N) (cs : List (ℕ × Bool)) :
    ∀ i < N, (SE.ctl N cs false ∘ Net.tau j) i = SE.ctl N (cs.map fun p => (Net.tau j p.1, p.2)) false i := by
  intro i hi
  simp only [Function.comp, SE.ctl, if_pos hi, if_pos (Net.tau_lt hj hi)]
  rw [← lookup_map_inj (tau_inj j) cs (Net.tau j i), Net.tau_tau]

variable {N : ℕ} {avail : Kind → ℕ → Bool}

theorem circ_g (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool)) :
    (Tk.g Kd tg cs).circ N = mc N Kd tg (SE.ctl N cs false) := rfl

theorem rl1_g (j : ℕ) (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool)) :
    rl1 j (Tk.g Kd tg cs) = Tk.g Kd (tg.map (Net.tau j)) (cs.map fun p => (Net.tau j p.1, p.2)) :=
  rfl

theorem rl1_sound (havail : ∀ K k, avail K k = true → CanonSym K k) (j : ℕ) (t : Tk)
    (h : rlOK N j avail t = true) :
    Derivable (theory N) (drawn [swAt N j, t.circ N, swAt N j]) ((rl1 j t).circ N) := by
  cases t with
  | s l =>
    simp only [rlOK, Tk.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hj, hl⟩ := h
    have h1 := toP_sound l hl
    have hc : Derivable (theory N) (drawn [swAt N j, (Tk.s l).circ N, swAt N j])
        (drawn [swAt N j, (toP l).circ N, swAt N j]) := by
      simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.prod_cons, List.prod_nil, mul_one]
      exact dleft _ (dright _ h1)
    refine hc.trans ?_
    cases l with
    | H i => exact placeG_swap _ (by simp) (fun p hp => by simp [L.lo, L.wd] at hp hl; omega) rfl j hj
    | Z i => exact placeG_swap _ (by simp) (fun p hp => by simp [L.lo, L.wd] at hp hl; omega) rfl j hj
    | C i => exact placeG_swap _ (by simp) (fun p hp => by simp [L.lo, L.wd] at hp hl; omega) rfl j hj
    | K i => exact placeG_swap _ (by simp) (fun p hp => by simp [L.lo, L.wd] at hp hl; omega) rfl j hj
    | S i => exact placeG_swap _ (by simp) (fun p hp => by simp [L.lo, L.wd] at hp hl; omega) rfl j hj
  | p m w ps =>
    simp only [rlOK, Tk.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at h
    obtain ⟨hj, ⟨⟨⟨hnd, hlt⟩, hm⟩, -⟩⟩ := h
    exact placeG_swap (circW m w) hnd (fun p hp => by simpa using hlt p hp) hm j hj
  | g Kd tg cs =>
    simp only [rlOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨hj, hok⟩, hb⟩ := h
    have hok' := hok
    simp only [Tk.ok, SE.Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at hok'
    obtain ⟨⟨hnd, hlt⟩, ha⟩ := hok'
    have ha' : tg.length = kindSp Kd := by rw [← SE.kindSp_eq]; exact ha
    have hlt' : ∀ t ∈ tg, t < N := fun t ht => by simpa using hlt t ht
    rw [circ_g, rl1_g, circ_g, ← mc_congr N Kd (tg.map (Net.tau j)) (ctl_rl1 hj cs)]
    by_cases hbc : j ∈ ctrlWires N tg (SE.ctl N cs false) ∧
        j + 1 ∈ ctrlWires N tg (SE.ctl N cs false)
    · have hb' : bothCtl N j tg cs = true := by
        simp only [bothCtl, Bool.and_eq_true, decide_eq_true_eq]; exact hbc
      rcases hb with hb | hb
      · rw [hb'] at hb; exact absurd hb (by decide)
      · exact mc_swap_sym N j hj Kd tg _ ha' hnd hlt' (havail _ _ hb)
    · exact mc_swap N j hj Kd tg _ ha' hnd hlt' hbc

theorem rlOK_hj {j : ℕ} {t : Tk} (h : rlOK N j avail t = true) : j + 2 ≤ N := by
  cases t <;> simp only [rlOK, Bool.and_eq_true, decide_eq_true_eq] at h <;>
    first | exact h.1 | exact h.1.1

/-- A word conjugated by one swap, token by token. -/
theorem conjW (havail : ∀ K k, avail K k = true → CanonSym K k) (j : ℕ) (hj : j + 2 ≤ N) :
    ∀ (l : List Tk), (∀ t ∈ l, rlOK N j avail t = true) →
      Derivable (theory N) (swAt N j * wcT N l * swAt N j) (wcT N (l.map (rl1 j)))
  | [], _ => by
    simp only [wcT, List.map_nil, drawn, List.reverse_nil, List.prod_nil, mul_one]
    exact swsw N j hj
  | x :: l, hl => by
    rw [wcT_cons, List.map_cons, wcT_cons]
    have ih := conjW havail j hj l (fun t ht => hl t (List.mem_cons_of_mem _ ht))
    have hx := rl1_sound havail j x (hl x List.mem_cons_self)
    simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons, List.prod_nil, mul_one] at hx
    have e : swAt N j * (wcT N l * x.circ N) * swAt N j =
        (swAt N j * wcT N l) * 1 * (x.circ N * swAt N j) := by simp only [mul_one, mul_assoc]
    rw [e]
    have hs := (swsw N j hj).symm
    refine (dctx (swAt N j * wcT N l) (x.circ N * swAt N j) hs).trans ?_
    have e2 : swAt N j * wcT N l * (swAt N j * swAt N j) * (x.circ N * swAt N j) =
        (swAt N j * wcT N l * swAt N j) * (swAt N j * x.circ N * swAt N j) := by
      simp only [mul_assoc]
    rw [e2]
    exact dmul ih (by simpa only [mul_assoc] using hx)

/-- An equation conjugated by one swap. -/
theorem rel1 (havail : ∀ K k, avail K k = true → CanonSym K k) (j : ℕ) (hj : j + 2 ≤ N)
    {l r : List Tk} (hl : ∀ t ∈ l, rlOK N j avail t = true) (hr : ∀ t ∈ r, rlOK N j avail t = true)
    (d : Derivable (theory N) (wcT N l) (wcT N r)) :
    Derivable (theory N) (wcT N (l.map (rl1 j))) (wcT N (r.map (rl1 j))) :=
  (conjW havail j hj l hl).symm.trans ((dctx _ _ d).trans (conjW havail j hj r hr))

/-! ## Relabelling by a swap network -/

/-- Relabelling through the transpositions of `σ`, the first first. -/
def rlS : List ℕ → Tk → Tk
  | [], t => t
  | j :: σ, t => rlS σ (rl1 j t)

/-- The side conditions of `rlS`. -/
def rlSOK (N : ℕ) (avail : Kind → ℕ → Bool) : List ℕ → Tk → Bool
  | [], _ => true
  | j :: σ, t => rlOK N j avail t && rlSOK N avail σ (rl1 j t)

theorem relS (havail : ∀ K k, avail K k = true → CanonSym K k) :
    ∀ (σ : List ℕ) {l r : List Tk}, (∀ t ∈ l ++ r, rlSOK N avail σ t = true) →
      Derivable (theory N) (wcT N l) (wcT N r) →
      Derivable (theory N) (wcT N (l.map (rlS σ))) (wcT N (r.map (rlS σ)))
  | [], l, r, _, d => by simpa [rlS] using d
  | j :: σ, l, r, h, d => by
    have hh : ∀ t ∈ l ++ r, rlOK N j avail t = true ∧ rlSOK N avail σ (rl1 j t) = true := by
      intro t ht; have := h t ht; simp only [rlSOK, Bool.and_eq_true] at this; exact this
    have d1 : Derivable (theory N) (wcT N (l.map (rl1 j))) (wcT N (r.map (rl1 j))) := by
      by_cases hn : l ++ r = []
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hn
        simpa using d
      · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hn
        exact rel1 havail j (rlOK_hj (hh t ht).1) (fun t ht => (hh t (List.mem_append_left _ ht)).1)
          (fun t ht => (hh t (List.mem_append_right _ ht)).1) d
    have d2 := relS havail σ (l := l.map (rl1 j)) (r := r.map (rl1 j)) (fun t ht => by
      rw [← List.map_append] at ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
      exact (hh u hu).2) d1
    simpa only [List.map_map, Function.comp_def, rlS] using d2

/-- A relabelled table entry: `l' = rlS σ l`, `r' = rlS σ r`. -/
theorem rel_entry (havail : ∀ K k, avail K k = true → CanonSym K k) (σ : List ℕ)
    {l r l' r' : List Tk}
    (h : (l.map (rlS σ) == l' && r.map (rlS σ) == r' && (l ++ r).all (rlSOK N avail σ)) = true)
    (d : Derivable (theory N) (wcT N l) (wcT N r)) :
    Derivable (theory N) (wcT N l') (wcT N r') := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, hok⟩ := h
  exact relS havail σ hok d

/-- One swap around a token: `[S j, t, S j] = [rl1 j t]`. -/
theorem swq_entry (havail : ∀ K k, avail K k = true → CanonSym K k) (j : ℕ) {t t' : Tk}
    (h : (rl1 j t == t' && rlOK N j avail t) = true) :
    Derivable (theory N) (wcT N [.s (.S j), t, .s (.S j)]) (wcT N [t']) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hok⟩ := h
  have e1 : wcT N [.s (.S j), t, .s (.S j)] = drawn [swAt N j, t.circ N, swAt N j] := rfl
  have e2 : wcT N [rl1 j t] = (rl1 j t).circ N := by simp [wcT, drawn]
  rw [e1, e2]
  exact rl1_sound havail j t hok

/-! ## Colours: Equation (81) -/

/-- `X` on wire `w`, as a placed token. -/
def xT (w : ℕ) : Tk := .p 1 [.H 0, .Z 0, .H 0] [w]

theorem xT_circ (w : ℕ) (hw : w < N) : Derivable (theory N) ((xT w).circ N) (xAt N w) := by
  have e : circW 1 [L.H 0, L.Z 0, L.H 0] = (x : Circ 1) := by
    simp only [circW, drawn, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
    show Circuit.pad 0 h * (Circuit.pad 0 z * Circuit.pad 0 h) = x
    rw [pad_zero1, pad_zero1]
    simp [x, drawn]
  show Derivable (theory N) (placeG N (circW 1 [L.H 0, L.Z 0, L.H 0]) [w]) (xAt N w)
  rw [e]
  exact (place1_placeG x N w hw).symm

/-- The side conditions of `x81_entry`: `w` a control of the gate, coloured `b`,
and `cs'` the same controls with the colour of `w` exchanged. -/
def x81OK (N w : ℕ) (Kd : Kind) (tg : List ℕ) (cs cs' : List (ℕ × Bool)) : Bool :=
  decide (w < N) && !(tg.contains w) && (Tk.g Kd tg cs).ok N &&
    match SE.ctl N cs false w with
    | some b => (List.range N).all fun i =>
        SE.ctl N cs' false i == setCtl (SE.ctl N cs false) w (some !b) i
    | none => false

/-- Equation (81): `X` on a control on both sides of a multi-controlled gate. -/
theorem x81_entry (w : ℕ) (Kd : Kind) (tg : List ℕ) (cs cs' : List (ℕ × Bool))
    (h : x81OK N w Kd tg cs cs' = true) :
    Derivable (theory N) (wcT N [xT w, .g Kd tg cs, xT w]) (wcT N [.g Kd tg cs']) := by
  simp only [x81OK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hw, htg⟩, -⟩, hc⟩ := h
  have htg' : w ∉ tg := by simpa using htg
  generalize hb : SE.ctl N cs false w = ob at hc
  cases ob with
  | none => exact absurd hc (by simp)
  | some b =>
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    have e1 : wcT N [xT w, .g Kd tg cs, xT w] =
        drawn [(xT w).circ N, mc N Kd tg (SE.ctl N cs false), (xT w).circ N] := rfl
    have e2 : wcT N [.g Kd tg cs'] = mc N Kd tg (SE.ctl N cs' false) := by simp [wcT, drawn, Tk.circ]
    rw [e1, e2, mc_congr N Kd tg hc]
    have hx := xT_circ (N := N) w hw
    have h81 := D.eq81' N Kd tg (SE.ctl N cs false) w b hw htg' hb
    refine Derivable.trans ?_ h81
    simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons, List.prod_nil, mul_one]
    exact dmul hx (dmul (Derivable.refl _) hx)

/-- The controls of a gate written in another order. -/
theorem g_entry (Kd : Kind) (tg : List ℕ) (cs cs' : List (ℕ × Bool))
    (h : ((List.range N).all fun i => SE.ctl N cs false i == SE.ctl N cs' false i) = true) :
    Derivable (theory N) (wcT N [.g Kd tg cs]) (wcT N [.g Kd tg cs']) := by
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have e : wcT N [.g Kd tg cs] = wcT N [.g Kd tg cs'] := by
    simp only [wcT, drawn, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one, Tk.circ]
    exact mc_congr N Kd tg h
  rw [e]

/-! ## Symmetries of the canonical gates below the full width -/

/-- `CanonSym K k`, decided semantically on `k + kindSp K` wires. -/
def symCheck (K : Kind) (k : ℕ) : Bool :=
  (List.range (k + kindSp K)).all fun u =>
    !(decide (kindSp K ≤ u ∧ u + 2 ≤ k + kindSp K)) ||
      Fast.check (drawn [swAt (k + kindSp K) u, canonC K k, swAt (k + kindSp K) u]) (canonC K k)

/-- Below the full width, the symmetries of the canonical gates follow from
completeness (Lemma 5.1). -/
theorem canonSym_small (ih : IH N) (K : Kind) (k : ℕ) (hk : k + kindSp K < N)
    (hc : symCheck K k = true) : CanonSym K k := by
  intro u hu hu2
  apply ih _ hk
  apply Fast.sem_of_fast
  simp only [symCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  rcases hc u (by omega) with h | h
  · exact absurd ⟨hu, hu2⟩ h
  · exact h

end QCert.RealCliffordCH.Sec8.WS
