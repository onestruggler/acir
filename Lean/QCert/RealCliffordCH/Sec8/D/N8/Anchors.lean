/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.5: the equations the engine starts from

The tables of the engine (`SymEngine`) at five local wires: the schema (19)
at every width (`t19`), Definition 2.4 of the box as (269) (`t269`), the
naturality of `mc` under a local swap (`swapE`, from `Net.mc_swap`), and the
commutation of a letter idle on a local wire with `H` or `Z` on that wire
(`qcommE`).
-/
import QCert.RealCliffordCH.Sec8.D.EngineFrame

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

/-! ## Rules at their own width -/

theorem Gen.pad_zero_heq {n : ℕ} (g : Gen Gate n) : HEq (g.pad 0) g := by
  induction g with
  | @gate0 m c => exact Minimality.heq_index (Nat.zero_add m) (fun t => (Gen.gate0 c : Gen Gate t))
  | @gate1 m c =>
    exact Minimality.heq_index (Nat.zero_add m) (fun t => (Gen.gate1 c : Gen Gate (t + 1)))
  | @gate2 m c =>
    exact Minimality.heq_index (Nat.zero_add m) (fun t => (Gen.gate2 c : Gen Gate (t + 2)))
  | @gate3 m c =>
    exact Minimality.heq_index (Nat.zero_add m) (fun t => (Gen.gate3 c : Gen Gate (t + 3)))
  | @up m g ih => exact Minimality.heq_up (Nat.zero_add m) ih

theorem pad_zero_heq {n : ℕ} (w : Circ n) : HEq (Circuit.pad 0 w) w := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one]
    exact Minimality.heq_index (Nat.zero_add n) (fun t => (1 : Circ t))
  | mul_of g w ih =>
    rw [map_mul]
    exact Minimality.heq_mul (Nat.zero_add n)
      (Minimality.heq_of (Nat.zero_add n) (Gen.pad_zero_heq g)) ih

/-- A rule of Figure 4 on its own wires. -/
theorem rule_full {k : ℕ} {w v : Circ k} (r : Rule k w v) : Derivable (theory k) w v :=
  derivable_cast (Nat.zero_add k) (pad_zero_heq w) (pad_zero_heq v) (derivable_rule r 0)

/-! ## The letters -/

/-- The box on wire `0` with all other wires black controls. -/
def bx0 : Lt := .g .box [0] [(1, true), (2, true), (3, true), (4, true)] true
/-- The doubly controlled `ZX`, `XZ` of (269). -/
def wW : Lt := .g .zx [0] [(1, true), (2, true)] false
def wV : Lt := .g .xz [0] [(1, true), (2, true)] false
/-- The inner box of (269): box wire `1`, controls `0, 3, 4` and the bulk. -/
def cC : Lt := .g .box [1] [(0, true), (3, true), (4, true)] true

theorem bx0_circ (m : ℕ) : bx0.circ 5 (m + 5) = box (m + 4) := by
  show mc (m + 5) .box [0] (ctl 5 [(1, true), (2, true), (3, true), (4, true)] true) = _
  rw [mc_congr (m + 5) .box [0] (c' := blackOn 1 ((m + 4) + kindSp .box)) (fun i hi => by
    by_cases h5 : i < 5
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp [ctl, blackOn, kindSp] <;> rfl
    · have h1 : 1 ≤ i ∧ i < m + 4 + 1 := ⟨by omega, by omega⟩
      simp [ctl, blackOn, kindSp, h5, h1])]
  exact mc_canon .box (m + 4)

theorem z0_circ (m : ℕ) : (L.Z 0).circ (m + 5) = (z : Circ (m + 5)) := rfl

/-- (19) on five local wires. -/
theorem t19 (m : ℕ) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.Z 0), bx0]) (wc 5 (m + 5) [bx0, .s (.Z 0)]) := by
  have h := rule_full (Rule.e19 m)
  have e1 : wc 5 (m + 5) [.s (.Z 0), bx0] = drawn [z, box (m + 4)] := by
    simp only [wc, List.map_cons, List.map_nil]; rw [bx0_circ]; rfl
  have e2 : wc 5 (m + 5) [bx0, .s (.Z 0)] = drawn [box (m + 4), z] := by
    simp only [wc, List.map_cons, List.map_nil]; rw [bx0_circ]; rfl
  rw [e1, e2]; exact h


/-! ## Naturality under a local swap -/

/-- Looking up through an involution of the keys. -/
theorem lookup_inv (f : ℕ → ℕ) (hf : ∀ x, f (f x) = x) : ∀ (cs : List (ℕ × Bool)) (i : ℕ),
    (cs.map fun p => (f p.1, p.2)).lookup i = cs.lookup (f i)
  | [], _ => rfl
  | (p, v) :: cs, i => by
    simp only [List.map_cons, List.lookup_cons]
    have e : (i == f p) = (f i == p) := by
      by_cases h : i = f p
      · subst h; simp [hf]
      · have : f i ≠ p := fun e => h (by rw [← e, hf])
        simp [h, this]
    rw [e, lookup_inv f hf cs i]

/-- The relabeling of a multi-controlled letter by the transposition of `j`
and `j + 1`. -/
def swapG (j : ℕ) (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool)) (b : Bool) : Lt :=
  .g Kd (tg.map (Net.tau j)) (cs.map fun p => (Net.tau j p.1, p.2)) b

/-- `mc` conjugated by a local swap, when the two wires are not both
controls. -/
theorem swapE (m K j : ℕ) (hj : j + 2 ≤ K) (Kd : Kind) (tg : List ℕ) (cs : List (ℕ × Bool))
    (b : Bool) (hx : (Lt.g Kd tg cs b).ok K = true)
    (hnc : ¬ ((cs.lookup j).isSome = true ∧ j ∉ tg ∧ (cs.lookup (j + 1)).isSome = true ∧
      j + 1 ∉ tg)) :
    Derivable (theory (m + K)) (wc K (m + K) [.s (.S j), .g Kd tg cs b, .s (.S j)])
      (wc K (m + K) [swapG j Kd tg cs b]) := by
  simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
  obtain ⟨⟨hnd, hlt⟩, ha⟩ := hx
  have e1 : wc K (m + K) [.s (.S j), .g Kd tg cs b, .s (.S j)] =
      drawn [swAt (m + K) j, mc (m + K) Kd tg (ctl K cs b), swAt (m + K) j] := rfl
  rw [e1]
  have h := mc_swap (m + K) j (by omega) Kd tg (ctl K cs b) (by rw [← kindSp_eq]; exact ha) hnd
    (fun t ht => by have := hlt t ht; simp at this; omega) (by
      intro ⟨h1, h2⟩
      rw [MS.mem_ctrlWires] at h1 h2
      apply hnc
      simp only [ctl, if_pos (show j < K by omega), if_pos (show j + 1 < K by omega)] at h1 h2
      exact ⟨h1.2.1, h1.2.2, h2.2.1, h2.2.2⟩)
  have heq : mc (m + K) Kd (tg.map (Net.tau j)) (ctl K cs b ∘ Net.tau j) =
      wc K (m + K) [swapG j Kd tg cs b] := by
    show _ = drawn [mc (m + K) Kd (tg.map (Net.tau j))
      (ctl K (cs.map fun p => (Net.tau j p.1, p.2)) b)]
    rw [show ∀ x : Circ (m + K), drawn [x] = x from fun x => by simp [drawn]]
    refine mc_congr (m + K) Kd _ (fun i hi => ?_)
    simp only [Function.comp_apply, ctl]
    rw [lookup_inv (Net.tau j) (Net.tau_tau j)]
    by_cases hik : i < K
    · rw [if_pos hik, if_pos (by unfold Net.tau; split_ifs <;> omega)]
    · rw [if_neg hik, if_neg (by unfold Net.tau; split_ifs <;> omega)]
  rw [heq] at h
  exact h

/-! ## A letter idle on a wire commutes with `H` or `Z` on that wire -/

theorem lowW_padTop {M : ℕ} (X : Circ M) : LowW M (padTop X) := by
  intro g hg
  simp only [padTop, FreeMonoid.toList_map, List.mem_map] at hg
  obtain ⟨y, _, rfl⟩ := hg
  rw [gHi_padTop]; exact gHi_le y

theorem highW_place1 (w : Circ 1) : ∀ (N j : ℕ), HighW j (place1 N j w)
  | N + 1, j + 1 => by
    intro x hx
    have e : place1 (N + 1) (j + 1) w = shift (place1 N j w) := rfl
    rw [e] at hx
    simp only [Circuit.shift, FreeMonoid.toList_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [gLo]
    have := highW_place1 w N j y hy
    omega
  | _, 0 => fun _ _ => Nat.zero_le _
  | 0, _ + 1 => by intro x hx; simp [place1] at hx

/-- A one-wire gate on wire `q`, conjugated by the swaps carrying `q` to the
top, is on the top wire. -/
theorem place1_toTop (M q : ℕ) (hq : q ≤ M) (w : Circ 1) :
    Derivable (theory (M + 1))
      (swW (M + 1) (topNet M q) * place1 (M + 1) q w * swW (M + 1) (topNet M q).reverse)
      (place1 (M + 1) M w) := by
  have h1 := place1_placeG w (M + 1) q (by omega)
  have h2 := placeG_net w (ps := [q]) (by simp) (by simp; omega) rfl (topNet M q).reverse
    (topNet_rev_ok M q)
  rw [List.reverse_reverse] at h2
  have hp : [q].map (pos (topNet M q)) = [M] := by
    simp [pos_topNet M q hq q hq]
  rw [hp] at h2
  have h3 := place1_placeG w (M + 1) M (by omega)
  exact (dright _ (dleft _ h1)).trans (h2.trans h3.symm)

/-- `H` or `Z` on a local wire `q` passes a letter avoiding `q`. -/
theorem qcommE (m k q : ℕ) (hq : q ≤ k) (x : Lt) (hx : x.ok (k + 1) = true)
    (hav : x.avoids q = true) (l : L) (hl : l = .H q ∨ l = .Z q) :
    Derivable (theory (m + k + 1)) (wc (k + 1) (m + k + 1) [x, .s l])
      (wc (k + 1) (m + k + 1) [.s l, x]) := by
  set M := m + k
  set c := swW (M + 1) (topNet M q)
  set c' := swW (M + 1) (topNet M q).reverse
  have hcc : Derivable (theory (M + 1)) (c' * c) 1 := (frame k).inv m q
  have hx' := (frame k).top m q x hq hx hav
  obtain ⟨w, hw⟩ : ∃ w : Circ 1, (l.circ (M + 1) : Circ (M + 1)) = place1 (M + 1) q w := by
    rcases hl with rfl | rfl
    · exact ⟨h, rfl⟩
    · exact ⟨z, rfl⟩
  have hy := place1_toTop M q (by omega) w
  have hcomm : Derivable (theory (M + 1)) (place1 (M + 1) M w * padTop ((x.drop q).circ k M))
      (padTop ((x.drop q).circ k M) * place1 (M + 1) M w) :=
    comm_low_high _ _ (lowW_padTop _) (highW_place1 w (M + 1) M)
  have e1 : wc (k + 1) (M + 1) [x, .s l] = place1 (M + 1) q w * x.circ (k + 1) (M + 1) := by
    simp only [wc, List.map_cons, List.map_nil, drawn, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, Lt.circ, hw]
  have e2 : wc (k + 1) (M + 1) [.s l, x] = x.circ (k + 1) (M + 1) * place1 (M + 1) q w := by
    simp only [wc, List.map_cons, List.map_nil, drawn, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, Lt.circ, hw]
  rw [e1, e2]
  have back : ∀ X : Circ (M + 1), Derivable (theory (M + 1)) X (c' * (c * X * c') * c) := by
    intro X
    have e : c' * (c * X * c') * c = (c' * c) * X * (c' * c) := by simp only [mul_assoc]
    rw [e]
    have := dmul (dmul hcc (Derivable.refl X)) hcc
    simpa using this.symm
  have split : ∀ A B : Circ (M + 1), Derivable (theory (M + 1)) (c * (A * B) * c')
      ((c * A * c') * (c * B * c')) := by
    intro A B
    have e : (c * A * c') * (c * B * c') = c * A * (c' * c) * B * c' := by simp only [mul_assoc]
    rw [e]
    have := dctx (c * A) (B * c') hcc.symm
    simpa only [mul_assoc, mul_one] using this
  refine (back _).trans ((dctx _ _ ((split _ _).trans ((dmul hy hx').trans (hcomm.trans
    ((dmul hx' hy).symm.trans (split _ _).symm))))).trans (back _).symm)


/-! ## Three-wire circuits at the bottom -/

theorem pad_zero3 (w : Circ 3) : Circuit.pad 0 w = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, ih]
    congr 1
    match g with
    | .gate0 c => exact nomatch c
    | .gate1 c => rfl
    | .gate2 c => rfl
    | .gate3 c => exact nomatch c
    | .up g =>
      match g with
      | .gate0 c => exact nomatch c
      | .gate1 c => rfl
      | .gate2 c => rfl
      | .up g =>
        match g with
        | .gate0 c => exact nomatch c
        | .gate1 c => rfl
        | .up g => exact match g with | .gate0 c => nomatch c

theorem padTop_pad3 (k : ℕ) (w : Circ 3) : padTop (Circuit.pad k w) = Circuit.pad (k + 1) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    match g with
    | .gate0 c => exact nomatch c
    | .gate1 c => rfl
    | .gate2 c => rfl
    | .gate3 c => exact nomatch c
    | .up g =>
      match g with
      | .gate0 c => exact nomatch c
      | .gate1 c => rfl
      | .gate2 c => rfl
      | .up g =>
        match g with
        | .gate0 c => exact nomatch c
        | .gate1 c => rfl
        | .up g => exact match g with | .gate0 c => nomatch c

/-! ## (269): Definition 2.4 of the box -/

theorem drawn_one {n : ℕ} (x : Circ n) : drawn [x] = x := by simp [drawn]

theorem wW_circ (m : ℕ) : wW.circ 5 (m + 5) = Circuit.pad (m + 2) zx2 := by
  have h1 : ∀ n : ℕ, mc (n + 3) .zx [0] (ctl 5 [(1, true), (2, true)] false) =
      Circuit.pad n (zx 2) := by
    intro n
    induction n with
    | zero =>
      rw [mc_congr 3 .zx [0] (c' := blackOn 1 3) (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctl, blackOn] <;> rfl)]
      exact (mc_canon .zx 2).trans (pad_zero3 _).symm
    | succ n ih =>
      exact (mc_top (n + 3) .zx [0] _ rfl (by simp) (by simp) (by simp [ctl])).trans
        (by rw [ih, padTop_pad3])
  exact (h1 (m + 2)).trans rfl

theorem wV_circ (m : ℕ) : wV.circ 5 (m + 5) = Circuit.pad (m + 2) xz2 := by
  have h1 : ∀ n : ℕ, mc (n + 3) .xz [0] (ctl 5 [(1, true), (2, true)] false) =
      Circuit.pad n (xz 2) := by
    intro n
    induction n with
    | zero =>
      rw [mc_congr 3 .xz [0] (c' := blackOn 1 3) (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [ctl, blackOn] <;> rfl)]
      exact (mc_canon .xz 2).trans (pad_zero3 _).symm
    | succ n ih =>
      exact (mc_top (n + 3) .xz [0] _ rfl (by simp) (by simp) (by simp [ctl])).trans
        (by rw [ih, padTop_pad3])
  exact (h1 (m + 2)).trans rfl

theorem tau02_swW (m : ℕ) : Circuit.pad (m + 2) (tau02 : Circ 3) = swW (m + 5) [0, 1, 0] := rfl

theorem ctrl_cC (m : ℕ) :
    ctrlWires (m + 5) [1] (ctl 5 [(0, true), (3, true), (4, true)] true) =
      0 :: List.range' 3 (m + 2) := by
  have hr : List.range (m + 5) = [0, 1, 2] ++ List.range' 3 (m + 2) := by
    rw [List.range_eq_range']
    rw [show m + 5 = 3 + (m + 2) by omega, ← List.range'_append_1]
    rfl
  unfold ctrlWires
  rw [hr, List.filter_append]
  have h1 : ([0, 1, 2] : List ℕ).filter (fun j =>
      (ctl 5 [(0, true), (3, true), (4, true)] true j).isSome && !([1].contains j)) = [0] := by
    rfl
  rw [h1, List.filter_eq_self.2]
  · rfl
  · intro j hj
    rw [List.mem_range'_1] at hj
    by_cases h5 : j < 5
    · rcases (by omega : j = 3 ∨ j = 4) with rfl | rfl <;> rfl
    · simp [ctl, h5]; omega

theorem white_cC (m : ℕ) :
    whiteWires (m + 5) [1] (ctl 5 [(0, true), (3, true), (4, true)] true) = [] := by
  unfold whiteWires
  rw [List.filter_eq_nil_iff]
  intro j _
  by_cases h5 : j < 5
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
      decide
  · simp [ctl, h5]

theorem cC_circ (m : ℕ) :
    cC.circ 5 (m + 5) = placeG (m + 5) (box (m + 3)) (1 :: 0 :: List.range' 3 (m + 2)) := by
  show mc (m + 5) .box [1] (ctl 5 [(0, true), (3, true), (4, true)] true) = _
  unfold mc
  rw [ctrl_cC, white_cC]
  simp only [colourW, List.map_nil, List.nil_append, List.append_nil, drawn_one, List.length_cons,
    List.length_range', List.cons_append]
  rfl

/-- The inner box of (269) as Definition 2.4 writes it. -/
theorem cC_def (m : ℕ) :
    Derivable (theory (m + 5)) (conj (Circuit.pad (m + 2) (tau02 : Circ 3)) (shift (box (m + 3))))
      (cC.circ 5 (m + 5)) := by
  have h1 := shift_placeG_id (m + 4) (box (m + 3))
  have h2 := placeG_net (N := m + 5) (box (m + 3)) (ps := List.range' 1 (m + 4))
    List.nodup_range' (fun p hp => by rw [List.mem_range'_1] at hp; omega) (by simp)
    [0, 1, 0] (by intro x hx; simp at hx; omega)
  have hps : (List.range' 1 (m + 4)).map (pos ([0, 1, 0] : List ℕ).reverse) =
      1 :: 0 :: List.range' 3 (m + 2) := by
    rw [show m + 4 = 2 + (m + 2) by omega, ← List.range'_append_1]
    simp only [List.map_append]
    rw [List.map_congr_left (l := List.range' (1 + 2) (m + 2)) (g := id) (fun q hq => by
      rw [List.mem_range'_1] at hq
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        pos, List.foldl, Net.tau, id]
      split_ifs <;> omega), List.map_id]
    rfl
  rw [hps] at h2
  rw [cC_circ]
  simp only [conj, tau02_swW]
  have e : drawn [swW (m + 5) [0, 1, 0], shift (box (m + 3)), swW (m + 5) [0, 1, 0]] =
      swW (m + 5) [0, 1, 0].reverse * shift (box (m + 3)) * swW (m + 5) [0, 1, 0] := by
    simp [drawn, mul_assoc]
  rw [e]
  have e2 : swW (m + 5) [0, 1, 0].reverse * placeG (m + 4 + 1) (box (m + 3)) (List.range' 1 (m + 4)) *
      swW (m + 5) [0, 1, 0] =
      swW (m + 5) [0, 1, 0].reverse * placeG (m + 5) (box (m + 3)) (List.range' 1 (m + 4)) *
        swW (m + 5) [0, 1, 0] := rfl
  exact (dctx _ _ h1).trans (e2 ▸ h2)

/-- (269) on five local wires: Definition 2.4. -/
theorem t269 (m : ℕ) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [bx0]) (wc 5 (m + 5) [wW, cC, wV, cC]) := by
  have e1 : wc 5 (m + 5) [bx0] = box (m + 4) := by
    simp only [wc, List.map_cons, List.map_nil, drawn_one]; exact bx0_circ m
  have e2 : wc 5 (m + 5) [wW, cC, wV, cC] =
      drawn [Circuit.pad (m + 2) zx2, cC.circ 5 (m + 5), Circuit.pad (m + 2) xz2,
        cC.circ 5 (m + 5)] := by
    simp only [wc, List.map_cons, List.map_nil, wW_circ, wV_circ]
  have e3 : box (m + 4) = drawn [Circuit.pad (m + 2) zx2,
      conj (Circuit.pad (m + 2) (tau02 : Circ 3)) (shift (box (m + 3))), Circuit.pad (m + 2) xz2,
      conj (Circuit.pad (m + 2) (tau02 : Circ 3)) (shift (box (m + 3)))] := rfl
  rw [e1, e2, e3]
  have hc := cC_def m
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one]
  exact dmul hc (dmul (Derivable.refl _) (dmul hc (Derivable.refl _)))

end QCert.RealCliffordCH.Sec8.D.N8
