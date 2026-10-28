/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.7 (Lemmas D.12–D.13): the interface of package (v)

The commutation properties of multi-controlled gates that Appendix E uses,
stated on `N` wires with completeness on fewer wires as a hypothesis, in
the conventions of `MC` (see `PLAN.md`).  In Lemma D.13 the controls `Λˣ`,
`Λʸ` are colourings `x`, `y` of the top wires `k, …, N - 1` (`colOn k N`),
the half-black dots of the figures are Boolean parameters `c₁, c₂, …`
(`ctlAt`), and "`x ≠ y`" is `DiffOn k N x y`.  Every statement here was
checked numerically against the definitions at `N = 3, …, 6` (scratch
`r87/iface.py`).  They are stated, not yet proved: package (v) of `PLAN.md`
replaces each `sorry` by its proof and keeps the statements.
-/
import QCert.RealCliffordCH.Sec8.D.N8
import QCert.RealCliffordCH.Sec8.Net

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

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
    rw [List.map_cons, drawn_cons, List.reverse_cons, List.map_append, List.map_singleton]
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

/-! ## Lemma D.12 -/

/-- (315): `X` on the box wire commutes with the box. -/
theorem eq315 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, Bx N]) (drawn [Bx N, xAt N 0]) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have h := eq308 (k + 1) hN ih 1 le_rfl (by omega) x
  have e : atBot (k + 1) (x : Circ 1) = xAt (k + 1) 0 := (Net.pad_atBot1 k x).symm
  rw [e] at h
  exact h

/-- (316): `X` on the box wire commutes with the multi-controlled `H`. -/
theorem eq316 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, mc N .hg [0, 1] (blackOn 2 N)])
      (drawn [mc N .hg [0, 1] (blackOn 2 N), xAt N 0]) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have h := eq314 (k + 1) hN ih 1 le_rfl (by omega) x
  have e : atBot (k + 1) (x : Circ 1) = xAt (k + 1) 0 := (Net.pad_atBot1 k x).symm
  rw [e] at h
  exact h

/-- (317): the multi-controlled `ZX` and `XZ` are inverse. -/
theorem eq317 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .zx [0] (colOn 1 N x), mc N .xz [0] (colOn 1 N x)]) 1 ∧
    Derivable (theory N) (drawn [mc N .xz [0] (colOn 1 N x), mc N .zx [0] (colOn 1 N x)]) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 + 1 := ⟨N - 2, by omega⟩
  have hc : ∀ i, (colOn 1 (m + 1 + 1) x i).isSome = true ↔ 1 ≤ i ∧ i < (m + 1) + 1 := by
    intro i; simp only [colOn]; split_ifs with h <;> simp [h] <;> omega
  have ezx := mc_full .zx (m + 1) _ hc
  have exz := mc_full .xz (m + 1) _ hc
  simp only [Net.kindSp, Net.canonC] at ezx exz
  rw [show List.range 1 = [0] from rfl] at ezx exz
  rw [ezx, exz]
  obtain ⟨hnd, hws⟩ := whiteWires_ok (m + 1 + 1) [0] (colOn 1 (m + 1 + 1) x)
  have hbox : Derivable (theory (m + 1 + 1)) (box (m + 1) * box (m + 1)) 1 := by
    have h := eq299 (m + 1 + 1) hN ih
    have e := Net.mc_canon .box (m + 1)
    simp only [Net.kindSp, Net.canonC] at e
    rw [show List.range 1 = [0] from rfl] at e
    simpa [Bx, e, drawn] using h
  set B' : Circ (m + 1 + 1) := conj swap (box (m + 1)) with hB'
  have hB : Derivable (theory (m + 1 + 1)) (B' * B') 1 := by
    have e : B' * B' = swap * box (m + 1) * (swap * swap) * box (m + 1) * swap := by
      simp [hB', conj, drawn, mul_assoc]
    rw [e]
    refine (dright _ (cancel_mid (swap_inv m) (swap * box (m + 1)) (box (m + 1)))).trans ?_
    have e2 : swap * box (m + 1) * box (m + 1) * swap =
        swap * (box (m + 1) * box (m + 1)) * swap := by simp only [mul_assoc]
    rw [e2]
    refine (cancel_mid hbox swap swap).trans ?_
    simpa using swap_inv m
  have hch := ch_inv m
  have exz' : xz (m + 1) = ch * B' * ch * B' := by simp [xz, hB', drawn, mul_assoc]
  have ezx' : zx (m + 1) = B' * ch * B' * ch := by simp [zx, hB', drawn, mul_assoc]
  have lift : ∀ G : Circ (m + 1 + 1), Derivable (theory (m + 1 + 1)) G 1 →
      Derivable (theory (m + 1 + 1))
        (colourW (m + 1 + 1) (whiteWires (m + 1 + 1) [0] (colOn 1 (m + 1 + 1) x)) G) 1 := by
    intro G hG
    rw [Net.colourW_eq]
    refine (dctx _ _ hG).trans ?_
    rw [mul_one]; exact xs_inv _ _ hnd hws
  constructor
  · rw [Net.drawn_cons, Net.drawn_cons, show drawn ([] : List (Circ (m + 1 + 1))) = 1 from rfl, one_mul]
    refine (colourW_mul _ _ hnd hws _ _).trans (lift _ ?_)
    rw [exz', ezx']; exact palin hch hB
  · rw [Net.drawn_cons, Net.drawn_cons, show drawn ([] : List (Circ (m + 1 + 1))) = 1 from rfl, one_mul]
    refine (colourW_mul _ _ hnd hws _ _).trans (lift _ ?_)
    rw [exz', ezx']; exact palin hB hch

/-- (333): the multi-controlled `ZX` written with a multi-controlled `H`
(box wire 2, `H` on wire 0) and a box (box wire 1). -/
theorem eq333 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .zx [0] (blackOn 1 N))
      (drawn [mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))]) := by
  sorry

/-- (334): the same for the multi-controlled `XZ`. -/
theorem eq334 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .xz [0] (blackOn 1 N))
      (drawn [mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N))]) := by
  sorry

/-! ## Lemma D.13: commutations of coloured multi-controlled gates -/

/-- Two gates commute. -/
abbrev Comm (N : ℕ) (g₁ g₂ : Circ N) : Prop := Derivable (theory N) (drawn [g₁, g₂]) (drawn [g₂, g₁])

/-- (335) -/
theorem eq335 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N .box [0] (colOn 1 N y)) := by
  sorry

/-- (336) -/
theorem eq336 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  sorry

/-- (337) -/
theorem eq337 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [0, 1] (colOn 2 N y)) := by
  sorry

/-- (338) -/
theorem eq338 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y)) := by
  sorry

/-- (339) -/
theorem eq339 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  sorry

/-- (340) -/
theorem eq340 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  sorry

/-- (342) -/
theorem eq342 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [0, 2] (ctlOr (ctlAt 1 c₂) (colOn 3 N y))) := by
  sorry

/-- (344) -/
theorem eq344 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 N y))) := by
  sorry

/-- (345) -/
theorem eq345 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [1, 0] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  sorry

/-- (346) -/
theorem eq346 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (a : Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N (Kind.sgnZX a) [0] (colOn 1 N y)) := by
  sorry

/-- (347) -/
theorem eq347 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  sorry

/-- (348) -/
theorem eq348 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N y))) := by
  sorry

/-- (349) -/
theorem eq349 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₁) (colOn 2 N y))) := by
  sorry

/-- (350) -/
theorem eq350 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (a c₁ c₂ c₃ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N (Kind.sgnZX a) [2] (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 0 c₃) (colOn 3 N y)))) := by
  sorry

/-- (351) -/
theorem eq351 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (a b : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (colOn 1 N x)) (mc N (Kind.sgnZX b) [0] (colOn 1 N y)) := by
  sorry

/-- (352) -/
theorem eq352 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a b c₁ c₂ : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  sorry

end QCert.RealCliffordCH.Sec8.D
