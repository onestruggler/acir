/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.3: Lemma 8.5, by induction on `|G⁻¹(x0y) - G⁻¹(x1y)|`

`D((-1)_[G⁻¹(x0y)]X_[G⁻¹(x0y),G⁻¹(x1y)])` is the multi-controlled `XZ` on the
wire of the distinguished bit, controlled by `x` and `y`, and
`D((-1)_[G⁻¹(x1y)]X_[G⁻¹(x0y),G⁻¹(x1y)])` the `ZX` there.

With `p < q` the two indices, `dZXab` unfolds twice into five letters (the
paper's five factors): two letters on the wire `β` flipped by `p ↦ p + 1`,
the letter of the induction hypothesis on the pair `(p + 1, q - 1)` (on the
wire `t`, the bit `β` flipped), and two more letters on the wire `β`
(`Step85`).  The step at the canonical position (`t = 0`, `β = 1`, the
wires above white: `step85w`) is the paper's chain read algebraically: the
first two letters are `Mκ`, the last two its inverse ((317)); by (354) over
every colouring of the wires other than `1`, the single-qubit `(-1)ᵏ XZ` on
wire `1` is `Mκ R`, where every factor of `R` passes the result by (352)
(its controls differ above wire `1`); and (359) recolours the control on
wire `1`.  The other colours above are reached by (81) (`step85c`), any two
wires by the frame of `[t, β]` (`step85`), and `lemma85` is the induction.

Every claim was checked numerically first (`gen/sec8/e/m85.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Eq361
import QCert.RealCliffordCH.Sec8.E.Step84

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## The algebra of the step -/

theorem alg85 {Q : Type*} [Monoid Q] {Mk Mk' U U' R I J : Q} (hU : U = Mk * R)
    (hMM : Mk' * Mk = 1) (hUU : U * U' = 1) (h359 : U' * I * U = J) (hRJ : R * J = J * R) :
    Mk' * I * Mk = J := by
  have hR : R = Mk' * U := by rw [hU, ← mul_assoc, hMM, one_mul]
  have hMk' : Mk' = R * U' := by rw [hR, mul_assoc, hUU, mul_one]
  have hMk : Mk = U * (U' * Mk) := by rw [← mul_assoc, hUU, one_mul]
  have hRi : R * (U' * Mk) = 1 := by
    rw [hR, mul_assoc, ← mul_assoc U, hUU, one_mul, hMM]
  calc Mk' * I * Mk = (R * U') * I * (U * (U' * Mk)) := by rw [← hMk', ← hMk]
    _ = R * (U' * I * U) * (U' * Mk) := by simp only [mul_assoc]
    _ = R * J * (U' * Mk) := by rw [h359]
    _ = J * (R * (U' * Mk)) := by rw [hRJ, mul_assoc]
    _ = J := by rw [hRi, mul_one]

/-- A product commutes with `c` when its factors do. -/
theorem comm_prod_left {N : ℕ} {c : Circ N} :
    ∀ (l : List (Circ N)), (∀ a ∈ l, D.Comm N a c) → D.Comm N l.prod c
  | [], _ => by simpa using D.N13.comm_one c
  | a :: l, h => by
    rw [List.prod_cons]
    exact D.N13.Comm.mul_left (h a (by simp)) (comm_prod_left l (fun b hb => h b (by simp [hb])))

/-! ## The step at the canonical position -/

section Canonical

variable {M : ℕ}

/-- The wires `2, …` white. -/
abbrev W85 (M : ℕ) : ℕ → Option Bool := colOn 2 (M + 3) fun _ => false

/-- The outer letters: target `1`, control `a` on wire `0`, white above. -/
abbrev O85 (M : ℕ) (k a : Bool) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX k) [1] (ctlOr (ctlAt 0 a) (W85 M))

/-- The inner letter and the result: target `0`, control `c` on wire `1`, white above. -/
abbrev I85 (M : ℕ) (k c : Bool) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX k) [0] (ctlOr (ctlAt 1 c) (W85 M))

/-- The single-qubit `(-1)ᵏ XZ` on wire `1`. -/
abbrev U85 (M : ℕ) (k : Bool) : Circ (M + 3) := mc (M + 3) (Kind.sgnZX k) [1] (fun _ => none)

/-- The colourings of the wires other than `1`. -/
abbrev F85 (M : ℕ) (k : Bool) (i : ℕ) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX k) [1] (bitsOn (0 :: D.N15.S8 M) i fun _ => none)

theorem bitOf_01 (a : Bool) (j : ℕ) (hj : 2 ≤ j) : bitOf (if a then 1 else 0) j = 0 :=
  bitOf_small (by
    calc (if a then 1 else 0) < 2 ^ 1 := by cases a <;> norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega))

theorem ctl_O85 (a : Bool) :
    ∀ j < M + 3, ctlOf (if a then 1 else 0) 1 j = ctlOr (ctlAt 0 a) (W85 M) j := by
  intro j hj
  rcases j with _ | _ | j
  · cases a <;> simp [ctlOf, ctlOr, ctlAt, colOn, bitOf]
  · simp [ctlOf, ctlOr, ctlAt, colOn]
  · simp [ctlOf, ctlOr, ctlAt, colOn, hj, bitOf_01 a (j + 2) (by omega)]

theorem ctl_I85 (c : Bool) :
    ∀ j < M + 3, setCtl (colOn 1 (M + 3) fun _ => false) 1 (some c) j = ctlOr (ctlAt 1 c) (W85 M) j := by
  intro j hj
  rcases j with _ | _ | j
  · simp [setCtl, ctlOr, ctlAt, colOn]
  · simp [setCtl, ctlOr, ctlAt, colOn]
  · simp [setCtl, ctlOr, ctlAt, colOn, hj]

theorem U85_true : U85 M true = D.N15.xzAt (M + 3) 1 := by
  simp [mc, ctrlWires, whiteWires, canonAt, colourW, drawn, D.N15.xzAt, Kind.sgnZX]

theorem U85_false : U85 M false = D.N15.zxAt (M + 3) 1 := by
  simp [mc, ctrlWires, whiteWires, canonAt, colourW, drawn, D.N15.zxAt, Kind.sgnZX]

theorem F85_zero (k : Bool) : F85 M k 0 = O85 M k false := Net.mc_congr _ _ _ (fun j hj => by
  rcases j with _ | _ | j
  · simp [bitsOn, setCtl, ctlOr, ctlAt, colOn]
  · rw [bitsOn_of_not_mem _ _ _ 1 (by simp [D.N15.mem_S8])]; simp [ctlOr, ctlAt, colOn]
  · rw [bitsOn_zero_apply]
    have hm : j + 2 ∈ 0 :: D.N15.S8 M := by simp [D.N15.mem_S8]; omega
    simp [hm, ctlOr, ctlAt, colOn, hj])

theorem F85_one (k : Bool) : F85 M k 1 = O85 M k true := Net.mc_congr _ _ _ (fun j hj => by
  rw [show bitsOn (0 :: D.N15.S8 M) 1 (fun _ => none) =
    setCtl (bitsOn (D.N15.S8 M) 0 (fun _ => none)) 0 (some true) from rfl]
  rcases j with _ | _ | j
  · simp [setCtl, ctlOr, ctlAt, colOn]
  · simp only [setCtl]; rw [if_neg (by omega), bitsOn_of_not_mem _ _ _ 1 (by simp [D.N15.mem_S8])]
    simp [ctlOr, ctlAt, colOn]
  · simp only [setCtl]; rw [if_neg (by omega), bitsOn_zero_apply]
    have hm : j + 2 ∈ D.N15.S8 M := by simp [D.N15.mem_S8]; omega
    simp [hm, ctlOr, ctlAt, colOn, hj])

variable (ih : IH (M + 3))
include ih

/-- (317) for the outer letters. -/
theorem inv85 (k a : Bool) :
    Derivable (theory (M + 3)) (O85 M (!k) a * O85 M k a) 1 := by
  have h := rot_inv ih k (t := 1) (s := if a then 1 else 0) (by omega)
  rwa [Net.mc_congr _ _ _ (ctl_O85 a), Net.mc_congr _ _ _ (ctl_O85 a)] at h

theorem d1_xz_zx : Derivable (theory 1) ((xz 0 : Circ 1) * zx 0) 1 :=
  ih 1 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))

theorem d1_zx_xz : Derivable (theory 1) ((zx 0 : Circ 1) * xz 0) 1 :=
  ih 1 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))

/-- The single-qubit `XZ` and `ZX` on wire `1` are inverse. -/
theorem U85_inv (k : Bool) : Derivable (theory (M + 3)) (U85 M k * U85 M (!k)) 1 := by
  cases k
  · rw [Bool.not_false, U85_false, U85_true]
    exact (D.N15.placeG_mul1 1 (by omega) (zx 0) (xz 0)).symm.trans
      ((D.N15.placeG_der1 1 (by omega) (by omega) (d1_zx_xz ih)).trans
        (D.N15.placeG_one1 1 (by omega)))
  · rw [Bool.not_true, U85_true, U85_false]
    exact (D.N15.placeG_mul1 1 (by omega) (xz 0) (zx 0)).symm.trans
      ((D.N15.placeG_der1 1 (by omega) (by omega) (d1_xz_zx ih)).trans
        (D.N15.placeG_one1 1 (by omega)))

/-- (359): the single-qubit `(-1)ᵏ XZ` on wire `1` recolours the control there. -/
theorem rec85 (k1 k2 c : Bool) :
    Derivable (theory (M + 3)) (U85 M (!k1) * I85 M k2 c * U85 M k1) (I85 M k2 !c) := by
  have h := D.N15.eq359 (M + 3) (by omega) ih k2 (fun _ => false) 1 le_rfl (by omega) c
  rw [Net.mc_congr _ _ _ (ctl_I85 c), Net.mc_congr _ _ _ (ctl_I85 !c)] at h
  cases k1
  · have h2 := h.2
    rw [D.N15.drawn_three'] at h2
    rwa [Bool.not_false, U85_true, U85_false]
  · have h1 := h.1
    rw [D.N15.drawn_three'] at h1
    rwa [Bool.not_true, U85_true, U85_false]

/-- (354) for the outer letters, in either order. -/
theorem merge85 (k b : Bool) :
    Derivable (theory (M + 3)) (O85 M k (!b) * O85 M k b) (mc (M + 3) (Kind.sgnZX k) [1] (W85 M)) := by
  have h := mergeAtZ ih k (t := 1) (by omega) (W85 M) (by simp [colOn]) (w := 0) (by omega)
    (by omega) b
  rw [drawn_two] at h
  have e : ∀ v : Bool, ∀ j < M + 3, setCtl (W85 M) 0 (some v) j = ctlOr (ctlAt 0 v) (W85 M) j := by
    intro v j hj
    rcases j with _ | j <;> simp [setCtl, ctlOr, ctlAt, colOn]
  have e0 : ∀ j < M + 3, setCtl (W85 M) 0 none j = W85 M j := by
    intro j hj
    rcases j with _ | j <;> simp [setCtl, colOn]
  rwa [Net.mc_congr _ _ _ (e b), Net.mc_congr _ _ _ (e !b), Net.mc_congr _ _ _ e0] at h

/-- Every colouring but the first two passes the result ((352)). -/
theorem comm85 (k1 k2 c : Bool) {i : ℕ} (h2 : 2 ≤ i) (hi : i < 2 ^ (M + 2)) :
    D.Comm (M + 3) (F85 M k1 i) (I85 M k2 c) := by
  set x : ℕ → Bool := fun j => (bitsOn (0 :: D.N15.S8 M) i (fun _ => none) j).getD false
  obtain ⟨j, hj, hb⟩ := bitsOn_black (D.N15.S8 M) (i / 2) (fun _ => none) D.N15.S8_nodup
    (by omega) (by simp only [D.N15.S8, List.length_map, List.length_range]; rw [pow_succ] at hi; omega)
  have hj' := D.N15.mem_S8.1 hj
  have hxj : x j = true := by
    simp only [x, bitsOn, setCtl, if_neg (show j ≠ 0 by omega), hb, Option.getD_some]
  have hd : DiffOn 2 (M + 3) (fun _ => false) x := ⟨j, hj'.1, hj'.2, by simp [hxj]⟩
  have h := D.eq352 (M + 3) (by omega) ih (fun _ => false) x hd k2 k1 c (decide (i % 2 = 1))
  have e1 : mc (M + 3) (Kind.sgnZX k1) [1]
      (ctlOr (ctlAt 0 (decide (i % 2 = 1))) (colOn 2 (M + 3) x)) = F85 M k1 i :=
    Net.mc_congr _ _ _ (fun q hq => by
      rcases q with _ | _ | q
      · simp [ctlOr, ctlAt, colOn, bitsOn, setCtl]
      · rw [bitsOn_of_not_mem _ _ _ 1 (by simp [D.N15.mem_S8])]; simp [ctlOr, ctlAt, colOn]
      · obtain ⟨b, hb'⟩ := D.N15.bitsOn_mem (0 :: D.N15.S8 M) i (fun _ => none) (q + 2)
          (by simp [D.N15.mem_S8]; omega)
        simp [ctlOr, ctlAt, colOn, hq, x, hb'])
  rw [e1] at h
  exact h.symm

omit ih in
theorem S8_cons_nodup : (0 :: D.N15.S8 M).Nodup :=
  List.nodup_cons.2 ⟨by simp [D.N15.mem_S8], D.N15.S8_nodup⟩

/-- The single-qubit `(-1)ᵏ XZ` on wire `1` over every colouring of the other wires. -/
theorem U85_split (k : Bool) : Derivable (theory (M + 3))
    (F85 M k 0 * F85 M k 1 * ((List.range (2 ^ (M + 2) - 2)).map fun i => F85 M k (2 + i)).prod)
    (U85 M k) := by
  have hm := mergeListGen (N := M + 3) (Kind.sgnZX k) [1] (fun c hc w hw hwN b =>
      mergeAtZ ih k (t := 1) (by omega) c (hc 1 (by simp)) (w := w) (by simpa using hw) hwN b)
    (0 :: D.N15.S8 M) (fun _ => none) S8_cons_nodup
    (fun t ht => by simp at ht; subst ht; simp [D.N15.mem_S8])
    (fun w hw => by simp [D.N15.mem_S8] at hw; omega) (by simp)
  have eI : mc (M + 3) (Kind.sgnZX k) [1] (idleOn (0 :: D.N15.S8 M) fun _ => none) = U85 M k :=
    Net.mc_congr _ _ _ (fun j hj => by rw [D.N15.idleOn_apply]; split_ifs <;> rfl)
  rw [eI] at hm
  have hL : 2 ^ (0 :: D.N15.S8 M).length = 2 + (2 ^ (M + 2) - 2) := by
    simp only [List.length_cons, D.N15.S8, List.length_map, List.length_range]
    have : 4 ≤ 2 ^ (M + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (M + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show M + 1 + 1 = M + 2 by omega]; omega
  rw [hL, List.range_add, List.map_append, List.prod_append, List.map_map] at hm
  refine (der_of_eq ?_).trans hm
  rw [show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- The step of Lemma 8.5 at the canonical position, the wires above white. -/
theorem step85w (k1 k2 α b0 : Bool) :
    Derivable (theory (M + 3))
      (drawn [O85 M k1 α, O85 M k1 !α, I85 M k2 !b0, O85 M (!k1) !α, O85 M (!k1) α])
      (I85 M k2 b0) := by
  set R := ((List.range (2 ^ (M + 2) - 2)).map fun i => F85 M k1 (2 + i)).prod
  -- `U = Mκ R`
  have hU : Derivable (theory (M + 3)) (U85 M k1) (O85 M k1 (!α) * O85 M k1 α * R) := by
    refine (U85_split ih k1).symm.trans (dright _ ?_)
    rw [F85_zero, F85_one]
    have h1 := merge85 ih k1 true
    have h2 := merge85 ih k1 α
    rw [Bool.not_true] at h1
    exact h1.trans h2.symm
  -- `Mκ' Mκ = 1`
  have hMM : Derivable (theory (M + 3))
      (O85 M (!k1) α * O85 M (!k1) (!α) * (O85 M k1 (!α) * O85 M k1 α)) 1 := by
    have e : O85 M (!k1) α * O85 M (!k1) (!α) * (O85 M k1 (!α) * O85 M k1 α) =
        O85 M (!k1) α * (O85 M (!k1) (!α) * O85 M k1 (!α)) * O85 M k1 α := by
      simp only [mul_assoc]
    rw [e]
    refine (dright _ (dleft _ (inv85 ih k1 (!α)))).trans ?_
    rw [mul_one]
    exact inv85 ih k1 α
  -- `R` passes the result
  have hRJ : Derivable (theory (M + 3)) (R * I85 M k2 b0) (I85 M k2 b0 * R) := by
    have h := comm_prod_left (c := I85 M k2 b0) ((List.range (2 ^ (M + 2) - 2)).map
      fun i => F85 M k1 (2 + i)) (fun a ha => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
        have := List.mem_range.1 hi
        exact comm85 ih k1 k2 b0 (by omega) (by omega))
    unfold D.Comm at h
    rw [drawn_two, drawn_two] at h
    exact h.symm
  have h359 := rec85 ih k1 k2 (!b0)
  rw [Bool.not_not] at h359
  have key := alg85 (Q := (conGen (theory (M + 3))).Quotient)
    (Mk := ((O85 M k1 (!α) * O85 M k1 α : Circ (M + 3)) : (conGen (theory (M + 3))).Quotient))
    (Mk' := ((O85 M (!k1) α * O85 M (!k1) (!α) : Circ (M + 3)) : (conGen (theory (M + 3))).Quotient))
    (U := (U85 M k1 : (conGen (theory (M + 3))).Quotient))
    (U' := (U85 M (!k1) : (conGen (theory (M + 3))).Quotient))
    (R := (R : (conGen (theory (M + 3))).Quotient))
    (I := (I85 M k2 (!b0) : (conGen (theory (M + 3))).Quotient))
    (J := (I85 M k2 b0 : (conGen (theory (M + 3))).Quotient))
    (by rw [← Con.coe_mul]; exact D.N15.q_of hU)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact D.N15.q_of hMM)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact D.N15.q_of (U85_inv ih k1))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact D.N15.q_of h359)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact D.N15.q_of hRJ)
  have e : drawn [O85 M k1 α, O85 M k1 !α, I85 M k2 !b0, O85 M (!k1) !α, O85 M (!k1) α] =
      O85 M (!k1) α * O85 M (!k1) (!α) * I85 M k2 (!b0) * (O85 M k1 (!α) * O85 M k1 α) := by
    simp [drawn, mul_assoc]
  rw [e]
  apply D.N15.of_q
  rw [Con.coe_mul, Con.coe_mul]
  exact key

end Canonical

/-! ## Any colours above, and any two wires -/

/-- An equation `u a u = b` read backwards, `u` an involution. -/
theorem conj_back {N : ℕ} {u a b : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (h : Derivable (theory N) (u * a * u) b) : Derivable (theory N) (u * b * u) a := by
  refine (dright _ (dleft _ h.symm)).trans ?_
  have e : u * (u * a * u) * u = (u * u) * a * (u * u) := by simp only [mul_assoc]
  rw [e]
  refine (dmul (dright _ hu) hu).trans ?_
  simp only [one_mul, mul_one]
  exact Derivable.refl _

/-- `X` on the wires `ws` on both sides turns black controls there white ((81)). -/
theorem colr85 {N : ℕ} (ws : List ℕ) (hnd : ws.Nodup) (K : Kind) (tg : List ℕ)
    (c c' : ℕ → Option Bool) (hc : ∀ j ∈ ws, j < N ∧ j ∉ tg ∧ c j = some true)
    (hc' : ∀ j < N, c' j = if j ∈ ws then some false else c j) :
    Derivable (theory N) (drawn (ws.map (xAt N)) * mc N K tg c * drawn (ws.map (xAt N)))
      (mc N K tg c') := by
  have h := D.N13.mc_colour N K tg c ws hnd hc
  rw [Net.colourW_eq] at h
  exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hc' j hj).symm)))

section Colours

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- The outer letters with the colours `x` above. -/
abbrev Ox85 (M : ℕ) (x : ℕ → Bool) (k a : Bool) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX k) [1] (ctlOr (ctlAt 0 a) (colOn 2 (M + 3) x))

/-- The inner letter and the result with the colours `x` above. -/
abbrev Ix85 (M : ℕ) (x : ℕ → Bool) (k c : Bool) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX k) [0] (ctlOr (ctlAt 1 c) (colOn 2 (M + 3) x))

/-- The step at the canonical position, any colours above ((81)). -/
theorem step85c (x : ℕ → Bool) (k1 k2 α b0 : Bool) :
    Derivable (theory (M + 3))
      (drawn [Ox85 M x k1 α, Ox85 M x k1 !α, Ix85 M x k2 !b0, Ox85 M x (!k1) !α,
        Ox85 M x (!k1) α])
      (Ix85 M x k2 b0) := by
  set ws := (D.N15.S8 M).filter fun j => x j
  have hnd : ws.Nodup := D.N15.S8_nodup.filter _
  have hmem : ∀ j, j ∈ ws ↔ (2 ≤ j ∧ j < M + 3) ∧ x j = true := by
    intro j; simp [ws, D.N15.mem_S8]
  have hu := D.xs_inv (M + 3) ws hnd (fun w hw => ((hmem w).1 hw).1.2)
  set u := drawn (ws.map (xAt (M + 3)))
  have col : ∀ (k : Bool) (tg : List ℕ) (w : ℕ) (b : Bool), tg = [1 - w] → w < 2 →
      Derivable (theory (M + 3))
        (u * mc (M + 3) (Kind.sgnZX k) tg (ctlOr (ctlAt w b) (W85 M)) * u)
        (mc (M + 3) (Kind.sgnZX k) tg (ctlOr (ctlAt w b) (colOn 2 (M + 3) x))) := by
    intro k tg w b htg hw
    refine conj_back hu ?_
    refine colr85 ws hnd _ tg _ _ (fun j hj => ?_) (fun j hj => ?_)
    · obtain ⟨⟨h2, hN⟩, hx⟩ := (hmem j).1 hj
      refine ⟨hN, by rw [htg]; simp; omega, ?_⟩
      simp [ctlOr, ctlAt, colOn, show j ≠ w by omega, h2, hN, hx]
    · by_cases hj2 : 2 ≤ j
      · by_cases hjw : j ∈ ws
        · rw [if_pos hjw]; simp [ctlOr, ctlAt, colOn, show j ≠ w by omega, hj2, hj]
        · rw [if_neg hjw]
          have hx : x j = false := by
            by_contra h; exact hjw ((hmem j).2 ⟨⟨hj2, hj⟩, by simpa using h⟩)
          simp [ctlOr, ctlAt, colOn, hj2, hj, hx]
      · rw [if_neg (fun h => hj2 ((hmem j).1 h).1.1)]
        simp [ctlOr, ctlAt, colOn, hj2]
  have cO : ∀ k a, Derivable (theory (M + 3)) (u * O85 M k a * u) (Ox85 M x k a) :=
    fun k a => col k [1] 0 a rfl (by omega)
  have cI : ∀ k c, Derivable (theory (M + 3)) (u * I85 M k c * u) (Ix85 M x k c) :=
    fun k c => col k [0] 1 c rfl (by omega)
  have k := D.N15.via_conj hu
    (l := [O85 M k1 α, O85 M k1 !α, I85 M k2 !b0, O85 M (!k1) !α, O85 M (!k1) α])
    (r := [I85 M k2 b0])
    (List.Forall₂.cons (cO _ _) (List.Forall₂.cons (cO _ _) (List.Forall₂.cons (cI _ _)
      (List.Forall₂.cons (cO _ _) (List.Forall₂.cons (cO _ _) List.Forall₂.nil)))))
    (List.Forall₂.cons (cI _ _) List.Forall₂.nil)
    (by rw [D.N15.drawn_one']; exact step85w ih k1 k2 α b0)
  rwa [D.N15.drawn_one'] at k

end Colours

/-- The step of the induction of Lemma 8.5 (Appendix E.3) at the wires `β`
(the outer letters) and `t` (the inner letter), `s` the state of `G(p)`. -/
def Step85 (n : ℕ) : Prop :=
  ∀ (β t s : ℕ) (k1 k2 : Bool), β < n → t < n → β ≠ t →
    Derivable (theory n)
      (drawn [mc n (Kind.sgnZX k1) [β] (ctlOf s β), mc n (Kind.sgnZX k1) [β] (ctlOf (s ^^^ 2 ^ t) β),
        mc n (Kind.sgnZX k2) [t] (ctlOf (s ^^^ 2 ^ β) t),
        mc n (Kind.sgnZX !k1) [β] (ctlOf (s ^^^ 2 ^ t) β), mc n (Kind.sgnZX !k1) [β] (ctlOf s β)])
      (mc n (Kind.sgnZX k2) [t] (ctlOf s t))

theorem kindSp_sgnZX (k : Bool) : kindSp (Kind.sgnZX k) = 1 := by cases k <;> rfl

/-- The step at every pair of wires. -/
theorem step85 {M : ℕ} (ih : IH (M + 3)) : Step85 (M + 3) := by
  intro β t s k1 k2 hβ ht hβt
  have hnd : [t, β].Nodup := by simp [Ne.symm hβt]
  have hps : ∀ p ∈ [t, β], p < M + 3 := by simp [hβ, ht]
  have h0 : frm [t, β] 0 = t := frm_getD hnd hps (by simp)
  have h1 : frm [t, β] 1 = β := frm_getD hnd hps (by simp)
  -- the colours above are those of `s` whichever bit `t`, `β` is flipped
  have hcol : ∀ q, q = t ∨ q = β →
      colOn 2 (M + 3) (pull2 t β (s ^^^ 2 ^ q)) = colOn 2 (M + 3) (pull2 t β s) := by
    intro q hq
    funext j
    simp only [colOn]
    split_ifs with hj
    · have hne : frm [t, β] j ≠ q := by
        rcases hq with rfl | rfl
        · intro e; have := frm_injective _ (e.trans h0.symm); omega
        · intro e; have := frm_injective _ (e.trans h1.symm); omega
      simp [pull2, bitOf_xor_ne hne]
    · rfl
  set x := pull2 t β s
  set α := decide (bitOf s t = 1)
  set b0 := decide (bitOf s β = 1)
  have fT : ∀ (k : Bool) (s' : ℕ), Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [t, β])
      (mc (M + 3) (Kind.sgnZX k) [0] (ctlOr (ctlAt 1 (decide (bitOf s' β = 1)))
        (colOn 2 (M + 3) (pull2 t β s')))))
      (mc (M + 3) (Kind.sgnZX k) [t] (ctlOf s' t)) :=
    fun k s' => (frame2_one ih (Kind.sgnZX k) (kindSp_sgnZX k) ht hβ (Ne.symm hβt) s').1
  have fB : ∀ (k : Bool) (s' : ℕ), Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [t, β])
      (mc (M + 3) (Kind.sgnZX k) [1] (ctlOr (ctlAt 0 (decide (bitOf s' t = 1)))
        (colOn 2 (M + 3) (pull2 t β s')))))
      (mc (M + 3) (Kind.sgnZX k) [β] (ctlOf s' β)) :=
    fun k s' => (frame2_one ih (Kind.sgnZX k) (kindSp_sgnZX k) hβ ht hβt s').2
  have g1 := fB k1 s
  have g2 := fB k1 (s ^^^ 2 ^ t)
  have g3 := fT k2 (s ^^^ 2 ^ β)
  have g4 := fB (!k1) (s ^^^ 2 ^ t)
  have g5 := fB (!k1) s
  have g6 := fT k2 s
  rw [hcol t (Or.inl rfl), bit_flip] at g2 g4
  rw [hcol β (Or.inr rfl), bit_flip] at g3
  have k := via_frame hnd hps
    (l := [Ox85 M x k1 α, Ox85 M x k1 !α, Ix85 M x k2 !b0, Ox85 M x (!k1) !α, Ox85 M x (!k1) α])
    (r := [Ix85 M x k2 b0])
    (List.Forall₂.cons g1 (List.Forall₂.cons g2 (List.Forall₂.cons g3
      (List.Forall₂.cons g4 (List.Forall₂.cons g5 List.Forall₂.nil)))))
    (List.Forall₂.cons g6 List.Forall₂.nil)
    (by rw [D.N15.drawn_one']; exact step85c ih x k1 k2 α b0)
  rwa [D.N15.drawn_one'] at k

/-! ## The induction -/

/-- The kind of a decoded letter: the sign on the lower index (`w = false`)
or the upper one, the bit of the lower state on the distinguished wire. -/
def kind85 (w : Bool) (s t : ℕ) : Kind := Kind.sgnZX (decide ((w = false) = (bitOf s t = 0)))

theorem kindZX_eq (n a which : ℕ) :
    kindZX n a which = Kind.sgnZX (decide ((which = 0) = (bitOf (gray a) (tOf n a) = 0))) := by
  unfold kindZX Kind.sgnZX
  by_cases h : (which = 0) = (bitOf (gray a) (tOf n a) = 0)
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

/-- The bit of `s xor 2^β` on wire `β`, in the form the kinds use. -/
theorem kb_flip (which s β : ℕ) :
    decide ((which = 0) = (bitOf (s ^^^ 2 ^ β) β = 0)) = !decide ((which = 0) = (bitOf s β = 0)) := by
  have h := bit_flip s β
  have h1 := bitOf_lt_two s β
  have h2 := bitOf_lt_two (s ^^^ 2 ^ β) β
  rcases (show bitOf s β = 0 ∨ bitOf s β = 1 by omega) with hb | hb <;>
    rcases (show bitOf (s ^^^ 2 ^ β) β = 0 ∨ bitOf (s ^^^ 2 ^ β) β = 1 by omega) with hb' | hb' <;>
    simp_all

theorem kb0 (b : ℕ) : decide ((0 = 0) = (b = 0)) = decide (b = 0) := by
  by_cases h : b = 0 <;> simp [h]

theorem kb1 (b : ℕ) : decide ((1 = 0) = (b = 0)) = !decide (b = 0) := by
  by_cases h : b = 0 <;> simp [h]

theorem drawn5 {N : ℕ} (A B X C E : Circ N) :
    drawn [A, drawn [B, X, C], E] = drawn ([A, B] ++ [X] ++ [C, E]) := by
  simp [drawn, mul_assoc]

/-- `G⁻¹` pairs have odd distance. -/
theorem dist_odd (t : ℕ) : ∀ (m p : ℕ), (p ^^^ msk t) - p ≤ m → p.testBit t = false →
    ((p ^^^ msk t) - p) % 2 = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p hm hp
  rcases pair_step hp with ⟨_, he⟩ | ⟨β, _, _, hp1, _, he⟩
  · rw [he]; omega
  · have hlt : p + 1 < (p + 1) ^^^ msk t := pair_lt hp1
    have := ih (((p + 1) ^^^ msk t) - (p + 1)) (by rw [he] at hm; omega) (p + 1) le_rfl hp1
    rw [he]; omega

/-- Lemma 8.5 given its step, for `p` with bit `t` clear and `q = p xor (2^(t+1) - 1)`:
`D((-1)_[p]X_[p,q])` (`w = false`) and `D((-1)_[q]X_[p,q])` (`w = true`) are the
multi-controlled `XZ` or `ZX` on wire `t` controlled by the other bits of `G(p)`. -/
theorem lemma85_of {M : ℕ} (hstep : Step85 (M + 3)) :
    ∀ (m p t : ℕ), (p ^^^ msk t) - p ≤ m → p.testBit t = false → p ^^^ msk t < 2 ^ (M + 3) →
      ∀ w : Bool, Derivable (theory (M + 3))
        (dZXab (M + 3) ((p ^^^ msk t) - p) (if w then p ^^^ msk t else p) p (p ^^^ msk t))
        (mc (M + 3) (kind85 w (gray p) t) [t] (ctlOf (gray p) t)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p t hm hp hq w
  have ht : t < M + 3 := lt_of_testBit_pow (testBit_pair_hi hp) hq
  rcases pair_step hp with ⟨hon, he⟩ | ⟨β, hβt, hβ, hp1, hq1, he⟩
  · have hp3 : p + 1 < 2 ^ (M + 2 + 1) := by rw [he] at hq; exact hq
    rw [he, show p + 1 - p = 1 by omega, dZXab_one, dZX1_mc (M + 2), kindZX_eq, tOf_eq hon hp3]
    apply der_of_eq
    cases w <;> simp [kind85]
  · set q' := (p + 1) ^^^ msk t with hq'
    have hlt : p + 1 < q' := pair_lt hp1
    have hodd := dist_odd t _ (p + 1) le_rfl hp1
    rw [← hq'] at hodd
    have hq2 : q' + 1 < 2 ^ (M + 3) := by rw [he] at hq; omega
    have hm' : q' - (p + 1) < m := by rw [he] at hm; omega
    have ih' := ih (q' - (p + 1)) hm' (p + 1) t le_rfl hp1 (by omega) w
    rw [← hq'] at ih'
    rw [he, show q' + 1 - p = (q' - (p + 1) + 1) + 1 by omega,
      dZXab_odd _ _ _ _ (by omega) (by omega)]
    have hin : ∀ s', dZXab (M + 3) (q' - (p + 1) + 1) s' (p + 1) (q' + 1) =
        if s' = p + 1 then drawn [dZX1 (M + 3) q' 1, dZXab (M + 3) (q' - (p + 1)) (p + 1) (p + 1) q',
          dZX1 (M + 3) q' 0]
        else drawn [dZX1 (M + 3) q' 1, dZXab (M + 3) (q' - (p + 1)) q' (p + 1) q', dZX1 (M + 3) q' 0] := by
      intro s'
      rw [dZXab_even _ _ _ _ (by omega) (by omega), Nat.add_sub_cancel]
    have hinner : dZXab (M + 3) (q' - (p + 1) + 1) (if w then q' + 1 else p + 1) (p + 1) (q' + 1) =
        drawn [dZX1 (M + 3) q' 1, dZXab (M + 3) (q' - (p + 1)) (if w then q' else p + 1) (p + 1) q',
          dZX1 (M + 3) q' 0] := by
      rw [hin]; cases w <;> simp; omega
    have hsel : (if (if w then q' + 1 else p) = p then
          drawn [dZX1 (M + 3) p 0, dZXab (M + 3) (q' - (p + 1) + 1) (p + 1) (p + 1) (q' + 1), dZX1 (M + 3) p 1]
        else drawn [dZX1 (M + 3) p 0, dZXab (M + 3) (q' - (p + 1) + 1) (q' + 1) (p + 1) (q' + 1),
          dZX1 (M + 3) p 1]) =
        drawn [dZX1 (M + 3) p 0, dZXab (M + 3) (q' - (p + 1) + 1) (if w then q' + 1 else p + 1) (p + 1)
          (q' + 1), dZX1 (M + 3) p 1] := by
      cases w <;> simp; omega
    rw [hsel, hinner]
    -- the four outer letters
    have hp2 : p + 1 < 2 ^ (M + 2 + 1) := by rw [he] at hq; exact (by omega : p + 1 < 2 ^ (M + 3))
    have hq3 : q' + 1 < 2 ^ (M + 2 + 1) := hq2
    have hgp1 : gray (p + 1) = gray p ^^^ 2 ^ β := gray_succ_eq hβ
    have hgq : gray q' = gray p ^^^ 2 ^ t ^^^ 2 ^ β := by
      rw [hq', gray_pair, hgp1, ctlOf_xor_comm]
    have tp : tOf (M + 2 + 1) p = β := tOf_eq hβ hp2
    have tq : tOf (M + 2 + 1) q' = β := tOf_eq hq1 hq3
    have hbt : β ≠ t := by omega
    set k1 := decide (bitOf (gray p) β = 0)
    set k2 := decide ((w = false) = (bitOf (gray p) t = 0))
    have o1 : dZX1 (M + 3) p 0 = mc (M + 3) (Kind.sgnZX k1) [β] (ctlOf (gray p) β) := by
      rw [dZX1_mc (M + 2), kindZX_eq, tp, kb0]
    have o5 : dZX1 (M + 3) p 1 = mc (M + 3) (Kind.sgnZX !k1) [β] (ctlOf (gray p) β) := by
      rw [dZX1_mc (M + 2), kindZX_eq, tp, kb1]
    have o2 : dZX1 (M + 3) q' 1 = mc (M + 3) (Kind.sgnZX k1) [β] (ctlOf (gray p ^^^ 2 ^ t) β) := by
      rw [dZX1_mc (M + 2), kindZX_eq, tq, hgq, kb_flip, ctlOf_flip, bitOf_xor_ne hbt, kb1,
        Bool.not_not]
    have o4 : dZX1 (M + 3) q' 0 = mc (M + 3) (Kind.sgnZX !k1) [β] (ctlOf (gray p ^^^ 2 ^ t) β) := by
      rw [dZX1_mc (M + 2), kindZX_eq, tq, hgq, kb_flip, ctlOf_flip, bitOf_xor_ne hbt, kb0]
    have i3 : mc (M + 3) (kind85 w (gray (p + 1)) t) [t] (ctlOf (gray (p + 1)) t) =
        mc (M + 3) (Kind.sgnZX k2) [t] (ctlOf (gray p ^^^ 2 ^ β) t) := by
      rw [hgp1, kind85, bitOf_xor_ne (show t ≠ β by omega)]
    rw [i3] at ih'
    rw [o1, o2, o4, o5, drawn5]
    have hs := hstep β t (gray p) k1 k2 (by omega) ht (by omega)
    exact (drawn_mid _ _ ih').trans hs

theorem bitOf_of_testBit {s t : ℕ} (h : s.testBit t = false) : bitOf s t = 0 := by
  rw [bitOf_eq, h]; rfl

theorem bitOf_flip_one {s t : ℕ} (h : s.testBit t = false) : bitOf (s ^^^ 2 ^ t) t = 1 := by
  rw [bitOf_eq, Nat.testBit_xor, Nat.testBit_two_pow_self, h]; rfl

/-- **Lemma 8.5.** For a state `s` with bit `t` clear (the bitstring `x0y`),
`D((-1)_[G⁻¹(x0y)]X_[G⁻¹(x0y),G⁻¹(x1y)])` is the multi-controlled `XZ` on wire
`t` and `D((-1)_[G⁻¹(x1y)]X_[G⁻¹(x0y),G⁻¹(x1y)])` the `ZX`, both controlled by
the other bits of `s`. -/
theorem lemma85 {M : ℕ} (ih : IH (M + 3)) {s t : ℕ} (hs : s < 2 ^ (M + 3)) (ht : t < M + 3)
    (hst : s.testBit t = false) :
    Derivable (theory (M + 3))
      (dZX (M + 3) (gInv (M + 3) s) (gInv (M + 3) s) (gInv (M + 3) (s ^^^ 2 ^ t)))
      (mc (M + 3) .xz [t] (ctlOf s t)) ∧
    Derivable (theory (M + 3))
      (dZX (M + 3) (gInv (M + 3) (s ^^^ 2 ^ t)) (gInv (M + 3) s) (gInv (M + 3) (s ^^^ 2 ^ t)))
      (mc (M + 3) .zx [t] (ctlOf s t)) := by
  have hstep := step85 ih
  rw [gInv_flip hs ht]
  set p0 := gInv (M + 3) s
  have hp0 : p0 < 2 ^ (M + 3) := gInv_lt hs
  have hm : msk t < 2 ^ (M + 3) := by
    have : 2 ^ (t + 1) ≤ 2 ^ (M + 3) := Nat.pow_le_pow_right (by norm_num) ht
    unfold msk; omega
  have hq : p0 ^^^ msk t < 2 ^ (M + 3) := Nat.xor_lt_two_pow hp0 hm
  have hbit := bitOf_of_testBit hst
  cases hb : p0.testBit t with
  | false =>
    have L := lemma85_of hstep _ p0 t le_rfl hb hq
    have hlt : p0 < p0 ^^^ msk t := pair_lt hb
    rw [gray_gInv hs] at L
    constructor
    · rw [dZX_lt hlt (Or.inl rfl)]
      have := L false
      simp only [Bool.false_eq_true, if_false] at this
      refine this.trans (der_of_eq ?_)
      simp [kind85, hbit, Kind.sgnZX]
    · rw [dZX_lt hlt (Or.inr rfl)]
      have := L true
      simp only [if_true] at this
      refine this.trans (der_of_eq ?_)
      simp [kind85, hbit, Kind.sgnZX]
  | true =>
    set p := p0 ^^^ msk t with hpdef
    have hpb : p.testBit t = false := by
      rw [hpdef, Nat.testBit_xor, testBit_msk, hb]; simp
    have hpp : p ^^^ msk t = p0 := by
      simp only [p, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have L := lemma85_of hstep _ p t le_rfl hpb (by rw [hpp]; exact hp0)
    have hlt : p < p0 := by have := pair_lt hpb; rwa [hpp] at this
    have hg : gray p = s ^^^ 2 ^ t := by rw [hpdef, gray_pair, gray_gInv hs]
    rw [hpp, hg, ctlOf_flip] at L
    have hbit' := bitOf_flip_one hst
    constructor
    · rw [dZX_gt hlt (Or.inr rfl)]
      have := L true
      simp only [if_true] at this
      refine this.trans (der_of_eq ?_)
      simp [kind85, hbit', Kind.sgnZX]
    · rw [dZX_gt hlt (Or.inl rfl)]
      have := L false
      simp only [Bool.false_eq_true, if_false] at this
      refine this.trans (der_of_eq ?_)
      simp [kind85, hbit', Kind.sgnZX]

end QCert.RealCliffordCH.Sec8.E
