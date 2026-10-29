/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (358): the braid relation of the two rotations

Not the paper's route.  Write `a` for the `XZ` on wire `0` (controls black on
`1, …`), `b` for the `ZX` on wire `1` (black on `0, 2, …`) and `G = CZ · swap`
on the wires `0, 1`.  Then:

* `G G = 1` and `G a G = b` (the swap carries `a` to wire `1`, and the `CZ`
  turns `XZ` into `ZX` there, (357));
* by (354) over every colouring of the wires `2, …` (`mergeListZ`), the `XZ`
  on wire `0` controlled by wire `1` alone is `a · P`, `P` the product of the
  versions of `a` with a white control above wire `1`; `P` commutes with `a`
  ((351)) and with `b` ((352));
* on two wires `a₂ G a₂ G a₂ = G` (`a₂ = a P`, semantically: a two-wire
  identity, Lemma 5.1).

These force `a b a = b a b` in any monoid (`braid_of_merge`): with
`Y = P (G P G) P`, `a b a · Y = G` and `Y` commutes with `a`, so
`b = G a G = (a b a) a (a b a)⁻¹`.  Every step was checked numerically at
`N = 2, …, 5` (scratch `m358.py`).
-/
import QCert.RealCliffordCH.Sec8.D.N15.E359

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-! ## The algebra -/

/-- The braid relation from a conjugating involution: if `a` is invertible,
`G² = 1`, `X = a (G a G) a` and `X Y = G` with `Y` commuting with `a`, then
`a b a = b a b` for `b = G a G`. -/
theorem braid_of_conj {M : Type*} [Monoid M] {a ai G Y : M}
    (h1 : a * ai = 1) (h2 : ai * a = 1) (hG : G * G = 1)
    (hXY : a * (G * a * G) * a * Y = G) (hY : Y * a = a * Y) :
    a * (G * a * G) * a = (G * a * G) * a * (G * a * G) := by
  obtain ⟨u, rfl⟩ : ∃ u : Mˣ, (u : M) = a := ⟨⟨a, ai, h1, h2⟩, rfl⟩
  obtain ⟨g, rfl⟩ : ∃ g : Mˣ, (g : M) = G := ⟨⟨G, G, hG, hG⟩, rfl⟩
  have hgg : g * g = 1 := Units.ext (by simpa using hG)
  -- `Y` is `X⁻¹ g`, `X = u (g u g) u`
  have hY' : Y = (((u * (g * u * g) * u)⁻¹ * g : Mˣ) : M) := by
    have e : ((u * (g * u * g) * u : Mˣ) : M) * Y = g := by simpa using hXY
    calc Y = (((u * (g * u * g) * u)⁻¹ : Mˣ) : M) * (((u * (g * u * g) * u : Mˣ) : M) * Y) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [e, Units.val_mul]
  subst hY'
  have e : (u * (g * u * g) * u)⁻¹ * g * u = u * ((u * (g * u * g) * u)⁻¹ * g) := by
    apply Units.ext; simpa [mul_assoc] using hY
  have e1 : g * u = (u * (g * u * g) * u) * u * (u * (g * u * g) * u)⁻¹ * g := by
    calc g * u = (u * (g * u * g) * u) * ((u * (g * u * g) * u)⁻¹ * g * u) := by group
      _ = (u * (g * u * g) * u) * (u * ((u * (g * u * g) * u)⁻¹ * g)) := by rw [e]
      _ = (u * (g * u * g) * u) * u * (u * (g * u * g) * u)⁻¹ * g := by group
  have e2 : g * u * g * (u * (g * u * g) * u) = (u * (g * u * g) * u) * u := by
    calc g * u * g * (u * (g * u * g) * u)
        = ((u * (g * u * g) * u) * u * (u * (g * u * g) * u)⁻¹ * g) * g * (u * (g * u * g) * u) := by
          rw [← e1]
      _ = (u * (g * u * g) * u) * u * (u * (g * u * g) * u)⁻¹ * (g * g) * (u * (g * u * g) * u) := by
          group
      _ = (u * (g * u * g) * u) * u := by rw [hgg]; group
  have goal : u * (g * u * g) * u = (g * u * g) * u * (g * u * g) := by
    calc u * (g * u * g) * u = (u * (g * u * g) * u) * u * u⁻¹ := by group
      _ = (g * u * g * (u * (g * u * g) * u)) * u⁻¹ := by rw [e2]
      _ = (g * u * g) * u * (g * u * g) := by group
  have := congrArg Units.val goal
  simpa using this

/-- The braid relation from a merge: `a₂ = a P` with `a₂ G a₂ G a₂ = G` and `P`
commuting with `a` and with `G a G`. -/
theorem braid_of_merge {M : Type*} [Monoid M] {a ai G P a2 : M}
    (h1 : a * ai = 1) (h2 : ai * a = 1) (hG : G * G = 1) (ha2 : a2 = a * P)
    (h5 : a2 * G * a2 * G * a2 = G) (hPa : P * a = a * P)
    (hPb : P * (G * a * G) = (G * a * G) * P) :
    a * (G * a * G) * a = (G * a * G) * a * (G * a * G) := by
  set b := G * a * G with hb
  set Q := G * P * G with hQ
  have hQa : Q * a = a * Q := by
    calc Q * a = G * P * (G * a * G) * G := by
          simp only [hQ, mul_assoc]; rw [hG, mul_one]
      _ = G * (G * a * G) * P * G := by rw [mul_assoc G P, hPb, ← mul_assoc]
      _ = (G * G) * a * (G * P * G) := by simp only [mul_assoc]
      _ = a * Q := by rw [hG, one_mul]
  refine braid_of_conj h1 h2 hG (Y := P * Q * P) ?_ ?_
  · -- `a P G a P G a P = a P b Q a P = a b a (P Q P)`
    have e : a2 * G * a2 * G * a2 = a * P * (G * a * G) * (G * P * G) * a * P := by
      rw [ha2]; simp only [mul_assoc]; rw [← mul_assoc G G, hG, one_mul]
    rw [e, ← hb, ← hQ] at h5
    refine Eq.trans ?_ h5
    calc a * b * a * (P * Q * P) = a * b * (a * P) * Q * P := by simp only [mul_assoc]
      _ = a * b * (P * a) * Q * P := by rw [hPa]
      _ = a * (b * P) * (a * Q) * P := by simp only [mul_assoc]
      _ = a * (P * b) * (Q * a) * P := by rw [hPb, hQa]
      _ = a * P * b * Q * a * P := by simp only [mul_assoc]
  · calc P * Q * P * a = P * Q * (a * P) := by rw [mul_assoc, hPa]
      _ = P * (Q * a) * P := by simp only [mul_assoc]
      _ = P * (a * Q) * P := by rw [hQa]
      _ = (P * a) * Q * P := by simp only [mul_assoc]
      _ = a * (P * Q * P) := by rw [hPa]; simp only [mul_assoc]

/-! ## Derivations as equations in the quotient -/

theorem q_of {N : ℕ} {a b : Circ N} (h : Derivable (theory N) a b) :
    ((a : (conGen (theory N)).Quotient)) = (b : (conGen (theory N)).Quotient) :=
  (Con.eq _).2 h

theorem of_q {N : ℕ} {a b : Circ N}
    (h : ((a : (conGen (theory N)).Quotient)) = (b : (conGen (theory N)).Quotient)) :
    Derivable (theory N) a b :=
  (Con.eq _).1 h

/-! ## Two-wire identities at the bottom -/

section Two

variable {M : ℕ}

theorem atBot_cz : atBot (M + 3) (cz : Circ 2) = czAt (M + 3) 0 1 := by
  rw [czAt, placeG_pair (M + 3) cz (by omega)]

theorem atBot_sw : atBot (M + 3) (swap : Circ 2) = swAt (M + 3) 0 := by
  have e : swAt 2 0 = (swap : Circ 2) := by simp [swAt, place2, pad_zero2]
  rw [← e, atBot_swAt (m := 2) 0 (by norm_num) (M + 3) (by omega)]

theorem atBot_one' (N : ℕ) {m : ℕ} : atBot N (1 : Circ m) = 1 := by
  have := atBot_mul N (1 : Circ m) 1
  rw [mul_one] at this
  exact (mul_eq_left.1 this.symm)

/-- A two-wire identity, decided, on the bottom wires. -/
theorem lift2 (ih : IH (M + 3)) {a b : Circ 2} (h : S.sem 2 a = S.sem 2 b) :
    Derivable (theory (M + 3)) (atBot (M + 3) a) (atBot (M + 3) b) :=
  der_atBot (ih 2 (by omega) a b h) (M + 3) (by omega)

/-- The `XZ` on wire `0` controlled by wire `1` alone. -/
theorem xz01_atBot :
    mc (M + 3) .xz [0] (ctlAt 1 true) = atBot (M + 3) (mc 2 .xz [0] (ctlAt 1 true)) :=
  N13.mc_atBot (k := 2) .xz [0] (ctlAt 1 true) rfl (by simp) (by simp)
    (fun j hj => by simp only [ctlAt]; rw [if_neg (by omega)]) (M + 3) (by omega)

end Two

/-! ## The colourings of the wires `2, …` -/

section Cols

variable {M : ℕ}

/-- The wires `2, …, M + 2`. -/
abbrev S8 (M : ℕ) : List ℕ := (List.range (M + 1)).map (· + 2)

theorem S8_nodup : (S8 M).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem mem_S8 {j : ℕ} : j ∈ S8 M ↔ 2 ≤ j ∧ j < M + 3 := by
  simp only [S8, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨j - 2, by omega, by omega⟩

/-- The colour of wire `j` in the `i`-th colouring (wire `1` black). -/
def col8 (M i : ℕ) : ℕ → Bool := fun j => (bitsOn (S8 M) i (ctlAt 1 true) j).getD false

theorem bits8_eq (i : ℕ) :
    ∀ j < M + 3, bitsOn (S8 M) i (ctlAt 1 true) j = colOn 1 (M + 3) (col8 M i) j := by
  intro j hj
  by_cases hjS : j ∈ S8 M
  · obtain ⟨b, hb⟩ := bitsOn_mem (S8 M) i (ctlAt 1 true) j hjS
    have h2 := (mem_S8.1 hjS)
    simp [col8, hb, colOn, show 1 ≤ j by omega, hj]
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 := by rw [mem_S8] at hjS; omega
    rcases this with rfl | rfl
    · simp [colOn, ctlAt]
    · simp [col8, colOn, ctlAt, bitsOn_apply_not_mem hjS]

theorem bits8_eq' (i : ℕ) :
    ∀ j < M + 3, bitsOn (S8 M) i (ctlAt 1 true) j =
      ctlOr (ctlAt 1 true) (colOn 2 (M + 3) (col8 M i)) j := by
  intro j hj
  rw [bits8_eq i j hj]
  rcases j with _ | _ | j
  · simp [colOn, ctlOr, ctlAt]
  · simp [col8, colOn, ctlOr, ctlAt,
      bitsOn_apply_not_mem (show 1 ∉ S8 M by rw [mem_S8]; omega)]
  · simp [colOn, ctlOr, ctlAt]

theorem col8_white {i : ℕ} (hi : i + 1 < 2 ^ (M + 1)) :
    ∃ j, 2 ≤ j ∧ j < M + 3 ∧ col8 M i j = false := by
  obtain ⟨j, hj, hb⟩ := bitsOn_white (S8 M) i (ctlAt 1 true) S8_nodup (by simpa using hi)
  exact ⟨j, (mem_S8.1 hj).1, (mem_S8.1 hj).2, by simp [col8, hb]⟩

theorem bits8_last : ∀ j < M + 3,
    bitsOn (S8 M) (2 ^ (M + 1) - 1) (ctlAt 1 true) j = blackOn 1 (M + 3) j := by
  intro j hj
  by_cases hjS : j ∈ S8 M
  · have := bitsOn_last (S8 M) (ctlAt 1 true) j hjS
    simp only [S8, List.length_map, List.length_range] at this
    rw [this]; have := mem_S8.1 hjS; simp [blackOn]; omega
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 := by rw [mem_S8] at hjS; omega
    rcases this with rfl | rfl <;> simp [ctlAt, blackOn]

theorem idle8 : ∀ j < M + 3, idleOn (S8 M) (ctlAt 1 true) j = ctlAt 1 true j := by
  intro j _
  rw [idleOn_apply]
  by_cases hjS : j ∈ S8 M
  · rw [if_pos hjS]
    have h2 : 2 ≤ j := (mem_S8 (M := M)).1 hjS |>.1
    simp only [ctlAt]; rw [if_neg (by omega)]
  · rw [if_neg hjS]

end Cols

/-! ## The statement -/

section Main

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- (358): the braid relation of the `XZ` on wire `0` and the `ZX` on wire `1`. -/
theorem braid358 :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) .xz [0] (blackOn 1 (M + 3)),
        mc (M + 3) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))),
        mc (M + 3) .xz [0] (blackOn 1 (M + 3))])
      (drawn [mc (M + 3) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))),
        mc (M + 3) .xz [0] (blackOn 1 (M + 3)),
        mc (M + 3) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))]) := by
  set A := mc (M + 3) .xz [0] (blackOn 1 (M + 3)) with hA
  set Ai := mc (M + 3) .zx [0] (blackOn 1 (M + 3)) with hAi
  set B := Z1 M with hB
  set Cz := czAt (M + 3) 0 1 with hC
  set Sw := swAt (M + 3) 0 with hS
  set A2 := mc (M + 3) .xz [0] (ctlAt 1 true) with hA2
  -- inverses, (317)
  have e317 := D.eq317 (M + 3) (by omega) ih (fun _ => true)
  have ecol : ∀ K, mc (M + 3) K [0] (colOn 1 (M + 3) fun _ => true) = mc (M + 3) K [0] (blackOn 1 (M + 3)) :=
    fun K => Net.mc_congr _ _ _ (fun j _ => by simp [colOn, blackOn])
  rw [ecol, ecol, drawn_two', drawn_two'] at e317
  -- two-wire identities
  have hCC : Derivable (theory (M + 3)) (Cz * Cz) 1 := by
    have h := lift2 ih (a := (cz : Circ 2) * cz) (b := 1) (Fast.sem_of_fast (by decide +kernel))
    simp only [atBot_mul, atBot_cz, atBot_one'] at h; exact h
  have hSS : Derivable (theory (M + 3)) (Sw * Sw) 1 := swsw (M + 3) 0 (by omega)
  have hSCS : Derivable (theory (M + 3)) (Sw * Cz * Sw) Cz := by
    have h := lift2 ih (a := (swap : Circ 2) * cz * swap) (b := cz) (Fast.sem_of_fast (by decide +kernel))
    simp only [atBot_mul, atBot_cz, atBot_sw] at h; exact h
  have hCS : Derivable (theory (M + 3)) (Cz * Sw) (Sw * Cz) := by
    have h := lift2 ih (a := (cz : Circ 2) * swap) (b := swap * cz) (Fast.sem_of_fast (by decide +kernel))
    simp only [atBot_mul, atBot_cz, atBot_sw] at h; exact h
  have hGG : Derivable (theory (M + 3)) (Cz * Sw * (Cz * Sw)) 1 := by
    have h := lift2 ih (a := (cz : Circ 2) * swap * (cz * swap)) (b := 1)
      (Fast.sem_of_fast (by decide +kernel))
    simp only [atBot_mul, atBot_cz, atBot_sw, atBot_one'] at h; exact h
  have h5 : Derivable (theory (M + 3)) (A2 * (Cz * Sw) * A2 * (Cz * Sw) * A2) (Cz * Sw) := by
    have h := lift2 ih (a := mc 2 .xz [0] (ctlAt 1 true) * (cz * swap) * mc 2 .xz [0] (ctlAt 1 true) *
      (cz * swap) * mc 2 .xz [0] (ctlAt 1 true)) (b := cz * swap) (Fast.sem_of_fast (by decide +kernel))
    simp only [atBot_mul, atBot_cz, atBot_sw, ← xz01_atBot] at h; exact h
  -- `G a G = b`: the swap carries `a` to wire `1`, (357) there
  have hSA : Derivable (theory (M + 3)) (Sw * A * Sw) (X1 M) := by
    refine sw0_mc ih .xz rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have hSAi : Derivable (theory (M + 3)) (Sw * Ai * Sw) B := by
    refine sw0_mc ih .zx rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega
  have k357 := via_conj hSS (l := [Cz, Ai, Cz]) (L := [Cz, B, Cz]) (r := [A]) (R := [X1 M])
    (List.Forall₂.cons hSCS (List.Forall₂.cons hSAi (List.Forall₂.cons hSCS List.Forall₂.nil)))
    (List.Forall₂.cons hSA List.Forall₂.nil)
    (by rw [drawn_one']; exact eq357 (M + 3) (by omega) ih)
  rw [drawn_three', drawn_one'] at k357
  -- `Cz X1 Cz = Cz (Cz B Cz) Cz = B`
  have hCX1C : Derivable (theory (M + 3)) (Cz * X1 M * Cz) B := by
    refine (dctx Cz Cz k357.symm).trans ?_
    have e : Cz * (Cz * B * Cz) * Cz = (Cz * Cz) * B * (Cz * Cz) := by simp only [mul_assoc]
    rw [e]
    have := dmul (dright B hCC) hCC
    simpa using this
  have hGAG : Derivable (theory (M + 3)) (Cz * Sw * A * (Cz * Sw)) B := by
    refine (dleft _ hCS).trans ?_
    have e : Cz * Sw * A * (Sw * Cz) = Cz * (Sw * A * Sw) * Cz := by simp only [mul_assoc]
    rw [e]
    exact (dctx Cz Cz hSA).trans hCX1C
  -- the merge (354) over the colourings of the wires `2, …`
  set L := 2 ^ (M + 1) - 1 with hLdef
  have hL : 2 ^ (M + 1) = L + 1 := by have := Nat.one_le_two_pow (n := M + 1); omega
  set Dc : ℕ → Circ (M + 3) := fun i => mc (M + 3) (Kind.sgnZX true) [0] (bitsOn (S8 M) i (ctlAt 1 true))
    with hDc
  have mA := mergeListZ ih true (S8 M) (ctlAt 1 true) S8_nodup (by rw [mem_S8]; omega)
    (fun w hw => (mem_S8.1 hw).2) (by simp [ctlAt])
  have hlen : (S8 M).length = M + 1 := by simp [S8]
  rw [hlen, hL, List.range_succ, List.map_append, SE.drawn_append] at mA
  simp only [List.map_cons, List.map_nil, drawn_one'] at mA
  have eDL : mc (M + 3) (Kind.sgnZX true) [0] (bitsOn (S8 M) L (ctlAt 1 true)) = A :=
    Net.mc_congr _ _ _ bits8_last
  have eI : mc (M + 3) (Kind.sgnZX true) [0] (idleOn (S8 M) (ctlAt 1 true)) = A2 :=
    Net.mc_congr _ _ _ idle8
  rw [eDL, eI] at mA
  set PD := drawn ((List.range L).map Dc) with hPD
  have mA' : Derivable (theory (M + 3)) (A * PD) A2 := mA
  -- `P` commutes with `a` ((351)) and with `b` ((352))
  have cPA : D.Comm (M + 3) PD A := N13.comm_drawn_left _ (fun g hg => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hg
    have h := D.eq351 (M + 3) (by omega) ih (col8 M i) (fun _ => true) true true
    have e0 : mc (M + 3) (Kind.sgnZX true) [0] (colOn 1 (M + 3) fun _ => true) = A :=
      Net.mc_congr _ _ _ (fun j _ => by simp [colOn, blackOn])
    rw [e0] at h
    have e : mc (M + 3) (Kind.sgnZX true) [0] (colOn 1 (M + 3) (col8 M i)) = Dc i :=
      Net.mc_congr _ _ _ (fun j hj => (bits8_eq i j hj).symm)
    rw [e] at h
    exact h)
  have cPB : D.Comm (M + 3) PD B := N13.comm_drawn_left _ (fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' : i < L := by simpa using hi
    obtain ⟨j, hj2, hjN, hxj⟩ := col8_white (M := M) (i := i) (by omega)
    have hd : DiffOn 2 (M + 3) (col8 M i) (fun _ => true) := ⟨j, hj2, hjN, by simp [hxj]⟩
    have h := D.eq352 (M + 3) (by omega) ih (col8 M i) (fun _ => true) hd true false true true
    have e1 : mc (M + 3) (Kind.sgnZX true) [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) (col8 M i))) =
        Dc i := Net.mc_congr _ _ _ (fun j hj => (bits8_eq' i j hj).symm)
    have e2 : mc (M + 3) (Kind.sgnZX false) [1] (ctlOr (ctlAt 0 true) (colOn 2 (M + 3) fun _ => true)) =
        B := Net.mc_congr _ _ _ (fun k _ => by simp [ctlOr, ctlAt, colOn, blackOn])
    rw [e1, e2] at h
    exact h)
  unfold D.Comm at cPA cPB
  rw [drawn_two', drawn_two'] at cPA cPB
  -- the algebra, in the quotient
  have key := braid_of_merge (a := (A : (conGen (theory (M + 3))).Quotient)) (ai := Ai)
    (G := ((Cz * Sw : Circ (M + 3)) : (conGen (theory (M + 3))).Quotient)) (P := PD) (a2 := A2)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact q_of e317.1)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact q_of e317.2)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact q_of hGG)
    (by rw [← Con.coe_mul]; exact (q_of mA').symm)
    (by simp only [← Con.coe_mul]; exact q_of h5)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (q_of cPA).symm)
    (by
      have hb : ((Cz * Sw : Circ (M + 3)) : (conGen (theory (M + 3))).Quotient) * A *
          ((Cz * Sw : Circ (M + 3))) = B := by
        simp only [← Con.coe_mul]; exact q_of hGAG
      rw [hb, ← Con.coe_mul, ← Con.coe_mul]; exact (q_of cPB).symm)
  have hb : ((Cz * Sw : Circ (M + 3)) : (conGen (theory (M + 3))).Quotient) * A *
      ((Cz * Sw : Circ (M + 3))) = B := by
    simp only [← Con.coe_mul]; exact q_of hGAG
  rw [hb] at key
  rw [drawn_three', drawn_three']
  apply of_q
  simp only [Con.coe_mul]
  exact key

end Main

/-- (358) at every width from three. -/
theorem eq358' (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N)
      (drawn [mc N .xz [0] (blackOn 1 N), mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .xz [0] (blackOn 1 N)])
      (drawn [mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)), mc N .xz [0] (blackOn 1 N),
        mc N .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))]) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  exact braid358 ih

end QCert.RealCliffordCH.Sec8.D.N15
