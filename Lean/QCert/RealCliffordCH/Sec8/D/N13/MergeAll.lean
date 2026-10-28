/- Reusable products over every control colouring. -/
import QCert.RealCliffordCH.Sec8.E.TransportCore
import QCert.RealCliffordCH.Sec8.D.N13.E335

namespace QCert.RealCliffordCH.Sec8.D.N13.MergeAll
open Circuit Net E Eng SE

def flip1 (x : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun i => if i = j then !x i else x i

theorem drawn_one' {N : ℕ} (a : Circ N) : drawn [a] = a := by simp [drawn]

theorem drawn_two' {N : ℕ} (a b : Circ N) : drawn [a, b] = b * a := by simp [drawn]

theorem colour_ind {N w : ℕ} (Q : (ℕ → Bool) → Prop)
    (hcongr : ∀ x y : ℕ → Bool, (∀ i, 1 ≤ i → i < N → i ≠ w → x i = y i) → Q x → Q y)
    (hflip : ∀ (x : ℕ → Bool) (j : ℕ), 1 ≤ j → j < N → j ≠ w → Q x → Q (flip1 x j))
    (h0 : Q fun _ => true) : ∀ x, Q x := by
  have key : ∀ k, ∀ x : ℕ → Bool, (∀ i, k ≤ i → x i = true) → Q x := by
    intro k
    induction k with
    | zero => exact fun x hx => hcongr _ _ (fun i _ _ _ => (hx i (Nat.zero_le _)).symm) h0
    | succ k ihk =>
      intro x hx
      have hx' : ∀ i, k ≤ i → (fun i => if i = k then true else x i) i = true := by
        intro i hi
        by_cases hik : i = k
        · simp [hik]
        · simp only [if_neg hik]; exact hx i (by omega)
      by_cases hk : 1 ≤ k ∧ k < N ∧ k ≠ w
      · cases hxk : x k
        · have h1 := hflip _ k hk.1 hk.2.1 hk.2.2 (ihk _ hx')
          refine hcongr _ _ (fun i _ _ _ => ?_) h1
          simp only [flip1]
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · simp [hik]
        · refine hcongr _ _ (fun i _ _ _ => ?_) (ihk _ hx')
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · simp [hik]
      · refine hcongr _ _ (fun i hi1 hiN hiw => ?_) (ihk _ hx')
        by_cases hik : i = k
        · subst hik; exact absurd ⟨hi1, hiN, hiw⟩ hk
        · simp [hik]
  intro x
  exact hcongr _ _ (fun i _ hiN _ => by simp [hiN])
    (key N (fun i => if i < N then x i else true) (fun i hi => by simp; omega))

/-! ## Products of commuting inverse pairs -/

/-- `∏ Aᵢ · ∏ Bᵢ = 1` when `Aᵢ Bᵢ = 1` and `Aᵢ` commutes with `Bⱼ`, `i ≠ j`. -/
theorem prod_cancel {N : ℕ} (A B : ℕ → Circ N) :
    ∀ n, (∀ i < n, ∀ j < n, i ≠ j → D.Comm N (A i) (B j)) →
      (∀ i < n, Derivable (theory N) (A i * B i) 1) →
      Derivable (theory N) (drawn ((List.range n).map A) * drawn ((List.range n).map B)) 1
  | 0, _, _ => by simpa [drawn] using Derivable.refl (Γ := theory N) 1
  | n + 1, hc, hi => by
    rw [List.range_succ, List.map_append, List.map_append, SE.drawn_append, SE.drawn_append]
    simp only [List.map_cons, List.map_nil, drawn_one']
    set P := drawn ((List.range n).map A)
    set Q := drawn ((List.range n).map B)
    have hPB : D.Comm N P (B n) := N13.comm_drawn_left _ (fun a ha => by
      obtain ⟨i, hi', rfl⟩ := List.mem_map.1 ha
      exact hc i (by simp at hi'; omega) n (by omega) (by simp at hi'; omega))
    unfold D.Comm at hPB
    rw [drawn_two', drawn_two'] at hPB
    have e : A n * P * (B n * Q) = A n * (P * B n) * Q := by simp only [mul_assoc]
    rw [e]
    refine (dright Q (dleft (A n) hPB.symm)).trans ?_
    have e2 : A n * (B n * P) * Q = (A n * B n) * (P * Q) := by simp only [mul_assoc]
    rw [e2]
    have h1 := hi n (by omega)
    have h2 := prod_cancel A B n (fun i hi j hj hij => hc i (by omega) j (by omega) hij)
      (fun i hi' => hi i (by omega))
    simpa using dmul h1 h2

/-! ## The bits of a colouring index -/

theorem bitsOn_mem (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) :
    ∀ j ∈ ws, ∃ b, bitsOn ws i base j = some b := by
  induction ws generalizing i with
  | nil => intro j hj; simp at hj
  | cons w ws ihw =>
    intro j hj
    simp only [bitsOn, setCtl]
    by_cases hjw : j = w
    · exact ⟨_, by rw [if_pos hjw]⟩
    · rw [if_neg hjw]; exact ihw (i / 2) j (by simpa [hjw] using hj)

/-- Below the last index some wire of `ws` is white. -/
theorem bitsOn_white : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool), ws.Nodup →
    i + 1 < 2 ^ ws.length → ∃ j ∈ ws, bitsOn ws i base j = some false
  | [], i, _, _, h => by simp at h
  | w :: ws, i, base, hnd, h => by
    have hnd' := List.nodup_cons.1 hnd
    by_cases hi : i % 2 = 1
    · obtain ⟨j, hj, hb⟩ := bitsOn_white ws (i / 2) base hnd'.2 (by
        rw [List.length_cons, pow_succ] at h; omega)
      refine ⟨j, by simp [hj], ?_⟩
      have hjw : j ≠ w := fun e => hnd'.1 (e ▸ hj)
      simp only [bitsOn, setCtl, if_neg hjw]; exact hb
    · exact ⟨w, by simp, by simp [bitsOn, setCtl, hi]⟩

theorem bitsOn_last : ∀ (ws : List ℕ) (base : ℕ → Option Bool) (j : ℕ), j ∈ ws →
    bitsOn ws (2 ^ ws.length - 1) base j = some true
  | [], _, j, hj => by simp at hj
  | w :: ws, base, j, hj => by
    simp only [bitsOn, setCtl, List.length_cons]
    have e1 : (2 ^ (ws.length + 1) - 1) % 2 = 1 := by
      have := Nat.one_le_two_pow (n := ws.length); rw [pow_succ]; omega
    have e2 : (2 ^ (ws.length + 1) - 1) / 2 = 2 ^ ws.length - 1 := by
      have := Nat.one_le_two_pow (n := ws.length); rw [pow_succ]; omega
    by_cases hjw : j = w
    · rw [if_pos hjw]; simp [e1]
    · rw [if_neg hjw, e2]; exact bitsOn_last ws base j (by simpa [hjw] using hj)

theorem mergeListB0 {M : ℕ} (ih : IH (M + 3)) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → 0 ∉ ws → (∀ w ∈ ws, w < M + 3) →
      base 0 = none →
      Derivable (theory (M + 3))
        (drawn ((List.range (2 ^ ws.length)).map fun i => mc (M + 3) .box [0] (bitsOn ws i base)))
        (mc (M + 3) .box [0] (idleOn ws base))
  | [], base, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil, drawn_one',
      bitsOn, idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, htw, hws, hb => by
    have hnd' := List.nodup_cons.1 hnd
    have hwt : w ≠ 0 := fun e => htw (by simp [e])
    have ih' := mergeListB0 ih ws (setCtl base w none) hnd'.2 (fun h => htw (by simp [h]))
      (fun x hx => hws x (by simp [hx])) (by simp [setCtl, Ne.symm hwt, hb])
    refine Derivable.trans ?_ ih'
    rw [List.length_cons, pow_succ, mul_comm, range_double, drawn_flatMap]
    apply drawn_map_congr
    intro i _
    have e0 : bitsOn (w :: ws) (2 * i) base = setCtl (bitsOn ws i base) w (some false) := by
      simp only [bitsOn]; congr 2 <;> simp [Nat.mul_div_cancel_left]
    have e1 : bitsOn (w :: ws) (2 * i + 1) base = setCtl (bitsOn ws i base) w (some true) := by
      simp only [bitsOn]; congr 2 <;> simp [Nat.mul_add_div] <;> omega
    rw [e0, e1, ← setCtl_bitsOn ws i base w none hnd'.1]
    have hct : bitsOn ws i base 0 = none := by
      rw [bitsOn_of_not_mem ws i base 0 (fun h => htw (by simp [h]))]; exact hb
    exact mergeC M ih (bitsOn ws i base) hct w (by omega) (hws w (by simp)) false

theorem idleOn_apply : ∀ (ws : List ℕ) (base : ℕ → Option Bool) (j : ℕ),
    idleOn ws base j = if j ∈ ws then none else base j
  | [], base, j => by simp [idleOn]
  | w :: ws, base, j => by
    simp only [idleOn, idleOn_apply ws, setCtl, List.mem_cons]
    by_cases h1 : j ∈ ws <;> by_cases h2 : j = w <;> simp [h1, h2]

theorem bitsOn_apply_not_mem {ws : List ℕ} {i : ℕ} {base : ℕ → Option Bool} {j : ℕ}
    (hj : j ∉ ws) : bitsOn ws i base j = base j := bitsOn_of_not_mem ws i base j hj

/-- The wires `2, …, M + 2`. -/
abbrev S5 (M : ℕ) : List ℕ := (List.range (M + 1)).map (· + 2)

/-- A colouring read through a frame. -/
def pullC (ps : List ℕ) (x : ℕ → Bool) : ℕ → Bool := fun i => x (frm ps i)

section Sq

variable {M : ℕ}

theorem S5_nodup : (S5 M).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem mem_S5 {j : ℕ} : j ∈ S5 M ↔ 2 ≤ j ∧ j < M + 3 := by
  simp only [S5, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨j - 2, by omega, by omega⟩

/-- The colours of the `i`-th colouring of the wires `2, …`, wire `1` black. -/
def col5 (M i : ℕ) : ℕ → Bool := fun j => (bitsOn (S5 M) i (ctlAt 1 true) j).getD false

theorem bitsOn5 (i : ℕ) : ∀ j < M + 3, bitsOn (S5 M) i (ctlAt 1 true) j = colOn 1 (M + 3) (col5 M i) j := by
  intro j hj
  by_cases hjS : j ∈ S5 M
  · obtain ⟨b, hb⟩ := bitsOn_mem (S5 M) i (ctlAt 1 true) j hjS
    have h2 := (mem_S5.1 hjS)
    simp [col5, hb, colOn, show 1 ≤ j by omega, hj]
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 := by rw [mem_S5] at hjS; omega
    rcases this with rfl | rfl
    · simp [colOn, ctlAt]
    · simp [col5, colOn, ctlAt, bitsOn_apply_not_mem hjS]

theorem col5_one (i : ℕ) : col5 M i 1 = true := by
  simp [col5, bitsOn_apply_not_mem (show 1 ∉ S5 M by rw [mem_S5]; omega), ctlAt]

theorem col5_white {i : ℕ} (hi : i + 1 < 2 ^ (M + 1)) :
    ∃ j, 2 ≤ j ∧ j < M + 3 ∧ col5 M i j = false := by
  obtain ⟨j, hj, hb⟩ := bitsOn_white (S5 M) i (ctlAt 1 true) S5_nodup (by simpa using hi)
  exact ⟨j, (mem_S5.1 hj).1, (mem_S5.1 hj).2, by simp [col5, hb]⟩

theorem bitsOn5_last : ∀ j < M + 3,
    bitsOn (S5 M) (2 ^ (M + 1) - 1) (ctlAt 1 true) j = blackOn 1 (M + 3) j := by
  intro j hj
  by_cases hjS : j ∈ S5 M
  · have := bitsOn_last (S5 M) (ctlAt 1 true) j hjS
    simp only [S5, List.length_map, List.length_range] at this
    rw [this]; have := mem_S5.1 hjS; simp [blackOn]; omega
  · rw [bitsOn_apply_not_mem hjS]
    have : j = 0 ∨ j = 1 := by rw [mem_S5] at hjS; omega
    rcases this with rfl | rfl <;> simp [ctlAt, blackOn]

theorem merged_boxes (ih : IH (M + 3)) :
    Derivable (theory (M + 3))
      (drawn ((List.range (2 ^ (M + 1))).map fun i =>
        mc (M + 3) .box [0] (bitsOn (S5 M) i (ctlAt 1 true))))
      (mc (M + 3) .box [0] (ctlAt 1 true)) := by
  have h := mergeListB0 ih (S5 M) (ctlAt 1 true) S5_nodup (by rw [mem_S5]; omega)
    (fun w hw => (mem_S5.1 hw).2) (by simp [ctlAt])
  simp only [S5, List.length_map, List.length_range] at h
  refine h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => ?_)))
  rw [idleOn_apply]
  by_cases hjS : j ∈ S5 M
  · rw [if_pos hjS]; have := mem_S5.1 hjS; simp [ctlAt]; omega
  · rw [if_neg hjS]

/-- Isolate the all-black box from the product over all colourings. -/
theorem isolate_black (ih : IH (M + 3)) (H : Circ (M + 3))
    (small : Comm (M + 3) (mc (M + 3) .box [0] (ctlAt 1 true)) H)
    (other : ∀ x : ℕ → Bool, DiffOn 2 (M + 3) x (fun _ => true) →
      Comm (M + 3) (mc (M + 3) .box [0] (colOn 1 (M + 3) x)) H)
    (boxes : ∀ x y : ℕ → Bool,
      Comm (M + 3) (mc (M + 3) .box [0] (colOn 1 (M + 3) x))
        (mc (M + 3) .box [0] (colOn 1 (M + 3) y))) :
    Comm (M + 3) (mc (M + 3) .box [0] (blackOn 1 (M + 3))) H := by
  set L := 2 ^ (M + 1) - 1
  let B := fun i => mc (M + 3) .box [0] (bitsOn (S5 M) i (ctlAt 1 true))
  have be : ∀ i, B i = mc (M + 3) .box [0] (colOn 1 (M + 3) (col5 M i)) :=
    fun i => Net.mc_congr _ _ _ (bitsOn5 i)
  have hL : 2 ^ (M + 1) = L + 1 := by have := Nat.one_le_two_pow (n := M + 1); omega
  have mB := merged_boxes ih
  rw [hL, List.range_succ, List.map_append, SE.drawn_append] at mB
  simp only [List.map_cons, List.map_nil, drawn_one'] at mB
  let P := drawn ((List.range L).map B)
  have mp : Derivable (theory (M + 3)) (B L * P) (mc (M + 3) .box [0] (ctlAt 1 true)) := mB
  have cp : Comm (M + 3) P H := comm_drawn_left _ (fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' : i < L := by simpa using hi
    obtain ⟨j, hj2, hjN, hxj⟩ := col5_white (M := M) (i := i) (by omega)
    rw [be]
    exact other _ ⟨j, hj2, hjN, by simp [hxj]⟩)
  have pp : Derivable (theory (M + 3)) (P * P) 1 :=
    prod_cancel B B L
      (fun i _ j _ _ => by rw [be, be]; exact boxes _ _)
      (fun i _ => by
        rw [be]
        have h := D.eq311 (M + 3) (by omega) ih (col5 M i)
        rwa [drawn_two] at h)
  have h := Comm.mul_left (Comm.congr mp.symm (Derivable.refl _) small) cp
  have e : Derivable (theory (M + 3)) ((B L * P) * P) (B L) := by
    rw [mul_assoc]
    simpa only [mul_one] using dleft (B L) pp
  have last : B L = mc (M + 3) .box [0] (blackOn 1 (M + 3)) :=
    Net.mc_congr _ _ _ bitsOn5_last
  exact Comm.congr (e.trans (der_of_eq last)) (Derivable.refl _) h

end Sq
end QCert.RealCliffordCH.Sec8.D.N13.MergeAll
