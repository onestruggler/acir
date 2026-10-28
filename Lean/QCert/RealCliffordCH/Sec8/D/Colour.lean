/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (81) for every multi-controlled gate

`X` on a control wire on both sides of a multi-controlled gate exchanges the
colour of that control.  In the conventions of `MC` this is syntactic: the
gate `mc N K tg c` is the canonical gate conjugated by `X` on its white
controls, the `X` gates on different wires commute, and `X X = 1`.
-/
import QCert.RealCliffordCH.Sec8.EngineN
import QCert.RealCliffordCH.Sec8.MC

namespace QCert.RealCliffordCH.Sec8.D

open Circuit Eng

/-! ## `X` gates -/

theorem place1_mul : ∀ (N j : ℕ) (a b : Circ 1), place1 N j (a * b) = place1 N j a * place1 N j b
  | N + 1, j + 1, a, b => by
    show shift (place1 N j (a * b)) = shift (place1 N j a) * shift (place1 N j b)
    rw [place1_mul N j a b, map_mul]
  | k + 1, 0, a, b => map_mul (Circuit.pad k) a b
  | 0, _, _, _ => (mul_one 1).symm

theorem place1_one : ∀ (N j : ℕ), place1 N j (1 : Circ 1) = 1
  | N + 1, j + 1 => by show shift (place1 N j 1) = 1; rw [place1_one N j, map_one]
  | k + 1, 0 => map_one (Circuit.pad k)
  | 0, _ => rfl

theorem place1_drawn (N j : ℕ) (l : List (Circ 1)) :
    place1 N j (drawn l) = drawn (l.map (place1 N j)) := by
  induction l with
  | nil => exact place1_one N j
  | cons a l ih =>
    simp only [drawn, List.reverse_cons, List.prod_append, List.prod_singleton, List.map_cons]
    rw [place1_mul, ← drawn, ih, drawn]

/-- `X` on wire `j`, as letters. -/
theorem xAt_eq (N j : ℕ) : xAt N j = circW N [L.H j, L.Z j, L.H j] := by
  simp only [xAt, x, place1_drawn, circW, List.map_cons, List.map_nil]; rfl

/-- A one-wire derivation on wire `j`. -/
theorem derivable_place1 : ∀ (N j : ℕ) {u v : Circ 1}, Derivable (theory 1) u v →
    Derivable (theory N) (place1 N j u) (place1 N j v)
  | N + 1, j + 1, _, _, d => derivable_shift (derivable_place1 N j d)
  | k + 1, 0, _, _, d => derivable_pad k d
  | 0, _, _, _, _ => Derivable.refl _

theorem xx1 : Derivable (theory 1) ((x : Circ 1) * x) 1 := by
  have e1 : Derivable (theory 1) (drawn [h, h]) (drawn []) := derivable_rule Rule.e1 0
  have e2 : Derivable (theory 1) (drawn [z, z]) (drawn []) := derivable_rule Rule.e2 0
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one] at e1 e2
  have ex : (x : Circ 1) * x = h * (z * ((h * h) * (z * h))) := by
    simp only [x, drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [ex]
  have s1 := dleft h (dleft z (dright (z * h) e1))
  rw [one_mul] at s1
  refine s1.trans ?_
  have s2 := dleft h (dright h e2)
  rw [one_mul, ← mul_assoc, ← mul_assoc] at s2
  rw [← mul_assoc, ← mul_assoc]
  refine s2.trans ?_
  exact e1

/-- `X X = 1`. -/
theorem xx (N j : ℕ) (hj : j < N) : Derivable (theory N) (xAt N j * xAt N j) 1 := by
  have h := derivable_place1 N j xx1
  rwa [place1_mul, place1_one] at h

theorem disj_comm (x y : L) : disj x y = disj y x := by
  simp only [disj, Bool.or_comm]

/-- A letter commutes with a word of letters on other wires. -/
theorem comm_one (N : ℕ) (x : L) : ∀ (b : List L), (∀ y ∈ b, disj x y = true) →
    Derivable (theory N) (x.circ N * circW N b) (circW N b * x.circ N)
  | [], _ => by rw [circW_nil, one_mul, mul_one]
  | y :: b, h => by
    rw [circW_cons]
    have ih := comm_one N x b (fun z hz => h z (by simp [hz]))
    have hxy : Derivable (theory N) (x.circ N * y.circ N) (y.circ N * x.circ N) :=
      comm_disj N y x (by rw [disj_comm]; exact h y (by simp))
    rw [← mul_assoc]
    refine (dright _ ih).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ hxy

/-- Words of letters on disjoint wires commute. -/
theorem circW_comm (N : ℕ) : ∀ (a b : List L), (∀ x ∈ a, ∀ y ∈ b, disj x y = true) →
    Derivable (theory N) (circW N a * circW N b) (circW N b * circW N a)
  | [], b, _ => by rw [circW_nil, one_mul, mul_one]
  | x :: a, b, h => by
    rw [circW_cons]
    have ih := circW_comm N a b (fun z hz y hy => h z (by simp [hz]) y hy)
    have hx := comm_one N x b (h x (by simp))
    rw [mul_assoc]
    refine (dleft _ hx).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact dright _ ih

/-- `X` gates on different wires commute. -/
theorem xAt_comm (N i j : ℕ) (h : i ≠ j) :
    Derivable (theory N) (xAt N i * xAt N j) (xAt N j * xAt N i) := by
  rw [xAt_eq, xAt_eq]
  apply circW_comm
  intro a ha b hb
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp [disj, below, L.lo, L.wd] <;> omega

/-! ## Products of commuting gates -/

/-- The product, in drawn order, of a list of pairwise commuting gates does
not depend on the order. -/
theorem drawn_perm {N : ℕ} {l₁ l₂ : List (Circ N)} (hp : l₁.Perm l₂)
    (hc : ∀ a ∈ l₁, ∀ b ∈ l₁, Derivable (theory N) (a * b) (b * a)) :
    Derivable (theory N) (drawn l₁) (drawn l₂) := by
  induction hp with
  | nil => exact Derivable.refl _
  | cons x _ ih =>
    simp only [drawn, List.reverse_cons, List.prod_append, List.prod_singleton] at ih ⊢
    exact dright _ (ih fun a ha b hb => hc a (by simp [ha]) b (by simp [hb]))
  | swap x y l =>
    simp only [drawn, List.reverse_cons, List.prod_append, List.prod_singleton, mul_assoc]
    exact dleft _ (hc x (by simp) y (by simp))
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ hc).trans (ih₂ fun a ha b hb => hc a (h₁.mem_iff.2 ha) b (h₁.mem_iff.2 hb))


/-! ## Equation (81) -/

theorem xs_comm (N : ℕ) (l : List ℕ) :
    ∀ a ∈ l.map (xAt N), ∀ b ∈ l.map (xAt N), Derivable (theory N) (a * b) (b * a) := by
  intro a ha b hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
  by_cases h : i = k
  · subst h; exact Derivable.refl _
  · exact xAt_comm N i k h

/-- The `X` gates of a list of wires, whatever their order. -/
theorem drawn_xs_perm {N : ℕ} {l₁ l₂ : List ℕ} (hp : l₁.Perm l₂) :
    Derivable (theory N) (drawn (l₁.map (xAt N))) (drawn (l₂.map (xAt N))) :=
  drawn_perm (hp.map _) (xs_comm N l₁)

theorem drawn_cons' {N : ℕ} (a : Circ N) (l : List (Circ N)) : drawn (a :: l) = drawn l * a := by
  simp [drawn, List.prod_append]

theorem drawn_append' {N : ℕ} (a b : List (Circ N)) : drawn (a ++ b) = drawn b * drawn a := by
  simp [drawn, List.prod_append]

theorem colourW_eq (N : ℕ) (ws : List ℕ) (g : Circ N) :
    colourW N ws g = drawn (ws.map (xAt N)) * g * drawn (ws.map (xAt N)) := by
  simp [colourW, drawn, List.prod_append, mul_assoc]

theorem ctrlWires_setCtl {N : ℕ} {tg : List ℕ} {c : ℕ → Option Bool} {j : ℕ} {b : Bool}
    (hc : c j = some b) (v : Bool) : ctrlWires N tg (setCtl c j (some v)) = ctrlWires N tg c := by
  unfold ctrlWires
  apply List.filter_congr
  intro i _
  by_cases h : i = j
  · subst h; simp [setCtl, hc]
  · simp [setCtl, h]

/-- Adding one wire to a filtered range. -/
theorem filter_perm_cons {N j : ℕ} (hj : j < N) {p q : ℕ → Bool} (hpj : p j = false)
    (hqj : q j = true) (hpq : ∀ i, i ≠ j → p i = q i) :
    ((List.range N).filter q).Perm (j :: (List.range N).filter p) := by
  rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _)
    (List.nodup_cons.2 ⟨by simp [hpj], (List.nodup_range).filter _⟩)]
  intro i
  simp only [List.mem_filter, List.mem_range, List.mem_cons]
  by_cases h : i = j
  · subst h; simp [hj, hqj]
  · rw [hpq i h]; simp [h]

/-- (81): `X` on a control wire on both sides exchanges the colour of that
control. -/
theorem eq81' (N : ℕ) (K : Kind) (tg : List ℕ) (c : ℕ → Option Bool) (j : ℕ) (b : Bool)
    (hj : j < N) (hjt : j ∉ tg) (hc : c j = some b) :
    Derivable (theory N) (drawn [xAt N j, mc N K tg c, xAt N j])
      (mc N K tg (setCtl c j (some !b))) := by
  unfold mc
  rw [ctrlWires_setCtl hc]
  set g := canonAt N K (ctrlWires N tg c).length (tg ++ ctrlWires N tg c)
  set W := whiteWires N tg c
  set W' := whiteWires N tg (setCtl c j (some !b))
  have hl : drawn [xAt N j, colourW N W g, xAt N j] = xAt N j * colourW N W g * xAt N j := by
    simp [drawn, mul_assoc]
  rw [hl, colourW_eq, colourW_eq]
  have hpw : ∀ i, i ≠ j → (c i == some false && !tg.contains i) =
      (setCtl c j (some !b) i == some false && !tg.contains i) := by
    intro i hi; simp [setCtl, hi]
  have htg : tg.contains j = false := by simpa using hjt
  cases b with
  | true =>
    -- `j` becomes white
    have hp : W'.Perm (j :: W) := filter_perm_cons hj (by simp [hc]) (by simp [setCtl, hjt]) hpw
    have h1 : Derivable (theory N) (drawn (W'.map (xAt N))) (drawn (W.map (xAt N)) * xAt N j) := by
      have := drawn_xs_perm (N := N) hp
      rwa [List.map_cons, drawn_cons'] at this
    have h2 : Derivable (theory N) (drawn (W'.map (xAt N))) (xAt N j * drawn (W.map (xAt N))) := by
      have := drawn_xs_perm (N := N) (hp.trans (List.perm_append_singleton j W).symm)
      rwa [List.map_append, drawn_append', List.map_singleton, show drawn [xAt N j] = xAt N j by
        simp [drawn]] at this
    refine Derivable.symm ((dmul (dmul h2 (Derivable.refl g)) h1).trans ?_)
    simp only [mul_assoc]; exact Derivable.refl _
  | false =>
    -- `j` becomes black
    have hp : W.Perm (j :: W') := filter_perm_cons hj (by simp [setCtl, hjt]) (by simp [hc, hjt])
      (fun i hi => (hpw i hi).symm)
    have h1 : Derivable (theory N) (drawn (W.map (xAt N))) (drawn (W'.map (xAt N)) * xAt N j) := by
      have := drawn_xs_perm (N := N) hp
      rwa [List.map_cons, drawn_cons'] at this
    have h2 : Derivable (theory N) (drawn (W.map (xAt N))) (xAt N j * drawn (W'.map (xAt N))) := by
      have := drawn_xs_perm (N := N) (hp.trans (List.perm_append_singleton j W').symm)
      rwa [List.map_append, drawn_append', List.map_singleton, show drawn [xAt N j] = xAt N j by
        simp [drawn]] at this
    simp only [← mul_assoc]
    refine (dmul (dmul (dmul (dmul (Derivable.refl (xAt N j)) h2) (Derivable.refl g)) h1)
      (Derivable.refl (xAt N j))).trans ?_
    have e : xAt N j * (xAt N j * drawn (W'.map (xAt N))) * g * (drawn (W'.map (xAt N)) * xAt N j) *
        xAt N j = (xAt N j * xAt N j) * (drawn (W'.map (xAt N)) * g * drawn (W'.map (xAt N))) *
          (xAt N j * xAt N j) := by simp only [mul_assoc]
    rw [e]
    have := dmul (dmul (xx N j hj) (Derivable.refl
      (drawn (W'.map (xAt N)) * g * drawn (W'.map (xAt N))))) (xx N j hj)
    simpa only [one_mul, mul_one] using this

end QCert.RealCliffordCH.Sec8.D
