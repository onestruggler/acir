/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Conjugation by an adjacent transposition

`X_[x,x+1] g X_[x,x+1] ≈ g'`, where `g'` is `g` with `x` and `x+1`
exchanged, whenever `g` does not involve both (`conj_swap`): this is one of
the relations (2a)–(2c), (3a)–(3g), or one of them conjugated
(`flipD`).  On words: `conj_swap_list`.
-/
import QCert.LiRossSelinger.Column

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-- The indices of a generator. -/
def Gen.idx : Gen n → List (Fin n)
  | .neg a => [a]
  | .x a b _ => [a, b]
  | .k a b c d _ _ _ => [a, b, c, d]

/-- The type of a generator. -/
def Gen.tag : Gen n → ℕ
  | .neg _ => 0
  | .x .. => 1
  | .k .. => 2

theorem deq {Γ : WRel (Gen n)} {w w' : Word (Gen n)} (h : w = w') : Derivable Γ w w' :=
  h ▸ Derivable.refl w

/-- From `X A ≈ B X` and `X² ≈ ε`, `A X ≈ X B`. -/
theorem flipD {Γ : WRel (Gen n)} {X A B : Word (Gen n)} (hX : Derivable Γ (X * X) 1)
    (h : Derivable Γ (X * A) (B * X)) : Derivable Γ (A * X) (X * B) := by
  have e1 : Derivable Γ (A * X) (X * X * (A * X)) := by
    have := (hX.symm).mul (Derivable.refl (A * X))
    rwa [one_mul] at this
  have e2 : Derivable Γ (X * X * (A * X)) (X * (B * X) * X) := by
    have := ((Derivable.refl X).mul h).mul (Derivable.refl X)
    exact (deq (by simp only [mul_assoc])).trans this
  have e3 : Derivable Γ (X * (B * X) * X) (X * B) := by
    have := (Derivable.refl (X * B)).mul hX
    rw [mul_one] at this
    exact (deq (by simp only [mul_assoc])).trans this
  exact e1.trans (e2.trans e3)

section
variable (x y : Fin n) (hxy : x < y)

/-- The relation `g' = g` with `x` and `y` exchanged, `g` not involving both. -/
def SwapOf (g g' : Gen n) : Prop :=
  g'.tag = g.tag ∧ g'.idx = g.idx.map (Equiv.swap x y) ∧ ¬ (x ∈ g.idx ∧ y ∈ g.idx)

end

theorem swap_x {x y : Fin n} : Equiv.swap x y x = y := Equiv.swap_apply_left x y
theorem swap_y {x y : Fin n} : Equiv.swap x y y = x := Equiv.swap_apply_right x y
theorem swap_o {x y z : Fin n} (h1 : z ≠ x) (h2 : z ≠ y) : Equiv.swap x y z = z :=
  Equiv.swap_apply_of_ne_of_ne h1 h2

/-- An adjacent transposition keeps the order of two indices other than
`x < x + 1`. -/
theorem swap_lt {x y p q : Fin n} (hy : y.val = x.val + 1) (hpq : p < q)
    (h : ¬ (p = x ∧ q = y)) : Equiv.swap x y p < Equiv.swap x y q := by
  have hpq' := Fin.lt_def.1 hpq
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  rw [Fin.lt_def]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [Fin.ext_iff] at * <;> omega

theorem nodup_vals {l : List (Fin n)} (h : (l.map Fin.val).Nodup) : l.Nodup := List.Nodup.of_map _ h

theorem conj_swap {x y : Fin n} (hxy : x < y) (hy : y.val = x.val + 1) {g g' : Gen n}
    (h : SwapOf x y g g') :
    Derivable (Table1 n) (FreeMonoid.of g' * FreeMonoid.of (Gen.x x y hxy))
      (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.of g) := by
  obtain ⟨ht, hi, hg⟩ := h
  have hX : Derivable (Table1 n) (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.of (Gen.x x y hxy)) 1 :=
    Derivable.of (Table1.r1a x y hxy)
  have hxy' := Fin.lt_def.1 hxy
  have vx : ∀ z : Fin n, z ≠ x → z.val ≠ x.val := fun z h e => h (Fin.ext e)
  have vy : ∀ z : Fin n, z ≠ y → z.val ≠ y.val := fun z h e => h (Fin.ext e)
  cases g with
  | neg c =>
    cases g' with
    | x _ _ _ => simp [Gen.tag] at ht
    | k _ _ _ _ _ _ _ => simp [Gen.tag] at ht
    | neg c' =>
      simp only [Gen.idx, List.map, List.cons.injEq, and_true] at hi
      subst hi
      by_cases hcx : c = x
      · subst hcx; rw [swap_x]
        exact flipD hX (Derivable.of (Table1.r3c c y hxy))
      by_cases hcy : c = y
      · subst hcy; rw [swap_y]
        exact (Derivable.of (Table1.r3c x c hxy)).symm
      rw [swap_o hcx hcy]
      have := vx c hcx; have := vy c hcy
      exact (Derivable.of (Table1.r2b x y c hxy (nodup_vals (by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or, List.nodup_nil, and_true, not_false_eq_true]
        omega)))).symm
  | x a b hab =>
    cases g' with
    | neg _ => simp [Gen.tag] at ht
    | k _ _ _ _ _ _ _ => simp [Gen.tag] at ht
    | x a' b' hab' =>
      simp only [Gen.idx, List.map, List.cons.injEq, and_true] at hi
      obtain ⟨ha', hb'⟩ := hi
      have hab'' := Fin.lt_def.1 hab
      simp only [Gen.idx, List.mem_cons, List.not_mem_nil, or_false] at hg
      by_cases hax : a = x
      · subst a
        have hby : b ≠ y := fun e => hg ⟨Or.inl rfl, Or.inr e.symm⟩
        have hyb : y < b := Fin.lt_def.2 (by have := vy b hby; omega)
        rw [swap_x] at ha'; rw [swap_o (ne_of_gt hab) hby] at hb'
        subst a'; subst b'
        exact (Derivable.of (Table1.r3a x y b hxy hyb)).symm
      by_cases hay : a = y
      · subst a
        rw [swap_y] at ha'; rw [swap_o (ne_of_gt (hxy.trans hab)) (ne_of_gt hab)] at hb'
        subst a'; subst b'
        exact flipD hX (Derivable.of (Table1.r3a x y b hxy hab))
      have := vx a hax; have := vy a hay
      by_cases hbx : b = x
      · subst b
        rw [swap_x] at hb'; rw [swap_o hax hay] at ha'
        subst a'; subst b'
        exact (Derivable.of (Table1.r3b a x y hab hxy)).symm
      by_cases hby : b = y
      · subst b
        have hax' : a < x := Fin.lt_def.2 (by omega)
        rw [swap_y] at hb'; rw [swap_o hax hay] at ha'
        subst a'; subst b'
        exact flipD hX (Derivable.of (Table1.r3b a x y hax' hxy))
      have := vx b hbx; have := vy b hby
      rw [swap_o hax hay] at ha'; rw [swap_o hbx hby] at hb'
      subst a'; subst b'
      exact (Derivable.of (Table1.r2a x y a b hxy hab (nodup_vals (by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or, List.nodup_nil, and_true, not_false_eq_true]
        omega)))).symm
  | k a b c d h₁ h₂ h₃ =>
    cases g' with
    | neg _ => simp [Gen.tag] at ht
    | x _ _ _ => simp [Gen.tag] at ht
    | k a' b' c' d' h₁' h₂' h₃' =>
      simp only [Gen.idx, List.map, List.cons.injEq, and_true] at hi
      obtain ⟨ha', hb', hc', hd'⟩ := hi
      have e₁ := Fin.lt_def.1 h₁; have e₂ := Fin.lt_def.1 h₂; have e₃ := Fin.lt_def.1 h₃
      simp only [Gen.idx, List.mem_cons, List.not_mem_nil, or_false] at hg
      by_cases hax : a = x
      · subst a
        have hb : b ≠ y := fun e => hg ⟨Or.inl rfl, Or.inr (Or.inl e.symm)⟩
        have hc : c ≠ y := fun e => hg ⟨Or.inl rfl, Or.inr (Or.inr (Or.inl e.symm))⟩
        have hd : d ≠ y := fun e => hg ⟨Or.inl rfl, Or.inr (Or.inr (Or.inr e.symm))⟩
        have hyb : y < b := Fin.lt_def.2 (by have := vy b hb; omega)
        rw [swap_x] at ha'; rw [swap_o (ne_of_gt h₁) hb] at hb'
        rw [swap_o (ne_of_gt (h₁.trans h₂)) hc] at hc'
        rw [swap_o (ne_of_gt (h₁.trans (h₂.trans h₃))) hd] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact (Derivable.of (Table1.r3d x y b c d hxy hyb h₂ h₃)).symm
      by_cases hay : a = y
      · subst a
        rw [swap_y] at ha'; rw [swap_o (ne_of_gt (hxy.trans h₁)) (ne_of_gt h₁)] at hb'
        rw [swap_o (ne_of_gt (hxy.trans (h₁.trans h₂))) (ne_of_gt (h₁.trans h₂))] at hc'
        rw [swap_o (ne_of_gt (hxy.trans (h₁.trans (h₂.trans h₃))))
            (ne_of_gt (h₁.trans (h₂.trans h₃)))] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact flipD hX (Derivable.of (Table1.r3d x y b c d hxy h₁ h₂ h₃))
      have := vx a hax; have := vy a hay
      rw [swap_o hax hay] at ha'
      by_cases hbx : b = x
      · subst b
        have hc : c ≠ y := fun e => hg ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl e.symm))⟩
        have hd : d ≠ y := fun e => hg ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inr e.symm))⟩
        have hyc : y < c := Fin.lt_def.2 (by have := vy c hc; omega)
        rw [swap_x] at hb'; rw [swap_o (ne_of_gt h₂) hc] at hc'
        rw [swap_o (ne_of_gt (h₂.trans h₃)) hd] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact (Derivable.of (Table1.r3e a x y c d h₁ hxy hyc h₃)).symm
      by_cases hby : b = y
      · subst b
        have hax2 : a < x := Fin.lt_def.2 (by omega)
        rw [swap_y] at hb'; rw [swap_o (ne_of_gt (hxy.trans h₂)) (ne_of_gt h₂)] at hc'
        rw [swap_o (ne_of_gt (hxy.trans (h₂.trans h₃))) (ne_of_gt (h₂.trans h₃))] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact flipD hX (Derivable.of (Table1.r3e a x y c d hax2 hxy h₂ h₃))
      have := vx b hbx; have := vy b hby
      rw [swap_o hbx hby] at hb'
      by_cases hcx : c = x
      · subst c
        have hd : d ≠ y := fun e =>
          hg ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr e.symm))⟩
        have hyd : y < d := Fin.lt_def.2 (by have := vy d hd; omega)
        rw [swap_x] at hc'; rw [swap_o (ne_of_gt h₃) hd] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact (Derivable.of (Table1.r3f a b x y d h₁ h₂ hxy hyd)).symm
      by_cases hcy : c = y
      · subst c
        have hbx2 : b < x := Fin.lt_def.2 (by omega)
        rw [swap_y] at hc'; rw [swap_o (ne_of_gt (hxy.trans h₃)) (ne_of_gt h₃)] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact flipD hX (Derivable.of (Table1.r3f a b x y d h₁ hbx2 hxy h₃))
      have := vx c hcx; have := vy c hcy
      rw [swap_o hcx hcy] at hc'
      by_cases hdx : d = x
      · subst d
        rw [swap_x] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact (Derivable.of (Table1.r3g a b c x y h₁ h₂ h₃ hxy)).symm
      by_cases hdy : d = y
      · subst d
        have hcx2 : c < x := Fin.lt_def.2 (by omega)
        rw [swap_y] at hd'
        subst a'; subst b'; subst c'; subst d'
        exact flipD hX (Derivable.of (Table1.r3g a b c x y h₁ h₂ hcx2 hxy))
      have := vx d hdx; have := vy d hdy
      rw [swap_o hdx hdy] at hd'
      subst a'; subst b'; subst c'; subst d'
      exact (Derivable.of (Table1.r2c x y a b c d hxy h₁ h₂ h₃ (nodup_vals (by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or, List.nodup_nil, and_true, not_false_eq_true]
        omega)))).symm

theorem conj_swap_list {x y : Fin n} (hxy : x < y) (hy : y.val = x.val + 1) :
    ∀ {l l' : List (Gen n)}, List.Forall₂ (SwapOf x y) l l' →
      Derivable (Table1 n) (FreeMonoid.ofList l' * FreeMonoid.of (Gen.x x y hxy))
        (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.ofList l)
  | [], [], .nil => by simp only [FreeMonoid.ofList_nil, one_mul, mul_one]; exact Derivable.refl _
  | g :: l, g' :: l', .cons hg hl => by
    have ih := conj_swap_list hxy hy hl
    rw [FreeMonoid.ofList_cons, FreeMonoid.ofList_cons]
    have e1 : Derivable (Table1 n) (FreeMonoid.of g' * FreeMonoid.ofList l' * FreeMonoid.of (Gen.x x y hxy))
        (FreeMonoid.of g' * FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.ofList l) := by
      have := (Derivable.refl (FreeMonoid.of g')).mul ih
      exact (deq (by simp only [mul_assoc])).trans (this.trans (deq (by simp only [mul_assoc])))
    have e2 := (conj_swap hxy hy hg).mul (Derivable.refl (FreeMonoid.ofList l))
    exact e1.trans (e2.trans (deq (by simp only [mul_assoc])))

theorem swapOf_negs {x y : Fin n} (hxy : x < y) (l : List (Fin n)) :
    List.Forall₂ (SwapOf x y) (l.map Gen.neg) ((l.map (Equiv.swap x y)).map Gen.neg) := by
  induction l with
  | nil => exact .nil
  | cons r l ih =>
    refine .cons ⟨rfl, rfl, fun h => ?_⟩ ih
    simp only [Gen.idx, List.mem_cons, List.not_mem_nil, or_false] at h
    exact ne_of_lt hxy (h.1.trans h.2.symm)

end QCert.LiRossSelinger
