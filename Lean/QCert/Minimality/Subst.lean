/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Substituting circuits for gates (Definition 18)

An encoding or decoding of Definition 18 replaces each gate by a circuit on
its own wires (`GateSubst`), and extends to circuits as a PROP morphism
(`GateSubst.map`): a gate on the bottom wires becomes its circuit padded,
a generator moved up becomes the circuit moved up.  The structural rules
are carried to derivable equations (`lift_map`), so a substitution that
sends each rule to a derivable equation carries derivations
(`derivable_map`, Lemma 20); and if decoding the encoding of each gate
derives the gate, decoding the encoding of every circuit derives the
circuit (`derivable_comp`, Lemma 19).
-/
import QCert.Minimality.Transfer

namespace QCert.Minimality

open QCert.Circuit

variable {G G' G'' : ℕ → Type}

/-- Each gate replaced by a circuit on its own wires. -/
structure GateSubst (G G' : ℕ → Type) where
  φ0 : G 0 → Circuit G' 0
  φ1 : G 1 → Circuit G' 1
  φ2 : G 2 → Circuit G' 2
  φ3 : G 3 → Circuit G' 3

namespace GateSubst

variable (Φ : GateSubst G G')

/-- The circuit a generator is replaced by. -/
def gen : {n : ℕ} → Gen G n → Circuit G' n
  | n, .gate0 c => Circuit.pad n (Φ.φ0 c)
  | _, @Gen.gate1 _ m c => Circuit.pad m (Φ.φ1 c)
  | _, @Gen.gate2 _ m c => Circuit.pad m (Φ.φ2 c)
  | _, @Gen.gate3 _ m c => Circuit.pad m (Φ.φ3 c)
  | _, .up g => shift (gen g)

/-- The substitution on circuits. -/
def map (n : ℕ) : Circuit G n →* Circuit G' n := FreeMonoid.lift Φ.gen

theorem map_of {n : ℕ} (g : Gen G n) : Φ.map n (FreeMonoid.of g) = Φ.gen g :=
  FreeMonoid.lift_eval_of _ _

theorem map_shift {n : ℕ} (w : Circuit G n) : Φ.map (n + 1) (shift w) = shift (Φ.map n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih, Circuit.shift_of, map_of, map_of, map_mul]
    rfl

theorem gen_pad (m : ℕ) {k : ℕ} (g : Gen G k) :
    Φ.gen (g.pad m) = Circuit.pad m (Φ.gen g) := by
  induction g with
  | @gate0 n c => exact (eq_of_heq (pad_pad_heq m n (Φ.φ0 c))).symm
  | @gate1 n c => exact (eq_of_heq (pad_pad_heq m n (Φ.φ1 c))).symm
  | @gate2 n c => exact (eq_of_heq (pad_pad_heq m n (Φ.φ2 c))).symm
  | @gate3 n c => exact (eq_of_heq (pad_pad_heq m n (Φ.φ3 c))).symm
  | up g ih =>
    show shift (Φ.gen (g.pad m)) = _
    rw [ih]
    exact (pad_shift m _).symm

theorem map_pad (m : ℕ) {k : ℕ} (w : Circuit G k) :
    Φ.map (m + k) (Circuit.pad m w) = Circuit.pad m (Φ.map k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, map_mul, ih]
    congr 1
    show Φ.map (m + k) (FreeMonoid.of (g.pad m)) = _
    rw [map_of, map_of, gen_pad]

end GateSubst

/-! ### Words on disjoint wires commute -/

section Words

variable {R : CRel G'}

theorem comm_words (hsc : ∀ c c' : G' 0, c = c') {n : ℕ} (u v : Circuit G' n)
    (h : ∀ a ∈ FreeMonoid.toList u, ∀ b ∈ FreeMonoid.toList v, Gen.apart a b = true) :
    Derivable (Lift R n) (u * v) (v * u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [one_mul, mul_one]
  | mul_of a u ih =>
    have ha : ∀ b ∈ FreeMonoid.toList v, Gen.apart a b = true := fun b hb =>
      h a (by simp) b hb
    have hu : ∀ a' ∈ FreeMonoid.toList u, ∀ b ∈ FreeMonoid.toList v, Gen.apart a' b = true :=
      fun a' ha' b hb => h a' (by simp [ha']) b hb
    -- move `a` across `v`
    have hav : Derivable (Lift R n) (FreeMonoid.of a * v) (v * FreeMonoid.of a) := by
      clear h hu ih
      induction v using FreeMonoid.inductionOn' with
      | one => rw [one_mul, mul_one]
      | mul_of b v ihv =>
        have hb : Gen.apart a b = true := ha b (by simp)
        have hv : ∀ b' ∈ FreeMonoid.toList v, Gen.apart a b' = true :=
          fun b' hb' => ha b' (by simp [hb'])
        rw [← mul_assoc]
        refine ((comm_apart hsc a b hb).mul (Derivable.refl _)).trans ?_
        rw [mul_assoc, mul_assoc]
        exact (Derivable.refl _).mul (ihv hv)
    rw [mul_assoc]
    refine ((Derivable.refl _).mul (ih hu)).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact hav.mul (Derivable.refl _)

theorem span_up_none_or {n : ℕ} (a : Gen G' n) :
    Gen.span a.up = none ∨ ∃ lo hi, Gen.span a.up = some (lo, hi) ∧ 1 ≤ lo := by
  cases h : Gen.span a with
  | none => left; simp [Gen.span, h]
  | some p => right; exact ⟨p.1 + 1, p.2 + 1, by simp [Gen.span, h], by omega⟩

theorem span_pad (m : ℕ) {k : ℕ} (b : Gen G' k) : Gen.span (b.pad m) = Gen.span b := by
  induction b with
  | gate0 c => rfl
  | gate1 c => rfl
  | gate2 c => rfl
  | gate3 c => rfl
  | up g ih => simp [Gen.span, Gen.pad, ih]

theorem span_le {k : ℕ} (b : Gen G' k) :
    Gen.span b = none ∨ ∃ lo hi, Gen.span b = some (lo, hi) ∧ hi ≤ k := by
  induction b with
  | gate0 c => left; rfl
  | gate1 c => right; exact ⟨0, 1, rfl, by omega⟩
  | gate2 c => right; exact ⟨0, 2, rfl, by omega⟩
  | gate3 c => right; exact ⟨0, 3, rfl, by omega⟩
  | @up n g ih =>
    rcases ih with h | ⟨lo, hi, h, hk⟩
    · left; simp [Gen.span, h]
    · right; exact ⟨lo + 1, hi + 1, by simp [Gen.span, h], by omega⟩

end Words

/-! ### Substitutions carry derivations -/

section Carry

theorem apart_of_le {n : ℕ} (k : ℕ) (a b : Gen G' n)
    (ha : Gen.span a = none ∨ ∃ lo hi, Gen.span a = some (lo, hi) ∧ k ≤ lo)
    (hb : Gen.span b = none ∨ ∃ lo hi, Gen.span b = some (lo, hi) ∧ hi ≤ k) :
    Gen.apart a b = true := by
  unfold Gen.apart
  rcases ha with ha | ⟨lo, hi, ha, hk⟩
  · rw [ha]
  · rcases hb with hb | ⟨lo', hi', hb, hk'⟩
    · rw [ha, hb]
    · rw [ha, hb]; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega

theorem span_up_ge {n : ℕ} (k : ℕ) (x : Gen G' n)
    (h : Gen.span x = none ∨ ∃ lo hi, Gen.span x = some (lo, hi) ∧ k ≤ lo) :
    Gen.span x.up = none ∨ ∃ lo hi, Gen.span x.up = some (lo, hi) ∧ k + 1 ≤ lo := by
  rcases h with h | ⟨lo, hi, h, hk⟩
  · left; simp [Gen.span, h]
  · right; exact ⟨lo + 1, hi + 1, by simp [Gen.span, h], by omega⟩

theorem span_ge_zero {n : ℕ} (x : Gen G' n) :
    Gen.span x = none ∨ ∃ lo hi, Gen.span x = some (lo, hi) ∧ 0 ≤ lo := by
  cases h : Gen.span x with
  | none => left; rfl
  | some p => right; exact ⟨p.1, p.2, rfl, Nat.zero_le _⟩

theorem mem_shift {n : ℕ} (u : Circuit G' n) (a : Gen G' (n + 1))
    (ha : a ∈ FreeMonoid.toList (shift u)) : ∃ x ∈ FreeMonoid.toList u, a = x.up := by
  simp only [Circuit.shift, FreeMonoid.toList_map, List.mem_map] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨x, hx, rfl⟩

theorem mem_pad (m : ℕ) {k : ℕ} (v : Circuit G' k) (b : Gen G' (m + k))
    (hb : b ∈ FreeMonoid.toList (Circuit.pad m v)) : ∃ y : Gen G' k, b = y.pad m := by
  simp only [Circuit.pad, FreeMonoid.toList_map, List.mem_map] at hb
  obtain ⟨y, -, rfl⟩ := hb
  exact ⟨y, rfl⟩

theorem span_pad_le (m : ℕ) {k : ℕ} (y : Gen G' k) :
    Gen.span (y.pad m) = none ∨ ∃ lo hi, Gen.span (y.pad m) = some (lo, hi) ∧ hi ≤ k := by
  rw [span_pad]; exact span_le y

/-- A scalar circuit moved up is the scalar circuit. -/
theorem shift_pad_scalar {R : CRel G'} (n : ℕ) (w : Circuit G' 0) :
    Derivable (Lift R (n + 1)) (shift (Circuit.pad n w)) (Circuit.pad (n + 1) w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [map_one]; exact Derivable.refl _
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul]
    refine Derivable.mul ?_ ih
    cases g with
    | gate0 c => exact Derivable.of (Lift.scalar c)

variable (Φ : GateSubst G G')

/-- The structural rules are carried to derivable equations. -/
theorem GateSubst.lift_map (hsc : ∀ c c' : G' 0, c = c') {R : CRel G} {R' : CRel G'}
    (hR : ∀ k w v, R k w v → Derivable (Lift R' k) (Φ.map k w) (Φ.map k v)) :
    ∀ {n : ℕ} {w v : Circuit G n}, Lift R n w v →
      Derivable (Lift R' n) (Φ.map n w) (Φ.map n v)
  | _, _, _, .rule r => hR _ _ _ r
  | _, _, _, .shift r => by
    rw [Φ.map_shift, Φ.map_shift]
    exact derivable_shift (GateSubst.lift_map hsc hR r)
  | _, _, _, @Lift.comm1 _ _ n c g => by
    rw [map_mul, map_mul, Φ.map_of, Φ.map_of]
    refine comm_words hsc _ _ fun a ha b hb => ?_
    obtain ⟨x, -, rfl⟩ := mem_shift _ a ha
    obtain ⟨y, rfl⟩ := mem_pad n _ b hb
    exact apart_of_le 1 _ _ (span_up_ge 0 x (span_ge_zero x)) (span_pad_le n y)
  | _, _, _, @Lift.comm2 _ _ n c g => by
    rw [map_mul, map_mul, Φ.map_of, Φ.map_of]
    refine comm_words hsc _ _ fun a ha b hb => ?_
    obtain ⟨x, hx, rfl⟩ := mem_shift _ a ha
    obtain ⟨x', -, rfl⟩ := mem_shift _ x hx
    obtain ⟨y, rfl⟩ := mem_pad n _ b hb
    exact apart_of_le 2 _ _ (span_up_ge 1 _ (span_up_ge 0 x' (span_ge_zero x')))
      (span_pad_le n y)
  | _, _, _, @Lift.comm3 _ _ n c g => by
    rw [map_mul, map_mul, Φ.map_of, Φ.map_of]
    refine comm_words hsc _ _ fun a ha b hb => ?_
    obtain ⟨x, hx, rfl⟩ := mem_shift _ a ha
    obtain ⟨x', hx', rfl⟩ := mem_shift _ x hx
    obtain ⟨x'', -, rfl⟩ := mem_shift _ x' hx'
    obtain ⟨y, rfl⟩ := mem_pad n _ b hb
    exact apart_of_le 3 _ _
      (span_up_ge 2 _ (span_up_ge 1 _ (span_up_ge 0 x'' (span_ge_zero x''))))
      (span_pad_le n y)
  | _, _, _, @Lift.scalar _ _ n c => by
    rw [Φ.map_of, Φ.map_of]
    exact shift_pad_scalar n (Φ.φ0 c)

/-- Lemma 20: a substitution sending each rule of `Base`, on its own wires,
to a derivable equation carries derivations. -/
theorem GateSubst.derivable_map (hsc : ∀ c c' : G' 0, c = c') {Base : CRel G} {Base' : CRel G'}
    (hB : ∀ k w v, Base k w v → Derivable (Lift (Padded Base') k) (Φ.map k w) (Φ.map k v))
    {n : ℕ} {w v : Circuit G n} (h : Derivable (Lift (Padded Base) n) w v) :
    Derivable (Lift (Padded Base') n) (Φ.map n w) (Φ.map n v) := by
  refine derivable_map_of _ _ (Φ.map n) (fun a b r => ?_) h
  refine Φ.lift_map hsc (fun k w v r => ?_) r
  cases r with
  | @pad j m w v b =>
    rw [Φ.map_pad, Φ.map_pad]
    exact derivable_pad m (hB _ _ _ b)

/-- Lemma 19: if decoding the encoding of each gate derives the gate, then
decoding the encoding of every circuit derives the circuit. -/
theorem GateSubst.derivable_comp {Base : CRel G} (E : GateSubst G G') (D : GateSubst G' G)
    (h0 : ∀ c, Derivable (Lift (Padded Base) 0) (D.map 0 (E.φ0 c)) (g0 c))
    (h1 : ∀ c, Derivable (Lift (Padded Base) 1) (D.map 1 (E.φ1 c)) (g1 c))
    (h2 : ∀ c, Derivable (Lift (Padded Base) 2) (D.map 2 (E.φ2 c)) (g2 c))
    (h3 : ∀ c, Derivable (Lift (Padded Base) 3) (D.map 3 (E.φ3 c)) (g3 c)) :
    ∀ {n : ℕ} (w : Circuit G n), Derivable (Lift (Padded Base) n) (D.map n (E.map n w)) w := by
  have hgen : ∀ {n : ℕ} (g : Gen G n),
      Derivable (Lift (Padded Base) n) (D.map n (E.gen g)) (FreeMonoid.of g) := by
    intro n g
    induction g with
    | @gate0 m c =>
      show Derivable _ (D.map (m + 0) (Circuit.pad m (E.φ0 c))) _
      rw [D.map_pad]; exact derivable_pad m (h0 c)
    | @gate1 m c =>
      show Derivable _ (D.map (m + 1) (Circuit.pad m (E.φ1 c))) _
      rw [D.map_pad]; exact derivable_pad m (h1 c)
    | @gate2 m c =>
      show Derivable _ (D.map (m + 2) (Circuit.pad m (E.φ2 c))) _
      rw [D.map_pad]; exact derivable_pad m (h2 c)
    | @gate3 m c =>
      show Derivable _ (D.map (m + 3) (Circuit.pad m (E.φ3 c))) _
      rw [D.map_pad]; exact derivable_pad m (h3 c)
    | @up m g ih =>
      show Derivable _ (D.map (m + 1) (shift (E.gen g))) _
      rw [D.map_shift]
      exact derivable_shift ih
  intro n w
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [map_one]; exact Derivable.refl _
  | mul_of g w ih =>
    rw [map_mul, map_mul, E.map_of]
    exact (hgen g).mul ih

end Carry

end QCert.Minimality
