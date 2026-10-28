/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément's relations at every placement of indices

Relations (1)–(19) are stated for all distinct indices, so they are
invariant under any injective map of indices; (20) and (21) are stated at
the first four and six indices only.  `RelK full` is the theory with
(1)–(19), and, when `full`, (20) and (21) at every injective placement
`f : Fin 4 → Fin n`, `f : Fin 6 → Fin n`.  It is invariant under injective
maps of indices (`Derivable.mapC`), so a derivation found on concrete
indices `0, …, m-1` holds at any distinct indices.

`RelK false` is contained in `Rel` (`relK_false_rel`); that `RelK true` is
too (`(20)` and `(21)` at any placement are consequences of `Rel`) is
`Conj.lean`'s `relK_rel`.
-/
import QCert.Clement2019.Syntax

namespace QCert.Clement2019

open FreeMonoid

variable {m n : ℕ}

/-- A generator moved along an injective map of indices. -/
def Gen.map (f : Fin m → Fin n) (hf : Function.Injective f) : Gen m → Gen n
  | .Z a => .Z (f a)
  | .H a b h => .H (f a) (f b) (hf.ne h)
  | .X a b h => .X (f a) (f b) (hf.ne h)

/-- A word moved along an injective map of indices. -/
def wmapC (f : Fin m → Fin n) (hf : Function.Injective f) : Word (Gen m) →* Word (Gen n) :=
  FreeMonoid.map (Gen.map f hf)

theorem wmapC_ofList (f : Fin m → Fin n) (hf : Function.Injective f) (l : List (Gen m)) :
    wmapC f hf (ofList l) = ofList (l.map (Gen.map f hf)) := rfl

theorem Gen.map_id (g : Gen n) : g.map id Function.injective_id = g := by
  cases g <;> rfl

theorem Gen.map_comp {k : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) (g : Fin k → Fin m)
    (hg : Function.Injective g) (x : Gen k) :
    (x.map g hg).map f hf = x.map (f ∘ g) (hf.comp hg) := by
  cases x <;> rfl

theorem wmapC_id (w : Word (Gen n)) : wmapC id Function.injective_id w = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih => rw [map_mul, ih]; simp [wmapC, Gen.map_id]

theorem wmapC_comp {k : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) (g : Fin k → Fin m)
    (hg : Function.Injective g) (w : Word (Gen k)) :
    wmapC f hf (wmapC g hg w) = wmapC (f ∘ g) (hf.comp hg) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of x w ih => rw [map_mul, map_mul, ih, map_mul]; simp [wmapC, Gen.map_comp]

/-- The two-level `H` at the indices `f i`, `f j`. -/
abbrev hF {k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f) (i j : Fin k)
    (h : i ≠ j := by decide) : Gen n := .H (f i) (f j) (hf.ne h)

/-- The left side of (20) at the indices `f 0, …, f 3`. -/
def l20L (f : Fin 4 → Fin n) (hf : Function.Injective f) : List (Gen n) :=
  [hF f hf 0 1, hF f hf 0 2, hF f hf 1 3, hF f hf 0 1, .Z (f 0), .Z (f 1), hF f hf 0 2, hF f hf 1 3]

/-- The right side of (20) at the indices `f 0, …, f 3`. -/
def l20R (f : Fin 4 → Fin n) (hf : Function.Injective f) : List (Gen n) :=
  [hF f hf 0 2, hF f hf 1 3, hF f hf 0 1, .Z (f 0), .Z (f 1), hF f hf 0 2, hF f hf 1 3, hF f hf 0 1]

/-- The left side of (21) at the indices `f 0, …, f 5`. -/
def l21L (f : Fin 6 → Fin n) (hf : Function.Injective f) : List (Gen n) :=
  [hF f hf 0 1, hF f hf 0 2, hF f hf 1 3, hF f hf 0 4, hF f hf 1 5, hF f hf 0 1, .Z (f 0),
    .Z (f 1), hF f hf 0 4, hF f hf 1 5, hF f hf 0 2, hF f hf 1 3]

/-- The right side of (21) at the indices `f 0, …, f 5`. -/
def l21R (f : Fin 6 → Fin n) (hf : Function.Injective f) : List (Gen n) :=
  [hF f hf 0 2, hF f hf 1 3, hF f hf 0 4, hF f hf 1 5, hF f hf 0 1, .Z (f 0), .Z (f 1),
    hF f hf 0 4, hF f hf 1 5, hF f hf 0 2, hF f hf 1 3, hF f hf 0 1]

theorem l20_map (f : Fin m → Fin n) (hf : Function.Injective f) (g : Fin 4 → Fin m)
    (hg : Function.Injective g) :
    (l20L g hg).map (Gen.map f hf) = l20L (f ∘ g) (hf.comp hg) ∧
      (l20R g hg).map (Gen.map f hf) = l20R (f ∘ g) (hf.comp hg) := ⟨rfl, rfl⟩

theorem l21_map (f : Fin m → Fin n) (hf : Function.Injective f) (g : Fin 6 → Fin m)
    (hg : Function.Injective g) :
    (l21L g hg).map (Gen.map f hf) = l21L (f ∘ g) (hf.comp hg) ∧
      (l21R g hg).map (Gen.map f hf) = l21R (f ∘ g) (hf.comp hg) := ⟨rfl, rfl⟩

theorem l20_congr {f g : Fin 4 → Fin n} (e : f = g) (hf : Function.Injective f)
    (hg : Function.Injective g) : l20L f hf = l20L g hg ∧ l20R f hf = l20R g hg := by
  subst e; exact ⟨rfl, rfl⟩

theorem l21_congr {f g : Fin 6 → Fin n} (e : f = g) (hf : Function.Injective f)
    (hg : Function.Injective g) : l21L f hf = l21L g hg ∧ l21R f hf = l21R g hg := by
  subst e; exact ⟨rfl, rfl⟩

/-- Relations (1)–(19) at all distinct indices and, when `full`, (20) and (21) at every
injective placement. -/
inductive RelK (full : Bool) {n : ℕ} : WRel (Gen n)
  | r1 (j : Fin n) : RelK full (Z_[j] * Z_[j]) 1
  | r2 {j k : Fin n} (hjk : j ≠ k) : RelK full (H_[j,k] * H_[j,k]) 1
  | r3 {j k : Fin n} (hjk : j ≠ k) : RelK full (X_[j,k] * X_[j,k]) 1
  | r4 {j k : Fin n} (hjk : j ≠ k) : RelK full (Z_[j] * Z_[k]) (Z_[k] * Z_[j])
  | r5 {j k l : Fin n} (hjk : j ≠ k) (hlj : l ≠ j) (hlk : l ≠ k) :
      RelK full (Z_[l] * H_[j,k]) (H_[j,k] * Z_[l])
  | r6 {j k l : Fin n} (hjk : j ≠ k) (hlj : l ≠ j) (hlk : l ≠ k) :
      RelK full (Z_[l] * X_[j,k]) (X_[j,k] * Z_[l])
  | r7 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hjt : j ≠ t) (hkl : k ≠ l)
      (hkt : k ≠ t) : RelK full (H_[j,k] * H_[l,t]) (H_[l,t] * H_[j,k])
  | r8 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hjt : j ≠ t) (hkl : k ≠ l)
      (hkt : k ≠ t) : RelK full (H_[j,k] * X_[l,t]) (X_[l,t] * H_[j,k])
  | r9 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hjt : j ≠ t) (hkl : k ≠ l)
      (hkt : k ≠ t) : RelK full (X_[j,k] * X_[l,t]) (X_[l,t] * X_[j,k])
  | r10 {j k : Fin n} (hjk : j ≠ k) : RelK full (X_[j,k] * Z_[k]) (Z_[j] * X_[j,k])
  | r11 {j k : Fin n} (hjk : j ≠ k) : RelK full (X_[j,k] * Z_[j]) (Z_[k] * X_[j,k])
  | r12 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      RelK full (X_[j,k] * X_[j,l]) (X_[k,l] * X_[j,k])
  | r13 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      RelK full (X_[j,k] * X_[l,j]) (X_[l,k] * X_[j,k])
  | r14 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      RelK full (X_[j,k] * H_[j,l]) (H_[k,l] * X_[j,k])
  | r15 {j k l : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      RelK full (X_[j,k] * H_[l,j]) (H_[l,k] * X_[j,k])
  | r16 {j k : Fin n} (hjk : j ≠ k) : RelK full (Z_[j] * Z_[k] * X_[j,k]) (X_[j,k] * Z_[j] * Z_[k])
  | r17 {j k : Fin n} (hjk : j ≠ k) : RelK full (Z_[j] * Z_[k] * H_[j,k]) (H_[j,k] * Z_[j] * Z_[k])
  | r18 {j k : Fin n} (hjk : j ≠ k) : RelK full (H_[j,k] * X_[j,k]) (Z_[k] * H_[j,k])
  | r19 {j k l t : Fin n} (hjk : j ≠ k) (hlt : l ≠ t) (hjl : j ≠ l) (hkt : k ≠ t) (hjt : j ≠ t) :
      RelK full (H_[j,k] * H_[l,t] * H_[j,l] * H_[k,t]) (H_[j,l] * H_[k,t] * H_[j,k] * H_[l,t])
  | r20 (hb : full = true) (f : Fin 4 → Fin n) (hf : Function.Injective f) :
      RelK full (ofList (l20L f hf)) (ofList (l20R f hf))
  | r21 (hb : full = true) (f : Fin 6 → Fin n) (hf : Function.Injective f) :
      RelK full (ofList (l21L f hf)) (ofList (l21R f hf))

variable {full : Bool}

theorem relK_map (f : Fin m → Fin n) (hf : Function.Injective f) {w v : Word (Gen m)}
    (h : RelK full w v) : RelK full (wmapC f hf w) (wmapC f hf v) := by
  have ne : ∀ {a c : Fin m}, a ≠ c → f a ≠ f c := fun h e => h (hf e)
  cases h with
  | r1 j => exact RelK.r1 (f j)
  | r2 h => exact RelK.r2 (ne h)
  | r3 h => exact RelK.r3 (ne h)
  | r4 h => exact RelK.r4 (ne h)
  | r5 h1 h2 h3 => exact RelK.r5 (ne h1) (ne h2) (ne h3)
  | r6 h1 h2 h3 => exact RelK.r6 (ne h1) (ne h2) (ne h3)
  | r7 h1 h2 h3 h4 h5 h6 => exact RelK.r7 (ne h1) (ne h2) (ne h3) (ne h4) (ne h5) (ne h6)
  | r8 h1 h2 h3 h4 h5 h6 => exact RelK.r8 (ne h1) (ne h2) (ne h3) (ne h4) (ne h5) (ne h6)
  | r9 h1 h2 h3 h4 h5 h6 => exact RelK.r9 (ne h1) (ne h2) (ne h3) (ne h4) (ne h5) (ne h6)
  | r10 h => exact RelK.r10 (ne h)
  | r11 h => exact RelK.r11 (ne h)
  | r12 h1 h2 h3 => exact RelK.r12 (ne h1) (ne h2) (ne h3)
  | r13 h1 h2 h3 => exact RelK.r13 (ne h1) (ne h2) (ne h3)
  | r14 h1 h2 h3 => exact RelK.r14 (ne h1) (ne h2) (ne h3)
  | r15 h1 h2 h3 => exact RelK.r15 (ne h1) (ne h2) (ne h3)
  | r16 h => exact RelK.r16 (ne h)
  | r17 h => exact RelK.r17 (ne h)
  | r18 h => exact RelK.r18 (ne h)
  | r19 h1 h2 h3 h4 h5 => exact RelK.r19 (ne h1) (ne h2) (ne h3) (ne h4) (ne h5)
  | r20 hb g hg =>
    rw [wmapC_ofList, wmapC_ofList, (l20_map f hf g hg).1, (l20_map f hf g hg).2]
    exact RelK.r20 hb (f ∘ g) (hf.comp hg)
  | r21 hb g hg =>
    rw [wmapC_ofList, wmapC_ofList, (l21_map f hf g hg).1, (l21_map f hf g hg).2]
    exact RelK.r21 hb (f ∘ g) (hf.comp hg)

/-- Derivations move along injective maps of indices. -/
theorem Derivable.mapC (f : Fin m → Fin n) (hf : Function.Injective f) {w v : Word (Gen m)}
    (h : Derivable (RelK full) w v) : Derivable (RelK full) (wmapC f hf w) (wmapC f hf v) := by
  have : conGen (RelK full (n := m)) ≤ (conGen (RelK full (n := n))).comap (wmapC f hf)
      (map_mul _) :=
    Con.conGen_le fun x y hxy => ConGen.Rel.of _ _ (relK_map f hf hxy)
  exact this h

/-- A derivation with (1)–(19) only is one in the full theory. -/
theorem liftK {w v : Word (Gen n)} (h : Derivable (RelK false) w v) :
    Derivable (RelK true) w v := by
  have : conGen (RelK false (n := n)) ≤ conGen (RelK true (n := n)) := by
    refine Con.conGen_le fun x y hxy => ConGen.Rel.of _ _ ?_
    cases hxy with
    | r1 j => exact RelK.r1 j
    | r2 h => exact RelK.r2 h
    | r3 h => exact RelK.r3 h
    | r4 h => exact RelK.r4 h
    | r5 h1 h2 h3 => exact RelK.r5 h1 h2 h3
    | r6 h1 h2 h3 => exact RelK.r6 h1 h2 h3
    | r7 h1 h2 h3 h4 h5 h6 => exact RelK.r7 h1 h2 h3 h4 h5 h6
    | r8 h1 h2 h3 h4 h5 h6 => exact RelK.r8 h1 h2 h3 h4 h5 h6
    | r9 h1 h2 h3 h4 h5 h6 => exact RelK.r9 h1 h2 h3 h4 h5 h6
    | r10 h => exact RelK.r10 h
    | r11 h => exact RelK.r11 h
    | r12 h1 h2 h3 => exact RelK.r12 h1 h2 h3
    | r13 h1 h2 h3 => exact RelK.r13 h1 h2 h3
    | r14 h1 h2 h3 => exact RelK.r14 h1 h2 h3
    | r15 h1 h2 h3 => exact RelK.r15 h1 h2 h3
    | r16 h => exact RelK.r16 h
    | r17 h => exact RelK.r17 h
    | r18 h => exact RelK.r18 h
    | r19 h1 h2 h3 h4 h5 => exact RelK.r19 h1 h2 h3 h4 h5
    | r20 hb => cases hb
    | r21 hb => cases hb
  exact this h

/-- Relations (1)–(19) are relations of `Rel`. -/
theorem relK_false_rel {w v : Word (Gen n)} (h : Derivable (RelK false) w v) :
    Derivable Rel w v := by
  have : conGen (RelK false (n := n)) ≤ conGen (Rel (n := n)) := by
    refine Con.conGen_le fun x y hxy => ConGen.Rel.of _ _ ?_
    cases hxy with
    | r1 j => exact Rel.r1 j
    | r2 h => exact Rel.r2 h
    | r3 h => exact Rel.r3 h
    | r4 h => exact Rel.r4 h
    | r5 h1 h2 h3 => exact Rel.r5 h1 h2 h3
    | r6 h1 h2 h3 => exact Rel.r6 h1 h2 h3
    | r7 h1 h2 h3 h4 h5 h6 => exact Rel.r7 h1 h2 h3 h4 h5 h6
    | r8 h1 h2 h3 h4 h5 h6 => exact Rel.r8 h1 h2 h3 h4 h5 h6
    | r9 h1 h2 h3 h4 h5 h6 => exact Rel.r9 h1 h2 h3 h4 h5 h6
    | r10 h => exact Rel.r10 h
    | r11 h => exact Rel.r11 h
    | r12 h1 h2 h3 => exact Rel.r12 h1 h2 h3
    | r13 h1 h2 h3 => exact Rel.r13 h1 h2 h3
    | r14 h1 h2 h3 => exact Rel.r14 h1 h2 h3
    | r15 h1 h2 h3 => exact Rel.r15 h1 h2 h3
    | r16 h => exact Rel.r16 h
    | r17 h => exact Rel.r17 h
    | r18 h => exact Rel.r18 h
    | r19 h1 h2 h3 h4 h5 => exact Rel.r19 h1 h2 h3 h4 h5
    | r20 hb => cases hb
    | r21 hb => cases hb
  exact this h

end QCert.Clement2019
