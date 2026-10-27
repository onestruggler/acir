/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The Reidemeister–Schreier theorem for monoids

Theorem 4.3 of Bian–Selinger, *Generators and relations for 2-qubit
Clifford+T operators* (arXiv:2204.02217), used by both Bian–Selinger
developments (`CliffordT2`, `CliffordCS3`).

Data: alphabets `X` (the subgroup's generators) and `Y` (the group's),
theories `Γ_X` and `Γ_Y`, a set `C` of cosets with a distinguished `I`,
a translation `f : X → Y*`, and a coset action `h : C × Y → X* × C`,
extended to words by `h**` (Definition 4.2, `hstar`).  Hypotheses:

(a) for every `x ∈ X`, `h**(I, f(x)) = (v, I)` with `v ∼ x`;
(b) for every coset `c` and axiom `(w, w')` of `Γ_Y`,
    `h**(c, w) = (v, d)`, `h**(c, w') = (v', d')` with `v ∼ v'`, `d = d'`.

Conclusion: `f*(v) ∼ f*(v')` implies `v ∼ v'`.
-/
import QCert.Presentation

namespace QCert

universe u v w

variable {X : Type u} {Y : Type v} {C : Type w}

/-- `h**` on lists: run the coset action from the coset `c`, collecting
the words. -/
def runCoset (h : C → Y → Word X × C) : C → List Y → Word X × C
  | c, [] => (1, c)
  | c, y :: ys => ((h c y).1 * (runCoset h (h c y).2 ys).1, (runCoset h (h c y).2 ys).2)

/-- `h**` (Definition 4.2). -/
def hstar (h : C → Y → Word X × C) (c : C) (w : Word Y) : Word X × C :=
  runCoset h c (FreeMonoid.toList w)

theorem runCoset_append (h : C → Y → Word X × C) (c : C) (l₁ l₂ : List Y) :
    runCoset h c (l₁ ++ l₂) =
      ((runCoset h c l₁).1 * (runCoset h (runCoset h c l₁).2 l₂).1,
        (runCoset h (runCoset h c l₁).2 l₂).2) := by
  induction l₁ generalizing c with
  | nil => simp [runCoset]
  | cons y ys ih => simp only [List.cons_append, runCoset, ih, mul_assoc]

theorem hstar_one (h : C → Y → Word X × C) (c : C) : hstar h c 1 = (1, c) := rfl

theorem hstar_mul (h : C → Y → Word X × C) (c : C) (w w' : Word Y) :
    hstar h c (w * w') =
      ((hstar h c w).1 * (hstar h (hstar h c w).2 w').1, (hstar h (hstar h c w).2 w').2) :=
  runCoset_append h c _ _

theorem hstar_of (h : C → Y → Word X × C) (c : C) (y : Y) :
    hstar h c (FreeMonoid.of y) = h c y := by
  simp [hstar, FreeMonoid.toList_of, runCoset]

section RS

variable {ΓX : WRel X} {ΓY : WRel Y} (h : C → Y → Word X × C)

/-- The relation of Claim B: `w ∼ w'` when, from every coset, `h**`
reaches the same coset along both, with derivably equal words. -/
def rsRel (ΓX : WRel X) (w w' : Word Y) : Prop :=
  ∀ c, (hstar h c w).2 = (hstar h c w').2 ∧ Derivable ΓX (hstar h c w).1 (hstar h c w').1

/-- The relation of Claim B is a congruence. -/
def rsCon (ΓX : WRel X) : Con (Word Y) where
  r := rsRel h ΓX
  iseqv :=
    { refl := fun w c => ⟨rfl, Derivable.refl _⟩
      symm := fun hww c => ⟨(hww c).1.symm, (hww c).2.symm⟩
      trans := fun h1 h2 c => ⟨(h1 c).1.trans (h2 c).1, (h1 c).2.trans (h2 c).2⟩ }
  mul' := by
    intro w w' u u' hw hu c
    rw [hstar_mul, hstar_mul]
    obtain ⟨hc, hd⟩ := hw c
    rw [← hc]
    exact ⟨(hu _).1, hd.mul (hu _).2⟩

/-- Claim B. -/
theorem rs_claimB
    (hb : ∀ (c : C) (w w' : Word Y), ΓY w w' →
      (hstar h c w).2 = (hstar h c w').2 ∧ Derivable ΓX (hstar h c w).1 (hstar h c w').1)
    {w w' : Word Y} (hw : Derivable ΓY w w') : rsRel h ΓX w w' := by
  have : conGen ΓY ≤ rsCon h ΓX := Con.conGen_le fun a b hab c => hb c a b hab
  exact this hw

/-- Claim A. -/
theorem rs_claimA (I : C) (f : X → Word Y)
    (ha : ∀ x, (hstar h I (f x)).2 = I ∧ Derivable ΓX (hstar h I (f x)).1 (FreeMonoid.of x))
    (v : Word X) :
    (hstar h I (FreeMonoid.lift f v)).2 = I ∧
      Derivable ΓX (hstar h I (FreeMonoid.lift f v)).1 v := by
  induction v using FreeMonoid.inductionOn' with
  | one => exact ⟨rfl, Derivable.refl _⟩
  | mul_of x v ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, hstar_mul, (ha x).1]
    exact ⟨ih.1, (ha x).2.mul ih.2⟩

/-- **Theorem 4.3** (Reidemeister–Schreier theorem for monoids). -/
theorem reidemeister_schreier (I : C) (f : X → Word Y)
    (ha : ∀ x, (hstar h I (f x)).2 = I ∧ Derivable ΓX (hstar h I (f x)).1 (FreeMonoid.of x))
    (hb : ∀ (c : C) (w w' : Word Y), ΓY w w' →
      (hstar h c w).2 = (hstar h c w').2 ∧ Derivable ΓX (hstar h c w).1 (hstar h c w').1)
    {v v' : Word X} (hv : Derivable ΓY (FreeMonoid.lift f v) (FreeMonoid.lift f v')) :
    Derivable ΓX v v' :=
  ((rs_claimA h I f ha v).2.symm.trans ((rs_claimB h hb hv) I).2).trans
    (rs_claimA h I f ha v').2

end RS

end QCert
