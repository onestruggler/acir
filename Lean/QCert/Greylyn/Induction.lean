/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: completeness from the Main Lemma

§3.3.5.  For a generator `x` and a state `s`, write `Step s x` for
`nw (x s) · x ≈ nw s`: Lemma 32 for the edge `s → x s` (with `nw` the
sequence of normal edges to `I`).  If `Step` holds for every state and
generator, the normal words make the equations complete
(`QCert.NormalWords`; Lemma 33 and Theorem 34).

* `NormalPath r N q`: `r ⇒ q` by a sequence of normal edges labelled `N`
  (Definition 25, Convention 1); then `nw r = nw q · N`.
* `step_of_square`: a square of the Main Lemma (Lemma 31) at `s` — normal
  edges `x s ⇒ q` labelled `N'`, a path `t → q` labelled `G'` from
  `t = N s` all of whose states have level below that of `s`, and
  `N' x ≈ G' N` — gives `Step s x`, given `Step` along the path.
* `steps_of`: the induction on the level of `s` (proof of Lemma 32) that
  turns the Main Lemma for basic generators (Definition 28) into `Step` for
  every state and basic generator.
* `step_all`: from basic generators to all, each generator being a word of
  basic ones (Lemma 30).
-/
import QCert.Greylyn.Normal

namespace QCert.Greylyn

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-- Lemma 32 for one edge: `nw (x s) · x ≈ nw s`. -/
def Step (s : St n) (x : Gen n) : Prop :=
  Derivable (Rel n) (nw (sem n x * s) * FreeMonoid.of x) (nw s)

/-- `r ⇒ q` by a sequence of normal edges labelled `N` (Definition 25,
Convention 1): `N` is the word of the syllables of `r`, `S r`, … down to
`q`, the last one first. -/
inductive NormalPath : St n → Word (Gen n) → St n → Prop
  | refl (r : St n) : NormalPath r 1 r
  | step {r q : St n} {N : Word (Gen n)} (hr : r ≠ 1) :
      NormalPath (⟪syl r⟫ * r) N q → NormalPath r (N * syl r) q

theorem NormalPath.nw_eq {r q : St n} {N : Word (Gen n)} (h : NormalPath r N q) :
    nw r = nw q * N := by
  induction h with
  | refl r => rw [mul_one]
  | @step r q N hr _ ih => rw [nw_of_ne hr, ih, mul_assoc]

/-- Every state along the path `w` from `t` (both ends included) has level
below `L` (Definition 27). -/
def AllBelow (L : ℕ ×ₗ ℕ ×ₗ ℕ) (t : St n) (w : Word (Gen n)) : Prop :=
  ∀ u v : Word (Gen n), w = u * v → level (⟪v⟫ * t) < L

theorem AllBelow.tail {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} {x : Gen n} {w : Word (Gen n)}
    (h : AllBelow L t (FreeMonoid.of x * w)) : AllBelow L t w := by
  intro u v huv; exact h (FreeMonoid.of x * u) v (by rw [huv, mul_assoc])

/-- Along a path of states of level below `L`, given `Step` for all such
edges, the normal words commute with the path. -/
theorem path_step (L : ℕ ×ₗ ℕ ×ₗ ℕ)
    (hstep : ∀ u y, level u < L → level (sem n y * u) < L → Step u y) :
    ∀ (w : Word (Gen n)) (t : St n), AllBelow L t w →
      Derivable (Rel n) (nw (⟪w⟫ * t) * w) (nw t) := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => intro t _; simp only [map_one, one_mul, mul_one]; exact Derivable.refl _
  | mul_of x w ih =>
    intro t hw
    have h1 : level (⟪w⟫ * t) < L := hw (FreeMonoid.of x) w rfl
    have h2 : level (sem n x * (⟪w⟫ * t)) < L := by
      have := hw 1 (FreeMonoid.of x * w) (by rw [one_mul])
      rwa [map_mul, FreeMonoid.lift_eval_of, mul_assoc] at this
    have hs := hstep _ x h1 h2
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc, ← mul_assoc (nw _)]
    exact (hs.mul (Derivable.refl w)).trans (ih t hw.tail)

/-- A square of the Main Lemma (Lemma 31) gives `Step` (proof of
Lemma 32). -/
theorem step_of_square {s : St n} (hs : s ≠ 1) {x : Gen n} (N' G' : Word (Gen n)) (q : St n)
    (hN : nw (sem n x * s) = nw q * N') (hq : ⟪G'⟫ * (⟪syl s⟫ * s) = q)
    (hG : AllBelow (level s) (⟪syl s⟫ * s) G')
    (hrel : Derivable (Rel n) (N' * FreeMonoid.of x) (G' * syl s))
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s x := by
  unfold Step
  have hp := path_step (level s) hstep G' _ hG
  rw [hq] at hp
  rw [hN, nw_of_ne hs, mul_assoc]
  refine ((Derivable.refl (nw q)).mul hrel).trans ?_
  rw [← mul_assoc]
  exact hp.mul (Derivable.refl _)

/-- The basic generators (Definition 28, `0`-based): `X_[α,α+1]`, `H_[0,1]`
and `ω_[0]`. -/
def Basic : Gen n → Prop
  | .X j k _ => (k : ℕ) = j + 1
  | .H j k _ => (j : ℕ) = 0 ∧ (k : ℕ) = 1
  | .ω j => (j : ℕ) = 0

/-- The induction on the level of `s` (proof of Lemma 32 from Lemma 31):
`Step` for every state and basic generator. -/
theorem steps_of
    (base : ∀ x, Basic x → Step (1 : St n) x)
    (main : ∀ (s : St n) x, s ≠ 1 → Basic x →
      (∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) → Step s x)
    (lift_basic : ∀ L : ℕ ×ₗ ℕ ×ₗ ℕ, (∀ (u : St n) x, Basic x → level u < L → Step u x) →
      ∀ u y, level u < L → level (sem n y * u) < L → Step u y) :
    ∀ (s : St n) x, Basic x → Step s x := by
  intro s
  induction s using wf_level.induction with
  | _ s ih =>
    intro x hx
    by_cases hs : s = 1
    · subst hs; exact base x hx
    · exact main s x hs hx (lift_basic (level s) (fun u x hx hu => ih u hu x hx))

/-- All letters of a word are basic. -/
def AllBasic (b : Word (Gen n)) : Prop := ∀ x ∈ FreeMonoid.toList b, Basic x

theorem word_step (hB : ∀ (s : St n) x, Basic x → Step s x) (b : Word (Gen n))
    (hb : AllBasic b) (s : St n) : Derivable (Rel n) (nw (⟪b⟫ * s) * b) (nw s) := by
  induction b using FreeMonoid.inductionOn' generalizing s with
  | one => simpa using Derivable.refl (nw s)
  | mul_of x w ih =>
    have hx : Basic x := hb x (by simp)
    have hw : AllBasic w := fun y hy => hb y (by simp [hy])
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc, ← mul_assoc (nw _)]
    exact ((hB _ x hx).mul (Derivable.refl w)).trans (ih hw s)

/-- From `Step` at basic generators, `Step` at every generator, each being
a word of basic generators (Lemma 30 (a)). -/
theorem step_all (hB : ∀ (s : St n) x, Basic x → Step s x)
    (decomp : ∀ y : Gen n, ∃ b, AllBasic b ∧ Derivable (Rel n) (FreeMonoid.of y) b) :
    ∀ (s : St n) y, Step s y := by
  intro s y
  obtain ⟨b, hb, hyb⟩ := decomp y
  have hsem : ⟪b⟫ = sem n y := by
    rw [← derivable_sound (fun _ _ h => sound h) hyb, FreeMonoid.lift_eval_of]
  have := word_step hB b hb s
  rw [hsem] at this
  exact ((Derivable.refl _).mul hyb).trans this

end

end QCert.Greylyn
