/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The normal form of the circuits on four wires over X, CX, CCX and Ex: Lafont's canonical forms of the even permutations of sixteen points, translated

Translation of `NormalForm.agda`.  Lafont's canonical form of an even
permutation of `n` points (`Lib/Alternating/Normalization`) is a canonical
form on the points `1, …, n - 1` followed by a stairs: a run of cycles
`ω₀ ω₁ …` that brings some point to position 0, its last cycle doubled when
it comes from the last point.  Read through the translation `g` of the
cycles into circuits, a stairs at the points from `d` on is the circuit
`Ω d * Ω (d + 1) * …` (`stairs`), and a canonical form is the product of its
stairs, the highest first (`canon`).  That circuit is the translation of
Lafont's canonical form, letter for letter (`canon_g`).

The normal form of a circuit is Lafont's normal form of its word in the
cycles (`nf`).  With Lafont's Lemmas 6 and 8 and the presentation
(`Presentation`) this gives: every circuit is equal by the rules to its
canonical circuit (`normal_form`); `nf` respects the rules (`nf_cong`) and
fixes the canonical circuits (`nf_canon`); canonical circuits with the same
function are the same (`canon_unique`); and every even permutation is
carried out by one (`canon_onto`).

Every statement here is generic: nothing is proved by evaluating a normal
form.  Lafont's `nf` works by rewriting, and on the word of a circuit it
passes through millions of letters.  To compute the normal form of a
circuit, read it off the circuit's permutation instead: `nf_sem` says it is
the canonical form that Lafont's Lemma 6 (`Alternating.canonical`) finds for
that permutation, by recursion on the sixteen points.

**Deviations from the Agda.**  The Agda's `canonᵈ` is `canond`.  `canon_onto`
returns a subtype (the Agda's `Σ`).  The packaging `nfp′`, `unique-nf` in the
Agda's normal-form records is not translated (the framework has no such
records); its content is `nf_cong`, `normal_form` and `unique`.
-/
import QCert.Alt16RevCir.Presentation

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp
open Alternating (Alt C)

variable {n : ℕ}

/-! ## Canonical circuits -/

/-- Lafont's canonical forms of the even permutations of sixteen points. -/
abbrev NF : Type := Alternating.NF 16

/-- A stairs at the points from `d` on: the cycles `Ω d`, `Ω (d + 1)`, …,
the last one doubled for `ωω`. -/
def stairs : {n : ℕ} → ℕ → C n → Circ 4
  | _, _, .ε => 1
  | _, d, .ωc c => Ω d * stairs (d + 1) c
  | _, d, .ωω => Ω d * Ω d

/-- A canonical form at the points from `d` on: the canonical form of the
points above `d`, then the stairs at `d`. -/
def canond : {n : ℕ} → ℕ → Alternating.NF n → Circ 4
  | 0, _, _ => 1
  | _ + 1, d, (x, c) => canond (d + 1) x * stairs d c

def canon (x : NF) : Circ 4 := canond 0 x

/-! These are Lafont's stairs and canonical forms, read through `g`. -/

theorem stairs_g : ∀ {n : ℕ} (d : ℕ) (c : C n),
    stairs d c = FreeMonoid.lift (gd d) (Alternating.sec c)
  | _, _, .ε => by rw [stairs, Alternating.sec_ε, map_one]
  | _, d, .ωc c => by
    rw [stairs, stairs_g (d + 1) c, Alternating.sec_ωc, map_mul, gd_up]
    rfl
  | _, _, .ωω => by
    rw [stairs, Alternating.sec_ωω, map_mul]
    rfl

theorem canond_g : ∀ {n : ℕ} (d : ℕ) (x : Alternating.NF n),
    canond d x = FreeMonoid.lift (gd d) (Alternating.inv_nf x)
  | 0, _, x => by rw [canond, Alternating.inv_nf_zero, map_one]
  | n + 1, d, (x, c) => by
    rw [canond, Alternating.inv_nf_succ, map_mul, gd_up, canond_g (d + 1) x, stairs_g d c]

theorem canon_g (x : NF) : canon x = FreeMonoid.lift g (Alternating.inv_nf x) :=
  canond_g 0 x

/-! ## The normal form of a circuit -/

/-- Lafont's normal form of the circuit's word in the cycles. -/
def nf (w : Circ 4) : NF := Alternating.nf (FreeMonoid.lift f w)

/-- Lafont's Lemma 8, read in the permutations: a word in the cycles and its
canonical form have the same permutation. -/
private theorem lemma_8 (u : Alternating.Circ n) (i : Fin n) :
    Alt.perm (Alternating.sem (Alternating.inv_nf (Alternating.nf u))) i =
      Alt.perm (Alternating.sem u) i :=
  Alternating.soundness (Alternating.inv_nf_nf Alternating.fig10 u) i

/-- The same for the word of a circuit.  The definitions of `nf` and `semA`
are unfolded first: left to unification at sixteen points, Lafont's `nf`
would be unfolded through its sixteen levels. -/
private theorem lemma_8₄ (w : Circ 4) (i : Fin 16) :
    Alt.perm (Alternating.sem (Alternating.inv_nf (nf w))) i = Alt.perm (semA w) i := by
  unfold nf semA
  exact lemma_8 (FreeMonoid.lift f w) i

/-- So the normal form of a word is the canonical form of its permutation,
canonical forms being unique.  The permutation is a variable: at sixteen
points `canonical` computes, and two spellings of its argument would be
compared through sixteen levels of it. -/
private theorem nf_semL (u : Alternating.Circ n) {a : Alt n} (h : a = Alternating.sem u) :
    Alternating.nf u = (Alternating.canonical n a).1 := by
  subst h
  exact Alternating.inv_nf_injective fun i =>
    (lemma_8 u i).trans ((Alternating.canonical n _).2 i).symm

/-- A canonical circuit carries out the permutation of Lafont's canonical
form: it is that form's circuit, and `g` keeps the meaning. -/
private theorem canon_sem (x : NF) (i : Fin 16) :
    Alt.perm (semA (canon x)) i = Alt.perm (Alternating.sem (Alternating.inv_nf x)) i := by
  rw [semA_sem, canon_g]
  exact g_sem (Alternating.inv_nf x) i

/-- Canonical circuits with the same permutation are the same. -/
theorem unique {x y : NF} (e : semA (canon x) = semA (canon y)) : x = y :=
  Alternating.inv_nf_injective fun i =>
    (canon_sem x i).symm.trans ((congrArg (fun p : Alt 16 => Alt.perm p i) e).trans (canon_sem y i))

/-- The normal form, read off the circuit's permutation. -/
theorem nf_sem (w : Circ 4) : nf w = (Alternating.canonical 16 (semA w)).1 :=
  nf_semL (FreeMonoid.lift f w) rfl

/-! ## The theorems -/

/-- The permutation of the canonical circuit of a circuit is the circuit's. -/
private theorem semA_canon_nf (w : Circ 4) : semA (canon (nf w)) = semA w :=
  Alternating.Alt.ext fun i => (canon_sem (nf w) i).trans (lemma_8₄ w i)

/-- Every circuit is equal by the rules to its canonical circuit: the two
have the same permutation. -/
theorem normal_form (w : Circ 4) : 4 ⊢ canon (nf w) ≈ w :=
  complete (feq_of_semA (semA_canon_nf w))

/-- Circuits equal by the rules have the same normal form. -/
theorem nf_cong {w v : Circ 4} (e : 4 ⊢ w ≈ v) : nf w = nf v :=
  Alternating.inv_nf_injective fun i =>
    (lemma_8₄ w i).trans
      ((congrArg (fun p : Alt 16 => Alt.perm p i) (semA_congr (sound e))).trans
        (lemma_8₄ v i).symm)

/-- A canonical circuit is its own normal form. -/
theorem nf_canon (x : NF) : nf (canon x) = x :=
  Alternating.inv_nf_injective fun i =>
    (lemma_8₄ (canon x) i).trans (canon_sem x i)

/-- Canonical circuits with the same function are the same. -/
theorem canon_unique {x y : NF} (e : sem (canon x) ≐ sem (canon y)) : x = y :=
  unique (semA_congr e)

/-- Every even permutation of the sixteen positions is carried out by a
canonical circuit. -/
def canon_onto (a : Alt 16) : {x : NF // ∀ i, Alt.perm (semA (canon x)) i = Alt.perm a i} :=
  ⟨(Alternating.canonical 16 a).1, fun i =>
    (canon_sem _ i).trans ((Alternating.canonical 16 a).2 i)⟩

end QCert.Alt16RevCir
