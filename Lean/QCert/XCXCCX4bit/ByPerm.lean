/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Presentations of permutation groups from completeness

Translation of `ByPerm.agda`.  Number the `2ᵏ` states of `k` wires (`enc`,
with inverse `dec`), and read each circuit as a Coxeter word (`tr`) whose
permutation it carries out on the numbered states (`at_`).  Then the
circuit's permutation (`perm`) is multiplicative by the semantics, it is
injective when the theory is complete, and it is onto when every
permutation is carried out by some circuit; with every letter invertible
(`grouplike`), the theory presents the symmetric group (`Full.presentation`).
When every circuit's word is even (four wires), the same data present the
alternating group (`Even.presentation`), given that every even word is
carried out.

**Order.**  Circuit words are in diagram order, and so is `perm`:
`perm (u * v) i = perm v (perm u i)` (`perm_mul`, the Agda's `perm-•`), the
product of the Agda's `Permutation′-group` and `Alt-group` (`∘ₚ`).  Mathlib's
`Equiv.Perm` and `alternatingGroup` multiply in operator order, so the
Agda's groups are their opposites: the presentations are stated in
`(Equiv.Perm (Fin N))ᵐᵒᵖ` and `(Alt N)ᵐᵒᵖ`, a generator `g` read as
`MulOpposite.op (perm (of g))` (`semP`, `semA`), so that a circuit is read as
`op` of its own permutation (`lift_semP`, `lift_semA`).  (`Gᵐᵒᵖ ≃* G` by
inversion, `MulEquiv.inv'`.)

**Deviations from the Agda.**

* The Agda's parameterised module `ByPerm k N enc dec dec-enc enc-dec tr at
  complete grouplike` is the structure `Data k N` with those fields (`at`
  is `at_`); its inner modules `Full realise` and `Even even realise` are
  the structures `Full k N` and `Even k N`, which extend it by their
  parameters.  `onto`, `ontoA` return subtypes (the Agda's `Σ`).
* The Agda builds a monoid presentation record (`monoid-presentation`) and
  turns it into a presentation by `monoidPresentation⇒presentation`; the
  framework has no monoid presentations, so `presentation_of` is that step
  for a reading into the opposite of a group, from the record's data
  (soundness `F_cong`, injectivity `F_inj`, surjectivity `F_onto`, the
  homomorphism laws, and `grouplike`).
* `circA` is irreducible (the Agda's `opaque` block), with its definition as
  the equation `circA_def`.
-/
import QCert.XCXCCX4bit.Semantics
import QCert.XCXCCX4bit.Coxeter
import QCert.XCXCCX4bit.Lib.Alternating
import Mathlib.Algebra.Group.Opposite
import Mathlib.Tactic.IrreducibleDef

namespace QCert.XCXCCX4bit.ByPerm

open QCert QCert.Circuit CircuitProp IndepProp
open Symmetric (SG)
open Alternating

/-! ## Presentations into the opposite of a group -/

/-- A reading `F` of the circuits in a group that reverses products (the
circuits being in diagram order), compatible with the theory, injective
modulo it and onto, gives a presentation of the opposite group, each
generator read as `op (F (of g))` (the Agda's `monoidPresentation⇒presentation`
of the record `monoid-presentation`). -/
theorem presentation_of {k : ℕ} {G : Type*} [Group G] (gl : Grouplike (VRel SRel k))
    (F : Circ k → G) (F_one : F 1 = 1) (F_mul : ∀ u v, F (u * v) = F v * F u)
    (F_cong : ∀ {u v}, k ⊢ u ≈ v → F u = F v) (F_inj : ∀ {u v}, F u = F v → k ⊢ u ≈ v)
    (F_onto : ∀ g, ∃ u, F u = g) :
    IsPresentationOf (VRel SRel k) (fun g => MulOpposite.op (F (FreeMonoid.of g))) := by
  have lift_eq : ∀ w : Circ k,
      FreeMonoid.lift (fun g => MulOpposite.op (F (FreeMonoid.of g))) w = MulOpposite.op (F w) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => rw [map_one, F_one, MulOpposite.op_one]
    | mul_of g w ih =>
      rw [map_mul, ih, FreeMonoid.lift_eval_of, ← MulOpposite.op_mul, F_mul]
  exact
    { grouplike := gl
      sound := fun w w' h => by rw [lift_eq, lift_eq, F_cong (Derivable.of h)]
      complete := fun w w' h => by
        rw [lift_eq, lift_eq] at h
        exact F_inj (MulOpposite.op_injective h)
      surjective := fun g => by
        obtain ⟨u, hu⟩ := F_onto g.unop
        exact ⟨u, by rw [lift_eq, hu, MulOpposite.op_unop]⟩ }

/-! ## The data -/

/-- The Agda's module parameters: a numbering of the states, a translation
of the circuits into Coxeter words carried out on the numbered states, and
completeness. -/
structure Data (k N : ℕ) where
  enc : Fin N → Bits k
  dec : Bits k → Fin N
  dec_enc : ∀ i, dec (enc i) = i
  enc_dec : ∀ x, enc (dec x) = x
  tr : Circ k → Word (SG N)
  at_ : ∀ u i, sem u (enc i) = enc (Symmetric.perm (tr u) i)
  complete : ∀ {u v : Circ k}, sem u ≐ sem v → k ⊢ u ≈ v
  grouplike : Grouplike (VRel SRel k)

namespace Data

variable {k N : ℕ} (B : Data k N)

/-- The permutation of the numbered states that a circuit carries out. -/
def perm (u : Circ k) : Equiv.Perm (Fin N) := Symmetric.perm (B.tr u)

theorem perm_at (u : Circ k) (i : Fin N) : B.perm u i = B.dec (sem u (B.enc i)) :=
  (B.dec_enc _).symm.trans (congrArg B.dec (B.at_ u i).symm)

theorem perm_cong {u v : Circ k} (e : k ⊢ u ≈ v) (i : Fin N) : B.perm u i = B.perm v i :=
  (B.perm_at u i).trans ((congrArg B.dec (sound e (B.enc i))).trans (B.perm_at v i).symm)

/-- The Agda's `perm-•`: diagram order. -/
theorem perm_mul (u v : Circ k) (i : Fin N) : B.perm (u * v) i = B.perm v (B.perm u i) := by
  rw [perm_at, sem_mul, B.at_ u i, ← perm_at]
  rfl

/-- The Agda's `perm-ε`. -/
theorem perm_one (i : Fin N) : B.perm 1 i = i :=
  (B.perm_at 1 i).trans (B.dec_enc i)

theorem perm_inj {u v : Circ k} (e : ∀ i, B.perm u i = B.perm v i) : k ⊢ u ≈ v :=
  B.complete fun x => by
    rw [← B.enc_dec x, B.at_ u, B.at_ v]
    exact congrArg B.enc (e (B.dec x))

/-- A circuit that carries out `π` has `π` as its permutation. -/
theorem perm_of (u : Circ k) (π : Equiv.Perm (Fin N)) (h : ∀ i, sem u (B.enc i) = B.enc (π i))
    (i : Fin N) : B.perm u i = π i :=
  (B.perm_at u i).trans ((congrArg B.dec (h i)).trans (B.dec_enc _))

/-- `perm` reverses products in Mathlib's (operator-order) group. -/
theorem perm_mul' (u v : Circ k) : B.perm (u * v) = B.perm v * B.perm u :=
  Equiv.ext fun i => B.perm_mul u v i

/-- The semantics of a generator in the Agda's (diagram-order) symmetric
group, Mathlib's opposite one. -/
def semP (g : Gn k) : (Equiv.Perm (Fin N))ᵐᵒᵖ := MulOpposite.op (B.perm (FreeMonoid.of g))

end Data

/-! ## The symmetric group -/

/-- The Agda's module `Full realise`: every Coxeter word is carried out by a
circuit. -/
structure Full (k N : ℕ) extends Data k N where
  realise : (w : Word (SG N)) → {u : Circ k // ∀ i, sem u (enc i) = enc (Symmetric.perm w i)}

namespace Full

variable {k N : ℕ} (F : Full k N)

/-- Every permutation: the circuit of a word that denotes it. -/
def onto (π : Equiv.Perm (Fin N)) : {u : Circ k // ∀ i, F.perm u i = π i} :=
  ⟨(F.realise (Symmetric.go N π)).1, fun i =>
    F.perm_of _ π (fun j => ((F.realise _).2 j).trans
      (congrArg F.enc (Symmetric.go_sem N π j))) i⟩

/-- A circuit's reading is `op` of its permutation. -/
theorem lift_semP (w : Circ k) :
    FreeMonoid.lift F.semP w = MulOpposite.op (F.perm w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact congrArg MulOpposite.op (Equiv.ext fun i => (F.perm_one i).symm)
  | mul_of g w ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, Data.semP, ← MulOpposite.op_mul, ← F.perm_mul']

/-- The circuits on `k` wires present the symmetric group of the `N`
states (in diagram order). -/
theorem presentation : IsPresentationOf (VRel SRel k) F.semP :=
  ByPerm.presentation_of F.grouplike F.perm (Equiv.ext F.perm_one) F.perm_mul'
    (fun e => Equiv.ext (F.perm_cong e)) (fun e => F.perm_inj (fun i => congrArg (· i) e))
    (fun π => ⟨(F.onto π).1, Equiv.ext (F.onto π).2⟩)

end Full

/-! ## The alternating group

The sign is reasoned about here, at a variable `N`: at a numeral, comparing
two spellings of a sign would make the kernel evaluate it. -/

/-- The Agda's module `Even even realise`: every circuit's word is even, and
every even word is carried out by a circuit. -/
structure Even (k N : ℕ) extends Data k N where
  even : ∀ u, parity (tr u) = false
  realise : (w : Word (SG N)) → parity w = false →
    {u : Circ k // ∀ i, sem u (enc i) = enc (Symmetric.perm w i)}

namespace Even

variable {k N : ℕ} (E : Even k N)

/-- The Agda's `even′`. -/
theorem even' (u : Circ k) : sign (E.perm u) = false :=
  (sign_of (E.tr u) (E.perm u) fun _ => rfl).trans (E.even u)

/-- The even permutation of a circuit (the Agda's `permᴬ`). -/
def permA (u : Circ k) : Alt N := Alt.mk (E.perm u) (E.even' u)

/-- Every even permutation: the circuit of an even word that denotes it. -/
def onto (π : Equiv.Perm (Fin N)) (s : sign π = false) : {u : Circ k // ∀ i, E.perm u i = π i} :=
  let r := E.realise (Symmetric.go N π)
    ((sign_of (Symmetric.go N π) π (Symmetric.go_sem N π)).symm.trans s)
  ⟨r.1, fun i =>
    E.perm_of r.1 π (fun j => (r.2 j).trans (congrArg E.enc (Symmetric.go_sem N π j))) i⟩

/-- Every element of `Alt N`, through its evenness proof here, at a variable
`N` (the Agda's `ontoᴬ`). -/
def ontoA (a : Alt N) : {u : Circ k // ∀ i, E.perm u i = Alt.perm a i} :=
  E.onto (Alt.perm a) (Alt.even a)

/-- A circuit carrying out an element of `Alt N` (the Agda's `circᴬ`),
irreducible: unfolded at a numeral `N` it would be evaluated through
Symmetric's word whenever two spellings of its function meet. -/
irreducible_def circA (a : Alt N) : Circ k := (E.ontoA a).1

theorem circA_sem (a : Alt N) (i : Fin N) : sem (E.circA a) (E.enc i) = E.enc (Alt.perm a i) := by
  rw [circA_def, E.at_]
  exact congrArg E.enc ((E.ontoA a).2 i)

/-- `permA` reverses products in Mathlib's (operator-order) group. -/
theorem permA_mul (u v : Circ k) : E.permA (u * v) = E.permA v * E.permA u :=
  Alt.ext fun i => E.perm_mul u v i

theorem permA_one : E.permA 1 = 1 := Alt.ext fun i => E.perm_one i

/-- The semantics of a generator in the Agda's (diagram-order) alternating
group, Mathlib's opposite one. -/
def semA (g : Gn k) : (Alt N)ᵐᵒᵖ := MulOpposite.op (E.permA (FreeMonoid.of g))

/-- A circuit's reading is `op` of its even permutation. -/
theorem lift_semA (w : Circ k) :
    FreeMonoid.lift E.semA w = MulOpposite.op (E.permA w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact congrArg MulOpposite.op E.permA_one.symm
  | mul_of g w ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, semA, ← MulOpposite.op_mul, ← E.permA_mul]

/-- The circuits on `k` wires present the alternating group of the `N`
states (in diagram order). -/
theorem presentation : IsPresentationOf (VRel SRel k) E.semA :=
  ByPerm.presentation_of E.grouplike E.permA E.permA_one E.permA_mul
    (fun e => Alt.ext (E.perm_cong e))
    (fun e => E.perm_inj (fun i => congrArg (fun a => Alt.perm a i) e))
    (fun a => ⟨(E.ontoA a).1, Alt.ext (E.ontoA a).2⟩)

end Even

end QCert.XCXCCX4bit.ByPerm
