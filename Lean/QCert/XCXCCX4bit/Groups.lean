/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The groups of circuits: `G₁ ≅ Sym(2)`, `G₂ ≅ Sym(4)`, `G₃ ≅ Sym(8)` and `G₄ ≅ Alt(16)`

Translation of `Groups.agda`: the paper's Propositions B.1–B.3 and Corollary
5.2.  On `k ≤ 3` wires the theory presents the symmetric group of the `2ᵏ`
states, and on four wires the alternating group of the sixteen states.
Each is `ByPerm` at the numbering of the states that the completeness proof
used: a circuit is read as a Coxeter word (`Width2`/`Width3`'s translation;
on four wires, the symbols of `EvenRS 16` that `Four` translates it to, as
words of `S₁₆`), every permutation is the circuit of a Coxeter word
(Symmetric's `go`; on four wires an even word, rewritten into symbols by
`EvenRS`'s `rs` and realised by `Four`'s `R`), and every letter is an
involution (`inv_sem`, `grouplike`).  Every four-wire circuit is even: its
Coxeter word is a word of symbols, each of two letters (`Fourw.parity_f`).

The presentations read a generator as its permutation of the numbered
states in the opposite of Mathlib's group (`ByPerm.Data.semP`,
`ByPerm.Even.semA`), since circuit words are in diagram order and Mathlib's
permutations compose in operator order (see `ByPerm`).  They are named here
`perm₁ … perm₄`, and `lift_perm₁ … lift_perm₄` say that a circuit is read
as its function on the numbered states.

**Deviations from the Agda.**

* The Agda's private modules `One`, `Two`, `Three` and the public `Fourw`
  are namespaces, each building its `ByPerm.Full` (resp. `ByPerm.Even`)
  structure value `F` (resp. `E`) where the Agda opens the parameterised
  module.  `One`'s word `circ` is `FreeMonoid.lift (fun _ => X)`.
* `Fourw`'s `rs-parity` is `EvenWord.Coset.rs_parity` (proved there, at a
  variable width), not repeated here; `realise` uses `coset_even`.
* `perm₁ … perm₄` and `lift_perm₁ … lift_perm₄` are new: the framework's
  `IsPresentationOf` takes the semantics as an argument, where the Agda's
  record holds it as a field.
-/
import QCert.XCXCCX4bit.ByPerm
import QCert.XCXCCX4bit.Width1
import QCert.XCXCCX4bit.Width2
import QCert.XCXCCX4bit.Width3
import QCert.XCXCCX4bit.Completeness
import QCert.XCXCCX4bit.EvenWord

namespace QCert.XCXCCX4bit.Groups

open QCert QCert.Circuit CircuitProp IndepProp
open Symmetric (SG)
open Alternating ByPerm

/-! ## Every letter is an involution -/

theorem inv_sem : ∀ {n : ℕ} (g : Gn n) (x : Bits n), semG g (semG g x) = x
  | _, .gate0 (.gate g), _ => nomatch g
  | _, .gate1 (.gate .X_gate), a ∷ _ => by cases a <;> rfl
  | _, .gate2 (.gate .CX_gate), a ∷ b ∷ _ => by cases a <;> cases b <;> rfl
  | _, .gate2 .swap, _ ∷ _ ∷ _ => rfl
  | _, .gate3 (.gate .CCX_gate), a ∷ b ∷ c ∷ _ => by cases a <;> cases b <;> cases c <;> rfl
  | _, .up g, a ∷ x => congrArg (a ∷ ·) (inv_sem g x)

theorem grouplike {k : ℕ} (complete : ∀ {u v : Circ k}, sem u ≐ sem v → k ⊢ u ≈ v) :
    Grouplike (VRel SRel k) := fun g =>
  ⟨FreeMonoid.of g, complete fun x => by rw [sem_mul, sem_of, sem_of, sem_one]; exact inv_sem g x⟩

/-! ## One wire: `Sym(2)` -/

namespace One

def enc : Fin 2 → Bits 1
  | 0 => false ∷ .nil
  | 1 => true ∷ .nil
  | ⟨_ + 2, h⟩ => absurd h (by omega)

def dec : Bits 1 → Fin 2
  | false ∷ .nil => 0
  | true ∷ .nil => 1

theorem dec_enc : ∀ i, dec (enc i) = i := by decide

theorem enc_dec : ∀ x, enc (dec x) = x
  | false ∷ .nil => rfl
  | true ∷ .nil => rfl

def s₀ : SG 2 := ⟨0, by decide⟩

def trB : Bool → Word (SG 2)
  | false => 1
  | true => FreeMonoid.of s₀

def tr (u : Circ 1) : Word (SG 2) := trB (Width1.par u)

/-- The Agda's `by`. -/
theorem by_ : ∀ (b : Bool) (i : Fin 2),
    sem (Width1.nf b) (enc i) = enc (Symmetric.perm (trB b) i) := by
  decide

theorem at_ (u : Circ 1) (i : Fin 2) : sem u (enc i) = enc (Symmetric.perm (tr u) i) :=
  (sound (Width1.nf_ok u) (enc i)).trans (by_ (Width1.par u) i)

/-- A Coxeter word of `S₂` as a circuit: `X` for its one letter. -/
def circ : Word (SG 2) →* Circ 1 := FreeMonoid.lift fun _ => X

theorem circ_of : ∀ (g : SG 2) (i : Fin 2),
    sem (circ (FreeMonoid.of g)) (enc i) = enc (Symmetric.perm (FreeMonoid.of g) i)
  | ⟨0, _⟩, i => by
    show sem (circ (FreeMonoid.of s₀)) (enc i) = enc (Symmetric.perm (FreeMonoid.of s₀) i)
    rw [circ, FreeMonoid.lift_eval_of]; revert i; decide
  | ⟨_ + 1, h⟩, _ => absurd h (by omega)

theorem circ_at (w : Word (SG 2)) (i : Fin 2) : sem (circ w) (enc i) = enc (Symmetric.perm w i) := by
  induction w using FreeMonoid.inductionOn' generalizing i with
  | one => rfl
  | mul_of g w ih => rw [map_mul, sem_mul, circ_of, ih, Symmetric.perm_mul_apply]

/-- The Agda's `open ByPerm … ; open Full realise`. -/
def F : Full 1 2 where
  enc := enc
  dec := dec
  dec_enc := dec_enc
  enc_dec := enc_dec
  tr := tr
  at_ := at_
  complete := Width1.complete₁
  grouplike := grouplike Width1.complete₁
  realise w := ⟨circ w, circ_at w⟩

end One

/-- The semantics of `presentation₁`. -/
abbrev perm₁ : Gn 1 → (Equiv.Perm (Fin 2))ᵐᵒᵖ := One.F.semP

/-- A one-wire circuit is read as its function on the numbered states. -/
theorem lift_perm₁ (w : Circ 1) (i : Fin 2) :
    (FreeMonoid.lift perm₁ w).unop i = One.dec (sem w (One.enc i)) := by
  rw [Full.lift_semP]; exact One.F.perm_at w i

/-- Proposition B.1: one-wire circuits present `Sym(2)`. -/
theorem presentation₁ : IsPresentationOf (VRel SRel 1) perm₁ := One.F.presentation

/-! ## Two and three wires: `Sym(4)`, `Sym(8)` -/

namespace Two

theorem enc_dec : ∀ x, Width2.enc (Width2.dec x) = x
  | false ∷ false ∷ .nil => rfl
  | true ∷ false ∷ .nil => rfl
  | true ∷ true ∷ .nil => rfl
  | false ∷ true ∷ .nil => rfl

theorem at_ (u : Circ 2) (i : Fin 4) :
    sem u (Width2.enc i) = Width2.enc (Symmetric.perm (Width2.translate u) i) :=
  (sound (Width2.translate_ok u) (Width2.enc i)).trans
    (ByCoxeter.Via.Pc_sem 2 4 Width2.T Width2.enc Width2.T_act (Width2.translate u) i)

def F : Full 2 4 where
  enc := Width2.enc
  dec := Width2.dec
  dec_enc := Width2.dec_enc
  enc_dec := enc_dec
  tr := Width2.translate
  at_ := at_
  complete := Width2.complete₂
  grouplike := grouplike Width2.complete₂
  realise w := ⟨Coxeter.Circuits.Pc Width2.T 0 w,
    ByCoxeter.Via.Pc_sem 2 4 Width2.T Width2.enc Width2.T_act w⟩

end Two

namespace Three

theorem enc_dec : ∀ x, Width3.enc (Width3.dec x) = x
  | false ∷ false ∷ false ∷ .nil => rfl
  | true ∷ false ∷ false ∷ .nil => rfl
  | true ∷ true ∷ false ∷ .nil => rfl
  | false ∷ true ∷ false ∷ .nil => rfl
  | false ∷ true ∷ true ∷ .nil => rfl
  | true ∷ true ∷ true ∷ .nil => rfl
  | true ∷ false ∷ true ∷ .nil => rfl
  | false ∷ false ∷ true ∷ .nil => rfl

theorem at_ (u : Circ 3) (i : Fin 8) :
    sem u (Width3.enc i) = Width3.enc (Symmetric.perm (Width3.translate u) i) :=
  (sound (Width3.translate_ok u) (Width3.enc i)).trans
    (ByCoxeter.Via.Pc_sem 3 8 Width3.T Width3.enc Width3.T_act (Width3.translate u) i)

def F : Full 3 8 where
  enc := Width3.enc
  dec := Width3.dec
  dec_enc := Width3.dec_enc
  enc_dec := enc_dec
  tr := Width3.translate
  at_ := at_
  complete := Width3.complete₃
  grouplike := grouplike Width3.complete₃
  realise w := ⟨Coxeter.Circuits.Pc Width3.T 0 w,
    ByCoxeter.Via.Pc_sem 3 8 Width3.T Width3.enc Width3.T_act w⟩

end Three

/-- The semantics of `presentation₂`. -/
abbrev perm₂ : Gn 2 → (Equiv.Perm (Fin 4))ᵐᵒᵖ := Two.F.semP

/-- The semantics of `presentation₃`. -/
abbrev perm₃ : Gn 3 → (Equiv.Perm (Fin 8))ᵐᵒᵖ := Three.F.semP

/-- A two-wire circuit is read as its function on the numbered states. -/
theorem lift_perm₂ (w : Circ 2) (i : Fin 4) :
    (FreeMonoid.lift perm₂ w).unop i = Width2.dec (sem w (Width2.enc i)) := by
  rw [Full.lift_semP]; exact Two.F.perm_at w i

/-- A three-wire circuit is read as its function on the numbered states. -/
theorem lift_perm₃ (w : Circ 3) (i : Fin 8) :
    (FreeMonoid.lift perm₃ w).unop i = Width3.dec (sem w (Width3.enc i)) := by
  rw [Full.lift_semP]; exact Three.F.perm_at w i

/-- Proposition B.2: two-wire circuits present `Sym(4)`. -/
theorem presentation₂ : IsPresentationOf (VRel SRel 2) perm₂ := Two.F.presentation

/-- Proposition B.3: three-wire circuits present `Sym(8)`. -/
theorem presentation₃ : IsPresentationOf (VRel SRel 3) perm₃ := Three.F.presentation

/-! ## Four wires: `Alt(16)` -/

-- The four-wire instance, public for the normal form (`NormalForm`).
namespace Fourw

open Placed ToPlaced ByEvenRS

/-- A circuit as the Coxeter word of its symbols. -/
def tr (u : Circ 4) : Word (SG 16) :=
  FreeMonoid.lift (EvenRS.f 16) (Realisation.translate Four.tw (pg u))

theorem at_ (u : Circ 4) (i : Fin 16) :
    sem u (Four.enc i) = Four.enc (Symmetric.perm (tr u) i) :=
  (sound ((pg_ok u).trans (Four.RL.translate_ok Four.tw (Four.tw_ok KFaithful.faithful₃) (pg u)))
    (Four.enc i)).trans ((ιs_sem _ (Four.enc i)).trans (Four.RL.Rs_act _ i))

/-- The Coxeter word of a word of symbols has even length. -/
theorem parity_f (w : Word (EvenRS.Sch 16)) : parity (FreeMonoid.lift (EvenRS.f 16) w) = false := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of x w ih =>
    rw [map_mul, parity_mul, ih, FreeMonoid.lift_eval_of]
    rcases x with ⟨_ | _, d, p, q⟩ <;> simp [EvenRS.f, parity_mul]

theorem even (u : Circ 4) : parity (tr u) = false :=
  parity_f (Realisation.translate Four.tw (pg u))

/-- An even word is realised: rewritten into symbols. -/
def realise (w : Word (SG 16)) (pw : parity w = false) :
    {u : Circ 4 // ∀ i, sem u (Four.enc i) = Four.enc (Symmetric.perm w i)} :=
  ⟨ιs (Four.RL.Rs (EvenRS.rs 16 false w).1), fun i =>
    (ιs_sem _ (Four.enc i)).trans ((Four.RL.Rs_act _ i).trans
      (congrArg Four.enc (EvenRS.rs_sem w (EvenWord.Coset.coset_even 16 w pw) i)))⟩

/-- The Agda's `open ByPerm … ; open Even even realise`. -/
def E : Even 4 16 where
  enc := Four.enc
  dec := Four.dec
  dec_enc := Four.dec_enc
  enc_dec := Four.enc_dec
  tr := tr
  at_ := at_
  complete := Completeness.complete₄
  grouplike := grouplike Completeness.complete₄
  even := even
  realise := realise

end Fourw

/-- The semantics of `presentation₄`. -/
abbrev perm₄ : Gn 4 → (Alt 16)ᵐᵒᵖ := Fourw.E.semA

/-- A four-wire circuit is read as its function on the numbered states. -/
theorem lift_perm₄ (w : Circ 4) (i : Fin 16) :
    Alt.perm (FreeMonoid.lift perm₄ w).unop i = Four.dec (sem w (Four.enc i)) := by
  rw [Even.lift_semA]; exact Fourw.E.perm_at w i

/-- Corollary 5.2: four-wire circuits present `Alt(16)`. -/
theorem presentation₄ : IsPresentationOf (VRel SRel 4) perm₄ := Fourw.E.presentation

end QCert.XCXCCX4bit.Groups
