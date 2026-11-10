/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Even words and their symbols, at a variable width

Translation of `EvenWord.agda`.  `EvenRS N`'s rewriting `rs` ends in the
coset of the parity of the word (`Coset.rs_parity`), so an even word, and
Symmetric's word for an even permutation, rewrite into symbols with the same
permutation (`Coset.coset_even`, `Coset.coset_sign`, `Coset.sym_sem`).  A
permutation of `j + m` states that agrees with `liftN j` of a conjugate of
`ρ` by `r`, and is the permutation of an even word, makes `ρ` even
(`Lift.lift_sign`).  Everything here is at variable widths: at a numeral,
comparing two spellings of a sign would make the kernel evaluate a sign.

The Agda's modules `Coset N` and `Lift j m` are the namespaces `Coset` and
`Lift`, with `N` (resp. `j`, `m`) explicit arguments.  `Coset.syms` is
irreducible (the Agda's `opaque` block), with its definition as the equation
`Coset.syms_def`.
-/
import QCert.XCXCCX4bit.EvenRS
import QCert.XCXCCX4bit.NFLib
import Mathlib.Tactic.IrreducibleDef

namespace QCert.XCXCCX4bit.EvenWord

open Symmetric Coxeter Alternating NFLib

namespace Coset

export EvenRS (Sch f rs)

variable (N : ℕ)

open EvenRS in
/-- The coset `rs` reaches is the parity of the word. -/
theorem rs_parity (c : Bool) (w : Word (SG N)) : (rs N c w).2 = (c ^^ parity w) := by
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => simp [rs_one]
  | mul_of g w ih =>
    rw [rs_mul, rs_of, ih, parity_mul, parity_of]
    cases c <;> simp [h]

theorem coset_even (w : Word (SG N)) (pw : parity w = false) : (rs N false w).2 = false := by
  rw [rs_parity, pw]; rfl

/-- Symmetric's word for a permutation, read by Symmetric's semantics. -/
theorem go_sem (π : Equiv.Perm (Fin N)) : ∀ i, perm (go N π) i = π i := Symmetric.go_sem N π

/-- Symmetric's word for an even permutation. -/
theorem coset_sign (π : Equiv.Perm (Fin N)) (s : sign π = false) :
    (rs N false (go N π)).2 = false :=
  coset_even N _ ((sign_of _ π (go_sem N π)).symm.trans s)

theorem coset_alt (a : Alt N) : (rs N false (go N (Alt.perm a))).2 = false :=
  coset_sign N (Alt.perm a) (Alt.even a)

/-- The symbols of Symmetric's word for an even permutation, which denote
it (`sym_sem`).  Irreducible: unfolded, a circuit built from it would be
reduced through `rs` of Symmetric's word whenever two spellings meet. -/
irreducible_def syms (a : Alt N) : Word (Sch N) := (rs N false (go N (Alt.perm a))).1

theorem sym_sem (a : Alt N) : ∀ i, perm (FreeMonoid.lift (f N) (syms N a)) i = Alt.perm a i := by
  intro i
  rw [syms_def, EvenRS.rs_sem _ (coset_alt N a) i, go_sem]

end Coset

namespace Lift

/-- An even word whose permutation is lifted from a conjugate of `ρ` (the
Agda's `r ∘ₚ (ρ ∘ₚ r)` is `r.trans (ρ.trans r)`). -/
theorem lift_sign (j m : ℕ) (w : Word (SG (j + m))) (pw : parity w = false)
    (r ρ : Equiv.Perm (Fin m)) (e : ∀ i, perm w i = liftN j (r.trans (ρ.trans r)) i) :
    sign ρ = false := by
  rw [← sign_sandwich r ρ, ← sign_by_liftN j (perm w) _ e, sign_of w (perm w) (fun _ => rfl), pw]

end Lift

end QCert.XCXCCX4bit.EvenWord
