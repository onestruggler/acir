/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness at a fixed width from the Coxeter presentation

Translation of `ByCoxeter.agda`: Appendix B's argument, for any width `k`
with `N = 2ᵏ` states.  The states are numbered by an encoding
`enc : Fin N → Bits k` with a left inverse (a Gray code, so that consecutive
states differ in one bit), and circuits `T d` realise the transpositions of
consecutive states (`T_act`).  Given the Coxeter relations for the `T d` and
every gate as a word in them (`tw_ok`), a circuit is its translation into a
Coxeter word (`translate_ok`), and two circuits with the same function have
translations with the same permutation, hence equivalent circuits
(`Coxeter.Circuits.perm_complete'`): the theory is complete at width `k`.

The Agda's module `Via k N T cox enc dec dec-enc T-act tw tw-ok` is the
namespace `Via` here, its parameters explicit arguments of each lemma
(`Via.complete k N T cox enc dec dec_enc T_act tw tw_ok`).  `SymI.⟦ p ⟧ ⟨$⟩ʳ i`
is `Coxeter.perm p i` (diagram order), and the Agda's `tw ʷ` is
`FreeMonoid.lift tw`.
-/
import QCert.XCXCCX4bit.Semantics
import QCert.XCXCCX4bit.Coxeter

namespace QCert.XCXCCX4bit.ByCoxeter.Via

open QCert QCert.Circuit CircuitProp IndepProp Coxeter Coxeter.Circuits

variable (k N : ℕ) (T : ℕ → Circ k) (enc : Fin N → Bits k)

/-- A Coxeter word's circuit acts on the numbered states as its
permutation. -/
theorem Pc_sem
    (T_act : ∀ (g : SG N) (i : Fin N), sem (T (tr 0 g)) (enc i) = enc (perm (FreeMonoid.of g) i))
    (p : Word (SG N)) (i : Fin N) : sem (Pc T 0 p) (enc i) = enc (perm p i) := by
  induction p using FreeMonoid.inductionOn' generalizing i with
  | one => rfl
  | mul_of g p ih =>
    rw [map_mul, sem_mul, perm_mul_apply, Pc_of, ← ih]
    exact congrArg (sem (Pc T 0 p)) (T_act g i)

variable {k N}

/-- The translation of a circuit into a Coxeter word (the Agda's `tw ʷ`). -/
def translate (tw : Gn k → Word (SG N)) : Circ k →* Word (SG N) := FreeMonoid.lift tw

theorem translate_ok (tw : Gn k → Word (SG N))
    (tw_ok : ∀ g, k ⊢ FreeMonoid.of g ≈ Pc T 0 (tw g)) (u : Circ k) :
    k ⊢ u ≈ Pc T 0 (translate tw u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of g u ih =>
    rw [map_mul, map_mul, translate, FreeMonoid.lift_eval_of]
    exact (tw_ok g).mul ih

variable (k N)

/-- Completeness at width `k`. -/
theorem complete (cox : Coxeter N T (VRel SRel k))
    (dec : Bits k → Fin N) (dec_enc : ∀ i, dec (enc i) = i)
    (T_act : ∀ (g : SG N) (i : Fin N), sem (T (tr 0 g)) (enc i) = enc (perm (FreeMonoid.of g) i))
    (tw : Gn k → Word (SG N)) (tw_ok : ∀ g, k ⊢ FreeMonoid.of g ≈ Pc T 0 (tw g))
    {u v : Circ k} (e : sem u ≐ sem v) : k ⊢ u ≈ v := by
  have at_ : ∀ (w : Circ k) i, sem w (enc i) = enc (perm (translate tw w) i) := fun w i =>
    (sound (translate_ok T tw tw_ok w) (enc i)).trans (Pc_sem k N T enc T_act _ i)
  have same_perm : ∀ i, perm (translate tw u) i = perm (translate tw v) i := fun i =>
    (dec_enc _).symm.trans
      ((congrArg dec ((at_ u i).symm.trans ((e (enc i)).trans (at_ v i)))).trans (dec_enc _))
  exact (translate_ok T tw tw_ok u).trans
    ((perm_complete' cox le_rfl (translate tw u) (translate tw v) same_perm).trans
      (translate_ok T tw tw_ok v).symm)

end QCert.XCXCCX4bit.ByCoxeter.Via
