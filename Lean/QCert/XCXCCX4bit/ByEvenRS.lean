/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness on four wires from the presentation of `A₁₆`

Translation of `ByEvenRS.agda`.  The four-wire circuits act on the 16
states as even permutations, and `EvenRS 16` presents `A₁₆` by symbols
`γ c d`, each a product of two transpositions of numbered states, and the
relations `RSRel`.  So, as `ByCoxeter` does from `S_N`'s presentation: if the
states are numbered (`enc`, with a left inverse `dec`), every symbol has a
word of placed letters that realises it (`R`, `R_act`), the relations hold
for those words (`R_rel`), and every placed letter is a word in the symbols
(`tw`, `tw_ok`), then two words of placed letters with the same function are
equal.

Realisation (`R`, `R_act`) gives the realisation of a word of symbols (`Rs`,
a homomorphism: `Rs_act`) and the semantics of the two sides of a relation
(`rel_sem`, from `EvenRS.rs_sound_sem`), which is what a faithful subgroup
needs to decide a relation; `complete` adds the relations and the
translation of the letters.

**Deviation from the Agda.**  The Agda's parameterised module `Realisation
enc dec dec-enc enc-dec R R-act` is the structure `Realisation`, whose
fields are those parameters; its theorems take the structure first
(`RL.Rs`, `RL.rel_sem`), and the inner module `Complete R-rel tw tw-ok` is
the theorem `complete`, which takes `R_rel`, `tw` and `tw_ok` as arguments.
The Agda's `R*` is `Rs` (computed letter by letter from the list of the
word's symbols, `RL.RL`), and `SymI.⟦ w ⟧ ⟨$⟩ʳ i` is `Symmetric.perm w i`.
-/
import QCert.XCXCCX4bit.ToPlaced
import QCert.XCXCCX4bit.EvenRS

namespace QCert.XCXCCX4bit.ByEvenRS

open QCert QCert.Circuit CircuitProp IndepProp
open Placed EvenRS

/-! ## Realising the symbols -/

/-- A numbering of the states and a realisation of the symbols of `A₁₆` by
words of placed letters. -/
structure Realisation where
  enc : Fin 16 → Bits 4
  dec : Bits 4 → Fin 16
  dec_enc : ∀ i, dec (enc i) = i
  enc_dec : ∀ x, enc (dec x) = x
  R : Sch 16 → List PG
  R_act : ∀ (x : Sch 16) (i : Fin 16), semPs (R x) (enc i) = enc (Symmetric.perm (f 16 x) i)

namespace Realisation

variable (RL : Realisation)

/-- The realisation of a list of symbols. -/
def RLs : List (Sch 16) → List PG
  | [] => []
  | x :: l => RL.R x ++ RLs l

/-- The realisation of a word of symbols (the Agda's `R*`). -/
def Rs (w : Word (Sch 16)) : List PG := RL.RLs (FreeMonoid.toList w)

theorem RLs_append (l l' : List (Sch 16)) : RL.RLs (l ++ l') = RL.RLs l ++ RL.RLs l' := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, RLs, RLs, ih, List.append_assoc]

theorem Rs_mul (u v : Word (Sch 16)) : RL.Rs (u * v) = RL.Rs u ++ RL.Rs v := by
  simp only [Rs, FreeMonoid.toList_mul, RLs_append]

theorem Rs_of (x : Sch 16) : RL.Rs (FreeMonoid.of x) = RL.R x := by
  simp only [Rs, FreeMonoid.toList_of, RLs, List.append_nil]

theorem Rs_one : RL.Rs 1 = [] := rfl

theorem Rs_act (w : Word (Sch 16)) (i : Fin 16) :
    semPs (RL.Rs w) (RL.enc i) = RL.enc (Symmetric.perm (FreeMonoid.lift (f 16) w) i) := by
  induction w using FreeMonoid.inductionOn' generalizing i with
  | one => rfl
  | mul_of x w ih =>
    rw [Rs_mul, Rs_of, semPs_append, RL.R_act, ih, map_mul, FreeMonoid.lift_eval_of,
      Symmetric.perm_mul_apply]

/-- Two words of symbols whose Coxeter words have the same permutation have
realisations with the same function. -/
theorem Rs_sem (u v : Word (Sch 16))
    (e : ∀ i, Symmetric.perm (FreeMonoid.lift (f 16) u) i =
      Symmetric.perm (FreeMonoid.lift (f 16) v) i) :
    semPs (RL.Rs u) ≐ semPs (RL.Rs v) := fun x => by
  rw [← RL.enc_dec x, Rs_act, Rs_act, e]

/-- The two sides of a relation have realisations with the same function. -/
theorem rel_sem {u v : Word (Sch 16)} (r : RSRel 16 u v) : semPs (RL.Rs u) ≐ semPs (RL.Rs v) :=
  RL.Rs_sem u v (rs_sound_sem r)

/-! ## Completeness, given the relations and the letters as words in the
symbols -/

theorem Rs_cong (R_rel : ∀ {u v}, RSRel 16 u v → 4 ⊢ ιs (RL.Rs u) ≈ ιs (RL.Rs v))
    {u v : Word (Sch 16)} (h : Derivable (RSRel 16) u v) : 4 ⊢ ιs (RL.Rs u) ≈ ιs (RL.Rs v) := by
  let c : Con (Word (Sch 16)) :=
    { r := fun u v => 4 ⊢ ιs (RL.Rs u) ≈ ιs (RL.Rs v)
      iseqv := ⟨fun _ => Derivable.refl _, Derivable.symm, Derivable.trans⟩
      mul' := fun {u u' v v'} hu hv => by
        show 4 ⊢ ιs (RL.Rs (u * v)) ≈ ιs (RL.Rs (u' * v'))
        rw [Rs_mul, Rs_mul, ιs_append, ιs_append]
        exact hu.mul hv }
  have : conGen (RSRel 16) ≤ c := Con.conGen_le fun _ _ r => R_rel r
  exact this h

/-- A list of letters as a word in the symbols, letter by letter. -/
def translate (tw : PG → Word (Sch 16)) : List PG → Word (Sch 16)
  | [] => 1
  | g :: u => tw g * translate tw u

theorem translate_ok (tw : PG → Word (Sch 16))
    (tw_ok : ∀ g, 4 ⊢ ι g ≈ ιs (RL.Rs (tw g))) :
    ∀ u : List PG, 4 ⊢ ιs u ≈ ιs (RL.Rs (translate tw u))
  | [] => Derivable.refl _
  | g :: u => by
    show 4 ⊢ ι g * ιs u ≈ ιs (RL.Rs (tw g * translate tw u))
    rw [Rs_mul, ιs_append]
    exact (tw_ok g).mul (translate_ok tw tw_ok u)

/-- Two words of placed letters with the same function are equal. -/
theorem complete (R_rel : ∀ {u v}, RSRel 16 u v → 4 ⊢ ιs (RL.Rs u) ≈ ιs (RL.Rs v))
    (tw : PG → Word (Sch 16)) (tw_ok : ∀ g, 4 ⊢ ι g ≈ ιs (RL.Rs (tw g)))
    (u v : List PG) (e : semPs u ≐ semPs v) : 4 ⊢ ιs u ≈ ιs v := by
  have at_ : ∀ (w : List PG) (i : Fin 16),
      semPs w (RL.enc i) = RL.enc (Symmetric.perm (FreeMonoid.lift (f 16) (translate tw w)) i) :=
    fun w i => by
      rw [← ιs_sem w (RL.enc i), sound (RL.translate_ok tw tw_ok w) (RL.enc i),
        ιs_sem _ (RL.enc i), Rs_act]
  have same_perm : ∀ i, Symmetric.perm (FreeMonoid.lift (f 16) (translate tw u)) i =
      Symmetric.perm (FreeMonoid.lift (f 16) (translate tw v)) i := fun i => by
    rw [← RL.dec_enc (Symmetric.perm _ i), ← at_ u i, e, at_ v i, RL.dec_enc]
  exact (RL.translate_ok tw tw_ok u).trans ((RL.Rs_cong R_rel
    (rs_complete 16 (translate tw u) (translate tw v) same_perm)).trans
    (RL.translate_ok tw tw_ok v).symm)

end Realisation

end QCert.XCXCCX4bit.ByEvenRS
