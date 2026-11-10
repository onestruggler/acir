/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness

Translation of `Examples/Groups/Alternating/Completeness.agda`: in a sound
theory where the rules of Fig. 10 hold, circuits with the same denotation
are congruent.

This is Lafont's proof of Theorem 4 from Lemmas 6 and 8.  Two circuits with
the same permutation reduce to canonical forms (Lemma 8, `Normalization`),
which denote that permutation too (soundness), so they are the same
canonical form (Lemma 6, `UniqueNormalForm`), and the circuits are
congruent.  On the way `nf` respects the congruence (`nf_cong`), obtained
here without checking the coset action against every relation.

**Deviations from the Agda.**  The Agda's parameterised module
`Completeness T rules sound-T` is the namespace `Completeness`, whose lemmas
take `rules` and `sound_T` as arguments (`Completeness.completeness` is the
Agda's `Completeness.completeness`; the name `completeness` is
`Presentation`'s, for Theorem 4's relations).  The packaging of `nf` as a
`NormalForm` record with unique normal forms (`nfp′`, `unique-nf`) is not
translated: the framework has no such records.
-/
import QCert.Alt16RevCir.Lib.Alternating.Derivations
import QCert.Alt16RevCir.Lib.Alternating.Soundness
import QCert.Alt16RevCir.Lib.Alternating.UniqueNormalForm

namespace QCert.Alt16RevCir.Alternating.Completeness

open QCert QCert.Circuit

variable {T : Theory} (rules : Fig10 T)
  (sound_T : ∀ {n : ℕ} {w v : Circ n}, T n w v → ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i)
  {n : ℕ}

include rules sound_T

/-! ## Completeness -/

/-- Circuits with the same denotation have the same canonical form. -/
theorem nf_unique {w v : Circ n} (eq : ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i) :
    nf w = nf v :=
  inv_nf_injective fun k =>
    (sound sound_T (inv_nf_nf rules w) k).trans
      ((eq k).trans (sound sound_T (inv_nf_nf rules v) k).symm)

/-- Circuits with the same denotation are congruent. -/
theorem completeness {w v : Circ n} (eq : ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i) :
    Derives T n w v :=
  calc Derives T n w (inv_nf (nf w)) := (inv_nf_nf rules w).symm
    Derives T n _ (inv_nf (nf v)) := derives_of_eq (congrArg inv_nf (nf_unique rules sound_T eq))
    Derives T n _ v := inv_nf_nf rules v

/-! ## The normal form -/

/-- `nf` respects the congruence. -/
theorem nf_cong {w v : Circ n} (d : Derives T n w v) : nf w = nf v :=
  nf_unique rules sound_T (sound sound_T d)

end QCert.Alt16RevCir.Alternating.Completeness
