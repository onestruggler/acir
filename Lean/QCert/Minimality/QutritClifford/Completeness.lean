/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of Cliff₃ (Theorem 22 (3))

Theorem 21 for Cliff₃ with the scalar-refined presentation of Li, Mosca,
Ross, van de Wetering and Zhao as the source.  The refined presentation is
complete as soon as theirs is (`refined_complete`, Lemma 50, with its
hypothesis "no hidden phases" proved), the encoding preserves the semantics
(`sem_E`), the decoding carries the refined rules to derivable equations
(`rel_derivable`, Appendix G.3, hence Lemma 20), and decoding the encoding
derives the circuit (`DE`, Appendix F.3 and Lemma 19).  So the completeness
of their presentation gives that of Cliff₃ (`complete_of_source`).
-/
import QCert.Minimality.QutritClifford.Derivations
import QCert.Minimality.QutritClifford.Soundness
import QCert.QutritClifford.Theorem

namespace QCert.Minimality.QutritClifford

open QCert.Circuit

/-- Theorem 22 (3) from the completeness of Li, Mosca, Ross, van de Wetering
and Zhao's presentation: Cliff₃ (with (E) corrected) is complete. -/
theorem complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.QutritClifford.Gate n),
      QCert.QutritClifford.gateSem.sem n w = QCert.QutritClifford.gateSem.sem n v →
        Derivable (QCert.QutritClifford.Theory n) w v) :
    pres.Complete fun n => sem.sem n := by
  intro n w v h
  exact complete_of_transfer (Lift Th n) (RTh n) (sem.sem n) (RS.sem n) (E.map n) (D.map n)
    sem_E (fun a b hab => refined_complete hsrc hab)
    (fun a b hab => D.derivable_map hsc (fun k w v r => rel_derivable r) hab) DE w v h

/-- Theorem 22 (3): Cliff₃ is complete, given the completeness of Li et al.'s
presentation as formalised in `QCert.QutritClifford`. -/
theorem complete : pres.Complete fun n => sem.sem n :=
  complete_of_source fun _ _ _ h => QCert.QutritClifford.complete h

end QCert.Minimality.QutritClifford
