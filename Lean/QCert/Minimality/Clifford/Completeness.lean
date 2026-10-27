/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of Cliff₂ (Theorem 22 (1))

Theorem 21 for Cliff₂ with Selinger's presentation as the source: the
encoding preserves the semantics (`sem_E`), the decoding carries Selinger's
relations to derivable equations (`rel_derivable`, Appendix G.1, hence
Lemma 20 for every derivation), and decoding the encoding derives the
circuit (`DE`, Appendix F.1 and Lemma 19).  So the completeness of
Selinger's presentation gives that of Cliff₂ (`complete_of_source`).
-/
import QCert.Minimality.Clifford.Derivations
import QCert.Minimality.Clifford.Soundness
import QCert.SelingerClifford.Theorem

namespace QCert.Minimality.Clifford

open QCert.Circuit

/-- Theorem 22 (1) from the completeness of Selinger's presentation:
Cliff₂ is complete. -/
theorem complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.SelingerClifford.Gate n),
      QCert.SelingerClifford.S.sem n w = QCert.SelingerClifford.S.sem n v →
        Derivable (QCert.SelingerClifford.Theory n) w v) :
    pres.Complete fun n => sem.sem n := by
  intro n w v h
  exact complete_of_transfer (Lift Th n) (QCert.SelingerClifford.Theory n) (sem.sem n)
    (QCert.SelingerClifford.S.sem n) (E.map n) (D.map n) sem_E (hsrc n)
    (fun a b hab => D.derivable_map hsc (fun k w v r => rel_derivable r) hab) DE w v h

/-- Theorem 22 (1): Cliff₂ is complete, given the completeness of
Selinger's presentation as formalised in `QCert.SelingerClifford`. -/
theorem complete : pres.Complete fun n => sem.sem n :=
  complete_of_source fun n _ _ h => (QCert.SelingerClifford.presentation n).complete h

end QCert.Minimality.Clifford
