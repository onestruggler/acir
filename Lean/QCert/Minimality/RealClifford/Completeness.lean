/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of RCliff₂ (Theorem 22 (2))

Theorem 21 for RCliff₂ with Makary, Ross and Selinger's presentation as the
source.  Their semantics is by real orthogonal matrices; read over `ℂ`
(entrywise, an injective map) the matrix of an encoded circuit is the
circuit's (`sem_E_real`).  The decoding carries their relations to
derivable equations (`rel_derivable`, Appendix G.2, hence Lemma 20), and
decoding the encoding derives the circuit (`DE`, Appendix F.2 and
Lemma 19).  So the completeness of their presentation gives that of
RCliff₂ (`complete_of_source`).
-/
import QCert.Minimality.RealClifford.Derivations
import QCert.Minimality.RealClifford.Soundness
import QCert.RealStabilizer.Theorem

namespace QCert.Minimality.RealClifford

open QCert.Circuit

/-- Reading a real matrix over `ℂ` is injective. -/
theorem ofReal_map_injective {n : ℕ} :
    Function.Injective fun U : Matrix.unitaryGroup (State 2 n) ℝ =>
      (U : Op ℝ 2 n).map Complex.ofRealHom := by
  intro U V h
  apply Subtype.ext
  ext s t
  have := congrFun (congrFun h s) t
  simpa using this

/-- Theorem 22 (2) from the completeness of Makary, Ross and Selinger's
presentation: RCliff₂ is complete. -/
theorem complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.RealStabilizer.Gate n),
      QCert.RealStabilizer.S.sem n w = QCert.RealStabilizer.S.sem n v →
        Derivable (QCert.RealStabilizer.Theory n) w v) :
    pres.Complete fun n => sem.sem n := by
  intro n w v h
  exact complete_of_transfer_map (Lift Th n) (QCert.RealStabilizer.Theory n) (sem.sem n)
    (QCert.RealStabilizer.S.sem n) (E.map n) (D.map n)
    (fun U => (U : Op ℝ 2 n).map Complex.ofRealHom) ofReal_map_injective
    (fun U => (U : Op ℂ 2 n)) sem_E_real (hsrc n)
    (fun a b hab => D.derivable_map hsc (fun k w v r => rel_derivable r) hab) DE w v h

/-- Theorem 22 (2): RCliff₂ is complete, given the completeness of Makary,
Ross and Selinger's presentation as formalised in `QCert.RealStabilizer`. -/
theorem complete : pres.Complete fun n => sem.sem n :=
  complete_of_source fun n _ _ h => (QCert.RealStabilizer.presentation n).complete h

end QCert.Minimality.RealClifford
