/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The sixteen rows of Table 1 of qcert.pdf

This entry point imports every main theorem. A successful build checks the
statements and proof terms, but does not by itself exclude `sorry`: use
`QCert.Audit` to inspect the axioms of the results.

The individual developments follow the source papers independently of the
Agda formalization.
-/
-- Groups of m-level matrices (rows 1–5).
import QCert.Greylyn.Theorem
import QCert.BianSelingerUn.Theorem
import QCert.LiRossSelinger.Theorem
import QCert.HadamardPi.Theorem
import QCert.Clement2019.Theorem
-- Circuit presentations (rows 6–15).
import QCert.SelingerClifford.Theorem
import QCert.QuditClifford.Theorem
import QCert.RealStabilizer.Theorem
import QCert.CNOTDihedral.Theorem
import QCert.PhaseAffine.Theorem
import QCert.CliffordT2.Theorem
import QCert.CliffordCS3.Theorem
import QCert.RealCliffordCH.Theorem
import QCert.ToffoliHadamard.Theorem
import QCert.QutritClifford.Theorem
-- Completeness and minimality of six fragments (row 16).
import QCert.Minimality.Theorems
