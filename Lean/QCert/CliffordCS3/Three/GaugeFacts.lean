/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The concrete hypotheses of the local coset calculation
-/
import QCert.CliffordCS3.Three.RestrictedGauge
import QCert.CliffordCS3.Three.PhaseGaugeSupport

namespace QCert.CliffordCS3.Three.RestrictedGauge

theorem facts : Facts where
  conjugate_A := PhasePoint.C_atom_dresses
  commute_t4 := PhaseGaugeSupport.C_token4
  commute_t5 := PhaseOuter.C_token5
  correction_A := PhaseGaugeSupport.r_A
  correction_t4 := PhaseGaugeSupport.r_token4
  correction_t5 := PhaseGaugeSupport.r_token5
  correction_t6 := PhaseGaugeSupport.r_T

end QCert.CliffordCS3.Three.RestrictedGauge
