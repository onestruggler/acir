/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Disjoint exchanges with the same target wire
-/
import QCert.CliffordCS3.Three.AtomWhiteTransport

namespace QCert.CliffordCS3.Three.PermutationEven

open QuotientGroup LocalKZ AtomTokens
noncomputable section

theorem token6_token0 : Commute T (u (Cert.token 0)) := by
  rw [T_eq, token0_form]
  exact ((Commute.refl Q).mul_right (C_Q.symm.pow_right 2)).conj K

theorem token6_token4 : Commute T (u (Cert.token 4)) := by
  rw [T_eq, token4_form]
  exact ((Commute.refl Q).mul_right (D_Q.symm.pow_right 2)).conj K

theorem token6_token2 : Commute T (u (Cert.token 2)) := by
  rw [T_eq, token2_form]
  exact ((((Commute.refl Q).mul_right (C_Q.symm.pow_right 2)).mul_right
    (D_Q.symm.pow_right 2)).mul_right (S0_Q.symm.pow_right 2)).conj K

end
end QCert.CliffordCS3.Three.PermutationEven
