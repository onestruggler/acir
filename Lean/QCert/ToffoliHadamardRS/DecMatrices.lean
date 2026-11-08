/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: decoded values

Translation of `DecMatrices.agda`: the decodings of the basic generators
`(-1)_[0]`, `X_[d,d+1]` and `K_[0,1,2,3]` of Li, Ross and Selinger have
their values, checked by computing them.
-/
import QCert.ToffoliHadamardRS.Decode
import QCert.ToffoliHadamardRS.Decide

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (sem)

theorem dM0 : semO (dec (mG 0)) = FreeMonoid.lift (sem 8) (Mw 0) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX01 : semO (dec (xG 0 1)) = FreeMonoid.lift (sem 8) (Xw 0 1) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX12 : semO (dec (xG 1 2)) = FreeMonoid.lift (sem 8) (Xw 1 2) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX23 : semO (dec (xG 2 3)) = FreeMonoid.lift (sem 8) (Xw 2 3) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX34 : semO (dec (xG 3 4)) = FreeMonoid.lift (sem 8) (Xw 3 4) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX45 : semO (dec (xG 4 5)) = FreeMonoid.lift (sem 8) (Xw 4 5) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX56 : semO (dec (xG 5 6)) = FreeMonoid.lift (sem 8) (Xw 5 6) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dX67 : semO (dec (xG 6 7)) = FreeMonoid.lift (sem 8) (Xw 6 7) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem dK0123 : semO (dec (kG 0 1 2 3)) = FreeMonoid.lift (sem 8) (Kw 0 1 2 3) :=
  semO_eq_sem8_of_check (by decide +kernel)

end QCert.ToffoliHadamardRS
