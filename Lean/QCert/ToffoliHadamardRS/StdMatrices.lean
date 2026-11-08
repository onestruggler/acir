/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: standard values

Translation of `StdMatrices.agda`: the circuits `T d` of Figure 7 and
`(-1)_[0]` encode words with the values of `X_[d,d+1]` and `(-1)_[0]`,
checked by computing them.
-/
import QCert.ToffoliHadamardRS.Decide
import QCert.ToffoliHadamardRS.Syntactics

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (sem)

theorem mT0 : semO (T (k := 1) 0) = FreeMonoid.lift (sem 8) (Xw 0 1) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mT1 : semO (T (k := 1) 1) = FreeMonoid.lift (sem 8) (Xw 1 2) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mT2 : semO (T (k := 1) 2) = FreeMonoid.lift (sem 8) (Xw 2 3) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mT3 : semO (T (k := 1) 3) = FreeMonoid.lift (sem 8) (Xw 3 4) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mT4 : semO (T (k := 1) 4) = FreeMonoid.lift (sem 8) (Xw 4 5) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mT5 : semO (T (k := 1) 5) = FreeMonoid.lift (sem 8) (Xw 5 6) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mT6 : semO (T (k := 1) 6) = FreeMonoid.lift (sem 8) (Xw 6 7) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem mm0 : semO (m0 (k := 0)) = FreeMonoid.lift (sem 8) (Mw 0) :=
  semO_eq_sem8_of_check (by decide +kernel)

end QCert.ToffoliHadamardRS
