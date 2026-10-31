# Three-qubit Clifford+CS coset certificate

This directory proves `CliffordCS3.rsData`. The two cosets have
representatives 1 and i_[7], and the macro letters follow `Macro8`.
No proof here assumes three-qubit Clifford+CS completeness.

`Certificate.complete_check` verifies all 98 residual equations and
coset endpoints using tables whose entries carry actual derivations:

| Table | Macro indices | Cases across both cosets |
| --- | --- | --- |
| `Cert/Permutations` | 0–27 | 56 |
| `Cert/PhaseCases` | 28, 30, 32, 34, 36, 38 | 12 |
| `Cert/KCases` | 29, 31, 33, 35, 37 | 10 |
| `Cert/LocalBlock` | 6, 39, 40, 41, 44–47 | 16 (index 6 also occurs above) |
| `Cert/PointCommutation` | 42 | 2 |
| `Cert/DisjointK` | 43 | 2 |
| `Cert/Interchange` | 48 | 2 |

`GeneratorRecovery.hyp_a` proves the nine recovery equations from the
verified ambient relations. `RecoveryClosure` transports short preimages
through the completed presentation of the ambient unitary group;
`RecoveryGeneration` derives the original gates by permutation identities,
pair-phase identities, and removal of the controls on the residual atom.

`Gauge` and `RestrictedGauge` reduce the two coset branches of the final
three equations to group equalities on four basis states. The last equation
is commutation of two controlled Hadamards (`BlockVertical`,
`BlockHorizontal`, `BlockInterchange`), derived from the circuit rules.

Proofs use the completed two-qubit presentation, group algebra in the
syntactic quotient, and kernel replay of independently constructed
certificates. Python matrix checks guide search; the derivations are
checked in Lean. `PartialCertificate` retains the earlier 34-case subset.

Build from `Lean/` with:

```sh
bash check.sh QCert/CliffordCS3/Theorem.lean
bash check.sh QCert/Audit.lean
```

The completed theorem and the dependent minimality theorem have no
`sorryAx` dependency. Certificate regeneration is documented in `../gen/README.md`.