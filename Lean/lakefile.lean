import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c5ea00351c28e24afc9f0f84379aa41082b1188f"

package QCert where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib QCert where

/-- The execution benchmark of the paper's comparison with Agda
(`pldi/compare/README.md`); not part of the default build. -/
lean_exe cliffordbench where
  root := `Bench.CliffordBench
