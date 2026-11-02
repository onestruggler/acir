# Clean Lean typechecking benchmark

Elapsed time: **67 minutes 37.4 seconds** (monotonic clock).

- All 845 standalone project modules freshly compiled successfully.
- Lean 4.30.0; Mathlib revision c5ea00351c28e24afc9f0f84379aa41082b1188f.
- Intel Core i9-14900KS, WSL Ubuntu, 32 logical CPUs and 106 GiB RAM available.
- Lake worker setting: LEAN_NUM_THREADS=32; each Lean process: -j4.
- Observed peak: 32 concurrent compilers; sampled total proportional resident memory 34.4 GiB.
- Project output started empty; artifact-cache restoration and downloads disabled. Mathlib and other external dependencies remained prebuilt.
- All 100 axiom audit entries use only standard Lean axioms.
- Two generator fragments (meet_head.lean and meet_tail.lean) are not standalone modules and were excluded; their generated module was compiled.
- Base commit: cbad07d0eb660a7977958e51bf39a6834857e69f, plus the two local proof-checking fixes recorded in source-fixes.patch.
- The measurement includes ordinary Lake Lean artifacts (.olean, .ilean and generated C), without native C compilation.

Reproduction: run run.py under WSL. It makes a new temporary copy, reuses only dependency packages, and invokes all modules explicitly. See command.json and metadata.json for the exact invocation and source locations. sources.json records source hashes; build.log and individual Lake traces verify every fresh compilation. Timing and resource sampling begin with the build, excluding preparation and earlier failed diagnostic runs.

## Slowest modules

- QCert.RealCliffordCH.Sec8.D.W5.Family267: 1445.0 seconds
- QCert.RealCliffordCH.Sec8.D.W5.Family268: 1251.0 seconds
- QCert.RealCliffordCH.Sec8.D.W5.Base: 288.0 seconds
- QCert.RealCliffordCH.Sec8.D.W4.ConjComm242: 262.0 seconds
- QCert.RealCliffordCH.Sec8.D.W4.ConjComm243: 241.0 seconds
- QCert.CliffordT2.Eqs.Part12: 224.0 seconds
- QCert.ToffoliHadamard.Independence: 194.0 seconds
- QCert.RealCliffordCH.Sec8.D.N13.E322c2: 185.0 seconds
- QCert.RealCliffordCH.Sec8.D.N13.E322c1: 185.0 seconds
- QCert.ToffoliHadamard.Soundness: 177.0 seconds

## Local fixes and validation

Two standalone modules outside the main theorem import chain needed fixes:

- `QCert/RealCliffordCH/Sec8/A/ItemASteps.lean`: scoped heartbeat budget of 1,000,000 for `stepS2`.
- `QCert/RealCliffordCH/Sec8/A/ItemBFun.lean`: explicit finite-set cardinality arguments in `d3img_small` and `d4img_small`.

The fixes preserve the statements and introduce no axioms. Both files were rebuilt in the final clean run. All 845 compiled source hashes match the working checkout. The 100 audited results use only `propext`, `Classical.choice`, and `Quot.sound`.

The repository's separately requested Agda root check could not run: `/home/bonest/.local/bin/agda` is absent. No Agda sources changed.

Raw logs, timings, source hashes, proof-fix patch, and reproduction scripts are retained at `/tmp/acir-lean-clean-20261101-100109/`.
