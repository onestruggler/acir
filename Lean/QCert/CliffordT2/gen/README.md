# Generators of the CliffordT2 certificates

Python scripts that write the generated modules of `QCert/CliffordT2`.
Only the kernel's replay of their output is trusted; the scripts are here
so that the certificates can be regenerated and audited.  They need
Python 3 with numpy (tested with CPython 3.14.7 and numpy 2.5.3 on
Windows).

## Input: the authors' ancillary files

`agda_chain.py` reads, from the authors' Agda code for arXiv:2204.02217,
the words around the steps where their proofs of Equations 21, 28, 30,
43, 44 and 46 use (C18), (C19) and (C20).  The files are not committed.
Get the arXiv source, https://arxiv.org/src/2204.02217 (a tar archive,
SHA-256 `e53a10e2b4e2245fa6ecd052a12d7cb11a8c11479e9f52d06a7ace4e38cce9e0`,
the EPTCS 394 version).  Then put its `anc/` directory at `gen/anc`, or
point `CT2_ANC` at it.  The files read are:

| File | SHA-256 |
|---|---|
| `anc/Equation21.agda` | `26551b2337df1c646d2e4056378fbf69e3f024dde3f8234124debdf7c8092342` |
| `anc/Equation28.agda` | `4b370ee36efa7f302d975ceb5a5ba649ab1424ea0d7ed2e29b8b51c972246a7d` |
| `anc/Equation30.agda` | `2ab122f37e48335fbdd4085447f8613fa49c18da55baa5cb6ef4c996a30c7ef7` |
| `anc/Equation43.agda` | `22a71e0c2a4805c982c8a674f3e2df257f2b2b068500cee393fdc8db25e4c0c1` |
| `anc/Equation44.agda` | `8203d6a2608f419cdd1e59ba1f91956c5b01c655b9fd2ede9e56a3097b8236ea` |
| `anc/Equation46.agda` | `cbd40fd4b63758a3e997481add1e8f7fc76e9863558585e7bf15adeb94f510d4` |

## Pipeline

Run the scripts in this order, from any directory:

| Step | Script | Reads | Writes | Time |
|---|---|---|---|---|
| 1 | `cliffnf.py` | — | `work/cliffnf.pkl` | about 1 min |
| 2 | `rotcert.py` | `work/cliffnf.pkl`, `anc/` | `work/eqcerts.pkl` | about 5 min |
| 3 | `emit.py` | `work/eqcerts.pkl` | `Cert/Axioms.lean`, `Cert/Clifford.lean`, `Cert/Rotations.lean` | seconds |
| 4 | `gen_equations.py` | `work/eqcerts.pkl` | `Equations.lean`, `Eqs/Part00.lean` … `Eqs/Part12.lean` | seconds |
| 5 | `gen_simplified.py` | — | `SimplifiedGreylyn.lean` | seconds |

What each step does:

1. Normal forms of the two-qubit Clifford group by a stabilizer chain.
   Each coset-table entry is a rewriting rule with a derivation from the
   relations of Figure 1.  The last level of the chain is done by coset
   enumeration with proofs.
   - `cliffnf.py` uses `ct.py` (the relations and the matrices), `chain.py`
     (the chain), `deriv.py` (rules, rewriting and search) and `psearch.py`
     (search through partial normal forms).
2. The Pauli-rotation lemmas, and the certificates of the 46 equations.
   - `rotcert.py` uses `rot.py` and `agda_chain.py`.
3. The rules as Lean definitions.
4. The 46 equations.  A certificate is cut into lemmas of at most 10 000
   steps (`CHUNK`).  A part file holds about 30 000 steps (`PART_STEPS`).
5. The 123 instances of Greylyn's relations, derived in the authors'
   five-generator form.

Every other module of the folder is written by hand, including
`Cert/Code.lean`.

## Where they read and write

`paths.py` sets three directories, each of which an environment variable
can override:

- `CT2_OUT`, for the Lean modules: by default the parent folder,
  `QCert/CliffordT2`.
- `CT2_WORK`, for the pickles: by default `gen/work`.
- `CT2_ANC`, for the ancillary files: by default `gen/anc`.

`work/` and `anc/` are ignored by git.

## Reproducibility

On 28 October 2026 one run of steps 1–5 from scratch reproduced all 18
generated modules byte for byte:

- `CT2_OUT` and `CT2_WORK` were fresh directories, and `anc/` was
  extracted from the archive above.
- `PYTHONHASHSEED` was set to 12345, a different seed from the run that
  first wrote the modules.
