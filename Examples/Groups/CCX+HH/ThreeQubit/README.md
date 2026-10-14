# Three-wire finite subgroup translation

This construction uses the existing two-level Table 1 presentation and
Clément's translation argument. It does not import a presentation of an
exceptional finite group.

The full eight-level dyadic group cannot be decoded into three-wire
`{X, CX, CCX, HH}` circuits: the circuit image is finite and the ambient
group is infinite. Instead, this directory uses a finite collection of
cosets **inside the circuit image**, with even signed permutations as its
base subgroup.

`Presentation.agda` assembles a sound and complete theory with **1185
circuit equations**: 1080 transition equations and 105 decoded base
equations. Its semantics is the common ordinary matrix interpretation in
`../Semantics.agda`, including global sign. `Orthogonal.agda` packages the
same theorem as a group sub-presentation of the dyadic orthogonal group.

## Exact finite data

The eight adjacent physical generators are `X0`, `X1`, `X2`, `CX10`,
`CX21`, `CCX210`, `HH01`, and `HH12`. They preserve 240 integral vectors:
the 112 vectors with two entries equal to ±2 and all other entries zero,
and the 128 vectors whose entries are ±1 with an even number of minus
signs. The coordinate frame has an orbit of 135 unoriented frames.

Its stabilizer consists of the even signed permutations on eight levels.
The 14 generators are the adjacent exchanges `X[i,i+1]` and sign pairs
`M[0] M[i+1]`, for `i = 0,...,6`. Concrete circuits for all 14 are given
in the data. Thus the exact diagnostic obtains the group order
`135 * (2^7 * 8!) = 696729600` without enumerating every group element.

`finite_cosets.py` constructs and verifies the complete orbit, the 14
stabilizer witnesses, and all 1080 transition factorizations. Its default
mode checks `finite_cosets.json`; `--write` regenerates that artifact.

## Proof organization

- `FiniteExtension.agda` proves the generic translation theorem: a
  complete base presentation, a factorization table, and separation of
  the representatives give a sound and complete circuit presentation.
  Its circuit axioms are the table equations and decoded base axioms.
- `Cosets.agda` supplies the 135 representatives, and `Table.agda` supplies
  the 1080 cells over the 14-letter base alphabet.
- `StabilizerGenerators.agda` gives the base generators, their circuit
  decoders, and source derivations proving each decoder correct. Eleven
  short circuit macros are checked once before composing the 14 plans.
- `Checks/Rows*.agda` checks each factorization as an exact dyadic matrix
  identity. `Factorizations.agda` applies the already proved completeness
  of Table 1 to turn these identities into source derivations. The
  checks do not evaluate whole representatives: `Checks/Matrices.agda`
  stores the matrix of each of the 135 representatives as a literal,
  `Checks/Matrices000.agda` … `Matrices108.agda` prove each one equal to
  the matrix of its encoded circuit, and `Checks/Assemble.agda` turns a
  cell into a comparison of stored matrices. The left side is the stored
  matrix of `rep c` times that of `e g`, which, every encoded generator
  being symmetric, is `e g` acting on its transpose; the right side is
  the base word acting on the stored matrix of the next representative.
  Every identity is decided by one boolean (`by-eq` of
  `CCX+HH/Decide.agda`) rather than by `refl`, which would make Agda
  compare the two matrices entry by entry.
- `QuarticInvariant.agda` proves that the sum of fourth powers is
  invariant under signs and exchanges. `Signature.agda` checks its value
  on a fixed probe for each representative; the 135 values are distinct.
  `Separation.agda` therefore proves that two base words followed by
  representatives can be equal only when their representatives agree.
- `FiniteNormalization.agda` provides a finite normal-form table
  presentation for the base. The concrete base development uses even
  sign vectors and the repository's symmetric-group normal forms.
  `StabilizerFaithfulness.agda` distinguishes these forms by their action
  on a vector with eight distinct positive coordinates; the signs and
  the permutation are recovered separately.
- `Compact/` proves that 105 explicit equations suffice for that base:
  seven phase squares, 21 phase commutations, 28 ordinary symmetric-group
  equations, and 49 exchange/phase conjugation equations. `Normalization`
  derives the finite normal-form table from these equations, while
  `Soundness` derives each equation in the existing Table 1 presentation.
  `Compact/Presentation.agda` gives both directions of the translation.
- `Presentation.agda` combines the complete base, the 1080 derived table
  cells, and separation through `FiniteExtension`. The Python finite
  diagnostic supplies data; the Agda proof establishes completeness.
- `NormalForm.agda` gives the canonical form: an even signed permutation
  followed by one of the 135 representatives. It proves normalization
  in the circuit calculus, uniqueness, and the exact section equation.

`compact_relations.json` stores the 105 base equations and their physical
decoders. Together with the 1080 cells in `finite_cosets.json`, it specifies
all 1185 concrete circuit equations. `compact_relations.py` expands and
checks every equation using independent exact physical matrix arithmetic.

## Executable normalization

`normalize.py` reads a circuit in **matrix-product order** and returns its
even signed permutation, coset number, and a deterministic physical word
for that normal form. The permutation maps input basis indices to output
indices; the eight signs are indexed by output row. Global signs are
retained. The physical word is a deterministic spelling of the normal
form, not necessarily the shortest circuit or the literal symmetric-group
word chosen by Agda's section.

```sh
python3 -B Examples/Groups/CCX+HH/ThreeQubit/normalize.py X0 HH01 CX10 HH12
python3 -B Examples/Groups/CCX+HH/ThreeQubit/normalize.py --json 'X0 HH01 CX10 HH12'
python3 -B Examples/Groups/CCX+HH/ThreeQubit/normalize.py --self-test
```

The CLI uses all 1080 stored factorizations and the 14 stored base
decoders. Its deterministic self-test compares independent exact physical
matrices for every cell, all eight generators, and 84 random words; it
also checks normalization of canonical words and even signed-permutation
sections. The CLI is an executable companion to `NormalForm.agda`.

## Word order

The original diagnostic's physical word lists act from left to right.
The normalization CLI and Agda words use the
repository's matrix multiplication order. A stored representative list
is read in that matrix order in `Cosets.agda`. A cell has the equation

```
encode(rep c) · encode(g) = base(output c g) · encode(rep(next c g)).
```

The JSON field `stabilizer_word_matrix_order` already records the right
orientation for its Agda word. The circuit witness lists are reversed by
the generator when forming their matrix-order plans. Every orientation
is tested independently by the exact factorization checks.

## Reproduction

```sh
python3 -B Examples/Groups/CCX+HH/ThreeQubit/finite_cosets.py
python3 -B Examples/Groups/CCX+HH/ThreeQubit/build_finite.py --check
python3 -B Examples/Groups/CCX+HH/ThreeQubit/build_stabilizer.py --check
python3 -B Examples/Groups/CCX+HH/ThreeQubit/build_compact.py --check
python3 -B Examples/Groups/CCX+HH/ThreeQubit/build_tags.py --check
python3 -B Examples/Groups/CCX+HH/ThreeQubit/compact_relations.py
agda Examples/Groups/CCX+HH/ThreeQubit/Orthogonal.agda
agda Examples/Groups/CCX+HH/ThreeQubit/NormalForm.agda
```

`build_finite.py` regenerates the data modules when called without
`--check`. The `--check` mode compares every generated module without
writing any file. The Agda proofs use `--safe --without-K` and rely on
ordinary kernel checking; Python output is not accepted as a proof.

The 1080 cells check in about three minutes in one Agda process, after
the five `Checks/Matrices*.agda` modules (about ten seconds each) have
checked the stored representatives. From scratch, `../Presentation.agda`
(with all of `CCX+HH-TwoLevel`) checks in under nine minutes with a peak
heap near 3.4 GB; it took about 45 minutes when every cell evaluated
both of its representatives and compared the matrices by `refl`.
