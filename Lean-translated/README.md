# EquaCert in Lean: a module-for-module translation of the Agda

This folder translates the Agda development of this repository (the
framework at the root — `Word/`, `Presentation/`, `Circuit/`,
`Normalization/` — and the developments under `Examples/`) into Lean 4,
module for module: every Agda module gets a Lean module of the
corresponding name, with the same definitions, the same lemmas (names
ASCII-fied where Lean needs it) and the same proof route.  It is meant to
supersede `../Lean/`, whose developments were written from the source
papers, independently of the Agda.

Lean 4.30.0 and the same Mathlib as `../Lean/` (`lakefile.lean`).

## Building

In WSL (`.lake` is a symlink to `/home/bones/equacert-lake`, whose
`packages/` is the Mathlib build of `../Lean/`, shared, never rebuilt):

```sh
./check.sh EquaCert/Some/Module.lean   # build a module and its imports (serialized)
tools/lean1.sh EquaCert/Some/Module.lean   # check one file, write nothing
./check.sh                              # the whole library
```

From PowerShell, run a script file through `wsl --exec bash <script>`
(quoting through `wsl --exec bash -lc '…'` is fragile).

## Status

| Agda | Lean (`EquaCert/…`) | Status |
| --- | --- | --- |
| `Word/Base` | `Word/Base` | translated |
| `Presentation/Base`, `Core` | `Presentation/Base` | translated |
| `Presentation/GroupLike` | `Presentation/GroupLike` | translated |
| `Presentation/Definitions` | `Presentation/Definitions` | translated |
| `Presentation/Embedding` | `Presentation/Embedding` | translated |
| `Presentation/Morphism`, `MorphismId` | `Presentation/Morphism` | translated (what the developments use) |
| `Circuit/Base` | `Circuit/Base` | translated |
| `Circuit/Prop` | `Circuit/Prop` | translated |

Each development's folder has a `STATUS.md` with its module map and what
is left.

## Conventions (read before translating a module)

**Where.**  The Agda module `A/B-C/D.agda` becomes `EquaCert/A/BC/D.lean`:
folder and file names lose `-` and `+` (`Real-Clifford+CH` → `RealCliffordCH`,
`Reidemeister-Schreier` → `ReidemeisterSchreier`), and stay ASCII
(`r7d₀_i01` → `r7d0_i01`).  Declarations live in a namespace
`EquaCert.<Development>` (sub-namespaces as needed against clashes).  The
parts of the EucDomain library that are needed are translated under
`EquaCert/EucDomain/` (e.g. `EquaCert/EucDomain/Quantum/Synthesis/Ring.lean`).

**Words and congruences** (`EquaCert/Word/Base`, `Presentation/Base`).

| Agda | Lean |
| --- | --- |
| `Word X` | `Word X` = `FreeMonoid X` (lists) |
| `[ x ]ʷ`, `ε`, `w • v` | `FreeMonoid.of x` (`[x]ʷ` in `open EquaCert.Word`), `1`, `w * v` |
| `w ^ n` | `w ^ n` (monoid power) |
| `wmap f`, `(f ʷ)` | `FreeMonoid.map f`, `FreeMonoid.lift f` |
| `WRel X`, `_===_` | `WRel X`, the relation itself |
| `_≈_` of `Presentation.Base Γ` | `Derivable Γ` (= Mathlib's `conGen Γ`) |
| `refl`, `sym`, `trans`, `cong`, `axiom` | `Derivable.refl`, `.sym`, `.trans`, `.cong`, `.ax` (also `.of`, `.mul`, `.symm`) |
| `assoc`, `left-unit`, `right-unit` | equalities of words (`mul_assoc`, `one_mul`, `mul_one`); `Derivable.assoc` etc. exist |
| `cleft`, `cright`, `refl'` | `Derivable.cleft`, `.cright`, `.refl'` |
| `Grouplike`, `Group-Lemmas` | `Grouplike` (a `Prop`), `GroupLemmas.inv`, `inverse_l`, `cancel_l`, … |
| `_IsPresentationOf_ G` etc. | `IsPresentationOf Γ sem`, `IsSubPresentationOf`, `IsMonoidPresentationOf`, `IsSubMonoidPresentationOf` (`sem : X → G` into a Mathlib group or monoid, read on words by `FreeMonoid.lift sem`) |
| `Presentation.Morphism` (`StarGroupIsomorphism`, …) | `EquaCert.Morphism.RSStep`, `lift_cong`, `idIso` |

Associativity being definitional for closed words and a rewrite
(`simp only [mul_assoc]`) for open ones, the Agda's `by-assoc`,
`by-passoc` and `assoc` steps become `rw`/`simp only [mul_assoc]` or
disappear; that is not a deviation worth recording.

An Agda group whose equality is not `≡` (a setoid: scaled matrices up to a
power of a unit, operators compared pointwise) becomes a Mathlib group on a
quotient, or the development's own group with `=`; say which in the
module header.

**Circuits** (`EquaCert/Circuit/Base`, `Circuit/Prop`).

| Agda (`Circuit.Base Gate`) | Lean |
| --- | --- |
| `Gen n`: `gate₀`…`gate₃`, `g ↥` | `Gen Gate n`: `.gate0`…`.gate3`, `.up g` |
| `Circuit n` | `Circuit Gate n` |
| `w ↑`, `w ↓ᵏ k` | `Circuit.shift w`, `Circuit.pad k w` (width `k + n`) |
| `Lift-Relation`'s `_VRel,_===_` (`srel`, `cong↑`, `comm₁`…`comm₃`, `ω↑=ω`) | `Lift R n` (`.rule`, `.shift`, `.comm1`…`.comm3`, `.scalar`) |
| `n ⊢ w ≈ v` | `Derives R n w v` |
| `lemma-cong↑`, `comm-gate₁-w↑`, `Central-Scalars.comm₀` | `Circuit.lemma_cong_up`, `Circuit.comm_gate₁_w`, `Circuit.comm₀` |
| `Circuit.Prop` (`σ`, `σ[ k ]`, `Lift-To-Prop`, `nat₁`, `pad`) | `EquaCert.CircuitProp` (`σ`, `σc k`, `PropRel`, `VRel`, `Der`, `nat₁`, `pad`) |

**Names.**  Keep the Agda's names; where Lean refuses them, change as
little as possible and consistently: `-` → `_`; superscript letters are not
identifier characters in Lean (`ˡ ʳ ʷ ᵗ ᵀ ᴾ …`): `inverseˡ` → `inverse_l`,
`⟦_⟧ᵍ` → `semG`; subscripts and Greek are fine (`comm₁`, `σ`); Lean
keywords (`axiom`, `at`, `by`, `fun`, `have`, `show`, `from`, `in`, `end`,
`open`, `Prop`, `Type`) and Mathlib tokens (`to`) need another name.  A
`--` in an Agda name cannot start a Lean name.

**Proofs.**  Follow the Agda's proof route: the same lemmas, the same case
splits, the same intermediate statements.  Tactics are fine for the steps
(`rw`, `simp`, `omega`, `decide`), but do not replace an Agda argument by a
different mathematical argument; where Lean forces a departure, say so in
the module header under **Deviation**.  No `sorry` in a committed module
unless `STATUS.md` lists it; no `native_decide`, no new axioms.  Decide
computations with `decide`/`decide +kernel`/`rfl`; the kernel pays per
unfolding, so compile tables once and compare with `Nat.beq`/`Bool`, and
qualify constructors in long list literals (`Gen.gate1 …`, not `.gate1 …`):
an unqualified dotted name elaborated before its expected type costs about
0.1 s each.

**Generated modules.**  Where the Agda's module is generated (its header
or the folder README says so), port the generator: a Python script in the
development's `gen/` folder that reads the Agda's own data (or imports the
Agda's generator) and writes the Lean module, byte for byte reproducibly.
Run Python in WSL (`python3`).

**Statements.**  Each development keeps the Agda's `MainTheorem` as a
Lean `MainTheorem` module stating the same results.  Where the Agda's
semantics lives in its own computational structures (tries, rings defined
as data), translate them as they are; a bridge to Mathlib's standard objects
(matrices over `ℂ`, `Matrix.unitaryGroup`, `alternatingGroup`) is welcome in
`MainTheorem` once the translation is complete.

## For agents working here in parallel

* Translate only your development's folder.  Create a framework module
  (outside `EquaCert/Examples/` and `EquaCert/EucDomain/`) only if it does
  not exist yet, build it, and commit it at once so that others see it;
  never change an existing framework module's declarations — put helpers in
  your own folder instead, or add new declarations at the end of the file.
* Keep `STATUS.md` in your folder current (module map: Agda module, Lean
  module, written/generated, builds?, open points).  An agent can be cut
  off at any moment; the next one resumes from `STATUS.md` and git.
* Build with `./check.sh` (serialized by a lock), iterate on one file with
  `tools/lean1.sh`.  Never run `lake build` directly.
* Commit your own paths only, as soon as a module builds:
  `git -c user.name="Bian@helan" -c user.email="bian@dal.ca" commit -m "<msg>" -- <paths>`
  after `git add <paths>`, from Git Bash on Windows (if `index.lock`
  exists, wait a few seconds and retry).  Do not push; do not touch
  `../Lean/`, the Agda, `pldi/` or other developments' folders.  Files here
  are LF (`.gitattributes`).
