# The alternating group on sixteen points as reversible circuits

A Lean translation of the Agda development `Examples/Groups/Alt16-RevCir/`:
the seven rules r1, …, r7 between circuits over NOT (`X`), CNOT (`CX`),
Toffoli (`CCX`) and the swap of two adjacent wires (`Ex`) present Alt(16) on
four wires, and Sym(2), Sym(4), Sym(8) on one, two and three (Section 6 of
`qcert.pdf`).

The Lean follows the Agda module for module (38 modules, the same names),
with the same definitions, the same lemmas (names ASCII-fied where Lean
needs it) and the same proof route, and the same generated derivations,
written by ports of the Agda's generators from the Agda's own search
results.  What the Agda imports from shared libraries is translated in
`Lib/` (16 modules).  Departures are listed under "Deviations" below, and
each is stated in its module's header.

## What is proved (`MainTheorem.lean`)

The Agda's `MainTheorem.agda`, statement for statement, in the namespace
`QCert.Alt16RevCir.MainTheorem`.  The circuits on `n` wires are `Circ n`;
`RRel n` is the relation of the rules r1, …, r7 (`TRel`) with the laws of
the swap and the structural rules, `CRel n` the translated relation of
`Syntactics`, and `LRel` Lafont's relation between the words in the cycles
`ω₀, …, ω₁₃`; `⊢ᴿ w ≈ v`, `⊢ w ≈ v` and `⊢ᴸ u ≈ t` are derivability by
them.  `sem w` is a circuit's function on the bit vectors of its wires, `≐`
pointwise equality, and `semA w` its even permutation of the sixteen
positions.  Wire 0 is the bottom wire, and words are in diagram order:
`w * v` is `w` then `v`.

* `presentationR : IsPresentationOf (RRel 4) permA`: the four-wire circuits
  modulo the rules present Alt(16), with `lift_permA` and `semA_sem` saying
  that a circuit is read as its function on the numbered states, and
  `group₄ : (conGen (RRel 4)).Quotient ≃* Alt 16`;
* `soundR`, `completeR`: two circuits are equal by the rules exactly when
  they are the same function on the states;
* `normal_formR`, `nf_congR`, `canon_g`, `nf_canon`, `canon_unique`,
  `canon_onto`: every circuit is equal by the rules to a unique canonical
  circuit, the translation of Lafont's canonical form letter for letter;
* the first step, `circuits_iso_cycles` with `f_well_defined`,
  `g_well_defined`, `f_left_inv_gen`, `g_left_inv_gen`, and its
  `presentation` of Alt(16) by the translated relation, with `sound` and
  `complete`;
* the second step, `relations_to_rules`, `rules_to_relations`,
  `rules_iso_relations` (the identity is an isomorphism) and
  `rules_iso_cycles` (the first step holds for the rules, with the same
  translations);
* `presentation₁`, `presentation₂`, `presentation₃`, `complete₁`, …: on one,
  two and three wires the rules present Sym(2), Sym(4) and Sym(8).

**The form of the statements.**  The Agda's groups of permutations multiply
in diagram order (`∘ₚ`), as the circuits do, while Mathlib's `Equiv.Perm`
and `alternatingGroup` multiply in operator order and the framework's
`IsPresentationOf Γ sem` reads a word by `FreeMonoid.lift sem`.  So the
presentations are stated in the opposite groups `(Equiv.Perm (Fin N))ᵐᵒᵖ`
and `(Alt 16)ᵐᵒᵖ`, a generator read as `op` of its permutation of the
numbered states.  The Agda's `IsGroupIsomorphism … (f ʷ)` between two word
groups is a `MulEquiv` between the monoids of words modulo the two
relations, with an equation saying that it is `f ʷ` (or the identity) on
classes.

No `sorry`, no new axioms, no `native_decide`.  `#print axioms` of every
statement of `MainTheorem` gives `[propext, Classical.choice, Quot.sound]`
(`soundR`, `sound`, `canon_g`, `g_well_defined` and `g_left_inv_gen` only
`[propext, Quot.sound]`).

## The proof

As the Agda's README describes it, with the Lean names.

1. **The first step** (`Syntactics`, `Translation`, `Semantics`,
   `Numbering`, `Lemmas`, `Bridge`, `Iso`, `Presentation`, `NormalForm`):
   Lafont's presentation of Alt(16) by the cycles of three consecutive
   points (`Lib/Alternating`) is carried to the circuits along the
   translations `f` and `g`; the relations between the cycles' circuits
   `Ω i` and one rule per gate form the translated relation, which is
   therefore complete, and Lafont's canonical forms give the normal form.
2. **Three wires and below** (`Theory`, `Engine`, `BySymmetric`, `Width1`,
   `Width2`, `Width3`, `ThreeWire`): a step of the same kind from the
   Coxeter presentation of the symmetric group (`Lib/Symmetric`), with the
   Coxeter relations between the edge Toffolis and the gates' words derived
   from the rules by a Knuth–Bendix completion and replayed by the engine.
3. **Four wires** (`FourWire`, `Frames`, `Letters`, `Four/Part1`–`Part14`,
   `Four/Relations`): the 105 relations between the cycles and the six gate
   words, derived from the rules in 788 lemmas of 15 607 steps, each a
   three-wire step, a step between words in the NOT gates and swaps, a
   change of frame, or a rule that involves all four wires.
4. **The second step** (`Equivalence`): the two relation sets have the same
   consequences, so the rules present Alt(16).

## Module map

All 38 modules of the Agda folder have a Lean module of the same name in
`QCert/Alt16RevCir/`; "generated" modules are written by a script of `gen/`.

| Agda (`Examples/Groups/Alt16-RevCir/`) | Lean (`QCert/Alt16RevCir/`) | |
| --- | --- | --- |
| `Syntactics`, `Translation`, `Semantics`, `Numbering` | the same | written |
| `Lemmas`, `Bridge`, `Iso`, `Presentation`, `NormalForm` | the same | written |
| `Theory`, `Engine`, `BySymmetric` | the same | written |
| `Width1`, `Width2`, `Width3`, `ThreeWire` | the same | written |
| `Width2/Derivations`, `Width3/Derivations` | the same | generated (`mk_narrow.py`) |
| `FourWire`, `Frames`, `Letters` | the same | written |
| `Four/Part1`–`Part14`, `Four/Relations` | the same | generated (`mk_four.py`) |
| `Equivalence`, `MainTheorem` | the same | written |

What the Agda imports from outside its folder:

| Agda library | Lean | |
| --- | --- | --- |
| `Examples/Groups/Alternating` (all but `Alternative`) | `Lib/Alternating/` (13 modules, the same names) | written |
| `Examples/Groups/Symmetric` (`Syntactics`, `Semantics`, `Interpretation`, `Soundness`, `Completeness`, `Presentation`, `Surjectivity`) | `Lib/Symmetric` | written; completeness from `QCert.ToffoliHadamardRS.CoxeterFrames` |
| `Circuit/Prop` (and `Circuit/Base`'s `Lift-Relation` lemmas) | `Lib/CircuitProp` | written, over `QCert.Circuit.Basic` |
| `Presentation/Morphism`, `MorphismId`, `Definitions`, `Embedding` | `Lib/Morphism` | written |
| `Word`, `Presentation.Base`, `GroupLike` | `QCert.Presentation` (`FreeMonoid`, `Derivable`, `IsPresentationOf`, `Grouplike`) | reused |
| `Data.Fin.Permutation` | Mathlib's `Equiv.Perm (Fin N)` | reused |

`Lib/CircuitProp` and `Lib/Symmetric` are the modules of the same names of
`QCert/XCXCCX4bit/Lib` (the Lean translation of the earlier Agda proof of
the same theorem), copied so that this folder does not depend on that one.

## Generators (`gen/`)

Each is a port of the Agda generator of the same name and writes the Lean
modules from the same inputs, which it reads from the Agda folder
(`Examples/Groups/Alt16-RevCir/gen/`).  `mk_narrow.py` reads the saved
completions `narrow2.json`, `narrow3.json` and replays every chain by the
Agda generator's `replay`.  `mk_four.py` imports the Agda's compiler
(`four.py`, `inst.py`, `gatesc.py`, and `mk_four.py`'s `rule7`,
`pair_orbits`, `relators`), which compiles the macro derivations of
`search/` and replays every step, and writes the lemmas it collects, in the
same order and the same fourteen parts, with `Four/Relations.lean`.  Like the
Agda's, the generators are untrusted: Lean checks what they write.  Run them
with WSL's `python3` from `gen/`:

```sh
cd QCert/Alt16RevCir/gen
python3 mk_narrow.py 2 && python3 mk_narrow.py 3 && python3 mk_four.py
```

They regenerate the checked-in modules byte for byte (about fifteen
seconds).

## Deviations from the Agda

Collected from the module headers, which state each one where it occurs.

* **Words.**  The framework's words are `FreeMonoid` (lists), so the Agda's
  associativity steps and `by-assoc`/`by-passoc` disappear or become
  reasoning in the quotient monoid of the theory (`CircuitProp.cl`), and the
  two calculations of `Frames` with several of them are done once in any
  monoid (`step_calc`, `conj_calc`).  `sound` and `s_to_t` are inclusions of
  generated congruences, where the Agda's are inductions on derivations.
* **Letters are names.**  The Agda's letter lists are lists of generators.
  Here they are lists of names in an alphabet (`Engine`'s `L2`, `L3`, `L4`,
  with `Alpha.gen` the generator of a name), which the kernel compares by
  comparing numerals; `top` and `bot` are the engine's `liftE` and `padE`
  along the maps of names that shifting and widening are.
* **Computation.**  The Agda's `refl` on a Boolean is `decide +kernel` on a
  Boolean checker with a soundness lemma (`Engine.check`, `Letters.check4`,
  `same`, …).  The engine walks to a position with an accumulator (`rwAt`),
  so that the word it carries stays evaluated in the kernel.
* **Kernel cost.**  One application of the Agda-style `semG` to a state
  costs the kernel about half a millisecond (both `Gn n` and `Bits n` are
  indexed families), so long comparisons are decided on the states as
  numbers: a letter is an operation on numbers (`Semantics`' `Op`), checked
  against `semG` once per letter, and `sameOps_sound` carries the result to
  `sem` (`same₄` for the four-wire rules, `FourWire.same3` for the
  three-wire steps: `Semantics` 79 s → 10 s).  The permutation of a closed
  word in Lafont's cycles is evaluated on the positions as numbers
  (`Bridge`'s `cycN`, `actN`, `sem_val`).
* **Evidence of a step.**  In the Agda a step that evaluation decides (`bo`,
  `to`, `hs`, `fr`) takes its evidence as a hidden argument solved by eta.
  Here such a step is a constructor of `Letters.Step4` whose evidence the
  run evaluates itself, so that a lemma is one kernel check instead of one
  for each of its steps.
* **Strings.**  The Agda decodes the strings of `Letters` by evaluation;
  here `ℓ "…"`, `ℓ₃ "…"`, `ℓʰ "…"` are term elaborators that produce the
  lists of names, and `bo`, `tp` (the Agda's `to`, a Mathlib keyword), `hs`,
  `fr`, `rw`, `rwˢ`, `deriveℓ` are notations taking the string literals.
* **Symmetric and alternating groups.**  A letter of `S_N` is its index with
  its bound (`SG N`), and `SymRel N` lists the Coxeter relations at every
  index, so `BySymmetric` needs no recursion on shifts.  The sign is
  Mathlib's `Equiv.Perm.sign` read as a Boolean and `Alt n` is
  `alternatingGroup (Fin n)`; Lafont's words are circuits over one
  three-wire gate, as in the Agda.  Permutations are `Equiv.Perm`.
* **Parameterised modules** are structures (`BySymmetric.Step`) or
  namespaces whose lemmas take the parameters as arguments
  (`Lemmas.FromCycles`, `Alternating.Completeness`).
* **The main statements** are stated in the opposites of Mathlib's groups,
  with the semantics named (`perm₁`, …, `permA`) and characterised
  (`lift_permA`, `semA_sem`), the isomorphisms are `MulEquiv`s of quotient
  monoids, and `group₄` is added; `canon_onto` returns a subtype.
* **Unification at sixteen points.**  Lafont's `nf` and `canonical` compute
  through sixteen levels, so `NormalForm` unfolds its own definitions before
  it applies a lemma about them (`lemma_8₄`), as the Agda README's first
  trap asks.
* **Smaller reuse.**  `Lemmas.conjugate` is stated over any relation and
  `Theory` reuses it; `Semantics.lift_sound` is the soundness of the
  structural rules over any relation; `Presentation.presentation_semA` gives
  both presentations.
* **Not translated** (unused by the development):
  `Examples/Groups/Alternating/Alternative` and the Fig. 10 theory
  (`sound-R`, `sound-A`, `presentation-Fig10`, `presentation′`), and the
  normal-form records `nfp′`, `unique-nf`.
* **Names.**  `x⁼` is `xE`, `xᵀ` is `xT`, hyphens are underscores, `⟦_⟧` is
  `sem`, `⟦_⟧ᴬ` is `semA`, `Circuit`/`Gen` are `Circ`/`Gn` (the framework's
  names being visible), `t⇒s`/`s⇒t` are `t_to_s`/`s_to_t`.

## Typechecking

```sh
./check.sh QCert/Alt16RevCir/MainTheorem.lean
```

`MainTheorem.lean` reaches all 54 modules of the folder.  With its imports
outside the folder built and its own build artifacts removed, the folder
builds in 288 s (`LEAN_NUM_THREADS=2 lake build` of the 54 modules, wall
time, 10 November 2026 on an Intel Core i5-13400TEF under WSL; Agda checks
the 38 modules of `Alt16-RevCir` in 28 s there, the sum of its per-module
times; `pldi/compare/th4.json`, the forms `Agda A16`, `Lean A16`).

Most of that is not checking.  A module with the folder's imports and no
content takes 4.0 to 4.5 s (Lean 4.30, Mathlib cached): the time of loading
Mathlib, which every module pays, and the fourteen generated parts form a
chain of imports, as in the Agda, so they are built one after the other.
The per-module times of that build sum to 354 s, about 220 s of it loading.
The slowest modules are `Lib/Symmetric` (13 s), the generated parts and
`Four/Relations` (9 to 12 s each), `Semantics` (10 s), `Width3/Derivations`
(9 s), `Bridge` (8 s) and `Lemmas` (7 s), the loading included.
