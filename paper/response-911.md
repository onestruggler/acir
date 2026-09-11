# Author response — POPL 2027 paper #911

*Normal Forms and Complete Relations for Circuits in Agda*

We thank the reviewers for three careful and generous reviews. Nearly
every suggestion is adopted in the revised draft, and the paper is
better for it.

## Summary of changes

- **Introduction.** §1.2 ("A first taste") and the related-work
  subsection are gone (Reviewers A, D). The approach is explained in
  plain language before the contributions, the design decision
  (setoids rather than quotients) is announced up front with its
  reason and a pointer to §7.2, and a paragraph argues why this is a
  programming-languages problem and a design story (Reviewer B). The
  contribution list is reorganized; the intro now says that every
  claim is verified and that the unformalized ones are collected in
  §7.3.
- **Section 2** is revised and expanded in detail, since Reviewer A
  found it rushed towards the end; this also partly answers Reviewer
  D's request for expanded examples. Code and circuit diagrams sit
  side by side, the coset table is explained case by case with its
  four rewrites drawn (Figure 1), the soundness law is typeset as
  Agda, the tower and the three theorems are given in words, and the
  proof of completeness is unfolded on the example.
- **Section 4** opens with five numbered design principles (Reviewer
  B), drops the "Module X" phrasing and the repeated `Gen` listing,
  explains the left-biased indices in prose (Reviewer D), numbers the
  five coset-table hypotheses (Reviewer A), respaces the
  presentation-theorem display, and condenses §4.7 (Reviewer D).
- **Section 5** opens with what each example was chosen to exercise
  and states the shape of every normal form; the three amalgam normal
  forms are written as regular expressions and compared with the
  Matsumoto–Amano and Glaudell–Ross–Taylor forms (Reviewers A, B, D).
- **Section 6** ("Related Work and Comparison") absorbs the intro's
  related work and the related-tools paragraph, organized along the
  axes of its comparison table (now Table 3); every citation was
  re-checked against its source.
- **Section 7** has measured typechecking costs, a breakdown of the
  seven thousand "core" lines, and a limitations subsection stating
  exactly what is not formalized (Reviewers A, D); the size table is
  replaced by prose. **Section 8** is shortened to two directions.
- Code is typeset by Agda's LaTeX backend with its natural colours,
  the standard library is cited properly, Coq is now Rocq, "the
  library" is no longer personified, and every listed typo is fixed
  (Reviewers B, D). The text is about 23 pages.

## Reviewer A

**Sections 1 and 2, pace.** Agreed. §1.2 is deleted, the introduction
is rewritten to be approachable without prior exposure, and §2 is
expanded so that a reader reaches §4 having seen the whole pipeline on
the symmetric groups.

**l.203, 207.** `Gen` is defined as data in §2.1 with its constructors
explained; `gate₂ σ-gate` is introduced there.

**l.224.** You are right. The sentence now says each axiom is stated
once with its gates at the bottom and the width left open (the implicit
`n`), and that `cong↑` moves it to any height.

**l.271.** Explained in prose: `C n` has `n+1` elements, ε up to a
staircase of `n` swaps, matching the index of `Sₙ` in `Sₙ₊₁`; the
representatives on one, two, and three wires are drawn.

**l.280.** Yes: `ract` pushes one generator past a coset
representative. The residual is a circuit rather than a generator
because pushing a swap into a staircase can leave nothing or one swap
here, and a longer circuit in richer gate sets. §2.3 explains the four
cases, annotated in the code and drawn in Figure 1, and the extension
to whole circuits by the stateful traversal.

**l.291.** The soundness law is typeset as the Agda declaration
`ract-sound`.

**l.295–296.** "Symmetric" was a module name; §2 no longer names
modules. The tower paragraph is in words: the traversal gives one level
of normalization, and iterating it is the coset tower, one digit per
level.

**l.302–305, 336, 344–355, 362–363.** The `nfp'-t` listing is gone;
only the carrier `NF` remains, annotated with what it unfolds to and
with a four-wire "staircase of staircases" drawn beside it. `inv-nf`
is defined as the section rebuilding a circuit from its digits. The
three `MainTheorems` statements are given in words. The one Agda
statement kept, `symmetric-presentation`, is preceded by an explanation
of the presentation record and followed by a note on the mixfix name
`_IsPresentationOf_`.

**Sec. 3 (l.402, 407).** "A relation `R` on the free monoid `X*`"; the
induced homomorphism is derived explicitly (freeness gives `X* → G`,
soundness descends it to the quotient).

**Sec. 4 (l.467, 521, 630, 636).** The helper symbols are gone and the
text says what the conjugation helpers are for; the word setoid is
named where `≈` is packaged as a setoid (§4.2); the five hypotheses
carry `-- 1` … `-- 5` comments and are explained one by one;
"NormalForma" was a typo. We agree §4 is where the artifact carries
the detail; it now leads with rationale and quotes less code.

**Sec. 5.** The section opens with what each example exercises;
"flagship" is justified (smallest universal gate set in common use, the
first canonical form, whose syllable pattern the later qutrit and
qudit forms follow).

**Sec. 7 (size).** We share the reaction. §7.1 now says what the seven
thousand lines under `Presentation` are: about a thousand are the core
proper, 4,300 are the five product constructions with their
normal-form and presentation theorems (the amalgamation alone 1,800),
and 600 are the solvers. The constructions are proved once and reused
by every case study, so we do not expect them to shrink much; the
examples are where reuse pays.

## Reviewer B

**A design story.** The introduction now says so up front: a paragraph
explains the approach without formal vocabulary, another states the
design decision, and a third argues why completeness of circuit
calculi is a programming-languages question and that the contribution
is a design validated on large examples. The rationale you found at
l.488–492 now opens §4 as five numbered principles; the former
"lessons learned" subsection is folded into them, next to the code it
explains.

**Agda colours.** The code is typeset by Agda's LaTeX backend: the
three code-quoting sections are literate Agda files scope-checked
against the library, so every identifier carries its natural colour,
with the font distinctions kept.

**Citation for agda-stdlib.** Added (Daggitt et al., JOSS 2025).

**l.178, 192.** Both sentences are gone; the introduction now states
that unformalized claims are marked where they occur and collected in
§7.3.

**MLTT rather than cubical/HoTT.** Foreshadowed in the introduction:
the library computes with syntax (coset tables and normal-form maps
pattern-match on concrete words, and its central devices are maps
*into* the syntax), and, secondarily, the congruence is an inductive
family whose derivations are data to induct on; pointers to §4.2,
§6.5, and §7.2.

**l.344–355, 569–575, 675, 677–680.** De-formalized (see Reviewer A);
`Gen` is no longer repeated in §4.4, which instead states the rationale
for left-biased indices (the passage you liked at l.577–585 is kept and
made explicit); "from MainTheorems.agda's aliases" is gone; the
presentation-theorem display is respaced so that `⋄`, `⊕^`, and `⋆`
read as operations.

**Personification, "Module", repetition.** Fixed throughout; the home
module is named once per subsection, in parentheses.

**`--safe`, `--cubical-compatible`.** Mentioned once, in the
introduction, together with why constructivity matters: normal forms
and sections are computable, so each completeness theorem is also a
verified decision procedure. Thank you for the pointer about
`--without-K` returning in version 3.0; we will use whichever name the
released library uses at camera-ready time.

**Section 5 inventory, l.820, l.824.** The section opens with what
each family was chosen to exercise; "qupit" is defined at first use;
l.824 now names the three construction theorems whose composition is
the Pauli presentation, which is all there is to show.

**Table 3: Coq → Rocq.** Done throughout.

**Your question: `Bijection`, not `Inverse`?** The two are
interderivable in the standard library, so the choice is stylistic, but
deliberate, and §4.3 now explains it. What downstream code consumes is
a section `inv-nf` with the single law `inv-nf ∘ nf ≈ id`, i.e. a
`RightInverse` (our `NormalForm`). The other law, exactness
`nf ∘ inv-nf ≈ id`, is kept as a separate hypothesis: carriers may
contain junk no word reaches (a coset type before pruning, a product
carrier before a quotient), and exactness is what `by-completeness`
trades against uniqueness. An `Inverse` would force an explicit inverse
map and both laws on every client. `Bijection` is used where
surjectivity onto the carrier is proved as a property and the section
is read off from the surjectivity witness, which is how the extension
construction consumes its factor normal forms. The constructive point
behind the zoo is also stated: an `Injection` gives no algorithm
producing a word from a normal form, whereas the section of a
`RightInverse` is exactly that algorithm, so the witnesses differ as
data even though they coincide classically.

## Reviewer D

**Introduction and §1.2.** Removed and rewritten as above; the approach
is explained before the contributions, without terminology that used
to appear before its definition.

**Examples and normal-form shapes.** Every subsection of §5 states the
shape of its normal form: a residue; the factorial tuple; residues plus
factorial tuple for wreath products; `n` pairs of exponents for Pauli
groups; and, for the three amalgamations, the alternating form written
as a regular expression. For qubit and qutrit Clifford+T the expression
is compared letter by letter with the Matsumoto–Amano and
Glaudell–Ross–Taylor forms; for U₃(ℤ[½,i]) it is a new canonical form.
The expanded §2 walks through the symmetric-group example in full.

**Unnecessary information.** §4.7 is condensed to a paragraph without
the record listing, and the size table is replaced by prose giving
rounded sizes and what they consist of. We kept the comparison table
(now Table 3), since the other reviewers engaged with it.

**Tactic language.** We would put it differently: Agda is also a tactic
language, since its metaprogramming (reflection) is written in Agda,
and in that sense the development does use tactics. The associativity
solvers `by-assoc` and `by-passoc` of §4.8, in the `Presentation.Tactic`
namespace, are tactics we wrote: each normalizes both sides of a goal
to a canonical form and closes it by `refl`. The modular-arithmetic
support library instantiates the standard library's ring solver
(`Tactic.RingSolver`) to ℤ_p, the counterpart of the `ring` tactic of
Rocq and Lean. What we do not use is proof search, because the
obligations are finite case splits closed by evaluation or by short
setoid-reasoning derivations. Two places would profit from more
automation: generating a coset table's hypothesis records from the
table alone, for which reflection would suffice, and finding the
tables, which we deliberately keep outside the checker (§6.7).

**Typechecking time.** Added to §7.1: the whole development (61
modules, standard-library interfaces cached) checks from scratch in
1 min 42 s with Agda 2.8.0, peaking at 3.5 GB; a third of that is the
amalgamated-product construction, checked once; the three amalgamation
case studies take 19 s together, and every other module is under 4 s.

**HTML rendering with links.** Agreed. The artifact will ship an
`agda --html` rendering in which every identifier links to its
definition, and the camera-ready will link module names into it.

**Compiler integration.** Addressed in §1.1, which says why the
constructivity matters (every completeness theorem doubles as a
verified decision procedure, every normal-form witness is an
extractable normalizer), and in §6.2, which names the concrete target:
connecting the presented gate groups to the matrix semantics of
sqir or VyZX would give end-to-end completeness against matrices.

**§7.5 limitations (now §7.3).** Rewritten to state exactly what is not
formalized: the amalgamation case studies are syntactic, ending in
isomorphisms between the gate-set presentation and an amalgamated
product of presentations, and the identification of those presented
monoids with the concrete matrix monoids is taken from the literature;
the subsection also says why (the rings and matrices are absent from
the standard library, and each paper's completeness proof would have to
be formalized first). The second point is expanded with the examples
you asked for: gate sets with continuous parameters, such as the phase
and rotation gates of Clément et al.'s complete theories, whose normal
forms carry real angles and have no finite coset structure; and
subgroup steps of infinite index, such as the lamplighter groups
ℤ_N ≀ ℤ, where the hypotheses are statable but need induction rather
than finitely many evaluations. It also notes that amalgamation already
handles one shape of infinite index, which is why the Clifford+T
monoids are within reach.

**Wording.** "Against the standard library", "layered Agda library",
and "discharges the case analyses" are gone; "circuit theory" and the
structural rules are defined in §2.2 as the fixed-width shadow of the
monoidal (PROP) structure, which is where the notion comes from.

**§2.1, §2.3, l.298.** The empty circuit is the identity circuit and
carries its width as an index; cosets are explained as where the bottom
wire goes, with the coset table pushing generators past that staircase;
the record snippets at l.298 are replaced by the normal-form example.

**Typos (l.357, 364, 408, 579, 636, 820).** All fixed. At l.579 the
text states the point itself (the shift has type `Gen n → Gen (k + n)`,
with `k` on the left) instead of quoting the module's comment; "qupit"
is defined rather than removed.

## Other changes

Beyond the reviews: contribution (3) is split into the monoid-level
generalization and the presentation theorems for the product
constructions; the Pauli theorem is stated for all primes, since
nothing in its proof uses oddness; the amalgam carrier is stated as the
base normal form times the alternating coset part; and §6.3 now cites
the CNOT-dihedral presentations of Amy, Chen, and Ross and of Blake.
