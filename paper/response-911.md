# Author response — POPL 2027 paper #911

*Normal Forms and Complete Relations for Circuits in Agda*

We thank the three reviewers for their detailed and generous reviews.
Nearly every suggestion has been adopted in the revised draft, and the
paper is significantly better for it. Reviews of this depth are rare in
our experience, and three at once rarer still. Thank you for reading the
paper closely, for liking it, and for telling us where it fell short.

## What changed, in one paragraph

Section 1.2 ("A first taste") is gone, as Reviewers A and D asked; in
its place the introduction now explains the approach in plain language
before any formal vocabulary, announces up front the design decision the
paper returns to most (setoids rather than quotients, with a forward
reference to §7.2), and adds a
paragraph making the case that this is a programming-languages problem
and a design story (Reviewer B). The introduction's related-work
subsection is merged into §6, retitled "Related work and comparison",
so related work is discussed in one place (Reviewer A); the "related
tools" paragraph lives there too. Section 2 is reworked
within the same page budget: the generators are defined as data with an
explanation of `gate₂`, the empty circuit and its width index are
explained, the notion of *circuit theory* and the origin of the
structural rules (the fixed-width shadow of the monoidal structure) are
spelled out, cosets are explained as "where the bottom wire goes" with
pictures of the staircase representatives, the coset table is explained
case by case (each case annotated in the code, the pushed swap pictured
next to it) and its soundness law typeset as Agda, the tower paragraph
and the three theorem statements are de-formalised, `inv-nf` and
`_IsPresentationOf_` are defined where they are used, and the mixfix
underscore convention is explained once (Reviewers A, B, D). Section 4
opens with the design rationale
(Reviewer B), drops the "Module X" phrasing and the repeated `Gen`
listing, explains the left-biased indices in the text
(Reviewer D), numbers the five coset-table hypotheses in the listing
(Reviewer A), explains the word setoid and the conjugation helpers,
discusses `Bijection` versus `Inverse` (Reviewer B), fixes the spacing in
the presentation-theorem display, and condenses §4.7. Section 5 opens by
saying what each example was chosen to exercise, gives the shape of every
normal form, explains why Clifford+T is the flagship example, names the
three construction theorems whose composition is the Pauli presentation
(Reviewers A, B, D), and defines "qupit" at first use. Section 7 gains measured typechecking
costs, a subsection on why Agda and not a tactic language, an expanded
limitations paragraph with concrete examples of gate sets outside the
method, and an explanation of what the seven thousand "core" lines are
(Reviewers A, D). Code is typeset by Agda's LaTeX backend with its
natural colours, the standard library is cited properly, Coq is now
Rocq, and the personification of "the library" is gone (Reviewer B).
Every typo listed by the reviewers is fixed.

## Reviewer A

**Sections 1 and 2.** Done as you suggested: §1.2 deleted, §2 expanded
(see above), and the introduction rewritten to be approachable without
prior exposure to the field.

**l.203, 207 (`Gen`, `gate₂`).** `Gen` is now defined as data in §2.1,
with its three constructors explained; `gate₂ σ-gate` is introduced
there.

**l.224 (lowest wire count).** You are right; the sentence now says that
each axiom is stated once with its gates at the bottom of the wires and
the width left open (the implicit `n`), and that `cong↑` moves it to any
height.

**l.271 (`|C n| = n + 1`).** Explained in prose: `C n` has the `n+1`
elements ε, σ•ε, …, up to a staircase of `n` swaps, matching the index of
`Sₙ` in `Sₙ₊₁`; the six representatives on one, two and three wires are
drawn.

**l.280 (`ract`).** Yes: `ract` pushes one generator past a coset
representative, and the residual is a *circuit* rather than a generator
because pushing a swap into a staircase can leave nothing, one swap on
the wires above, or a longer staircase. §2.3 now explains the four cases,
annotated in the code with the pushed swap pictured beside it, and the
extension to whole circuits by the stateful traversal.

**l.291 (typeset like the Agda).** The soundness law is now typeset as
the Agda declaration `ract-sound`.

**l.295–296 ("Symmetric", "one Extension record per level").** The
capitalised "Symmetric" was the module name; the text now says "the
symmetric-group development (module `Examples.Groups.Symmetric`)". The
tower paragraph is rewritten in words: per level, the coset type, the
table, the section and the five hypotheses, packaged as one record and
folded upward.

**l.302–305, 336, 344–355, 362–363.** The `nfp'-t` listing is gone;
only the definition of the carrier `NF` remains, annotated with what it
unfolds to (`⊤ × C 1 × ⋯ × C k`) and with a worked example, the
"staircase of staircases" section of a four-wire normal form, drawn
beside it; `inv-nf` is defined as the section that rebuilds a circuit from
its digits; the three `MainTheorems` statements are given in words with
only their names quoted; and the one Agda statement we keep,
`symmetric-presentation`, is preceded by an explanation of the
presentation record and followed by a note on the mixfix name
`_IsPresentationOf_`.

**Sec. 3 (l.402, 407).** "A relation `R` on the free monoid `X*`", and
the induced homomorphism is now derived explicitly: the interpretation of
generators extends by freeness to `X* → G`, and soundness makes it
descend to the quotient.

**Sec. 4 (l.467, 521, 630, 636).** The four helper symbols are gone; the
text says what the conjugation helpers are for. The word setoid is named
and explained in §4.2 where `≈` is packaged as a setoid. The five
hypotheses carry `-- (1)` … `-- (5)` comments. "NormalForma" was a typo.

**Sec. 5.** The section now opens with what each example exercises, and
each subsection says what its normal form is; "flagship" is justified
(smallest universal gate set, the Matsumoto–Amano form as the template of
all later normal forms).

**Sec. 7 (size).** We share the reaction, and §7.1 now says what the
seven thousand lines under `Presentation` are: about a thousand are the
core proper (words modulo `≈`, the presentation records, grouplikeness,
morphism builders); 4,300 are the five product constructions with their
two-sided theorems, the amalgamation alone being 1,800; 600 are the
solvers; the rest are two group developments that predate the `Examples`
tree. We do expect it to shrink: the branch of the library developed since
submission has already retired one of two semidirect-product modules and
moved those group developments out, and the amalgamation module is the
next candidate for the transport-based simplification the construction
theorems make possible.

## Reviewer B

**A design story, and a POPL paper.** The introduction now says so up
front: a new paragraph explains the approach without formal vocabulary,
another states the design decision the paper keeps returning to
(setoids rather than quotients), and a third argues why completeness of
circuit calculi is a
programming-languages problem and what the contribution is (a design,
validated on large examples). The rationale that you found at l.488–492
now opens §4 as five numbered design principles.

**Agda colours.** The code is now typeset by Agda's own LaTeX backend:
the three sections that quote code are literate Agda files whose blocks
are scope-checked against the library, so every identifier carries its
natural colour (functions, datatypes, constructors, bound variables,
modules, keywords, comments), with the font distinctions kept.

**Citation for agda-stdlib.** Added (Daggitt et al., JOSS 2025).

**l.178, 192.** Fixed; the "everything in this section is verified"
sentence is gone, and the introduction now states that non-formalised
claims are marked explicitly where they occur and collected in §7.6.

**MLTT rather than cubical/HoTT.** Now foreshadowed in the introduction
(setoids rather than quotients, because our central devices are maps
*into* the syntax), with pointers to §4.2, §6.4 and §7.2.

**l.344–355, 569–575, 675, 677–680.** De-formalised (see Reviewer A);
`Gen` is no longer repeated in §4.4, which instead spells out the
rationale for left-biased indices (the passage you liked at l.577–585
is kept, and stated more explicitly);
"from MainTheorems.agda's aliases" is
gone; the presentation-theorem display is respaced so that `⋄`, `⊕^` and
`⋆` read as operations.

**Personification.** Fixed throughout ("we were careful about", "we
therefore keep both", "we turned it into a reusable module", and so on).

**Section 4 repetition, "Module".** Done: the module name is given in
parentheses once per subsection.

**`--safe`, `--cubical-compatible`.** Now mentioned once, in the
introduction, where the paragraph also says why the constructivity
matters: normal forms and sections are computable, so each completeness
theorem is also a verified decision procedure. Thank you for the pointer
about `--without-K` returning in version 3.0; we will use whichever name
the released library uses at camera-ready time.

**Section 5 inventory.** The section now opens with what each family was
chosen to exercise; l.824 now says which three construction theorems the
Pauli presentation composes and what normal form results, which is what
there is to show --- the proof is those three theorems applied in turn.

**l.820 "qupit".** Defined at first use (a qudit of odd prime dimension).

**Table 3: Coq → Rocq.** Done, throughout.

**Your question: `Bijection`, not `Inverse`?** The two are interderivable
in the standard library, so the choice is one of style, but it is
deliberate. What our downstream code consumes is a section `inv-nf`
together with the single law `inv-nf ∘ nf ≈ id`, that is, a
`RightInverse` (our `NormalForm`). The other law — exactness,
`nf ∘ inv-nf ≡ id` — is kept as a separate hypothesis, because carriers
are allowed to contain junk that no word reaches (a coset type before
pruning, a product carrier), and because exactness is exactly what the
converse lemma `by-completeness` trades against uniqueness. An `Inverse`
would bake an explicit inverse map and both laws into every witness.
`Bijection` is used where surjectivity onto the carrier is established as
a *property* and the section is then derived from it, as the first
projection of the surjectivity witness; this is how the extension
construction consumes its factor normal forms. The stylistic difference
you allude to is real: with `Bijection` the inverse map is a projection
out of a proof and computes only once that proof unfolds, whereas with
`RightInverse` the section is user-written first-order code that computes
by pattern matching and can be reasoned about definitionally. We prefer
the latter wherever a section is written by hand, which is why
`RightInverse` is the workhorse and `Bijection` the exception. §4.3 now
says this.

## Reviewer D

**Introduction and §1.2.** Removed and rewritten as described above; the
approach is now explained before the contributions, without the
terminology that used to appear before its definition.

**Examples and normal-form shapes.** Every subsection of §5 now states
the shape of its normal form (residue; factorial tuple; residues plus
factorial tuple for wreath products; `n` pairs of exponents for Pauli
groups; the alternating carriers for the amalgamations), and the section
opens with what each example exercises.

**Unnecessary information.** §4.7 is condensed to a paragraph without the
record listing, and Table 4 is replaced by prose that gives rounded sizes
and explains what the numbers consist of. We kept Table 3 in tabular
form, since the other reviewers engaged with it.

**Tactic language.** A new §7.4 ("Why Agda, and why not a tactic
language") answers this. In short: everything the library asks a user to
prove is a finite case split whose cases are either closed by evaluation
or filled by a setoid-reasoning derivation, neither of which benefits
much from proof search; the two solvers are verified functions, not tactics, and the
development uses no metaprogramming. Two places would profit from
automation (generating the hypothesis records of a coset table from the
table alone, and finding the tables), and we say why we keep the second
outside the checker. The design would transfer to Rocq or Lean provided
the setoid discipline is kept.

**Typechecking time.** Added to §7.1 with measurements: the whole
development (61 modules, standard-library interfaces cached) checks from
scratch in 1 min 42 s of wall-clock time with Agda 2.8.0, peaking at
3.5 GB;
a third of that is the amalgamated-product construction, checked once;
the three amalgamation case studies take 19 s together (the nine-coset
qutrit level with its seventy-two `refl` obligations is within the 8 s of
its module). Discharging by evaluation the obligations that reduce to
computation has not made checking slow; memory and the edit–check loop
of the largest modules are the costs to watch.

**HTML rendering with links.** Agreed, and done: the artifact ships an
`agda --html` rendering in which every identifier links to its
definition, and the camera-ready will link module names into it.

**Compiler integration.** A new "Towards compilers" item in §8: the
normal-form functions are executable, so a compiled normaliser is a
decision procedure an optimiser can call as an oracle, and connecting the
presented gate groups to the matrix semantics of sqir/voqc or VyZX would
turn our completeness theorems into end-to-end guarantees that a rewrite
engine equipped with one of our rule sets misses no valid rewrite.

**§7.5 limitations (now §7.6).** Expanded with examples: gate sets with continuous
parameters (rotation gates, whose complete theories have real-valued
normal forms and no finite coset structure); subgroup steps of infinite
index such as the lamplighter groups, where the hypotheses are statable
but need induction rather than finitely many evaluations; and finite but
large tables from computer search, which stay within the method but will
stress the evaluator.

**Wording.** "Against the standard library", "layered Agda library" and
"discharges the case analyses" are gone; "circuit theory" and the
structural rules are now defined in §2.2 as the fixed-width shadow of the
monoidal (PROP) structure, which is where the notion comes from.

**§2.1, §2.3, l.298.** The empty circuit is the identity circuit and
carries its width as an index; cosets are explained as the wire brought
to the bottom, with the coset table pushing generators past that
staircase; the record snippets at l.298 are replaced by the normal-form
example.

**Typos (l.357, 364, 408, 579, 636, 820).** All fixed; at l.579 the
text no longer appeals to "the module's comment" but states the point
itself, together with the type it concerns (`Gen n → Gen (k + n)`, with
`k` on the left); the comment in the source says the same; "qupit" is
defined rather than removed.
