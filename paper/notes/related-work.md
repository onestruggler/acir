# Related-work notes (P3) — verified 2026-07-09/10
Every claim here traces to a fetched abstract/page. Use with refs.bib keys.

## A. The Bian–Selinger Agda verification line (closest prior work)
Outline's instruction: "previous work of Selinger and Bian only works on the
syntactic side (they verify two sets of relations are equivalent, never
mentions their semantics)". Verified facts to support the delta:
- bian2023cliffordt2 (QPL'22): presentation of 2-qubit Clifford+T via
  Reidemeister–Schreier applied to Greylyn's U₄(ℤ[1/√2,i]) presentation
  (greylyn2014); "formally verified in the proof assistant Agda".
- bian2023cliffordcs3 (QPL'23): 3-qubit Clifford+CS; R–S applied recursively;
  "thousands of relations" simplified to 17; "both steps verified in Agda";
  the group is the amalgamated product of THREE finite subgroups, paralleling
  the 1-qubit Clifford+T structure.
- bian2021un (QPL'21): presentation of U_n(ℤ[1/2,i]) (paper proof; the n=3
  instance is our U33Di case study). bian2023thesis (Dalhousie 2023) collects
  these + the Agda formalization methodology; ch.2 covers monoid
  presentations, amalgamation, R–S, Agda. (Extension.agda's "Proposition
  2.55" = thesis numbering — cite thesis for the extension-presentation
  recipe.)
- OUR DELTA (verified against the repo): those verifications relate SYNTAX to
  SYNTAX (two presentations of the same group, iso of presented monoids); the
  present library adds the SEMANTIC side: `_IsPresentationOf_` targets an
  independently constructed stdlib group (permutations of Fin n, direct/
  semidirect/amalgamated products of groups, ...), with soundness +
  completeness (adequacy) via UniqueNormalForm, and reusable construction
  theorems (DP/NDP/SDP2/Amalgamation/Extension at group level). ALSO general
  reusable engine (CosetNF/Reidemeister-Schreier modules) rather than
  per-paper proofs; ALSO the generic Circuit layer with Lift-Relation.
- Related tools (outline asks to mention): lafontlp-tool (normalizer to
  Lafont normal form for linear permutation circuits, based on Lemmas 10–11
  of lafont2003boolean); qupit-tool (Selinger-style staircase normal forms
  for Sp(2n,ℤ_p), citing selinger2015clifford Prop 5.5 and li2025qutrit) —
  the computational companions of the (WIP) Symplectic tree.

## B. Completeness of circuit equational theories (paper mathematics)
- selinger2015clifford: n-qubit Clifford presentation via normal forms +
  rewrite system (LMCS'15). The direct qubit ancestor of our approach.
- li2025qutrit (QPL'25, EPTCS 426:23–78): THE companion paper ("published
  this year" in outline's sense; repo README title generalizes to all odd
  primes — describe the Symplectic tree as formalization-in-progress of this
  line). First completeness result for a circuit fragment in odd prime dims.
- clement2023complete (LICS'23): first complete equational theory for full
  quantum circuits; clement2024minimal (LICS'24): minimal version;
  clement2026realcliffordch (arXiv Feb 2026): Real-Clifford+CH — 13pp main +
  264pp appendix of equational derivations — THE motivating example for
  "completeness proofs are gigantic computations that should be machine-
  checked" (outline explicitly cites it as ~300pp).
- ZX side (contrast: graphical calculi, not circuit groups):
  backens2014zx (stabilizer), jeandel2018zx (Clifford+T, LICS'18),
  booth2022qupitzx (MFCS'22: stabilizer completeness in odd prime dims!),
  poor2023travaganza (QPL'23: simplified qupit axioms, normal forms).
  None of these are mechanized in a proof assistant (VyZX aims at the
  rules' soundness/infrastructure, see D).
- Normal-form ancestors: matsumoto2008representation (MA normal form for
  1-qubit Clifford+T), giles2013remarks (algebraic exposition),
  prakash2018qutrit (single-qutrit Clifford+T NF), jain2020qudit
  (single-qudit p≥5). Our CliffordT1 example = the MA-style structure
  captured as amalgamated product with verified NF.

## C. Presentations/rewriting: classical theory we mechanize pieces of
- sims1994computation (coset enumeration, Todd–Coxeter, R–S; our CosetNF is
  a verified, structurally-recursive cousin of these techniques);
  holt2005handbook (Schreier–Sims etc.); magnus2004combinatorial (R–S
  method, presentation of subgroups ch. 2.3). The mixed-radix/stabilizer-
  chain normal form of our Preliminaries: standard in CGT (base and strong
  generating sets) — cite sims1994computation + holt2005handbook.
- squier1987word, squier1994finiteness: limits of finite convergent
  rewriting for monoid presentations — relevant to "why NF-functions instead
  of confluent rewriting": our NF maps are arbitrary verified functions (no
  termination/confluence needed), sidestepping Squier obstructions.
- guiraud2018polygraphs, ara2025polygraphs: coherence-by-rewriting programme;
  lafont2003boolean: presentations of Boolean-circuit monoids by generators
  and relations — the non-quantum ancestor of circuit relation sets (and of
  our Lift-Relation structural rules: Lafont's S/T-gate stair normal forms).

## D. Quantum circuits in proof assistants (none do presentations/completeness
     of gate groups — the niche is open; verify claims per item when writing)
- paykin2017qwire (POPL'17): circuit language embedded in Coq; semantics via
  density matrices; no equational completeness.
- hietala2021voqc (POPL'21 dist. paper) + hietala2021proving (ITP'21): SQIR;
  verified OPTIMIZER: rewrites proved SOUND against denotational semantics —
  exactly "soundness-only"; completeness of a rule set is not addressed.
- lehmann2025vyzx (TOPLAS; arXiv:2311.11571): ZX diagrams inductively in Coq,
  soundness of ZX rewrite rules; completeness of ZX not mechanized.
- zhou2023coqq (POPL'23): Dirac-style program verification over MathComp.
- chareton2021qbricks (ESOP'21): Why3-automated circuit verification (path
  sums), not a proof-assistant presentation theory.
- liu2019quantum/QHLProver (CAV'19, AFP), bordg2020dirac (AFP): Isabelle
  program logics / algorithm verification.
- Positioning sentence: all verify PROGRAMS or rule SOUNDNESS; ours verifies
  COMPLETENESS of finite relation sets for gate-group presentations, i.e.
  the meta-theory of the calculi themselves.

## E. Group theory in proof assistants (again: no circuit presentations)
- Lean/mathlib: mathlib2020; FreeGroup, PresentedGroup (quotient of free
  group by normal closure — NOTE the contrast: our presented monoid is an
  inductive congruence closure on words, no free-group quotient needed, and
  it computes); Coxeter groups defined via PresentedGroup; Nielsen–Schreier
  formalized via groupoids (mathlib-doc-presented). No coset-enumeration /
  Todd–Coxeter-style completeness tooling for concrete presentations AFAIK
  (state carefully as "to our knowledge").
- Coq/MathComp: gonthier2013oddorder — deep finite group theory, but finite
  groups as concrete subgroups of permutation groups, not presentations.
- Isabelle: breitner2010freegroups (AFP free groups + Ping-Pong lemma?),
  kharim2023freegroups (CICM'23: Nielsen–Schreier combinatorially + first
  formalized conjugacy-problem decision procedure for free groups).
- Rewriting formalized: sternagel2013kb (RTA'13 KB completion),
  hirokawa2019abstract (abstract completion, LMCS), IsaFoR/CeTA programme —
  string/term rewriting meta-theory; our by-assoc/by-equal-nf are
  reflection-style COMPUTATIONAL decision procedures for specific
  presentations rather than generic completion.
- Univalent: vezzosi2019cubical, cubicallibrary (FreeGroup as HIT),
  agdaunimath (finite group theory, sign homomorphism), mangel2023sign.
  Contrast: our library is --safe, --cubical-compatible, SETOID-based
  (no univalence needed), aimed at stdlib inclusion; HIT quotients give
  quotient types but lose the definitional computation of our word-level nf
  functions (discuss fairly; barthe2003setoids for the setoid tradition).
- Agda: agdastdlib (Function.Bundles Injection/RightInverse/Bijection —
  our NF zoo IS these bundles on the word setoid; Algebra.Construct.*,
  Data.Fin.Permutation); bove2009agda, norell2007thesis.

## F. Framing lines to reuse in §Related (draft snippets)
- "To our knowledge, the only prior mechanizations of completeness for
  quantum-gate relation sets are the Agda developments accompanying
  [bian2023cliffordt2, bian2023cliffordcs3]; they relate two syntactic
  presentations by an isomorphism of finitely presented monoids. The present
  library subsumes that methodology (our amalgamation case studies re-prove
  the corresponding one-qubit/qutrit structures) and goes further: the
  presented monoid is related to an independently defined semantic group."
- "Verified quantum compilers [voqc etc.] prove soundness of rewrites;
  completeness of an equational theory is a statement about the rule set
  itself and requires normal forms — the subject of this paper."
- Careful-claims list (AFAIK-qualify): "no prior Agda formalization of
  Reidemeister–Schreier / coset enumeration"; "no prior proof-assistant
  presentation of wreath products / Pauli groups by generators and
  relations"; "first machine-checked completeness proof for the qutrit
  Clifford+T single-qutrit relation set". Each gets "to our knowledge".

## F2. Rig-categorical completeness school (added 2026-07-10 on user request; all verified by fetch)
- choudhury2022symmetries (PACMPL 6(POPL):6, 2022, doi 10.1145/3498667): Π as
  free symmetric rig groupoid; MECHANIZED in HoTT-Agda ~7,500 lines (NbE,
  verification, synthesis of reversible boolean circuits; full syntax + most
  proofs); text mentions difficulty of the word problem in Sn. Closest
  mechanization to ours → gets table row (Agda (HoTT) | ✓ | categorical | ✓ |
  classical) + niche-claim scoping in intro and related summary.
- carette2024squareroots (PACMPL 8(POPL), 2024, arXiv:2310.14056): rig
  groupoids + square roots ⇒ universal quantum language; §6 SOUNDNESS AND
  COMPLETENESS for: arbitrary Clifford (Thm 16), ≤2-qubit Clifford+T (Thm
  19), Gaussian Clifford+T (Thm 25); §6.1 warm-up = ≤2-qubit Clifford (via
  Selinger Fig. 9 / Bian–Selinger axioms). PARTIALLY MECHANIZED (their
  §7.2, verified from the PDF 2026-07-10): Agda atop agda-categories;
  formalised ALL of §5, ALL of §6.1, Lem 14 of §6.2, Lem 18 + (A14)–(A17)
  of §6.3, and the Sleator–Weinfurter CCX decomposition; no errors found in
  paper proofs; found a missing RigCategory coherence in agda-categories;
  weak-category assoc/unit bookkeeping reported as a major cost (contrast
  with our by-assoc). Table row added; intro + niche claims re-scoped.
- fang2026hadamard (PACMPL 10(POPL):5, 2026, arXiv:2506.06835): Hadamard-Π;
  completeness via NEW finite presentation + synthesis for orthogonal groups
  over ℤ[1/√2] (ties to li2021on!). Pen-and-paper. Cited also in conclusion
  as inviting target.
- heunen2026onerig (LICS'26 to appear, arXiv:2510.05032): semisimple rig
  categories; universal construction ⇒ sound+complete axiomatizations of
  controlled circuits (quantum + Toffoli); Gray-code induction. Pen-and-paper.

## F3. Blake FSCD'26 (added 2026-07-10 on user request; verified by fetch)
- blake2026simpler (FSCD 2026 to appear, LIPIcs, arXiv:2602.09874, Colin
  Blake): PROP-theoretic uniform treatment of SIX near-Clifford fragments
  (qubit Clifford, real Clifford, Clifford+T ≤2 qubits, Clifford+CS ≤3
  qubits, CNOT-dihedral, qutrit Clifford); transfers completeness results,
  eliminates redundant rules; MINIMAL rule sets for qubit Clifford, real
  Clifford, CNOT-dihedral. Pen-and-paper. Compared in related.tex (each
  simplification = finite derivability obligations = by-equal-nf target) and
  cited in intro's "long hand-checked computations" support sentence
  alongside selinger2015clifford, li2025qutrit, carette2024squareroots,
  fang2026hadamard.

## G. Still-unverified details (resolve in P5 if cited)
- %% VERIFY-DETAIL markers in refs.bib (page ranges, LNCS/LIPIcs volumes).
- Whether QutritCliffordT1's relation set matches a published source
  (li2025qutrit? prakash2018qutrit?) — check the repo's comments before
  claiming; else present as "derived in this work, verified in Agda".
- mathlib presence of Todd–Coxeter (searched: not found — keep AFAIK).
