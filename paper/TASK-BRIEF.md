# TASK BRIEF — POPL submission paper for this repository

This file is the standing contract for an autonomous, multi-session writing task.
Every scheduled run MUST read this file and `paper/PROGRESS.md` first, then continue
the next incomplete phase. All state lives on disk (this folder), never in
conversation memory — context may be summarized/reset between runs.

## Verbatim user instruction (2026-07-09 17:26)

> in 2 hours, you will begin to write a paper in ./paper folder for popl submission
> according to paper-outline.md; besides abiding the outline, you should also write
> extra stuff. the goal is: thoroughly explains this repo, emphasizes what we have
> formalized (uniqueNormalForm and presentation, maybe we should collect all these
> in one place for reader's convenience, you can modify the code according to the
> paper's need). compare this project thoroughly with other formalizations about
> group normal form, presentation, completeness, about circuit formalization and
> related stuff in Lean, Coq, Agda and other proof assistants (focus mainly on
> Agda). write the paper as detailed as possible. reference all related research as
> thoroughly as possible. if you almost hit a token usage limit, pause till it
> resets, and you should continue automatically after it resets. ignore
> lib-structure.md; it's obsolete.

Start time: **2026-07-09 19:27 local**. Before that: do nothing.

## Deliverable

A full-length, submission-grade POPL paper in `./paper/`:

- `paper/main.tex` — `\documentclass[acmsmall,review,anonymous]{acmart}` (POPL is
  PACMPL; acmsmall single column). `\citestyle{acmauthoryear}`.
- `paper/sections/*.tex` — one file per section, `\input` from main.
- `paper/refs.bib` — thorough bibliography (target 50+ genuinely relevant entries,
  each verified to exist via web search; no hallucinated citations — every entry
  must come from a search result with real authors/venue/year/arXiv id).
- `paper/notes/` — working notes (repo survey, related-work notes, stats).
- Figures via `tikz`/`quantikz` written inline (no external image files).
- Title from paper-outline.md: "Normal forms and complete relations for circuits
  in Agda" (may refine subtitle, keep the substance).

**Anonymity**: `review,anonymous` mode. Never name the repo owner as author. Prior
work by Bian and Selinger is cited in the third person like anyone else's work
(this is standard double-blind practice). Refer to the code as "our Agda library,
included as anonymous supplementary material". Keep the Acknowledgements section
from the outline (Claude assistance disclosure) inside `\begin{acks}...\end{acks}`,
which acmart suppresses in anonymous mode — so it can be written now, shown later.

**LaTeX toolchain**: none installed (checked 2026-07-09: no TeX in WSL or Windows).
In P0, try once, non-interactively: `wsl --exec bash -lc 'sudo -n apt-get install -y
texlive-latex-extra texlive-publishers texlive-science latexmk 2>&1 | tail -2'`
(acmart is in texlive-publishers). If sudo needs a password this fails fast —
then DO NOT retry; write compile-clean LaTeX without local compilation, and add a
`paper/README.md` telling the user how to build. If install succeeds, compile with
`latexmk -pdf main.tex` after each writing phase and fix errors.

## Hard rules

- **Ignore `lib-structure.md`** (obsolete, per user).
- Follow `paper-outline.md` (repo root) as the skeleton, but ADD substantial extra
  material (see "Paper structure" below) — the user explicitly wants more.
- The user allows **modifying library code for the paper's needs** (chiefly: a new
  module collecting the headline results). Any library edit ⇒ re-typecheck ALL of:
  ```
  wsl --exec /home/onest/.cabal/bin/agda MainTheorems.agda
  ```
  (that single root now reaches every development; the four former roots
  Symmetric/Theorems, CliffordT1, QutritCliffordT1 and U33Di are all
  below it, and Symmetric/Theorems no longer exists)
  (run from PowerShell/Bash tool with `wsl --exec`; Git-Bash mangles Linux paths in
  other invocation forms — this exact form works). Plus the new collection module.
- Do not weaken `--safe`; do not leave holes in checked-in code.
- Do NOT git-commit or push anything unless the user asks later.
- Never write secrets into files. Never ask the user questions — fully autonomous.

## Repo orientation (verified as of 2026-07-09; re-verify details when citing)

Layered Agda library (Agda 2.8, stdlib 2.3, `--safe`) for presenting groups/monoids
by generators and relations and proving *completeness* of relation sets via normal
forms. Layers (details in CLAUDE.md):

- L0 `Notations.agda` — numeral patterns ₀–₁₅, ₁₊…₄₊, `auto = refl`.
- L1 `Word/Base.agda`, `Word/Properties.agda` — free monoid `Word X`; `[_]ʷ`, `ε`,
  `_•_`; `wconcatmap` postfix `_ʷ` (extends `f : X → Word Y` to words); stateful
  traversals `_ᵗ`/`_ᵗ'` driving coset enumeration; conjugation helpers.
- L2 `Presentation/{Base,Properties,Definitions,GroupLike,Morphism}.agda` —
  `_===_` (axioms) vs `_≈_` (generated monoid congruence); associativity solvers
  (`by-assoc`, pattern-guided `by-passoc`); **`_IsPresentationOf_`** (record: a
  `Grouplike` witness + semantics `⟦_⟧` + `IsGroupIsomorphism` onto the target
  group) and `_IsMonoidPresentationOf_`; `SubPresentation` = Soundness +
  Completeness of a semantics (setoid embedding).
- L3 `Presentation/Construct/` — amalgamated product `_⊕_` etc. (`Base.agda`);
  `Properties/`: DirectProduct, SemiDirectProduct(2), NDirectProduct, SugarProduct,
  Amalgamation (coset normal form `ANF`, `AmalDataNF`).
- Circuits: `Circuit/Base.agda` — `Gate : ℕ → Set`-indexed generators, `Circuit n =
  Word (Gen n)`, wire shifts `_↑`/`_↥ᵏ_`, `Lift-Relation` adding structural rules
  `cong↑`, `comm₁`, `comm₂` to any gate relation. THIS is the "inductively defined
  circuits + inductively defined relations" contribution of the outline.
- Normalization: `Normalization/NormalForm/Setoid.agda` — **`NormalForm`**
  (= stdlib `RightInverse`, i.e. section+retraction data), **`NormalFormInjective`**
  (= `Injection`), `BijectiveNormalForm` (= `Bijection`), `WeakNormalForm`,
  **`UniqueNormalForm`**, `by-normalization` (soundness + unique NF ⇒
  completeness). `Propositional.agda` re-export for `≡`-carriers.
  Outline's remark to develop: NF-injective is *strictly weaker* constructively
  than the section+retraction version.
- `Normalization/Reidemeister-Schreier.agda` — `Star-Injective-Simplified` /
  `Star-Injective-Full`: the coset-enumeration engine giving Schreier sections and
  left/right normal forms (the monoid generalization of Reidemeister–Schreier à la
  Bian–Selinger — outline contribution 3). `Normalization/CosetNF.agda` — coset
  towers (`CosetTable`, `PackedCosetTable`, `CosetTower`, `SingleLevel`): the
  subgroup-chain / stabilizer-chain "mixed-radix digit" normal form of the
  outline's Preliminary section.
- Specific groups `Examples/Groups/`: `Cyclic` (ℤ/n), `Sn` (symmetric, inductive
  R–S), `SnD` (ℤ/4 ≀ Sₙ — call it **signed permutations / hyperoctahedral-style
  wreath product** per outline), `Trivial` (two presentations + iso;
  `P1.Presentation.presentation`, `P2.Presentation.presentation`).
- Case studies:
  - `Examples/Groups/Symmetric/` — full completeness of the circuit presentation
    of Sₙ; `Theorems.agda` is the style exemplar collecting unique NF, soundness,
    completeness (loose endofunction + tight permutation semantics),
    `IsPresentationOf`. The outline's "Example: Permutations" walkthrough.
  - `Examples/Amalgamations/CliffordT1.agda` — 1-qubit Clifford+T as amalgamated
    product, ends in a monoid isomorphism. `QutritCliffordT1.agda` — qutrit
    analogue. `U33Di.agda` — U₃(ℤ[1/2,i]) as two-level amalgamation.
  - `Examples/Construct/DirectProduct/S3xC5/` — S₃×C₅ worked example.
- Recently added (this month, by Claude with owner review): group-level
  presentation theorems for constructions —
  `Presentation/Construct/Properties/DirectProduct.agda` `module Presentation`
  (product presents G₁×G₂, target `Algebra.Construct.DirectProduct.group`),
  `SemiDirectProduct.agda` `module Presentation` (presents the semidirect product
  built from an `SDP.Action`), `NDirectProduct.agda` (`⊗-group`, n-fold
  `presentation` by induction, trivial group at 0).
- **WIP / not to be leaned on**: `Examples/Groups/Symplectic/` tree and
  `Examples/Groups/ProjectivePauli/` (Pauli/Semantics.agda has unsolved metas at 257–304 as
  of 2026-07-09; the Symplectic tree is not in the verified 4-root closure). If
  they still fail to typecheck, either fix cheaply (≤1 short attempt) or describe
  as "work in progress towards the multi-qudit Clifford presentation" — the repo
  accompanies the paper "A Complete and Natural Rule Set for Multi-Qudit Clifford
  Circuits in All Odd Prime Dimensions". Do NOT claim it as a completed
  formalization unless it typechecks during this task.
- Outline's "7 examples formalized": enumerate honestly from the survey (P1);
  candidates: Sₙ, ℤ/n, trivial, S₃×C₅, SnD wreath, Clifford+T (qubit), qutrit
  Clifford+T, U₃(ℤ[1/2,i]) — count what actually holds and adjust the claim to
  match reality (paper text must match the artifact).

## Code consolidation (user-requested, do in P2)

Create `MainTheorems.agda` at repo root (module `MainTheorems`, `--safe`):
re-export/restate in one place every headline result, grouped with banner comments:
(a) all `_IsPresentationOf_` / `_IsMonoidPresentationOf_` values, (b) all
`NormalForm` / `NormalFormInjective` / `UniqueNormalForm` witnesses for concrete
presentations, (c) the completeness theorems (Sₙ etc.), (d) the construction
lifting theorems (direct/semidirect/n-fold/amalgamation), (e) the monoid isos of
the three Amalgamations examples. Follow the style of
`MainTheorems.agda` itself (72-char banners, `open import ... using`
lists). It must typecheck; add it to the roots you re-check. The paper's Examples
section then mirrors this module table-style, and the artifact section points to it.

## Paper structure (outline sections + mandated extras)

Follow `paper-outline.md` order; flesh out every stub. Planned sections:

1. Abstract.
2. Introduction — completeness proofs are gigantic computations (motivate with
   Clément et al.'s ~300-page handwritten completeness proof for a complete
   equational theory of quantum circuits — find the exact paper(s) by web search:
   "Complete equational theory quantum circuits Clément Perdrix", incl. the
   Real/Clifford+CH variant the outline names); mechanization gives correctness
   guarantees; contributions list per outline (library; inductive circuits;
   examples incl. one from a paper published this year; monoid amalgamation +
   monoid Reidemeister–Schreier generalizing Bian–Selinger; new stdlib theorems).
3. Example: Permutations — worked walkthrough of the Sₙ development (gate set,
   relations, normal form, coset tower, completeness statement), with quantikz
   circuit figures matched to Agda code snippets.
4. Preliminary — normal forms from subgroup/stabilizer chains via transversals
   (cite Schreier–Sims, Sims's book, Holt's Handbook); the mixed-radix
   digit-expansion analogy; specialization to circuits: Cir k ≤ Cir (k+1).
5. Library design — Word/Presentation/Normalization/Circuit layers; `_===_` vs
   `_≈_`; inductively defined circuits and lifted relations (`cong↑`, `comm₁/₂`);
   the NFProperty zoo and the constructive-strength discussion (injective NF
   strictly weaker than section+retraction — give the precise statement and a
   proof sketch/counter-model argument); the Reidemeister–Schreier engine and
   coset towers; the associativity/pattern solvers as proof engineering.
6. Examples — THE catalogue: a table + prose listing **every**
   `IsPresentationOf` record (relation set R, group G, premises), every
   NormalForm/UniqueNormalForm record, with file references and `MainTheorems`
   pointers. SnD presented as signed permutations / hyperoctahedral flavour.
   (Lamplighter only if time remains at the very end — otherwise "future work".)
7. Related work — THOROUGH comparative survey (user's core demand), organized:
   (a) syntactic-only precursors: Selinger–Bian Agda verifications
   (arXiv:2306.08530, arXiv:2204.02217 — fetch real titles; outline notes they
   only relate two relation sets, no semantics — our semantic completeness is the
   delta); their tools (http://www.mathstat.dal.ca/~xbian/LafontLP/ and
   .../qupit/index.php — fetch and describe).
   (b) group theory in proof assistants: Lean/mathlib (PresentedGroup, FreeGroup,
   Coxeter groups, Nielsen–Schreier, group solvers), Coq/MathComp (fingroup, Odd
   Order theorem), Agda (stdlib algebra, cubical Agda free groups & finite groups,
   setoid-based algebra), Isabelle (HOL-Algebra, Knuth–Bendix/IsaFoR rewriting).
   (c) quantum-circuit formalizations: QWIRE, SQIR/VOQC, VyZX (verified
   ZX-calculus), CoqQ, Qbricks, QHLProver, quantum libraries in Lean; verified
   optimizers (Amy's Feynman/staq lineage if formalized-adjacent).
   (d) completeness of graphical/equational calculi (paper mathematics to
   contrast): ZX completeness line (Backens; Jeandel–Perdrix–Vilmart; qutrit/qudit
   ZX), quantum-circuit complete equational theories (Clément et al. line),
   Clifford presentations (Selinger's n-qubit Clifford generators+relations, the
   odd-prime-qudit paper this repo accompanies), Lafont's algebraic theory of
   Boolean circuits (foundational for circuit presentations).
   For each: what they formalize, proof-assistant, whether NF/presentation/
   completeness is mechanized, and precisely how we differ. Focus depth on Agda.
8. Discussion / lessons (EXTRA): setoid-based vs cubical choice; what the stdlib
   lacked (list the concrete new theorems the library adds on the semantic side —
   grep for candidates in `ForStdlib/` and Morphism/Construct files); proof
   engineering tricks (numeral patterns, `by-assoc`, pattern solvers, coset
   tables as data); scaling observations (LOC, typechecking times per root).
9. Mechanization statistics (EXTRA): table of modules/LOC per layer (`wc -l` via
   Glob file list), axiom-freedom (`--safe` everywhere), stdlib version.
10. Conclusion and future work (Symplectic/multi-qudit completion, Lamplighter,
    stdlib upstreaming per ForStdlib/ staging).
11. Acknowledgements — per outline verbatim intent (Claude used for refactoring
    and paper drafting from the owners' outline, checked/revised by owners) inside
    `\begin{acks}` (auto-hidden while anonymous).
12. References.

Writing standards: POPL reviewer audience. Every Agda snippet quoted VERBATIM from
the repo (copy from files, cite as `Module.Name` + relative path in a footnote or
listing caption; use `agda`-styled `lstlisting`/`minted`-free setup — define a
simple `lstdefinelanguage` for Agda with Unicode letters, since no shell-escape).
State theorems both informally and as the Agda type. No invented lemma names. Be
generous with intuition but never sloppy with claims: anything stated as
formalized must exist in the repo and typecheck.

## Literature seed list (verify each via WebSearch before citing; expand freely)

Selinger n-qubit Clifford generators & relations; Bian–Selinger Clifford+T 1-qubit
and U_n(ℤ[1/2,i]) (2204.02217), 2306.08530; the 2025/2026 odd-prime multi-qudit
Clifford rule-set paper (this repo's companion); Clément–Heurtel–Mansfield–Perdrix–
Valiron complete equational theory for quantum circuits (LICS'23) + minimal
version + Real/Clifford+CH ~300pp variant; ZX completeness: Backens,
Jeandel–Perdrix–Vilmart, Vilmart, qutrit/qudit ZX (Wang; Booth–Carette; Poór–van
de Wetering); Lafont "Towards an algebraic theory of Boolean circuits" (2003);
Squier, Guiraud–Malbos (coherent presentations, polygraphs), Métayer; Sims
"Computation with finitely presented groups"; Holt et al. "Handbook of
Computational Group Theory"; Schreier–Sims; Magnus–Karrass–Solitar (R–S method);
Todd–Coxeter. Proof assistants: QWIRE (Paykin–Rand–Zdancewic POPL'17); SQIR/VOQC
(Hietala et al. POPL'21); VyZX (Lehmann–Caldwell–Rand); CoqQ (Zhou et al.);
Qbricks (Chareton et al. ESOP'21); Isabelle QHLProver (Liu et al.); Bordg et al.
Isabelle quantum; mathlib (The mathlib community, CPP'20) + PresentedGroup/Coxeter
/Nielsen–Schreier in Lean; MathComp fingroup + Gonthier et al. Odd Order (ITP'13);
cubical Agda (Vezzosi–Mörtberg–Abel ICFP'19) + cubical library group theory
(e.g. symmetric group / finite groups work by Choudhury?/Ljungström–Mörtberg —
verify); Agda 2 (Norell); agda-stdlib; setoid formalization literature
(Barthe–Capretta–Pons); Knuth–Bendix in Isabelle (Sternagel–Thiemann, IsaFoR/CeTA);
CoLoR (Coq rewriting); normalization by evaluation for monoids/solvers in Agda
(stdlib `Algebra.Solver.Monoid` lineage, Danielsson); free groups in HoTT/UF
(Nielsen–Schreier in HoTT — Andrew Swan?; verify). Add anything else surfaced by
searches on: "formalization group presentation proof assistant", "verified normal
form monoid Agda", "quantum circuit equational theory verified", "Clifford group
generators relations", "completeness graphical calculus formalization".

## Ops protocol

Phases and granular checklists live in `paper/PROGRESS.md`. Rules:

- On every scheduled/backstop run: read PROGRESS.md; if `status: DONE`, delete the
  hourly backstop cron job (CronList → CronDelete) and stop. If before start time,
  reply "waiting" and stop. Otherwise continue the FIRST unchecked item.
- Work in ONE continuous turn as long as productive; tick items in PROGRESS.md
  IMMEDIATELY as they complete (checkpointing — a turn may die at any moment from
  usage limits). Append one log line per completed item.
- If a usage/rate-limit failure kills a turn, the hourly cron revives the task
  after reset — by design, no user action needed. (This implements the user's
  "pause till it resets, continue automatically".)
- Between phases you MAY end the turn and `ScheduleWakeup` (60–270 s) to chain
  promptly with a warm cache; the hourly cron remains the crash backstop.
- All intermediate knowledge → files under `paper/notes/` (survey, refs-notes,
  stats), so context loss is harmless.
- Never block on the user. Never git-commit. Keep edits inside `paper/` except the
  sanctioned `MainTheorems.agda` (+ its typecheck).
- On completion: set `status: DONE`, write `paper/README.md` (build instructions,
  file map), delete the backstop cron job, send ONE PushNotification ("POPL paper
  draft complete in paper/ — N sections, M refs, MainTheorems.agda typechecks"),
  and end with a thorough summary message for the user.
