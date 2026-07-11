# PROGRESS — POPL paper task

status: DONE (2026-07-10; all phases complete — see log)
start-at: 2026-07-09 19:27 local
brief: paper/TASK-BRIEF.md  (read it fully before doing anything)

Rules: tick items the moment they complete; append a log line; all knowledge into
paper/notes/*; never rely on conversation memory. If a run dies mid-item, the next
run redoes that item only.

## P0 — Scaffold
- [x] Try TeX install once — OUTCOME 2026-07-09 19:27: `sudo: a password is required` → NO local TeX, never retry; write compile-clean LaTeX + README build instructions (lualatex recommended for Unicode)
- [x] `paper/main.tex` (acmart acmsmall,review,anonymous; agda-style.sty w/ Unicode literate table; quantikz2; \input stubs; CCS/keywords/acks done)
- [x] `paper/sections/` 9 stubs + `paper/refs.bib` skeleton (verified-only rule stated inside)

## P1 — Repo survey (into paper/notes/repo-survey.md) — DONE 2026-07-09 ~20:20
- [x] Grep-enumerate every `IsPresentationOf` / `IsMonoidPresentationOf` value → survey §3
- [x] Grep-enumerate NF witnesses → survey §3
- [x] Monoid isos + construction theorems → survey §3 (incl. NEW finds: Extension.agda GREEN, Amalgamation group-level dpres, wreath SnD, Pauli compositional presentation)
- [x] Key modules read; quotables in survey §2 (Word, PB ≈, Definitions, NF zoo, R–S, CosetNF towers, Construct.Base, Circuit.Base, StarPresentation, ForStdlib×7, Sn factorial NF)
- [x] WIP verdicts: Pauli/Presentation GREEN; Pauli/Semantics RED (metas 257–304); S3xC5/Presentation RED (parse 47.40); Symplectic tree blocked; SnD+Extension+S3xC5-Semantic+SnD-old GREEN
- [x] Count decision (survey §4: present table, "seven/eight families" prose care); LOC: 190 files/89,212 total; core 9,845; WIP tree 68,053

## P2 — MainTheorems.agda (collect headline results in one place) — DONE 2026-07-09 ~21:30
- [x] `MainTheorems.agda` written: completeness-by-normalization, 5 construction-theorem module aliases (DP/NDP/SDP2/Amal/Extension), trivial×2, cyclic (+unique-nf), symmetric (presentation + tight/loose unique-nf + soundness + completeness), Pauli (odd prime, ∀n), wreath ℤ/N≀Sₙ, and the 3 monoid isos (qubit CliffordT, qutrit CliffordT, U₃(ℤ[½,i]))
- [x] Typechecked GREEN on first attempt (EXIT=0); 4 standard roots re-checked OK OK OK OK. (Only pre-existing UselessPrivate warning in Extension.agda, not ours. Extension dpres premises recorded: real sound-ax nf-ε real-Q.)

## P3 — Literature (into paper/notes/related-work.md + refs.bib) — DONE 2026-07-09 ~22:40
- [x] All seed items verified by search/fetch. KEY IDs: 2306.08530=3-qubit Clifford+CS (QPL'23); 2204.02217=2-qubit Clifford+T (QPL'22); companion=Li–Mosca–Ross–vdW–Zhao QPL'25 EPTCS 426; ~300pp motivator=Clément Real-Clifford+CH arXiv:2602.06644 (13+264pp); Bian thesis 2023 (Prop 2.55 source); Booth–Carette MFCS'22 odd-prime ZX; LICS'23/24 line
- [x] Tools described: LafontLP (Lafont NF normalizer, Lemmas 10–11 of Lafont 2003); qupit (Sp(2n,ℤp) staircase NFs, cites Selinger Prop 5.5 + qutrit paper)
- [x] refs.bib: ~50 verified entries (VERIFY-DETAIL comments mark page-range residuals); notes/related-work.md has per-item comparisons + framing lines + careful-claims list

## P4 — Writing (each item = one sections/*.tex, full prose, snippets verbatim)
- [x] abstract.tex + intro.tex DONE (motivation w/ verified 264pp-appendix cite; contributions 0–4; §1.2 taste; §1.3 related-work summary + tools; honesty decision: "seven nontrivial example families" = cyclic, symmetric, wreath, Pauli, qubit-CT, qutrit-CT, U₃ with S₃×C₅+trivial as demonstrations; qutrit relation set presented as derived-in-this-work, NOT attributed to li2025qutrit)
- [x] permutations.tex DONE (3 quantikz figures: generators/comm₂+braid/staircase; SRel+VRel+C+[_]ᶜ+ract+NF-tower verbatim; loose vs tight semantics; unique-nf → by-normalization → completeness; MainTheorems statements quoted)
- [x] preliminaries.tex DONE (transversals→digits, mixed-radix incl. factorial system, RS method verify-not-search division of labour, Cir k chain, amalgamation forward-pointer)
- [x] design.tex DONE (words; ≈ 8-constructor congruence + setoid-vs-quotient discussion; IsPresentationOf verbatim; NF zoo = stdlib bundles + constructive-strength (injective-as-data weaker); by-normalization verbatim; circuits + suc-index unification remark; engine w/ 5 hypotheses verbatim + refl-discharge observation; ⋄ constructions + presentation theorems incl. extension recipe (thesis Prop 2.55 cite); ForStdlib 7 items w/ Action verbatim; solvers)
- [x] examples.tex DONE (2 tables; cyclic/trivial/S3xC5-honest/wreath-signed-permutations/Pauli-compositional; CliffordT1 w/ relations + tower + Matsumoto–Amano-as-amalgam observation; qutrit w/ full relation set (derived-in-this-work framing); U₃ w/ [S]-relations + 2-level structure; §WIP symplectic honest per ground rule)
- [x] related.tex DONE (comparison table w/ ding marks; Bian–Selinger syntax-to-syntax delta; quantum-PA soundness-vs-completeness; mathlib/MathComp/Isabelle/univalent; IsaFoR + Squier-obstruction point; niche summary w/ AFAIK scoping)
- [x] discussion.tex DONE (stats table from survey; setoid-vs-quotient balance sheet; ForStdlib gap analysis; 4 proof-engineering lessons; threats-to-interpretation incl. matrix-semantics gap honesty)
- [x] conclusion.tex DONE (summary; future: odd-prime Clifford via symplectic layer, lamplighter, HNN, upstreaming; methodological close)
- [x] Cite audit: all used keys defined; previously-uncited ZX cluster + greylyn + jain now cited; acks now cite qupit-code/paper-outline per outline; no dangling \ref (fig:sigma label unreferenced — harmless)

## P5 — Integration & QA — DONE 2026-07-10
- [x] Claims-vs-artifact audit: fixed 72-obligation count (×2 files), NF tower carrier digits (⊤ × C 1 × ⋯), removed ungrounded S3xC5 order-15 speculation
- [x] No TeX available → mechanical audits instead: environments balanced (fixed-string check, all OK), braces balanced per file, Unicode inventory vs coverage (added ᶜ ↪ ⋯ to BOTH tables), \aid made robust (\texttt + \DeclareUnicodeCharacter mirror, no fragile \lstinline), figures de-nested (minipage + plain quantikz), \citestyle moved to preamble, pifont added; anonymity audit: third-person Bian–Selinger, acks auto-hidden, artifact cited as anonymous supplement
- [x] paper/README.md written (build instructions, first-compile checklist, file map, artifact relation, anonymity notes)

## P6 — Finish
- [x] status: DONE; backstop cron deleted; notification sent; summary delivered

## Log
- 2026-07-09 17:35 — Task scheduled by planning session; briefs written; crons pending.
- 2026-07-09 19:27 — Started (one-shot cron). P0 scaffold; sudo TeX install refused as expected.
- 2026-07-09 ~20:20 — P1 survey done (notes/repo-survey.md); WIP verdicts recorded.
- 2026-07-09 ~21:30 — P2 MainTheorems.agda green on first typecheck; 4 roots OK.
- 2026-07-09 ~22:40 — P3 literature verified (~50 refs); notes/related-work.md.
- 2026-07-10 — P4 all nine sections written; P5 audits + fixes; README; DONE. Backstop cron deleted.
- 2026-07-10 — User granted sudo: TeX Live installed in WSL (+texlive-plain-generic for acmart's binhex.tex). latexmk -pdf GREEN: main.pdf, 26 pages, 0 errors, 0 undefined cites/refs, 0 missing chars, 0 overfull (after: \aid made \mbox-based for math mode; tab:compare citations moved to prose; 2 minor rewords). Pages 1/5/12/17 visually verified (layout, Unicode code blocks, quantikz figures, authoryear cites). Sudo password used transiently only, never persisted.
- 2026-07-10 — User-requested figure: sections/fig-relations.tex — the COMPLETE relation set of Clifford-pres as circuit equations (Selinger-Fig-8 style, but matrix-multiplication order = rightmost gate first; diagrams transcribe Agda words L→R). 4 Pauli + 8 conjugation (from act1 at p=2: H swaps X/Z; S: X↦XZ; CZ: X₀↦X₀Z₁, X₁↦Z₀X₁) + 22 twisted relators (R1 boxed = cocycle S²=Z; R9/R10 = Selinger C10/C11 with S⁻¹=S; M-gate laws; far-comm; power-collection) + 3 abbreviation definitions (⊥⊤, ⊤⊥, M_x). Iterations: \mbox-wrapped equations to stop mid-equation line breaks (empirically quantikz survives box-macro args — fbox proved it); caption shortened, detail moved to §5.8 body; tags renumbered to display order. Full page (Fig. 4, p.21), rebuild GREEN 29pp 0/0/0, visually verified at 110dpi.
- 2026-07-10 — User added Examples/Groups/Clifford/Qubit/Presentation.agda (Clifford-pres). Verified GREEN (+ Pauli/Semantics now GREEN — user fixed the metas; Symplectic NF-Inj still RED exit 42). Paper: new §5.8 "The qubit Clifford groups as an extension, with an explicit cocycle" (exact sequence, Clifford-pres/conj/corr code verbatim, cocycle S²=Z story, odd-p-splits remark, honest definition-vs-theorem status); §wip re-worded (stale Pauli-carriers parenthetical removed; relations+action sublayer green); intro fruit sentence; conclusion updated; stats table made exactly additive (new Zp support row; verified examples 35/8,962; WIP 118/67,606; total 191/89,355); survey notes status flips. Rebuild GREEN: 28pp, 0/0/0; §5.8 page visually verified. Clifford-pres NOT added to MainTheorems (it is a definition, not an IsPresentationOf theorem — index contract kept).
- 2026-07-10 — User correction integrated: carette2024squareroots IS partially mechanized (verified from PDF §7.2: Agda atop agda-categories; all of §5 + all of §6.1 (2q-Clifford completeness) + opening lemmas of §6.2/6.3; agda-categories RigCategory coherence bug found; weak-assoc bookkeeping = major cost). Fixed my wrong "pen-and-paper" claims in intro + related (2 places); added table row "Quantum Π with square roots | Agda (partial) | ✓ | categorical | – | 2q Clifford"; niche summary re-scoped; §6 content described in rig subsection w/ by-assoc contrast. Rebuild GREEN 27pp 0/0/0.
- 2026-07-10 — User-requested addition #2: blake2026simpler (FSCD'26, arXiv:2602.09874, PROP-theoretic simplification of 6 near-Clifford rule sets) verified & integrated: bib entry, related.tex comparison (simplification = derivability obligations = by-equal-nf target), and intro support sentence after the 264-pages line citing selinger/li (back-ref) + carette2024 + fang2026 + blake2026 as further long hand-checked computations. Rebuild GREEN: 27pp, 0/0/0.
- 2026-07-10 — User-requested additions: 4 refs verified & integrated (choudhury2022symmetries POPL'22 doi 10.1145/3498667 — HoTT-Agda-mechanized Π/rig-groupoid, ~7.5k lines; carette2024squareroots POPL'24; fang2026hadamard POPL'26 — completeness via O_n(ℤ[1/√2]) presentation; heunen2026onerig LICS'26). New related.tex subsection "Complete equational theories via rig categories" + table row; intro & niche-summary claims re-scoped honestly around Choudhury et al.; conclusion tie-in (O_n(ℤ[1/√2]) as target). Rebuild GREEN: 27 pages, 0 errors, 0 overfull, 0 undefined; new pages visually verified.
