# srel-wd campaign status (autonomous session, 2026-08-05/06)

## Completed and pushed (all --safe, exit 0)

### The Faithful front — COMPLETE
The completeness crux is fully proved and wired in:

- `SemInj.agda` — `sem-↑-inj` PROVED (the lifted interpretation is
  head-preserving cons; injectivity reads off the tail).  With
  `module Injectivity!`, ↑-faithfulness needs only `Faithful n`.
- `NF1HeadInj.agda` (new) — width-1 head-injectivity for the live
  gate set (`lemma-nf1-head-inj`).
- `LMHeadInj.agda` (new) — the full width induction, the
  inj₁ ≁ inj₂ separation, and the A/E/B/D box-parameter recovery:
  **`lemma-lm-head-inj-proved` / `lemma-lm-inj-proved`** with NO
  postulates and NO parameters.  This is the exact statement
  NF-Inj used to postulate ("the combinatorial heart of
  completeness"; ExtendedGate carried it as four postulates).
- `NF-Inj.agda` — the postulate REPLACED by the proven theorem; the
  module is now postulate-free and `--safe`; `⟦[]⟧-injective` is a
  full theorem.  The chain above it (Uniqueness, Surjectivity,
  TheoremLM, Presentation) re-typechecks.

Remaining on this route: the normalizer triple
(`Uniqueness.agda:73` — `nf-t`/`nf-t-cong`/`retract-t`), which is
the R–S tower's output; the tower needs srel-wd per width.  The
width induction is well-founded: srel-wd at width 1 is fully proved
(all 34 remaining holes are at widths ≥ 2).

### Coset halves (PushWDM3.agda, new leaf)
- order-CZ inj₁ width-2: **4 of 5 branches** —
  `OrdCZ-inj₁-c0/-00/-0d/-cc` (drift orbits closed by `nsum-p≡0`).
- Push-level closed forms: `GZM`/`EZM` (ZM through a D box =
  diag(x, x⁻¹), no emission), `GDrift`/`EDrift` (the shape-crossing
  drift direction ZM m • H • CZ^w • H³), `BDS^-box`/`BDZM-box` (the
  witness-free BD level), and `MbvW2` — five of six width-2
  mbv-push letter lemmas (lifted S/H on inj₁ cosets).

## The interactive queue (batch-mode walls; agda-mode recommended)

Two independent walls stop batch checking; all designs and partial
statements are preserved in the git history and the assistant's
campaign memory:

1. **The LCZ2 ≟-wall**: `with`/`rewrite` on any goal mentioning the
   width-2 LCZ2 engine at the (a=0, c≠0) shapes OOMs (the
   abstraction normalizes the whole Bézout-laden case tree; four
   attempts, including with the dd-split).  Affects: order-CZ inj₁
   (a=0,c≠0) — the shape-crossing orbit — and the width-2 inj₂
   (₁₊a)-branch.  Useful discoveries that survive: ℤ*-pair
   proof-irrelevance and `(b ≟ c) ≡ no neq` both hold by refl, so
   only the normalization cost blocks; the with-in-lemma technique
   is correct in principle.
2. **The Bézout conversion wall**: `liftH-cb` (lifted H on a
   fully-nonzero B box; ZM escape through BDZM/BDS^) times out even
   alone in a leaf file.  Blocks the c10/c11 width-2 walk assembly
   (whose other pieces are all proved).

## Remaining srel-wd holes (34, unchanged baseline)
order-CZ (3: general-width inj₁, w2-inj₂ (₁₊a), mixed),
comm-CZ-S↓/↑ (3 each: same classes), semi-M↑CZ/M↓CZ (3 each),
c10/c11 (3 each), c12 (4), c13–c15 (whole).  The width-2 instances
mostly reduce to the two walls above; general width needs the
push-MBvec engine (core-M1 class).

## Session update (2026-08-06, overnight): width-1 base CLOSED, width-2 reduced to the parked walls

The well-founded induction's base is now fully theorem-grade (all --safe, pushed):

- `SrelWD1.wd1` -- full level-1 well-definedness (15f01e6).
- `Tower01` -- the 0->1 CosetNF.SingleLevel level instantiated; width-1 NF
  `nf : Circuit 1 -> Circuit 0 x C 1` with injectivity + retraction (e770720).
- `Exact01.sect-coset` + `nf'∘gg=id` -- the width-1 NF is exact; the
  nf-t/retract-t triple of Uniqueness.agda:73 exists at width 1 (c6e63d2).
- `Faithful1.faithful1` -- completeness at width 1, composed from the tower
  retraction + soundness + NF-Inj's semantic injectivity; exports
  `up-inj`/`up-inj-up` at width 1 (d9720d1).
- `StrategyB2.wd-from-coset` -- Strategy B armed at width 2: every width-2
  srel-wd obligation follows from its coset half alone (984b9c5).

On top of it, the width-2 pairs (residuals all free):

- `SrelWD2`: unary sealed families inj1; comm-CZ-S up/down inj2 (both
  {suc zero} holes closed); order-CZ 5/6 branch families (96a6e1b).
- `SrelWD2H`: order-H nn, order-SH + comm-HHS all four branches (9a01b5f).
- `SrelWD2MCZ`: CZOrbit-0b (k-fold CZ orbit engine) + semi-M-up-CZ and
  semi-M-down-CZ inj2 at all CZ-stable shapes (6317595, dbd7fe2, 4d12f2f).
- Unary inj2 pairs were already importable (SrelWDGo / SrelWDMD2).

REMAINING AT WIDTH 2 = the parked engine cluster only (unchanged
interactive queue): LCZ2 shape-crossing branches (order-CZ inj1 a=0 c/=0;
semi-M CZ at a/=0 A-boxes), inj1 CZ patterns through Push2/LCZ2 general,
selinger c10-c15, structural core-M1.  Width-general filling awaits the
Circuit-level induction wiring (your CosetNF/Uniqueness front) -- Strategy B
is armed per-width from below once each tower level lands.
