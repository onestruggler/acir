# Venue survey (2026-09-04)

Target: publish the paper *as quickly as possible* at a venue that is
class A on **both** the CCF 2022 list and Tsinghua's TH-CPL list.

## Intersection of CCF-A and TH-CPL-A relevant to this paper

| Venue | CCF | TH-CPL | Fit | Next deadline | Notification | Format |
|---|---|---|---|---|---|---|
| **OOPSLA 2027 (PACMPL)** | A (SE/PL) | A (SE/PL) | good: PL + verification, PACMPL takes Agda/Coq formalisation papers; quantum papers appear regularly | **Round 1: 14 Oct 2026** (Round 2: 7 Apr 2027) | 18 Dec 2026 (R1); 2 Jul 2027 (R2) | acmart `acmsmall`, 23 pp + refs (25 pp revised) |
| **PLDI 2027 (PACMPL)** | A | A | good (verification track papers) | **12 Nov 2026** | 4 Mar 2027 (author response 16–18 Feb) | acmart `acmsmall`, PACMPL |
| CAV 2027 | A (theory) | A (theory) | medium: CAV prefers tools/automation; proof-assistant formalisations do appear | 20 Jan 2027 | 23 Apr 2027 | LNCS, ~18 pp |
| LICS 2027 | A (theory) | A (theory) | best *topical* fit (Clément LICS'23/'24/'26 complete equational theories are LICS papers) | expected Jan/Feb 2027 (not yet announced; Montreal, 21–24 Jun 2027) | ~Apr 2027 | LIPIcs, short (≈12–15 pp) |
| POPL 2028 (PACMPL) | A | A | good | ~Jul 2027 | ~Oct 2027 | too slow |
| FM 2027 | A | B | good | CfP not yet issued | — | TH-CPL only B |
| ICALP 2027 | B | A | medium | ~Feb 2027 | — | CCF only B |
| TOPLAS (journal) | A | A | good | rolling | slow (months–year) | no page limit |
| Information and Computation (journal) | A (theory) | A | medium | rolling | slow | — |

Not on either A list (for reference): ITP, CPP, FSCD, CSL, QPL, LMCS, JAR.

## Recommendation

**OOPSLA 2027 Round 1 (deadline 14 October 2026)** — the earliest
CCF-A ∩ TH-CPL-A deadline, with notification on 18 December 2026 and
a revise-and-resubmit cycle; PACMPL format (`acmsmall`), 23 pages.
Fallback: **PLDI 2027 (12 November 2026)**, same format, so the same
source builds for both.  If a shorter, more logic-flavoured version is
wanted, **LICS 2027** is the natural home of the completeness
literature this paper mechanises.

The paper is therefore written in `acmart` (`acmsmall`, PACMPL
metadata), like `paper/` (POPL submission), so it can be sent to
OOPSLA or PLDI without reformatting.

Sources: conf.researchr.org/track/splash-2027/splashoopsla2027;
pldi27.sigplan.org; conferences.i-cav.org/2027; lics.siglog.org;
CCF 2022 list (gist CrackedPoly/23650f5d0ab74be9dce83e7e4c0d36c4);
TH-CPL PDF (numbda.cs.tsinghua.edu.cn/~yuwj/TH-CPL.pdf).
