# Generators for the Selinger Clifford development

These scripts write the generated modules of `QCert/SelingerClifford`:

| module | written by | from |
|---|---|---|
| `Axioms.lean` | `genlean.gen_axioms` | the relations C1–C15 (`engine.BASE`) |
| `Lemmas.lean` | `genlean.gen_lemmas` | derivations found by `lemmas.py` |
| `Rules1.lean` … `Rules5.lean` | `genlean.gen_rules` | derivations found by `rules.py` |
| `Tables.lean` | `tables.py` | the statements of equations 3.3–3.101 |

`generate.py` runs the searches and writes the first seven; `tables.py`
writes `Tables.lean` (in a second, with no search).

## Running

The input is Selinger's machine-readable supplement, the ancillary file
`clifford-supplement.txt` of arXiv:1310.6813 (`anc/` of the paper's
source; SHA-256 `bb72bbb0…7f252`, checked by `generate.py`).  Put it next
to these scripts or point the environment variable `SELINGER_SUPPLEMENT`
at it.  Python 3 with NumPy (used only for numerical checks).

    python generate.py            # writes ../Axioms.lean … ../Rules5.lean
    python generate.py --check    # compares with them instead
    python tables.py [--check]    # writes (compares) ../Tables.lean

`generate.py` takes about ten minutes (the lemmas about a minute, the
rules the rest); `--cache FILE` keeps the derivations in a pickle so that
the writer can be rerun alone.  The searches are deterministic (no
iteration over hashed sets decides anything), so the modules are
reproduced byte for byte.

## What the scripts do

* `supp.py` — letters (`('H', i)`, `('S', i)`, `('Z', i)` the CZ of wires
  `i, i+1`, `('w',)` the scalar ω) in time order and our wire numbering
  (wire 0 at the bottom; the supplement numbers wires from the top of each
  equation's frame), numerical matrices, the boxes A–E, and the parser of
  the supplement.  Every statement and every proof line of the supplement
  is checked numerically.
* `engine.py` — the database of equations (C1–C15, the lemmas, and the
  lemmas upside down), the `Deriv` state whose steps are exactly
  `Rewrite.Step`, and the step finder: one rewrite by an equation the
  label names, the letters moved together up to commutation of letters on
  disjoint wires, matched against the next line up to commutation and
  ω⁸ = 1 (`try_step`), and the cancellation of involutions for the
  supplement's step "inv" (`solve_inv`).
* `rules.py` — equations 3.1–3.101, translated line by line from the
  supplement's proofs.
* `lemmas.py` — Lemmas 1.1–1.3 (equations (4)–(10), (14)–(18), (20),
  (21)), which the supplement proves by diagrams: a meet-in-the-middle
  search guided by each proof's labels, between waypoints read off the
  supplement's figures (each checked numerically).  Where a step labelled
  (11) is really the commutation C12 of two CZs sharing a wire, the
  fallback to C12 is reported.
* `genlean.py` — the Lean writer.
* `tables.py` — the push tables of Section 6: each of equations 3.3–3.101
  read as "a dirty gate before one or two boxes equals boxes followed by
  dirty gates", with the gates after the boxes as data, the equation of
  `Rules*.lean` as proof, and a `decide` check that they are allowed where
  they stand.
