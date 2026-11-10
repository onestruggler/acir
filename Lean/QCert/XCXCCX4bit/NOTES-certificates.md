# Notes of the `certificates` part

Modules: `BaseComm` (generated), `CBC`, `CCerts` (generated), `CFaithful`,
`KFaithful`, `Completeness`.  Generators in `gen/`: `mk_basecomm.py`,
`mk_ccerts.py`, run with WSL `python3` from `gen/`; both regenerate the
checked-in modules byte for byte.

## Modules

| Lean module | Agda | state | own build time |
|---|---|---|---|
| `BaseComm.lean` | `BaseComm.agda`, **generated** by `gen/mk_basecomm.py` | built | 28 s |
| `CBC.lean` | `CBC.agda` | built | ~6 s |
| `CCerts.lean` | `CCerts.agda`, **generated** by `gen/mk_ccerts.py` | built | **68 s** (kernel: 54 relation certificates, 12 rev certificates, the closure over 105 labels; each `conj_ok` costs about 0.1 s) |
| `CFaithful.lean` | `CFaithful.agda` | built | ~5 s |
| `KFaithful.lean` | `KFaithful.agda` | built | **41 s** (mostly `low_check`: 12 lower letters × 105 labels, a `find` and an `eqMatch` each) |
| `Completeness.lean` | `Completeness.agda` | built | ~6 s |

Axioms of `Completeness.complete₄`, `KFaithful.faithful₃`, `CFaithful.cfaith`,
`CBC.base`: `propext`, `Classical.choice`, `Quot.sound`.

## Names and API (for ByPerm, Groups, NormalForm, MainTheorem)

Namespaces `QCert.XCXCCX4bit.BaseComm`, `.CBC`, `.CCerts`, `.CFaithful`,
`.KFaithful`, `.Completeness`.

* `Completeness.complete₄ {u v : Circ 4} (e : sem u ≐ sem v) : 4 ⊢ u ≈ v`
  (`= Four.complete₄ KFaithful.faithful₃ e`) and `Completeness.sound₄ (d : 4 ⊢
  u ≈ v) : sem u ≐ sem v`.
* `KFaithful.faithful₃ : Faithful.Faithful 3`.  Also exported (as the Agda):
  `gg g : 4 ⊢ ι g * ι g ≈ 1` (every placed letter is an involution),
  `rev_cancel p : 4 ⊢ ιs p * ιs p.reverse ≈ 1`, `ρ g ν`, `low_ok`, `push`,
  `push_s` (`push*`), `isG`, `basic`, `NF`, `cons`, `nf`, `nf_ok`, `nf_low`,
  `expand`, `expand_ok`, `expands` (`expand*`), `expands_ok`, `expands_basic`,
  `flip3`, `flip_comm`, `mFs_low` (`mF*-low`), `Xs_low`.
* `CFaithful.cfaith (a b : List L) (e : sem (Xs a) ≐ sem (Xs b)) : 4 ⊢ Xs a ≈
  Xs b`; `conj_list`, `ψf`, `ψ`, `cl_tree` (the Agda's `cl`, renamed: `cl` is
  `CircuitProp.cl`), `ψs` (`ψ*`), `ψs_ok`, `Φs_cong` (`Φ*-cong`, from
  `Derivable (RSRel 8) u v`), `Xs_sem : sem (Xs ws) ≐ mFs ws`, `Φ_act`,
  `Φs_act : mFs (Φs w) (enc8 i) = enc8 (Symmetric.perm (FreeMonoid.lift (f 8)
  w) i)`.
* `CCerts`: `check ms l r` (abbrev for `LabelEngine.check eqLab c3 conj_ok mul
  klein_ok`), `Xs ws : Circ 4` (abbrev for `LabelEngine.Xs Xm ws`; `Xs [] =
  1`, `Xs (x :: xs) = Xm x * Xs xs` by `rfl`), `Xs_append` (an equation),
  `check_sound ms l r h`, `sy c d` (bounds auto-parameters), `Φ : Sch 8 →
  List L`, `Φs` (`Φ*`, `= (toList w).flatMap Φ`; `Φs_mul`, `Φs_one`,
  `Φs_of`), `Φ_act_ok`, `R_rel : RSRel 8 u v → 4 ⊢ Xs (Φs u) ≈ Xs (Φs v)`,
  `inv_sym`, `rev_ok`, `μ₀ : L` (the label 0; `CFrame.μ₀` is a function on
  `Fin 8` — do not open both), `base_word`, `base_ok`, `parT`, `symT`,
  `depT` (lists), `par`, `sym_of`, `dep` (`List.getD`), `star`, `conjs_ok`,
  `cstep`, `closure_ok`, `closure_all : allFin 105 closure_ok = true`.
  Moves are `LabelEngine.Move`'s constructors (`Move.H 3`, `open
  LabelEngine (Move)`).
* `CBC.base k : Comm Gbar (Fr G (baseW k))`, and CRel's calculus at it:
  `CBC.X_inv`, `CBC.BC₀`, `CBC.BC`, `CBC.X_conj x y h : 4 ⊢ Xm x * Xm y * Xm
  x ≈ Xm (c3 x y)`, `CBC.X_klein`.
* `BaseComm.BC211E`, `BC31E`, `BC4E : Eqnp` (the Agda's `BC211⁼`, `BC31⁼`,
  `BC4⁼`); their sides are `Gbarl ++ Frl k` and `Frl k ++ Gbarl` of `CBC`
  (`k = 2, 3, 4`) by computation.

## Deviations (each also in its module header)

* **BaseComm (performance).**  One `derive … (by decide +kernel)` per
  derivation, as `Equations4` does, did not finish: the kernel check of the
  496-step `BC31` grew past 11 GB in 8 minutes.  A segment of 40 steps
  checks in 0.6 s, so the generator cuts each derivation into segments of at
  most 40 steps (`CHUNK`), names the words between them (`BC31E_w3`,
  replayed by the generator from the same steps), checks each segment as its
  own theorem (`BC31E_d3 : 4 ⊢ ιs BC31E_w2 ≈ ιs BC31E_w3 := check_sound (ss
  := …) (by decide +kernel)`) and joins them by `Derivable.trans`.  The
  kernel's cost of one long engine run is superlinear in its length: keep
  long runs in segments.
* **CCerts.**  Each certificate is a private lemma of its own (`R_order_f1`,
  …, `R_far_t4_6`, `rev_f1`, …, `rev_t6`) that `R_rel` and `rev_ok`
  dispatch to: as clauses of one definition the checks exhausted its
  heartbeats (200000) after about thirty certificates.  `Φ_act_ok` is
  decided per symbol over the eight positions at once.  Tables are lists.
* **CBC.**  The Agda's `open CRel.Calculus base public` is restated:
  `X_inv`, `BC₀`, `BC`, `X_conj`, `X_klein` in `CBC`.
* **CFaithful.**  The Agda's `cl` is `cl_tree`; `Φs_cong` by
  `Con.conGen_le`; associativity in the quotient monoid (`CircuitProp.cl`).
* **KFaithful.**  `expand_ok` by the Agda's 31 clauses (the letters whose
  expansion is themselves by `rfl`); the Agda's `by g d e` is `by_ g e`;
  `faithful₃` through a lemma `core` taking the two normal forms as
  variables (the Agda's `where` block).

## Generators

* `gen/mk_basecomm.py` reads the Agda's `gen/bc_results.json`, loads this
  folder's `mk_equations4.py` under another module name (it imports the
  Agda's `mk_equations4` by the same name) and reuses its `lean_list` and
  `emit_step`, and the Agda generator's `steps_of`, `norm`, `r7_side`,
  `R7L`, `R7R` (for the replay of the intermediate words).
* `gen/mk_ccerts.py` imports the Agda's `gen/ccerts.py`, which runs the
  searches of `gen/c8/certgen.py` (the 54 relations), the BFS for the rev
  certificates and the closure tree; nothing is saved, the whole run takes
  about 8 s.
