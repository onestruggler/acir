# Notes of the `final` part

Modules: `ByPerm`, `Groups`, `NormalForm`, `MainTheorem`, and the folder's
`README.md`.

## Modules

| Lean module | Agda | state | own build time |
|---|---|---|---|
| `ByPerm.lean` | `ByPerm.agda` | built | ~5 s (mostly loading the imports) |
| `Groups.lean` | `Groups.agda` | built | ~5 s |
| `NormalForm.lean` | `NormalForm.agda` | built | ~15 s |
| `MainTheorem.lean` | `MainTheorem.agda` | built | ~5 s |

`#print axioms` of every statement of `MainTheorem` (and of
`NormalForm.Absorb.absorb_S`, `absorb_B`, `absorb_E`, `NormalForm.unique`):
`propext`, `Classical.choice`, `Quot.sound` (`sound`, `complete₁`: only
`propext`, `Quot.sound`; `NormalForm.count`: none).

## The main statements' form

Circuit words are in diagram order, and so is the product of the Agda's
`Permutation′-group`/`Alt-group`; Mathlib's `Equiv.Perm` and
`alternatingGroup` multiply in operator order.  The presentations are
stated in the opposites, `(Equiv.Perm (Fin N))ᵐᵒᵖ` and `(Alt 16)ᵐᵒᵖ`, a
generator read as `MulOpposite.op` of its permutation of the numbered
states (`Groups.perm₁ … perm₄`, i.e. `ByPerm.Data.semP`,
`ByPerm.Even.semA`), so that a circuit is read as `op` of its own function
(`Groups.lift_perm₁ … lift_perm₄`).  `MainTheorem.group₁ … group₄` are the
isomorphisms of the quotient monoids with Mathlib's groups themselves
(through `MulEquiv.inv'`).  This is explained in `MainTheorem`'s header and
in the README.

## Names and API

* `ByPerm`: `presentation_of` (a reading `F : Circ k → G` reversing products,
  compatible, injective modulo the theory and onto gives
  `IsPresentationOf (VRel SRel k) (fun g => op (F (of g)))`); the structure
  `Data k N` (the Agda's module parameters: `enc dec dec_enc enc_dec tr at_
  complete grouplike`) with `perm`, `perm_at`, `perm_cong`, `perm_mul`
  (diagram order), `perm_one`, `perm_inj`, `perm_of`, `perm_mul'`, `semP`;
  `Full k N` (extends `Data` by `realise`) with `onto`, `lift_semP`,
  `presentation`; `Even k N` (extends `Data` by `even`, `realise`) with
  `even'`, `permA`, `onto`, `ontoA`, `circA` (irreducible, `circA_def`),
  `circA_sem`, `permA_mul`, `permA_one`, `semA`, `lift_semA`, `presentation`.
* `Groups`: `inv_sem`, `grouplike`; `One` (`enc`, `dec`, `trB`, `tr`, `by_`,
  `at_`, `circ`, `circ_at`, `F : Full 1 2`), `Two.F`, `Three.F`,
  `Fourw` (`tr`, `at_`, `parity_f`, `even`, `realise`, `E : Even 4 16`);
  `perm₁ … perm₄`, `lift_perm₁ … lift_perm₄`, `presentation₁ … presentation₄`.
* `NormalForm`: `isHi`, `pos4`, `enc_idx`, `dec_st`, `isHi_idx`, `pos4_idx`,
  `idx_isHi`, `isHi_ltb` (the Agda's `isHi-<ᵇ`), `enc_st`, `idx_back` (the
  Agda's `back`), `idx_lo`, `tr` (at `SG (8 + 8)`), `at_`, `perm`,
  `perm_at`, `parity_tr`, `revC`, `revC_sem`, `D`/`D_def`/`D_sem`,
  `C`/`C_def`/`C_low`/`C_high`, `s14`, `fixB`, `fix`, `fix_parity`, `wS`,
  `γ`, `isHi_γ`, `r`/`r_def`/`r_cong`/`r_sem`, `γ_cong`, `Coords` (fields
  `E B S S8`), `NF`, `blk`, `w3_blk`, `NF_sem`, `NF_unique`, `Of.*` (the
  Agda's module `Of u`, every definition taking `u`: `π`, `Su`, `Su8`, `g`,
  `q`, `q'` (`q⁻`), `bF`, `bG`, `Bb`, `B0`, `B1`, `Ep`, `v`, `e_lift`,
  `Ep_even`, `coords`, `NF_enc`, `NF_u`, …), `coords`, `normal_form`,
  `unique`, `NF_onto` (a subtype), `count`, `absorb`, `absorption`,
  `Absorb.*` (taking `c w`: `c'`, `wk`, `absorb_S`, `R`, `R_half`, `A`,
  `absorb_B`, `absorb_E`).
* `MainTheorem` (namespace `QCert.XCXCCX4bit.MainTheorem`): `sound`,
  `complete`, `complete₁`, `complete₂`, `complete₃`, `perm₁ … perm₄`,
  `lift_perm₁ … lift_perm₄`, `presentation₁ … presentation₄`,
  `group₁ … group₄`, `normal_form`, `unique`, `onto`, `absorption`.

## Deviations (each also in its module header)

* `ByPerm`: the parameterised module and its inner modules are structures;
  `presentation_of` replaces the monoid presentation record and
  `monoidPresentation⇒presentation`; `circA` is an `irreducible_def`.
* `Groups`: namespaces build the structure values; `rs-parity` is
  `EvenWord.Coset.rs_parity`; `perm₁ … perm₄`, `lift_perm₁ … lift_perm₄`
  are new.
* `NormalForm`: `D`, `C`, `r` are `irreducible_def`s; `at_` and
  `parity_tr` reuse `Groups.Fourw`'s, `C_low` uses `KFaithful.Xs_low`,
  `Pc_st` uses `Placed.word_down`; `e_lift` by `Fin.addCases`; `Of` and
  `Absorb` are namespaces with explicit arguments; `NF_onto` a subtype.
  Proofs about `Of` go through rewriting lemmas (`Bb_apply`,
  `Bb_symm_apply`, `coords_E`, `coords_B`, `coords_S`, `q_g`) rather than
  `show`: a `show` across `bF`/`Ep` made the elaborator unfold `Four.enc`
  of a symbolic permutation and time out.
* `MainTheorem`: the presentations in the opposite groups, the named
  semantics and the isomorphisms `group₁ … group₄`; `onto` a subtype.

## For the coordinator

* Wire the folder in with `import QCert.XCXCCX4bit.MainTheorem`, which
  reaches all 47 modules of the folder (40 + 7 in `Lib/`).
* The README is `QCert/XCXCCX4bit/README.md`.
* The nine generators other than the certificates part's were rerun and
  regenerate their modules byte for byte (`git status` clean afterwards).
