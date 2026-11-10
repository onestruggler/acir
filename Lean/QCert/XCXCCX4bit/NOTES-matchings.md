# Notes of the `matchings` part (CBase, CFrame, CLabels, CRel, CSem, KData, NFTables)

## Modules

| Lean module | Agda | state | own build time |
|---|---|---|---|
| `CBase.lean` | `CBase.agda` | built | < 10 s |
| `CLabels.lean` | `CLabels.agda`, **generated** by `gen/mk_clabels.py` | built | ~12 s (elaborating the data) |
| `CFrame.lean` | `CFrame.agda`, **generated** by `gen/mk_cframe.py` (+ `gen/cframe_tail.txt`) | built | ~10 s |
| `CRel.lean` | `CRel.agda` | built | ~6 s |
| `CSem.lean` | `CSem.agda` | built | ~18 s (`Xm_sem_ok`: the 105 controlled matchings on the 16 states) |
| `KData.lean` | `KData.agda`, **generated** by `gen/mk_kdata.py` | built | ~4 s |
| `NFTables.lean` | `NFTables.agda`, **generated** by `gen/mk_nftables.py` | built | ~5 s |

Axioms of `CBase.W`, `CFrame.W'`, `CRel.Calculus.X_conj`,
`CRel.Calculus.X_klein`: `propext`, `Classical.choice`, `Quot.sound`; of
`CSem.Xm_sem`, `NFTables.hi_lift`, `NFTables.st_eta`: `propext`,
`Quot.sound`.

Generators (WSL `python3` from `gen/`; each regenerates its module byte for
byte): `mk_clabels.py` (imports the Agda's `gen/clabels.py` and
`gen/mk_clabels.py` for `BASE_PG`/`base_words`; checks the label numbering
against `CLabels.agda`), `mk_cframe.py` (imports the Agda's `mk_cframe.py`
for its search `pair_words`; fixed text in the header and in this folder's
`gen/cframe_tail.txt`), `mk_kdata.py` (the Agda's `mk_kdata.LOWER` and
`clabels.word_of`), `mk_nftables.py` (self-contained: the Agda's script
writes its module when imported, so its few lines of data are repeated).

Namespaces: `QCert.XCXCCX4bit.CBase`, `.CFrame`, `.CLabels`, `.CRel`
(with `.CRel.Calculus`), `.CSem`, `.KData`, `.NFTables`.  They do not clash
with each other, but `CFrame.sel4` clashes with `Placed.sel4`: do not open
`Placed` wholesale next to `CFrame` (CRel opens `Placed (PG Wire ι ιs every
avoids semPs ιX₀ conj_mul cl4)`).

## Names (Agda → Lean)

* CBase: `Comm` (abbrev, `4 ⊢ a * b ≈ b * a`), `comm-ε` `comm_ε`, `comm-•`
  `comm_mul`, `comm-≈` `comm_eqv`, `comm-sym` `comm_sym`, `comm-list`
  `comm_list`, `comm-circ` `comm_circ`, `G`, `Ḡ` **`Gbar`**
  (`= ι (.Xₚ 3) * G * ι (.Xₚ 3)`, left-associated), `commḠ` `commGbar`,
  `flip-comm₀/₂/₄/₆` `flip_comm₀…`, `on12`, `comm-on12` `comm_on12`, `fl`,
  `flipsC`, `pairC`, `canB`, `canS`, `canP`, `canon`, `wcheck`, `Pc₃`
  (`Coxeter.Circuits.Pc Width3.T`), `Pc-↓` **`Pc_down`** (an equation
  `PFrames.Pc o r = Circuit.pad 1 (Pc₃ o r)`, for NormalForm's `Pc-st`),
  `comm-flips`, `wcore`, `Wc`, `W`.
* CFrame: `mk`, `half`, `low` (computed: `2 v + e`, `x / 2`, `x % 2`), `μ₀`
  (a function on `Fin 8`; CCerts' label `μ₀` is another name in another
  namespace), `InC`, `_==₄_` `eq4`, `valid4`, `sel4`, `sel4b`, `sg d` (the
  letter `⟨d, _⟩ : SG 8`), `fw`, `flips4`, `flips_comm`, `flips_act`,
  `pairW`, `pair_act`, `pair_comm`, `same_half`, `act_inj`, `sel4_self`,
  `sel4b_self`, `σᵣ r`, `βᵣ r`, `σᵣ_inj r h`, `σᵣ_valid r h`, `pairᵣ r`,
  `flipsᵣ r`, `canonW r`, `canonW_act r h`, `W-core` **`W_core r h`** (the
  Agda's anonymous module `(r : CW) (h : InC r)` is the section `Core`, `r`
  and `h` explicit), `match` **`matchW`** (a keyword), `actF` (the fast
  action: on the values, `swN`/`actL` with `Nat.beq`), `actF_ok : actF w x =
  act w x` (**not** `rfl`: rewrite with it), `matchF`, `matchF_ok : matchF p
  x = matchW p x` (not `rfl`), `_==₈_` **`eq8`** (`Nat.beq` on the values),
  `eq8_sound`, `all8`, `all8_sound`, `eqMatch`, `eqMatch_sound` (states
  `matchW`), `match-InC` `match_InC`, `W′` **`W'`**.
* CLabels: `s₀ … s₆ : SG 8`, and the tables as **lists**: `pairsT tblT :
  List (List (Fin 8))`, `frmT orbCT : List (CW 8)`, `baseT : List (Fin
  105)`, `orbKT : List (Fin 5)`; `baseQ : Fin 5 → List PG`, `baseW : Fin 5 →
  CW 8`.  A word is `FreeMonoid.ofList [s₁, s₅]` (or `1`).
* CRel: `nthD d xs i` (the Agda's `lookup` on lists), `avoid?`, `distinct?`
  (Booleans), `frameD`, `L` (abbrev `Fin 105`), `frm`, `Xm`, `tbl`,
  `findIn`, `find : (Fin 8 → Fin 8) → Option L` (the Agda's `Maybe`; use
  `Option.getD` for `fromMaybe`), `c3`, `mul`, `_==ᴸ_` **`eqLab`**,
  `==ᴸ-sound` **`eqLab_sound`**, `Fr_cong`, `Fr-•` **`Fr_mul`**, `Fr_one`
  (new: `Fr b 1 = b`), `Fr_invol`, `Fr_comm`, `comm-≈ʳ` **`comm_eqv_r`**,
  `GG`, `ḠḠ` **`GbarGbar`**, `X₀X₀`, `split` **`splitG`**, `split-comm`
  **`splitG_comm`**, `w₀` (a product `of s₀ * of s₂ * of s₄ * of s₆`),
  `X₀_w₀`, `comm_X₃`, `comm_Pc_X₃`, `inC?`, `inC_sound`, `comm_Pc_Gbar`
  (`comm-Pc-Ḡ`), `orbC m`, `orbK m` (lookups the Agda writes inline),
  `BC₀_ok`, `BC_ok`, `cP`, `conj_ok`, `kleinList`, `κw`, `klein_ok`, `Qbar`,
  `P`.
* **CRel.Calculus** (the Agda's module `Calculus base`): `base : ∀ k : Fin
  5, Comm Gbar (Fr G (baseW k))`.  `Calculus.X_inv x` (no `base`),
  `Calculus.BC₀ base F h`, `Calculus.BC base x y h`, `Calculus.X_conj base
  x y h : 4 ⊢ Xm x * Xm y * Xm x ≈ Xm (c3 x y)` (left-associated, as
  `LabelEngine`'s `conj` wants), `Calculus.X_klein x y h` (no `base`: it
  does not use it).
* CSem: `allFin`, `allFin_sound`, `enc8`, `pos`, `pos_enc8`,
  `enc8_injective`, `mF`, `Xm_sem`, `mF*` **`mFs`**, `mF*-++`
  **`mFs_append`**; the fast evaluator `code`, `opL`, `atL`, `semK`,
  `bitsL`, `bitsL_inj`, `code_ok`, `semK_ok : bitsL (sem w x) = semK
  ((toList w).map code) (bitsL x)` (any width; usable elsewhere when a
  check must evaluate long circuits: `sem` costs the kernel about 4 times
  more), `eqBL`, `eqBL_sound`, `xmCheck`.
* KData: `rg : PG → CW 8` (twelve letters, `1` otherwise; match
  `| .CXₚ 0 1 _ => …`).
* NFTables: `w3`, `st b p = Width3.enc p ++ (b ∷ .nil) : Bits 4`, `w3_st`,
  `pos_st`, `st_eta`, `enc8_st`, `idx`, `enc′` **`enc'`**, `enc'_idx`,
  `isHi'`, `pos4'`, `idx_eta`, `isHi_lt : isHi' i = !Nat.blt i.1 8`, `rv`,
  `rv_rv`, `rev8 : Equiv.Perm (Fin 8)`, `hi_lift : idx true y = Fin.natAdd 8
  (rev8 y)` (the Agda's eight `suc`s; `Coxeter.liftN_natAdd` has the same
  form).  `Four.enc i = NFTables.enc' i` holds by `decide` (NormalForm's
  `enc-agree`).

## Using the side conditions (for CCerts / KFaithful)

`LabelEngine.check eqLab c3 conj_ok mul klein_ok ms l r` closes by
`decide +kernel`; labels are numerals `(41 : L)`.  Measured with the fast
`actF`: the certificate of `R-rel (far false 1 3)` (19 moves, with `I`, `K`,
`Ki`, `C`) 0.9 s; 105 `eqMatch`es of `rg (.Xₚ 2) * frm ν` against itself
1.9 s; 105 `find (matchF (frm ν))` 1.0 s.  (Before the fast `actF`, which
came after CCerts and KFaithful were first measured, these were 1.5 s,
3.0 s, 1.3 s.)

## Deviations (each also in its module header)

* Words are multiplied left-associatively; the Agda's associativity steps
  are reasoning in the quotient monoid (`CircuitProp.cl`, `Placed.cl4`).
* CFrame: `mk`, `half`, `low` compute; the Agda's tables of `refl` proofs
  are single `decide +kernel`s; the fast action works on the values of the
  positions (`swN`, `actL`) with `swN_eq`, `actL_val` for the Agda's
  `act-letter` table.
* CRel: tables are lists and `find` returns an `Option`; `distinct?` is a
  Boolean (`Coxeter.frame` is total), and `ko` uses `frame (kleinList x y)`
  directly; `viaN`'s `to-list` side conditions are equations of words.
* CSem: the check evaluates the circuits on lists of bits (`semK`) — the
  same check, 18 s instead of 56 s.
* KData, NFTables: tables of `refl` proofs over `Fin`/`Bool` are `decide`;
  `rev8` is an `Equiv.Perm`, `hi_lift` uses `Fin.natAdd 8`.
