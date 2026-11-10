# Notes of the `foundation` part

Modules: `Lib/CircuitProp`, `Lib/IProp`, `Lib/Reasoning`, `Lib/Engine`,
`Syntactics`, `Semantics`, `Kit`, `Width1`, `Involutions` (generated),
`ByCoxeter`, `Width2` (generated), `Narrow2`, `Width3` (generated).
Generators in `gen/` (`common.py`, `mk_involutions.py`, `mk_width2.py`,
`mk_width3.py`), run with WSL `python3` from `gen/`.

## Namespaces and opens

Every module is in `namespace QCert.XCXCCX4bit` or a sub-namespace:

| Lean | namespace | Agda |
|---|---|---|
| `Lib/CircuitProp` | `CircuitProp` | `Circuit/Prop.agda` (+ `Circuit/Base` `Lift-Relation` lemmas) |
| `Lib/IProp` | `IndepProp` | `Examples/Independence/Prop.agda` (`PGate` only) |
| `Lib/Reasoning` | `Reasoning` | `Examples/Independence/Reasoning.agda` (`Theory`: `ax_at`, `lift`) |
| `Lib/Engine` | `Engine` | `Examples/Independence/Engine.agda` (+ `Commuting` canonical forms) |
| `Syntactics`, `Semantics`, `Kit`, `Involutions`, `Narrow2` | (flat) `QCert.XCXCCX4bit` | |
| `Width1`, `Width2`, `Width3` | `Width1`, `Width2`, `Width3` | used qualified (`W1.`, …) |
| `ByCoxeter` | `ByCoxeter.Via` | the Agda's module `Via` |

Use `open QCert QCert.Circuit CircuitProp IndepProp Engine` (and the
`scoped` notations are active inside `namespace QCert.XCXCCX4bit`).

## Representation choices (everyone uses these)

* **Circuits.**  `Circ n := QCert.Circuit (PGate Gate) n` (the Agda's
  `Circuit n`), `Gn n := QCert.Gen (PGate Gate) n` (the Agda's `Gen n`).
  The names `Circuit`/`Gen` are avoided because `QCert.Circuit`/`QCert.Gen`
  are visible from our namespace (Lean resolves names along the whole
  namespace chain, which would make them ambiguous).
* **Gates.** `Gate.X_gate : Gate 1`, `Gate.CX_gate : Gate 2`,
  `Gate.CCX_gate : Gate 3`; `PGate.gate g` is the Agda's `⌈ g ⌉`,
  `PGate.swap` the swap.  Circuits `X`, `CX`, `CCX` (abbrevs, implicit
  width `{n}`: `X : Circ (n + 1)` …), `σ` (generic, `CircuitProp.σ`),
  `CXd` (`CX↓`), `CCXd` (`CCX↓`), `CCX₃₂₀`.
* **Diagram order.**  Words are `FreeMonoid` = lists, `w * v` is `w` then
  `v`; `sem (w * v) x = sem v (sem w x)` (`sem_mul`).
* **Shifting / padding.**  The Agda's `w ↑` is `shift w`
  (`QCert.Circuit.shift`), `g ↥` is `Gen.up g` (`g.up`), and the Agda's
  `w ↓ᵏ k : Circuit (n + k)` is the framework's `Circuit.pad k w : Circ (k + n)`
  (idle wires counted first in the width), `x ↧ᵏ k` is `Gen.pad k x`.  So
  the Agda's `ax-at r5 1 : 4 ⊢ …` is `ax_at SRel.r5 1 : 1 + 3 ⊢ …` and
  `pad₃ p 1 : (1 + 3) ⊢ pad 1 w ≈ pad 1 v` (`1 + 3` is `4` by `rfl`).
  Widths are written `n + k` (Agda `ₖ₊ n`) and `n + k + 1` (Agda `₁₊ k + n`).
* **The theory.**  `SRel : CRel (PGate Gate)` with constructors
  `r1 … r7` (each at the width it is drawn on); `CircuitProp.PropRel SRel`
  adds the swap rules (`Sym`: `σ_inv`, `σ_nat₁`, `σ_nat₂`, `σ_nat₃`), and
  `VRel SRel = Lift (PropRel SRel)`.  **`n ⊢ w ≈ v`** (scoped notation in
  `Syntactics`) is `CircuitProp.Der SRel n w v = QCert.Derives (PropRel SRel) n w v
  = Derivable (Lift (PropRel SRel) n) w v`, i.e. Mathlib's `conGen`:
  `Derivable.refl/symm/trans/mul/of`.  An axiom instance is
  `srel_rule SRel.r1` (`Derivable.of (Lift.rule (PropRel.srel _))`), a swap
  rule `sym_rule Sym.σ_inv`.
* **Derived structure (CircuitProp)**: `σc k` (= `σ[ k ]`), `σcInv k`
  (= `σ⁻[ k ]`), `σ_invol`, `yang_baxter`, `lemma_cong_up` (= `lemma-cong↑`),
  `comm_gate₁_w`/`comm_gate₂_w`/`comm_gate₃_w` (= `comm-gate₁-w↑` …, with
  `shift`s), `comm₀`, `natg₀…₄`, `nat₀…₄`, `σσInv` (= `σσ⁻`), `σInvσ`
  (= `σ⁻σ`), `pad₀ … pad₄`, `pad`.  `cl R n w` is the class of `w` in the
  quotient monoid (`cl_eq`, `cl_mul`, `cl_one`), handy for reasoning up to
  associativity: `apply cl_eq.1`, then rewrite with facts `have h : cl _ m a
  = cl _ m b := cl_eq.2 d` **stated at the goal's width spelling** (`rw`
  needs the widths syntactically equal), and `rw [cl_mul] at h`.
  For concrete words (no variable word on the left of a product)
  associativity is definitional: a chain of `Derivable.trans`/`.mul`
  elaborates by defeq.
* **States.** `Bits n`, an inductive vector (`Bits.nil`, `a ∷ x` =
  `Bits.cons a x`, scoped notation, wire 0 at the head), `deriving
  DecidableEq`.  `Fun n := Bits n → Bits n`; `f ≐ g` (`Feq`, pointwise);
  `f ⨾ g` (`seqF`, diagram order); `up f`.  `sem w` (the Agda's `⟦ w ⟧`;
  `⟦ ⟧` is Mathlib's quotient notation), `semG g` (`⟦ g ⟧ᵍ`), `semL` on
  letter lists; `sem_mul`, `sem_one`, `sem_of`, `sem_up` (`⟦↑⟧`).
  Decisions: `allB`, `eqB`, `eqV`, `eqF n f g`, `same n w v` with
  `allB_sound`, `eqB_sound`, `eqV_sound`, `eqF_sound`, `same_sound`; close
  `same n w v = true` / `eqF … = true` by `decide +kernel`.  Agda name map:
  `≐-refl/sym/trans` → `feq_refl/feq_sym/feq_trans`, `⨾-cong` → `seq_cong`,
  `up-cong` → `up_cong`.  `sound : n ⊢ w ≈ v → sem w ≐ sem v`.
  `Data.Vec`'s operations used downstream on states are in `Semantics`:
  `Bits.head`, `Bits.tail`, `Bits.get` (`lookup`), `Bits.update`
  (`x [ t ]%= f`), `Bits.append` with `x ++ y : Bits (k + m)` for
  `x : Bits m`, `y : Bits k` (so `x ++ (b ∷ .nil) : Bits (1 + n)`, the width
  of `Circuit.pad 1 w`), `Bits.cons_append`, `Bits.append_inj_left`
  (`++-injectiveˡ`).  Checked: `semG (g.pad 1) (x ++ (b ∷ .nil)) =
  semG g x ++ (b ∷ .nil)` holds by `rfl` for each gate after splitting `x`.
* **Engine / Kit.**  `Eqn n := Engine.Eqn SRel n` (structure, constructor
  `Engine.Eqn.eqn`, fields `lhs`, `rhs`, `prf`), `symE`, `liftE`, `eqnW`
  (`eqnʷ`; both side conditions `rfl`), `Eqn.pad m e : Eqn (m + k)` (for
  `k ≤ 4`).  Letters `Xₗ CXₗ CCXₗ σₗ` (abbrevs; `Xₗ ↥ ↥` is `Xₗ.up.up`).
  Steps `perm ys`, `rw i e` (Kit abbrevs).  A derivation is
  `derive l r steps (by decide +kernel)`: **at a closed width** (the kernel
  decides closed propositions only), and generic lemmas are
  `def fooE : Eqn (n + 3) := Eqn.pad n <| derive … (by decide +kernel)`.
  Rules `r1E … r7E`, swap rules `σσE σXE σCXE σCCXE σσσE`.  The Agda's names
  `x⁼`, `CX²⁼`, `em=me⁼`, `cjX0-01⁼` are `xE`, `CXsqE`, `em_eq_meE`,
  `cjX0_01E`.
* **Name clash `perm`.**  Kit's step `perm` (in `QCert.XCXCCX4bit`) and
  the groups part's permutation `Coxeter.perm` clash: do not `open Coxeter`
  wholesale in a module that writes derivations; `open Coxeter (SG tr)`,
  `open Coxeter.Circuits (Pc)` and write `Coxeter.perm` (as `Width2`,
  `Width3` do).
* **Widths in statements.**  `4 ⊢ Circuit.pad 1 (shift σ * CCX * shift σ) ≈ …`
  does not elaborate (`1 + (?m + 3) =?= 4` is not solved): write the width
  as `(1 + 3) ⊢ …` or annotate the padded word (`(CCX : Circ 3)`).
  `ax_at SRel.r5 1`, `pad₃ (Width3.complete₃ e) 1`, `nat₃ w`, `σInvσ 3`,
  `lift σ_invol` all check against goals written that way.
* **Commutation in `perm`.**  `Engine.comm` is `QCert.Minimality.Gen.apart`
  (disjoint wires) with soundness `QCert.Minimality.comm_apart`; the same
  as the Agda's `comm?` for gate sets without scalars (ours has none).
  The canonical form (`Engine.canon`, `split`, `unsplit`, `insert`) and the
  order (`Engine.less`) are the Agda's.

## Deviations

* Derivations are checked at the width they are drawn on and padded
  (`Eqn.pad`, by `CircuitProp.pad`), where the Agda checks them at a
  symbolic width (`derive … refl` at `₂₊ n`).
* `Engine.check` is the Boolean the Agda's `refl` decides (`run` then
  `eqL`); `derive` takes `check … = true`.
* `perm`'s commutation test is `Minimality.Gen.apart` (see above).

## Width 2 and 3 (public API, used by Groups, NormalForm, CBase, …)

`Width2.T`, `Width2.cox : Coxeter.Circuits.Coxeter 4 T (VRel SRel 2)`,
`Width2.enc : Fin 4 → Bits 2`, `dec`, `dec_enc`, `T_act`, `tw`, `tw_ok`,
`translate`, `translate_ok`, `complete₂`, `via`; the same names in `Width3`
(at `8`, `Bits 3`), with `tw_X0 … tw_X2`, `ok_X0 … ok_X2`, and `complete₃`.
`ByCoxeter.Via.Pc_sem k N T enc T_act p i`, `Via.translate tw`,
`Via.translate_ok T tw tw_ok u`, `Via.complete k N T enc cox dec dec_enc
T_act tw tw_ok e`.  `by2 l r (by decide +kernel) : Eqn (n + 2)` and
`ofList_map` (`⟪map⟫`) in `Narrow2` (flat namespace).

## Build times

Every module of this part checks in under 15 s of its own (given Mathlib and
the imports): `Lib/CircuitProp` ~10 s, `Lib/Engine` ~5 s, `Semantics` ~5 s,
`Kit` ~5 s, `Involutions` 1.6 s (kernel 0.6 s), `Width2` ~3 s, `Width3`
~8 s (elaboration 2.9 s, kernel 2.8 s).  Axioms of `Width3.complete₃`:
`propext`, `Classical.choice`, `Quot.sound`.

## Generators

`gen/common.py` parses the Agda's derivation text (`derive (lhs) (rhs)
(steps) refl`) and writes the Lean step for step.  `mk_involutions.py` and
`mk_width2.py` import and run the Agda's searches (`appA.py`, `width2.py`;
about 15 s each) and assert that they find the derivations of the checked-in
`Involutions.agda`, `Width2.agda`; `mk_width3.py` reads the Agda's saved
`width3_lemmas.json`.  All three regenerate the Lean modules byte for byte.
