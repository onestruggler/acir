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

## Build times

(see the end of this file; filled in as modules are built)

* `Lib/CircuitProp` ~10 s, `Lib/Engine` ~5 s, `Semantics` ~5 s, `Kit` ~5 s,
  `Involutions` 1.6 s (type checking 0.6 s).
