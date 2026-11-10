# Notes of the `groups` part (Coxeter, Lib, EvenRS, NFLib, EvenWord, LabelEngine)

## Modules

| Lean module | Agda | state |
|---|---|---|
| `Lib/Symmetric.lean` | what is used of `Examples/Groups/Symmetric` (Syntactics, Semantics, Interpretation, Soundness, Presentation, Surjectivity) | built |
| `Coxeter.lean` | `Coxeter.agda` (with the generic part of `Symmetric/CoxeterFrames`) | built |
| `Lib/Alternating.lean` | what is used of `Examples/Groups/Alternating` (Parity, Semantics) | built |
| `EvenRS.lean` | `EvenRS.agda` | built |
| `NFLib.lean` | `NFLib.agda` | built |
| `EvenWord.lean` | `EvenWord.agda` | built |
| `LabelEngine.lean` | `LabelEngine.agda` | built |

## Representation (read this before using `Coxeter`)

* **Letters of `S_N`**: `Symmetric.SG N = {d : ℕ // 2 + d ≤ N}` (an `abbrev`);
  the Agda's letter `gate₂ σ-gate ↥ … ↥` (`d` shifts) is `⟨d, proof⟩`.  A
  concrete letter: `(⟨2, by decide⟩ : SG 4)`; as a word `Symmetric.s 2 (by decide)`
  or `FreeMonoid.of ⟨2, by decide⟩`.  Proofs are irrelevant, so
  `⟨2, p⟩ = ⟨2, q⟩` by `rfl`.  Pattern matching on a letter: `⟨0, _⟩`,
  `⟨1, _⟩`, …, and `⟨d + 7, h⟩` refuted by `omega` (for `N = 8`).
* `tr o g = o + g.1` (as the Agda's `tr`); `tr_zero : tr 0 g = g.1`.
  For a numeral letter `tr 0 ⟨2, _⟩` reduces to `2` by `rfl`/`decide`.
* **Words** are the framework's `Word (SG N) = FreeMonoid (SG N)`;
  `CW N := Word (SG N)`.  `inv w = FreeMonoid.reverse w`.
* **Action / permutation.**  Two readings, as in the Agda:
  - `act w x : Fin N` is the Agda's `actₙ w x` (operator order:
    `act (u * v) x = act u (act v x)`, `act_mul`).
  - `perm w : Equiv.Perm (Fin N)` is the Agda's `SymI.⟦ w ⟧`:
    `perm w i` is `SymI.⟦ w ⟧ ⟨$⟩ʳ i` (diagram order:
    `perm (u * v) i = perm v (perm u i)`, `perm_mul_apply`;
    `perm (u * v) = (perm u).trans (perm v)`, `perm_mul`), and
    `(perm w).symm x = act w x` holds by `rfl` (the Agda's
    `actₙ w x = SymI.⟦ w ⟧ ⟨$⟩ˡ x`).  `perm_of : perm (of g) i = swp g i`.
  - `swp g x` is `⟨CoxeterFrames.sw g.1 x.1, _⟩` (if `x = d` then `d+1`, if
    `x = d+1` then `d`, else `x`); all of these compute by `decide` on
    numerals (checked: `perm (of ⟨2,_⟩) 2 = 3`, `act (frame [3, 1]) 0 = 3`
    at `N = 4`).
* **Agda permutation vocabulary → Mathlib**: `Permutation′ N` is
  `Equiv.Perm (Fin N)`; `π ⟨$⟩ʳ i` is `π i`; `π ⟨$⟩ˡ i` is `π.symm i`;
  `π ∘ₚ ρ` (Agda, diagram order) is `π.trans ρ` (`= ρ * π` in Mathlib's
  group); `flip π` is `π.symm`; `inverseʳ`/`inverseˡ` are
  `Equiv.symm_apply_apply` / `Equiv.apply_symm_apply`.  Pointwise equality
  of permutations is `Equiv.ext`.
* **S_N's relation** is `Symmetric.SymRel N : WRel (SG N)` (order, braid,
  far at absolute indices; the Agda's `N VRel,_===_` of Symmetric).
  `Symmetric.sound`, `Symmetric.complete`, `Symmetric.go` / `go_sem` (the
  Agda's `proj₁ (SSurj.go N π)` / `proj₂ …`; `go` is `@[irreducible]`, use
  `go_sem`/`perm_go`), and `Symmetric.presentation : IsPresentationOf
  (SymRel N) sem` with `sem g = (perm (of g)).symm` (operator order:
  `FreeMonoid.lift sem w = (perm w).symm`, `lift_sem`).
* **Circuits** (`Coxeter.Circuits`, the Agda's `Cox.Circuits N T`):
  `Pc T o : Word (SG n) →* Word A` (a monoid hom; `Pc T o (of g) = T (o + g.1)`
  by `rfl`, `Pc_zero_of`), `structure Coxeter (N) (T) (Γ) : Prop` with
  fields `order : ∀ i, 2 + i ≤ N → Derivable Γ (T i * T i) 1`,
  `braid : ∀ i, 3 + i ≤ N → Derivable Γ (T i * T (i+1) * T i) (T (i+1) * T i * T (i+1))`
  (left-associated `*`, unlike the Agda's right-associated `•`),
  `far : ∀ i j, 2 + i ≤ j → 2 + j ≤ N → Derivable Γ (T i * T j) (T j * T i)`.
  The Agda's `Cox.Circuits.Complete N T cox` is not a module: each lemma
  takes `cox` first: `Pc_cong cox o b h`, `perm_complete' cox hn p q h`,
  `perm_complete cox p q h`, `Pc_inv cox o b p`, `Pc_inv' cox o b p`,
  `stab cox j m bd b cb r fix`, `frame_eq cox j m bd b cb p q h` (the Agda's
  `frame≈`).  `Fr T b p = Pc T 0 p * b * Pc T 0 (inv p)`;
  `Fr_conj` is an equation (`=`).  `CommGe N T Γ j b` is the Agda's
  `Comm≥ j b`.
* **Frames**: `Coxeter.frame ts : Word (SG n)` for `ts : List (Fin n)` is
  total (no distinctness argument); `frame_act ts (d : ts.Nodup) i x
  (h : ts[i.1]? = some x) : act (frame ts) i = x`.  `Distinct ts` is
  `ts.Nodup`, `Avoid t ts` is `t ∉ ts`; the Agda's `xs ‼ i` is `xs[i]?`.
* **Lifts**: `Coxeter.liftN j ρ : Equiv.Perm (Fin (j + m))` (identity below
  `j`, `liftN_lo`; `liftN_natAdd`), `liftN_eq_extendDomain` (for signs).
* Not reproduced (only the Agda's own proof of `stab` used them): `stripN`,
  `strip-ok`, `liftW`, `⟦liftW⟧`, `cyc`, `outs`, `act-↑-0`, `act-↑-suc`.


## Signs and even permutations (`Lib/Alternating`)

* `parity (w : Word A) : Bool := decide (FreeMonoid.length w % 2 = 1)`
  (`parity_one`, `parity_of`, `parity_mul : parity (w * v) = (parity w ^^ parity v)`,
  `parity_map`).
* `sign (π : Equiv.Perm (Fin n)) : Bool := decide (Equiv.Perm.sign π = -1)`,
  i.e. **Mathlib's sign** (not the Agda's parity of Symmetric's word):
  `sign_eq_false_iff`, `sign_eq_true_iff`, `sign_of w π h : sign π = parity w`
  (from `∀ k, perm w k = π k`), `sign_perm`, `sign_letter`, `sign_cong`,
  `sign_comp : sign (π.trans ρ) = (sign π ^^ sign ρ)` (the Agda's `sign-∘`),
  `sign_id`, `sign_one`, `sign_flip`.  Never evaluate `sign` on a numeral
  permutation; use `sign_of`.
* `Alt n := ↥(alternatingGroup (Fin n))`; `Alt.perm a`, `Alt.even a :
  sign (Alt.perm a) = false`, `Alt.mk π h`, `Alt.ext`.  **Order**: Mathlib's
  group on `alternatingGroup` is in operator order, so the Agda's
  `a ∙ᴬ b` (diagram order, `∘ₚ`) is `b * a` (`Alt.perm_mul`); likewise the
  Agda's `Permutation′-group` is `Equiv.Perm (Fin N)` with `π ∘ₚ ρ = ρ * π`.
  The MainTheorem agent decides how to state presentations (the circuits'
  diagram-order words against operator-order groups: `MulOpposite`, or
  `perm` vs `(perm w).symm`; `Symmetric.presentation` uses
  `FreeMonoid.lift sem w = (perm w).symm`).

## EvenRS

* `EvenRS.G N = SG N`; `letter n d q = ⟨d, q⟩`; `s d q` is `Symmetric.s d q`.
* `structure Sch (N)` with constructor **`Sch.γ c d p q`** (fields `c d p q`,
  `p : 1 ≤ d`, `q : 2 + d ≤ N`, proofs); `DecidableEq`.  Match on
  `⟨false, 3, _, _⟩` etc.  `y N c d p q := FreeMonoid.of (Sch.γ c d p q)`.
* `f N : Sch N → Word (G N)` (`f ⟨false,d,_,q⟩ = s d q * s 0 _`,
  `f ⟨true,d,_,q⟩ = s 0 _ * s d q`); the Agda's `(f ʷ)` is
  `FreeMonoid.lift (f N)`.
* `γw N c d q` (the Agda's `γʷ`), `RSRel N` with constructors `order c d p q`,
  `braid₀ c q`, `braid c d p q` (`q : 3 + d ≤ N`), `far₀ c e p q`,
  `far c d e p q r`, with `far_lo N q r`, `far_pos p q` (left-associated
  products: `y … * y … * y …`).
* `h N c g = (γw N c g.1 g.2, !c)`, `rs N c w = hstar (h N) c w` (with
  `rs_one`, `rs_of`, `rs_mul`), `Sim N` (the Agda's `_~_`), `h_wd`,
  `h_f_gen`, `rs_complete N u v e`, `s0w`, `rep`, `step`, `rs_rep`,
  `rs_approx` (the Agda's `rs-≈`), `rs_sem`, `rs_sound`, `rs_sound_sem`.
  In `rs_rep … rs_sound_sem` the `N` is implicit.

## NFLib

* `step`, `part`, `ts`, `weight`, `part_cong`, `ts_cong`, `part_length`,
  `ts_length`, `nth_in₁`/`nth_in₂` (`‼-in₁/₂`), `nth_append` (`‼-++`),
  `nth_total` (returns `{x // xs[k]? = some x}`), `nth_ts : (ts S)[k]? = some x
  → S x = decide (k < weight S)`, `ts_distinct : (ts S).Nodup`, `frameL`,
  `frameL_act`, `weight_sum`, `weight_perm π S : weight (fun i => S (π i)) =
  weight S`, `sign_liftN`, `sign_by_liftN`, `sign_sandwich ρ π : sign
  (ρ.trans (π.trans ρ)) = sign π`.  Also `mem_part₁`/`mem_part₂`,
  `part_nodup₁/₂`.  `avoid?`/`distinct?` are `decide`.

## EvenWord

* `EvenWord.Coset`: `Sch`, `f`, `rs` re-exported (`Coset.Sch 8` works),
  `rs_parity N c w : (rs N c w).2 = (c ^^ parity w)`, `coset_even`,
  `go_sem N π`, `coset_sign`, `coset_alt`, `syms N a` (`irreducible_def`,
  with `syms_def`), `sym_sem N a : ∀ i, perm (FreeMonoid.lift (f N) (syms N a)) i
  = Alt.perm a i`.
* `EvenWord.Lift.lift_sign j m w pw r ρ e` (the Agda's `r ∘ₚ (ρ ∘ₚ r)` is
  `r.trans (ρ.trans r)`).

## LabelEngine

* Parameters explicit, in the Agda's order: `eqLab c3 cok mul kok` (the
  Agda's `_≟ᴸ_ c3 cok mul kok`).  `Move L` with constructors
  `Move.H i`, `Hi i`, `C i`, `I i z`, `K i`, `Ki i x y` (qualify them in long
  lists: `LabelEngine.Move.H 3`).  `localStep` (Agda `local`), `index`,
  `atPos` (Agda `at`), `step`, `eqL`, `run`, `check eqLab c3 cok mul kok ms l r : Bool`.
* Soundness: `Xs X : List L → Word A` (`Xs X (x :: xs) = X x * Xs X xs`),
  `Xs_append` (an equation), `Xs_append'` (as a derivation),
  `check_sound eq_sound inv conj klein ms l r h : Derivable Γ (Xs X l) (Xs X r)`
  with `inv : ∀ x, Derivable Γ (X x * X x) 1`,
  `conj : ∀ x y, cok x y = true → Derivable Γ (X x * X y * X x) (X (c3 x y))`
  (left-associated), `klein : ∀ x y, kok x y = true → Derivable Γ (X x * X y) (X (mul x y))`,
  `eq_sound : ∀ x y, eqLab x y = true → x = y`.  A check closes by
  `decide` (tested on a toy alphabet).

## Build times

Every module of this part checks in under 20 s (given Mathlib):
`Lib/Symmetric` ~16 s, `Coxeter` ~5 s, `Lib/Alternating` ~10 s, `EvenRS`
~10 s, `NFLib` ~15 s, `EvenWord` ~5 s, `LabelEngine` ~10 s.  Axioms: only
`propext`, `Classical.choice`, `Quot.sound`.
