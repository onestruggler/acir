# Notes of the `groups` part (Coxeter, Lib, EvenRS, NFLib, EvenWord, LabelEngine)

## Modules

| Lean module | Agda | state |
|---|---|---|
| `Lib/Symmetric.lean` | what is used of `Examples/Groups/Symmetric` (Syntactics, Semantics, Interpretation, Soundness, Presentation, Surjectivity) | built |
| `Coxeter.lean` | `Coxeter.agda` (with the generic part of `Symmetric/CoxeterFrames`) | built |

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

## Build times

`Lib/Symmetric` about 16 s, `Coxeter` about 5 s (given Mathlib).
