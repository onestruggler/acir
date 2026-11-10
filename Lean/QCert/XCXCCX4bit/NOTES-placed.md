# Notes of the `placed` part (Placed, ToPlaced, Faithful, ByEvenRS, Narrow3, PlacedEngine, Equations4, Four, PFrames, Lib/Words)

## Modules

| Lean module | Agda | state |
|---|---|---|
| `Placed.lean` | `Placed.agda` | built |
| `ToPlaced.lean` | `ToPlaced.agda` | built |
| `Faithful.lean` | `Faithful.agda` | built |
| `ByEvenRS.lean` | `ByEvenRS.agda` | built |

## Representation and names (read this before using `Placed`)

* Namespaces: `QCert.XCXCCX4bit.Placed`, `…ToPlaced`, `…Faithful`,
  `…ByEvenRS` (one per module, as the other parts).  Open `Placed` for the
  alphabet.
* **Wires** `Wire := Fin 4` (abbrev).  The Agda's `_==_`, `_<<_` are `weq`,
  `wlt` (`Nat.beq`/`Nat.blt` on the values).  Lemmas: `weq_sound`,
  `weq_refl`, `weq_iff`, `neq : (!weq a b) = true → a ≠ b`, `not_weq_iff`,
  `wlt_neq`, `wlt_flip`, `okCX_iff`, `okCCX_iff` (all by `decide` over
  `Fin 4`).
* **Letters** `PG` with constructors `PG.Xₚ t`, `PG.CXₚ c t ok`,
  `PG.CCXₚ a b t ok` (the Agda's `Xᵖ`, `CXᵖ`, `CCXᵖ`; `ᵖ` is not an identifier
  character in Lean, `ₚ` is).  `ok : okCX c t = true` / `okCCX a b t = true`
  is an **auto-parameter** `:= by decide`, so a closed letter is written
  `PG.CCXₚ 1 3 0` (or `.CCXₚ 1 3 0` where the type is known); in long
  generated lists write `PG.CCXₚ 1 3 0` (qualified).  They are exported, so
  `open Placed` gives `Xₚ`, `CXₚ`, `CCXₚ`.  Proofs are irrelevant: two
  letters with the same wires are equal by `rfl`.  Match with
  `| .CXₚ c t ok => …`.
* `ι : PG → Circ 4` (the placement, `Fr sw (gate) (frame wires)`), `ιs :
  List PG → Circ 4` (the Agda's `ι*`, **direct recursion**: `ιs (g :: u) =
  ι g * ιs u` by `rfl`, `ιs [] = 1`), `ιw : Word PG → Circ 4` (the Agda's
  `ιʷ`, `ιw w = ιs (toList w)`; `ιw_mul`, `ιw_ofList`).  `ιs_append`
  is an **equation** `ιs (xs ++ ys) = ιs xs * ιs ys`;
  `ToPlaced.ιs_append'` is the Agda's `ι*-++` as a derivation.
* `semP : PG → Fun 4`, `semPs : List PG → Fun 4` (the Agda's `⟦_⟧ᵖ`,
  `⟦_⟧ᵖ*`; `semPs (g :: u) x = semPs u (semP g x)` by `rfl`,
  `semPs_append`), with `Semantics`' `Bits.get`/`Bits.update`.
  `sem_ok g : sem (ι g) ≐ semP g`, `ιs_sem u : sem (ιs u) ≐ semPs u`.
* `every p l` (the Agda's `every`, recursion, `every_iff`), `avoids m g`,
  `apart`, `disjoint g h`, `forallPG p` with `forallPG_sound` (decide `p`
  on all 28 letters by `decide +kernel` on `forallPG p = true`).
* Swap network `sw : ℕ → Circ 4`, `cox : Coxeter.Circuits.Coxeter 4 sw
  (VRel SRel 4)`, `s₀ s₁ s₂ : SG 4`, `Fc : CW 4`, `cX`, `cCX`, `cCCX`.
  `Fr` is `Coxeter.Circuits.Fr sw` (left-associated: `Fr sw b p = Pc sw 0 p
  * b * Pc sw 0 (inv p)`); `Fr_conj` is an **equation**, use `rw [← Fr_conj]
  at e` to split a frame `Fr sw b (r * p)`.
* `Fr_cong`, `conj_mul inv_l a b`, `peel`, `unconj inv_l e` (the Agda's
  module `_ {P P⁻} (inv-l)`: the hypothesis `inv_l : 4 ⊢ Pinv * P ≈ 1` is
  the first explicit argument).
* `ι_X t F h₀`, `ι_CX c t {ok} F h₀ h₁`, `ι_CCX a b t {ok} F h₀ h₁ h₂`,
  `ι_CCX'` (`ok` implicit: give `(ok := by decide)` when nothing else
  determines it, e.g. in a `have` without type).  The hypotheses are
  `act F 0 = t` etc. with `0 : Fin 4`; `act (F * G) x` needs `rw [act_mul]`
  (it does not reduce for a symbolic `F`).
* `shiftFr (w : Circ 3) : 4 ⊢ shift (Circuit.pad 0 w) ≈ Fr sw
  (Circuit.pad 1 w) Fc`; `X_up₁ X_up₂ X_up₃ CX_up₁ CX_up₂ CCX_up₁` (the
  Agda's `X↑₁` …); `ιX₀ … ιX₃`, `ιCX₁₀`, `ιCX₂₁`, `ιCX₃₂`, `ιCCX₁₂₀`,
  `ιCCX₂₃₁`, `ιCCX₂₃₀`; `ToPlaced.ιCX₀₁ ιCX₁₂ ιCX₂₃`.
* **Relabel** is a structure `{π, net, net_π}`; `Relabel.π_inj`, `S R`,
  `Sinv R` (the Agda's `S⁻`), `S_Sinv R`, `Sinv_S R` (the inverses as
  derivations).  `relabel R g`, `relabel_ι R g`, `relabel_ιs R u`,
  `relabel_eq R e` (the Agda's `relabel-≈`), `weq_π`, `avoids_relabel`,
  `every_avoids`.  `ccx`, `ccxBy` (the Agda's `ccx-by`), `ι_ccxBy`,
  `avoids_ccxBy`.  `distinct4`, `dist4`, `sel4`, `ρ4 a b c d` (the
  distinctness an auto-parameter `by decide`), `fromPerm f inj`, `τ m`,
  `τ_top`.
* `disj_comm g h (e : disjoint g h = true)`, `comm_via`, `distinct_append`.
* `lhs₇`, `rhs₇`, `rule7₀`, `rule7 R`.
* `Complete₃ : Prop` (a `def`), `low₂ … low₄`, `cut₂ … cut₄`, `lowW`,
  `cutW` (on the list of letters), `lowW_ok`, `low_ι`, `low_ιs`,
  `x ++ (b ∷ .nil)` for the Agda's `x V.++ (b V.∷ V.[])`,
  `gen_down`, `word_down`, and the section `Narrow`: `narrow_low complete₃
  u v hu hv e`, `narrow complete₃ m u v hu hv e`, `narrowP complete₃ m u v
  hu hv e` (the Agda's `narrowᵖ`; `e : semPs u ≐ semPs v`).
* `ToPlaced`: `pgl : Gn 4 → List PG`, `pgl_ok`, `pgL` (list version),
  `pg u = pgL (toList u)` (computable by the kernel on a concrete circuit),
  `pg_mul`, `pg_of`, `pg_ok u : 4 ⊢ u ≈ ιs (pg u)`.
* `Faithful`: `target`, `keeps`, `every_append` (the Agda's `every-++`),
  `targets`, `keep_by`, `keeps_from`, `imp`, `keeps_τ_check`, `keeps_τ`,
  `every_keeps_τ`, `Faithful m : Prop` (a `def`), `faithful f₃ m`.
* `ByEvenRS`: the Agda's module `Realisation enc dec dec-enc enc-dec R R-act`
  is a **structure** `ByEvenRS.Realisation` with those fields; `RL.Rs w`
  (the Agda's `R*`; `Rs_mul`, `Rs_of`, `Rs_one`), `RL.Rs_act`,
  `RL.Rs_sem`, `RL.rel_sem r`, `RL.Rs_cong R_rel h`, `translate tw`,
  `RL.translate_ok`, and `RL.complete R_rel tw tw_ok u v e` (the inner
  module `Complete`).  `R_act` is stated with `Symmetric.perm (f 16 x) i`.

## Build times

`Placed` about 8 s, `ToPlaced` under 1 s of its own (plus imports),
`Faithful` under 1 s, `ByEvenRS` under 1 s.
