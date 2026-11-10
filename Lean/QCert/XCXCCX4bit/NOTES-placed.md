# Notes of the `placed` part (Placed, ToPlaced, Faithful, ByEvenRS, Narrow3, PlacedEngine, Equations4, Four, PFrames, Lib/Words)

## Modules

| Lean module | Agda | state | own build time |
|---|---|---|---|
| `Placed.lean` | `Placed.agda` | built | ~4 s (two `decide +kernel` over the 28 letters) |
| `ToPlaced.lean` | `ToPlaced.agda` | built | < 1 s |
| `Faithful.lean` | `Faithful.agda` | built | < 1 s |
| `ByEvenRS.lean` | `ByEvenRS.agda` | built | < 1 s |
| `Lib/Words.lean` | `Presentation/Tactics/Words.agda` (`commutes`, `Associative.word-of-list`, `Commuting`) | built | < 1 s |
| `Narrow3.lean` | `Narrow3.agda` | built | < 1 s |
| `PFrames.lean` | `PFrames.agda` | built | < 1 s |
| `PlacedEngine.lean` | `PlacedEngine.agda` (with its four tests) | built | ~1 s |
| `Equations4.lean` | `Equations4.agda`, **generated** by `gen/mk_equations4.py` | built | ~10 s (elaboration 4 s, kernel 5 s) |
| `Four.lean` | `Four.agda`, **generated** by `gen/mk_four.py` | built | ~13 s (kernel 11 s; peak RSS 4.2 GB with the imports) |

Axioms of `Four.complete₄`, `Equations4.eq8E`, `Equations4.E3E`,
`PFrames.frame_eq`, `Placed.disj_comm`, `ToPlaced.pg_ok`: `propext`,
`Classical.choice`, `Quot.sound`.

## Generators

`gen/mk_equations4.py` and `gen/mk_four.py` are ports of the Agda's
generators of the same names, writing Lean.  Both import the Agda's
generator (`Examples/Groups/XCXCCX-4bit/gen/…`) for its data: `mk_equations4`
for `steps_of` (the replay of a `pg_results.json` search result as engine
steps) and `NAMES`; `mk_four` for `G`, `T`, `ALL`, `R` (BFS), `BASIC`,
`EXC`, which the Agda module computes when imported (it writes nothing then).
Run with WSL `python3` from `gen/`; they regenerate the checked-in Lean
byte for byte.  `mk_equations4.letter`, `lean_list`, `emit_step`, `emit`
write PlacedEngine derivations and can be reused for `BaseComm`
(`mk_basecomm.py`).

## Representation and names (read this before using `Placed`)

* Namespaces: `QCert.XCXCCX4bit.Placed`, `…ToPlaced`, `…Faithful`,
  `…ByEvenRS`, `…Words`, `…Narrow3` (plus `by3` in the flat namespace, as
  `by2`), `…PFrames`, `…PlacedEngine`, `…Equations4`, `…Four`.  Open
  `Placed` for the alphabet.
* **Wires** `Wire := Fin 4` (abbrev).  The Agda's `_==_`, `_<<_` are `weq`,
  `wlt` (`Nat.beq`/`Nat.blt` on the values).  Lemmas: `weq_sound`,
  `weq_refl`, `weq_iff`, `neq : (!weq a b) = true → a ≠ b`, `not_weq_iff`,
  `wlt_neq`, `wlt_flip`, `okCX_iff`, `okCCX_iff` (all by `decide` over
  `Fin 4`).  The Agda's `T (not (a == b))` is `(!weq a b) = true`.
* **Letters** `PG` with constructors `PG.Xₚ t`, `PG.CXₚ c t ok`,
  `PG.CCXₚ a b t ok` (the Agda's `Xᵖ`, `CXᵖ`, `CCXᵖ`; `ᵖ` is not an identifier
  character in Lean, `ₚ` is).  `ok : okCX c t = true` / `okCCX a b t = true`
  is an **auto-parameter** `:= by decide`, so a closed letter is written
  `PG.CCXₚ 1 3 0` (or `.CCXₚ 1 3 0` where the type is known); in long
  generated lists write `PG.CCXₚ 1 3 0` (qualified).  They are exported, so
  `open Placed` gives `Xₚ`, `CXₚ`, `CCXₚ`.  Proofs are irrelevant: two
  letters with the same wires are equal by `rfl`.  Match with
  `| .CXₚ c t ok => …`, `| .CXₚ 0 1 _ => …` (Fin literal patterns work; an
  impossible letter is `| .CXₚ 0 0 ok => nomatch ok`).
* `ι : PG → Circ 4` (the placement, `Fr sw (gate) (frame wires)`), `ιs :
  List PG → Circ 4` (the Agda's `ι*`, **direct recursion**: `ιs (g :: u) =
  ι g * ιs u` by `rfl`, `ιs [] = 1`; so `ιs [g] = ι g * 1`), `ιw : Word PG →
  Circ 4` (the Agda's `ιʷ`, `ιw w = ιs (toList w)`; `ιw_mul`, `ιw_ofList`).
  `ιs_append` is an **equation** `ιs (xs ++ ys) = ιs xs * ιs ys`;
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
  the first explicit argument).  `cl4 w` abbreviates `cl (PropRel SRel) 4 w`.
* `ι_X t F h₀`, `ι_CX c t {ok} F h₀ h₁`, `ι_CCX a b t {ok} F h₀ h₁ h₂`,
  `ι_CCX'` (`ok` implicit: give `(ok := by decide)` when nothing else
  determines it, e.g. in a `have` without type).  The hypotheses are
  `act F 0 = t` etc. with `0 : Fin 4`; `act (F * G) x` needs `rw [act_mul]`
  (it does not reduce for a symbolic `F`), on numerals `by decide` works.
* `shiftFr (w : Circ 3) : 4 ⊢ shift (Circuit.pad 0 w) ≈ Fr sw
  (Circuit.pad 1 w) Fc`; `X_up₁ X_up₂ X_up₃ CX_up₁ CX_up₂ CCX_up₁` (the
  Agda's `X↑₁` …); `ιX₀ … ιX₃`, `ιCX₁₀`, `ιCX₂₁`, `ιCX₃₂`, `ιCCX₁₂₀`,
  `ιCCX₂₃₁`, `ιCCX₂₃₀`; `ToPlaced.ιCX₀₁ ιCX₁₂ ιCX₂₃`; `r5_4` (rule (5) at
  width 4); `Pc_Fc`, `Pc_inv_Fc` (the networks of `Fc` are `σcInv 3`, `σc 3`).
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
* `Complete₃ : Prop` (a `def`; pass `@Width3.complete₃`), `low₂ … low₄`,
  `cut₂ … cut₄`, `lowW`, `cutW` (on the list of letters), `lowW_ok`,
  `low_ι`, `low_ιs`, `gen_down`, `word_down` (with `x ++ (b ∷ .nil)` for the
  Agda's `x V.++ (b V.∷ V.[])`), and the section `Narrow`:
  `Placed.narrow_low complete₃ …`, `Placed.narrow complete₃ m u v hu hv e`,
  `Placed.narrowP complete₃ m u v hu hv e`.  **Use `Narrow3.narrow`,
  `Narrow3.narrowP` (the Agda's `narrowᵖ`; `e : semPs u ≐ semPs v`),
  `Narrow3.narrow_low`**, which have `Width3.complete₃` applied.
* `ToPlaced`: `pgl : Gn 4 → List PG`, `pgl_ok`, `pgL` (list version),
  `pg u = pgL (toList u)` (computable by the kernel on a concrete circuit),
  `pgL_append`, `pg_mul`, `pg_of`, `pg_ok u : 4 ⊢ u ≈ ιs (pg u)`.
* `Faithful`: `target`, `keeps`, `every_append` (the Agda's `every-++`),
  `targets`, `keep_by`, `keeps_from`, `imp`, `imp_sound`, `keeps_τ_check`,
  `keeps_τ`, `every_keeps_τ`, `Faithful m : Prop` (a `def`, so
  `Faithful.Faithful 3`), `faithful f₃ m`.
* `ByEvenRS`: the Agda's module `Realisation enc dec dec-enc enc-dec R R-act`
  is a **structure** `ByEvenRS.Realisation` with those fields; `RL.Rs w`
  (the Agda's `R*`; `RL.RLs` on lists; `Rs_mul`, `Rs_of`, `Rs_one`),
  `RL.Rs_act`, `RL.Rs_sem`, `RL.rel_sem r`, `RL.Rs_cong R_rel h`,
  `Realisation.translate tw u`, `RL.translate_ok tw tw_ok u`, and
  `RL.complete R_rel tw tw_ok u v e` (the inner module `Complete`).
  `R_act` is stated with `Symmetric.perm (f 16 x) i` (the Agda's
  `SymI.⟦ f x ⟧ ⟨$⟩ʳ i`).
* `Lib/Words`: `Words.commutes Γ x y`, `Words.commutesWord`,
  `Words.Associative.wordOfList` (= `FreeMonoid.ofList`),
  `Words.Commuting.commCanonical comm less` and
  `Words.Commuting.lemma_comm_canonical comm less hc xs` — the Agda's
  `Commuting X Γ comm? less` with a Boolean `comm` and its soundness as a
  hypothesis; the algorithm is foundation's `Engine.canon` (the same
  translation of the same Agda code), reused, not copied.
* `Narrow3`: `by3 l r (by decide +kernel) : Eqn (n + 3)` (flat namespace,
  like `by2`), `Narrow3.narrow`, `Narrow3.narrowP`, `Narrow3.narrow_low`.
* `PFrames`: `T₄ d = Circuit.pad 1 (Width3.T d)`, `cox₄`, and, with `T₄`
  and `cox₄` fixed, `PFrames.Pc o p` (abbrev for `Coxeter.Circuits.Pc T₄ o
  p`), `PFrames.Fr b p`, `PFrames.CommGe j b`, `Pc_cong`, `perm_complete`,
  `Pc_inv`, `Pc_inv'`, `Fr_conj` (an equation), `stab`, `frame_eq` (the
  Agda's `frame≈`), `P_eq e : (1 + 3) ⊢ Circuit.pad 1 w ≈ Circuit.pad 1 v`.
  `SG CW act inv frame frame_act` are re-exported from `Coxeter`.
* `PlacedEngine`: `eqPG`, `eqPG_sound`, `eqL`, `eqL_sound`, `code`,
  `less`, `Γp` (the Agda's `Γᵖ`), `back`, `commP` (the Agda's `comm?`,
  Boolean) with `commP_sound`, `commCanonical`; equations `Eqnp`
  (constructor `Eqnp.eqnp`, fields `lhs`, `rhs`, `prf : 4 ⊢ ιs lhs ≈ ιs
  rhs`; the Agda's `Eqnᵖ`, `lhs⁼`, `rhs⁼`), `symE`, `relabelE R e`, `r7E`,
  `r7at a b c d`; steps **`Step.perm ys`, `Step.rw i e`, `Step.narrow i k
  ys`** (write them qualified: `Kit`'s `perm`/`rw` are visible in every
  `QCert.XCXCCX4bit.*` namespace); `rewriteAt`, `matchesAt`, `narrowAt`,
  `checkAt`, `narrowCheck` (the Agda's `narrow-check`), `run`, `check`,
  `splice`, `checkAt_sound`, `perm_sound`, `rw_sound`, `narrow_sound`,
  `run_sound`, `check_sound`, and `derive l r ss (h : check ss l r = true)
  : Eqnp`, closed by `(by decide +kernel)` (one Boolean per derivation).
* `Equations4`: `E2E E4E E8E E5E E6aE E6eE E6dE E6bE E6cE E7E E3E eq8E`
  (the Agda's `E2⁼` … `eq8⁼`), all `Eqnp`.
* `Four`: `sy c d` (a symbol, bounds auto-parameters), `syw [(c, d), …]` (a
  word of symbols: the Agda's `[ sy c d ]ʷ • …`), `enc`, `dec`, `dec_enc`,
  `enc_dec`, `t`, `R`, `R_act`, `R_tgt`, `RL : Realisation` (the Agda's
  module `RL`), `pick`, `pick_ok`, `kR`, `every_RLs`, `rel_by`, `R_rel f₃`,
  `tw₀`, `twL₀`, `Oks₀` (`.nil`, `.cons`), `okL₀`, `basic f₃ …`, `viaN`,
  `tw₁`, `twL₁`, `Oks₁`, `okL₁`, `tw`, `ok_X₀ f₃ …` (the Agda's `ok-X₀`),
  `tw_ok f₃`, `complete f₃ u v e`, `complete₄ f₃ e : 4 ⊢ u ≈ v` (the Agda's
  module parameter `f₃ : Faithful ₃` is the first argument of the theorems
  that use it).  The Agda's `F.RL.R*-act` is `Four.RL.Rs_act`, `F.RL.Complete
  F.R-rel F.tw F.tw-ok`'s `translate`/`translate-ok` are
  `Realisation.translate Four.tw` / `Four.RL.translate_ok Four.tw (Four.tw_ok f₃)`.

## Deviations (each also in its module header)

* `Placed`: associativity is the free monoid's (`cl` reasoning for
  conjugation); `Coxeter.frame` is total, distinctness only for
  `frame_act`; `Bits.get/update/append` for `V.lookup`, `_[_]%=_`, `_++_`.
* `Narrow3`: `narrow…` are definitions in the namespace `Narrow3` applying
  `Placed`'s to `Width3.complete₃` (the Agda opens the module publicly).
* `ByEvenRS`: the parameterised module is a structure.
* `PFrames`: the specialised names are abbreviations/theorems in `PFrames`.
* `PlacedEngine`/`Equations4`: `derive … (by decide +kernel)` for the
  Agda's `derive … refl`; `comm?` is a Boolean with a soundness lemma.
* `Four`: `R_act` decided per symbol over the 16 states (the Agda: per
  symbol and state); `syw` for words of symbols; `R_rel`'s five clauses
  through `rel_by`; the module parameter `f₃` an argument.
