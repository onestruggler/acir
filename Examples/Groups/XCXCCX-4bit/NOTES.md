# XCXCCX-4bit — working notes (conventions and plan)

Formalization of `pldi/four-bit-astra/` ("Block Normal Forms and Certified
Equations for Four-Bit Reversible Circuits"): the theory T = Figure 1's
rules (1)–(7) plus the PROP laws is sound and complete for four-wire
circuits over X, CX, CCX, and G₄ ≅ Alt(16).

## Conventions

* Wires: wire 0 is the bottom wire.  The paper numbers wires from the top
  (wire 1 = most significant bit), so on n wires its wire w is our wire
  n − w.  On four wires: paper 1,2,3,4 = our 3,2,1,0.
* Words are in diagram order: `w • v` is w then v (the paper's algebra is
  composition order; its drawings are diagram order).
* Letters (`Gen n`, Circuit.Base over `PGate` of Examples.Independence.Prop):
  `Xₗ = gate₁ ⌈ X-gate ⌉` (X on wire 0), `CXₗ = gate₂ ⌈ CX-gate ⌉` (control
  wire 1, target wire 0), `CCXₗ = gate₃ ⌈ CCX-gate ⌉` (controls wires 2, 1,
  target wire 0), `σₗ = gate₂ swap` (swap wires 0, 1); `g ↥` shifts a letter
  up one wire.  Words `X`, `CX`, `CCX`, `σ` are the one-letter circuits.
* Semantics (Semantics.agda): `Bits n = Vec Bool n`, wire 0 first;
  `⟦ w ⟧ : Bits n → Bits n`, `⟦ w • v ⟧ x = ⟦ v ⟧ (⟦ w ⟧ x)`; `_≐_` pointwise;
  `same n w v : Bool` decides `⟦ w ⟧ ≐ ⟦ v ⟧` (`same-sound`); `sound`.
* Derivability: `n ⊢ w ≈ v` (Lift-To-Prop of Circuit.Prop).  Rules on their
  own widths: `r1 … r7` (Syntactics.agda).
* Proof engine (Kit.agda = Examples.Independence.Engine at our gates):
  equations `Eqn n` (letter lists with a proof), `derive l r steps refl`,
  steps `perm ys` (same word up to commuting letters on disjoint wires) and
  `rw i e`; `sym⁼`, `lift⁼` (one wire up).  Rules as `r1⁼ … r7⁼`, swap rules
  `σσ⁼ σX⁼ σCX⁼ σσσ⁼ σCCX⁼`, all on the bottom wires of any width.
* Involutions.agda: `CX²⁼ : Eqn (₂₊ n)`, `CCX²⁼ : Eqn (₃₊ n)` (Appendix A).
* Width2.agda: `complete₂ : ⟦ u ⟧ ≐ ⟦ v ⟧ → 2 ⊢ u ≈ v` (Prop. B.2).
* Narrow2.agda: `by2 l r refl : Eqn (₂₊ n)` for two-wire letter lists with
  the same function (a two-wire step inside any derivation).
* Width1/Width3.agda: `complete₁`, `complete₃` (Props. B.1, B.3).
* EvenRS.agda (N): A_N by Reidemeister–Schreier from S_N (`Sch`, `f`,
  `_RS,_===_` with constructors order/braid₀/braid/far₀/far, `rs-complete`,
  `rs`, `rs-sem`).
* Placed.agda: placed letters `Xᵖ t`, `CXᵖ c t`, `CCXᵖ a b t` (a < b; wires
  `₀ ₁ ₂ ₃`), `ι`/`ι*` (placement by swap networks), `relabel-ι`,
  `disj-comm`, `rule7`, `Narrow` (parameterised by complete₃).
  Narrow3.agda: `by3` (three-wire steps, Kit level) and the placed `narrow`
  on any triple from `Width3.complete₃`.  PlacedEngine.agda: `Eqnᵖ`,
  `derive` with steps `perm` / `rw` / `narrow i k ys`, `r7at a b c d`,
  `relabel⁼`.  PlacedEngine and Kit share names (`perm`, `rw`, `derive`,
  `sym⁼`, `Step`, `run`): open only one of them in a module; don't open
  Narrow3 unqualified beside PlacedEngine (`narrow` clashes).
* Coxeter.agda (N): Symmetric.CoxeterFrames for N states: `Circuits T`,
  `Coxeter` record, `Complete` with `perm-complete′`, `Fr`, `Fr-conj`,
  `Comm≥`, `stab`, `frame≈`.
* ByCoxeter.agda: `Via k N T cox enc dec dec-enc T-act tw tw-ok` gives
  `complete` at width k from Coxeter relations for the T d.

## Typechecking

Only under the shared lock (other sessions use the same 9 GB WSL VM):

    wsl --exec bash -c "bash '/mnt/c/Users/BONES_~1/AppData/Local/Temp/claude/7c9dda3f4aa13c5c/ae7c51dd-1ee1-46c6-8581-484559681a82/scratchpad/tc.sh' Examples/Groups/XCXCCX-4bit/<Module>.agda"

(tc.sh: `flock ~/.agda-job.lock`, `agda +RTS -M3G`, timeout, prints errors of
this folder only, residency and time.)  One Agda run at a time; never pass
option flags such as `--call-by-name` on the command line.

## Python tools (gen/)

* `xc.py`: letters `(kind, shift)`, kind in X, CX, CCX, SW; `perm(word, n)`
  (states as ints, bit w = wire w).
* `derive.py`: `Lib` of equations (name, arity, lhs, rhs on the bottom
  wires), `canon` (trace normal form), `occurrences`, Agda emission.
* `search.py`: `Searcher(lib, narrow=[(m, Table(m), 'by2')])`, bidirectional
  BFS over rule rewrites and narrow steps (blocks on m adjacent wires),
  `derivation(name, arity, waypoints)` → Agda text of a `derive`.

## Plan (the paper's certificates, ~380k deductions, are too big for Agda)

1. Width ≤ 3 (Appendix B): done for 2; width 3 by the Coxeter presentation
   of S₈ (edge Toffolis along the Gray code 000,001,011,010,110,111,101,100).
2. Four wires, placed gates: an alphabet of gates on any wires, interpreted
   by conjugation with swap networks; a step on any triple of wires is
   justified by width-3 completeness.
3. Γ layer (wire t never a control): V ⋊ S₈ with V elementary abelian;
   derives the paper's equation (8).
4. Controlled A₈ (gates controlled by wire 1 acting on wires 2–4) via the
   Reidemeister–Schreier presentation of A₈ from S₈'s Coxeter presentation
   (index 2) and frames over S₈; K (gates not targeting wire 1) = A₈ ⋊ S₈.
5. G₄ via the Reidemeister–Schreier presentation of A₁₆ from S₁₆ (index 2),
   states ordered with the half x₁ = 0 first, so that every Schreier
   generator but one is a K-element and K's faithfulness decides the rest.
6. The paper's normal form N(E,B,S), gate absorption, G₄ ≅ Alt(16).
