# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is the Agda formalisation accompanying the paper *"A Complete and Natural Rule Set for Multi-Qudit Clifford Circuits in All Odd Prime Dimensions"*. It is being prepared for submission to the Agda standard library. Tested with **Agda 2.8.0 + stdlib 2.4**, which is what the tagged submission artifact is verified against (earlier versions of the library were reported to work with Agda 2.7 + stdlib 2.2).

## Typechecking

```bash
# Typecheck via WSL (Agda 2.8, resolves dependencies automatically).
# On this branch the root states only the qupit chain, so that is all it
# reaches: the symplectic development and its simplified rules, the
# ProjectivePauli factor, the semidirect construction that assembles
# them, and the Clifford rule sets on top (Simplified-V1 → Paper-V0 →
# Paper-V1, plus Shared/PauliBase).
wsl --exec /home/onest/.cabal/bin/agda MainTheorems.agda
```

Everything else in the tree is **not** reached from the root here, and needs typechecking separately if you touch it: the symmetric, trivial and cyclic groups, the wreath product, the Clifford+T and U₃(ℤ[½,i]) amalgamations, `ProjectiveClifford/Qupit/Simplified-V2`, `ProjectiveClifford/Qubit/` and `Clifford/Qupit/`.

Use WSL Agda 2.8 (`wsl --exec /home/onest/.cabal/bin/agda`) for all files. The WSL install uses its own stdlib at `/home/onest/.agda/lib/agda-stdlib/`. The `.agda-lib` file (`qupit.agda-lib`) includes `.` and depends on `standard-library`.

**Always re-typecheck `MainTheorems.agda` after any edit to library files.** From PowerShell, invoke WSL directly (Git-Bash mangles the Linux path).

## Architecture

The library is layered bottom-up:

### Layer 0 — Notations (`Notations.agda`)
Numeral patterns `₀`–`₉`, successor patterns `₁₊`/`₂₊`/`₃₊`/`₄₊` (overloaded over ℕ and Fin), and the `auto` pattern (= `Eq.refl`).

### Layer 1 — Free monoid (`Word/`)
- **`Word/Base.agda`**: the `Word X` type (free monoid over generators `X`): constructors `[_]ʷ`, `ε`, `_•_`; powers `_^_`/`_^'_`; `wmap`, `wconcat`, `wconcatmap` and its postfix notation `_ʷ` (so `(f ʷ)` extends `f : X → Word Y` to words); folds `wfoldr`/`wfoldl`; the stateful traversals `_ᵗ`/`_ᵗ'` that drive coset enumeration; conjugation helpers `_ʰ`/`_ⁿ`/`_ʰ'`/`_ⁿ'`; `WRel X = Rel (Word X) 0ℓ`.
- **`Word/Properties.agda`**: `wmap`/`wconcat` fusion laws, `lemma-ʷ-∘`, `lemma-fʷ-w^n`, `wfoldr-cong`/`wfoldl-cong`, and `≡-dec` (decidable equality of words).

### Layer 2 — Group presentations (`Presentation/`)
- **`Base.agda`**: parameterised by `Γ : WRel X`. `_===_` is the raw relation; `_≈_` the monoid congruence it generates (refl/sym/trans/cong/assoc/left-unit/right-unit/axiom); `refl'` lifts `_≡_`; combinators `cleft_`, `cright_`, `_reversed`; `Alphabet = X`.
- **`Properties.agda`**: `≈-isEquivalence`, `word-setoid`, magma/semigroup/monoid structures and bundles; the associativity solvers (`to-list`/`from-list`, `mod-assoc`, `by-assoc`, `by-assoc-and`, and the pattern-guided `Pattern-Assoc.by-passoc`); word-power lemmas (`lemma-^-+`, `lemma-^^`, `word-comm`, …); `wfoldr`/`wfoldl` congruence lemmas.
- **`Definitions.agda`**: `_IsPresentationOf_` (group), `_IsMonoidPresentationOf_`, and `module SubPresentation` (`Soundness` & `Completeness` of a semantics ⟦_⟧ : Syn → Sem, i.e. ⟦_⟧ is a setoid embedding).
- **`GroupLike.agda`**: `Grouplike` (every generator has a left inverse) and `Group-Lemmas` (`_⁻¹`, cancellation, uniqueness of inverses, the group `•-ε-group`).
- **`Morphism.agda`**: parameterised by presentations `Γ`, `Δ`. Builders turning generator-level data into `IsMonoidHomomorphism`/`Monomorphism`/`Isomorphism` and the group versions, for both `(f ʷ)` and `wmap f`.

### Layer 3 — Constructions (`Presentation/Construct/`)
- **`Base.agda`**: amalgamated product `_⊕_` and related combinators on `WRel`.
- **`Properties/DirectProduct.agda`**, **`SemiDirectProduct.agda`**, **`NDirectProduct.agda`**, **`SugarProduct.agda`**: lift normal-form witnesses through the constructions. `SemiDirectProduct` takes a **word-valued** action `conj : H → N → Word N` (the relation `ConjRelʷ conj`); an earlier element-valued version, `conj : H → N → N`, was deleted once nothing imported it.
- **`Properties/Amalgamation.agda`**: amalgamated free product with coset normal form (`AmalDataNF`, `ANF`).

### Layer — Circuits (`Circuit/`)
- **`Base.agda`**: parameterised by `Gate : ℕ → Set`. Wire-indexed generators `Gen`, `Circuit n = Word (Gen n)`, shifts `_↑`/`_↥ᵏ_`, and `Lift-Relation` extending any gate relation with the structural rules `cong↑`, `comm₀`/`comm₁`/`comm₂` and `ω↑=ω`. `Lift-Relation` also proves `lemma-cong↑` and `comm-gate₀-w`/`comm-gate₁-w↑`/`comm-gate₂-w↑↑`, the comm rules extended from a single generator to a whole circuit.

### Layer — Normalization (`Normalization/`)
- **`NormalForm/Setoid.agda`**: setoid-valued normal-form witnesses on the stdlib `Function.Bundles` — `NormalFormInjective` = `Injection`, `BijectiveNormalForm` = `Bijection`, `NormalForm` = `RightInverse` (maps `word-setoid ⟶ₛ NF`) — plus `WeakNormalForm`. Uniqueness is **not** here.
- **`NormalForm/Uniqueness.agda`** (and `Uniqueness/Propositional.agda`, the same at the discrete setoid): `UniqueNormalForm`, `by-normalization` (soundness + unique NF ⇒ completeness) and the converse `by-completeness` (completeness + exact section `nf ∘ inv-nf ≗ id` ⇒ unique NF). `UniqueNormalForm` is indexed by the **section** `inv-nf`, not by a whole `NormalForm` record — so a client that already has the record passes `SNF.NormalForm.inv-nf nfp`, and `by-normalization` needs the record given explicitly (`{nfp}`), nothing else determining it. A second copy indexed by the record used to live in `Setoid.agda`; it is gone.
- **`NormalForm/Propositional.agda`**: `Normalization.NormalForm.Setoid Γ (setoid B)` re-exported for a plain carrier set `B` (an explicit module parameter) — the witnesses land in `≡` on `B` and all derivations are inherited. Types read `NormalForm Γ B` / `NormalFormInjective Γ B`. Because the re-export fixes the codomain to `setoid B`, the witnesses are function-aliases here, not record names: **opening or projecting a witness value goes through `Normalization.NormalForm.Setoid` directly (imported `as SNF`)** — e.g. `open SNF.NormalForm nfp renaming (…)` — while `Propositional` is used only for the `Γ B` types and record construction.
- **`Reidemeister-Schreier.agda`**: the injectivity/surjectivity engine. `Star-Injective-Simplified` proves `(f ʷ)` injective given a left inverse on generators; `Star-Injective-Full` (and its setoid variant) does coset enumeration and provides the Schreier section, right/left normal forms.
- **`CosetNF.agda`**: coset normal forms via Reidemeister–Schreier: `lemma-ᵗ-act` (letters-to-words action law), `module SingleLevel` (one level; its `Transfer.Unique` derives `nf' ∘ gg ≡ id` for the transported NF from base exactness + coset exactness of the table on sections, via cancellation and R–S injectivity), `CosetTable` / `PackedCosetTable` (coset tables with a distinguished identity coset), `CosetTower` (iterate up an ℕ-indexed family).

### Layer 4 — Specific groups (`Examples/Groups/`)
- **`Cyclic/`**: ℤ/nℤ. `Syntactics` (the relation `_Cn,_===_` over a one-element alphabet), `Presentation`, `Normalization`, `Theorems`.
- **`Trivial/`**: the trivial group, two presentations proved isomorphic. Everything is derived once from the single hypothesis that every generator is `≈ ε` (`gen≈ε`), then instantiated twice, so the directory is a **generic layer plus two instances**.
  - Generic, at the root, each parameterised by `(Γ, gen≈ε)`: `Normalization` (`w≈ε`, `nf`/`nfp`/`nfp'`), `Interpretation` (`⟦_⟧₀`, `GS`, `fʷ-cong-ax`, `grouplike`), `UniqueNormalForm` (`unfp`). `Semantics` is the shared target (`Terminal.group`, as `gp`) and takes no parameters.
  - **`Presentation1/`** is `⟨ ⊥ ∣ ⟩` (`EmptyRel`), **`Presentation2/ A`** is `⟨ A ∣ w = ε ⟩` (`TrivialRel`). Each has the same five modules: `Syntactics` supplies `pres` and `gen≈ε` (the only real content); `Normalization`, `Interpretation`, `UniqueNormalForm` just instantiate their generic namesakes; `Presentation` assembles `subpresentation`/`presentation`. Clients wanting the trivial group as a base case take `nfp`/`nfp'`/`gp`/`presentation` off `Presentation1.Presentation` (`NDirectProduct` does, at width 0).
  - `Presentation-Equivalence B` gives the monoid isomorphism between the two — a syntactic statement that never touches the semantics.
  - Note `gp` is re-exported, not abstracted over the module parameter, so it is `Presentation2.Presentation.gp`, never `.gp A`; `presentation` does take `A`.
- **`Symmetric/`**, **`Symplectic/`**, **`Clifford/`**, **`ProjectiveClifford/`**, **`Pauli/`**, **`ProjectivePauli/`**: see Layer 5.

There is no longer a `Presentation/Groups/`: it held a second Sₙ and a hand-rolled ℤ/4ℤ ≀ Sₙ, both over an inductive alphabet rather than circuit generators, and both are gone. The wreath product now comes from `Examples/Construct/SemiDirectProduct/SnD.agda`, which supplies `pres`, `nfp` and `nfp'` over the `Examples/Groups/Symmetric` alphabet.

### Layer 5 — Examples (`Examples/`)
- **`Groups/Symmetric/`**: completeness of the circuit presentation of Sₙ. There is no `Theorems.agda` façade — `MainTheorems` takes the five results (presentation, unique normal form for each semantics, soundness, completeness) straight from the modules that prove them. The layout follows the two chains: the **permutation** one is at the top level (`Semantics`, `Interpretation`, `Soundness`, `UniqueNormalForm`, `Surjectivity`, `Presentation`) and reaches a full presentation — `Semantics` is the target group alone and mentions no syntax, `Interpretation` is `⟦_⟧`/`⟦_⟧ᵍ`/`⟦↑⟧`, and `Soundness` is that `⟦_⟧` respects the relations; the **endofunction** one is `SubPresentation/` (`Semantics`, `Interpretation`, `UniqueNormalForm`, `SubPres`) and stops at a setoid embedding, since endofunctions are not all denotations. `Presentation` splits like Symplectic's: `subpresentation` needs only normalization, and `Surjectivity` is what promotes it. Shared support: `Syntactics`, `Cosets`, `Normalization`. `Completeness.agda` and `IndexedAction.agda` typecheck but nothing imports them.
- **`Groups/ProjectiveClifford/Qupit/`**: the paper's own subject. For an odd prime p, the qupit Clifford circuits read **modulo scalars** present `Pauli n ⋊ Sp(2n, ℤ/pℤ)`. Four rule sets over the same alphabet (Symplectic's `H`, `S`, `CZ`) — Simplified-V1, Simplified-V2, Paper-V0, Paper-V1 — each shown to present that group by transport from the one below it, over a base (`SemiDirect/`, on a different alphabet) that does the real work. Every layer above the base is an isomorphism plus a composition, which is why the stack is cheap to extend and why no rule set re-proves what another already has.
  - **`SemiDirect/`** is the base and defines `Pauli⋊Sp`. `Presentation` feeds the generic `SemiDirectProduct` machinery its two factors — `Symplectic.Simplified` for the symplectic part, `ProjectivePauli` for the Pauli part — together with `ConjAction`'s two well-definedness proofs for the conjugation action. Every input is a theorem, so it is unconditional.
  - **`Simplified-V1/`** is where the mathematics lives: the Pauli calculus (`Lemmas`, `LemmasXZ`, `LemmasCZ`, `SemiM`), the Ex-conjugation rules (`ExRules`), `Forward`, `Soundness`, a rewriting tactic layer (`Tactics`), and `Iso` onto the semidirect relation.
  - **`Paper-V0/`** is Figure 1 with the multiplier spelled over `R = S • Z^½`, as `RHR x x⁻¹`; 16 group-specific rules. Its `Iso` proves it isomorphic to Simplified-V1 and exports **`v1⇒pap`**, which transports Simplified-V1 theorems into its theory — which is why its `Lemmas` derives Selinger's c10–c15, the lower-wire rules and the swap calculus natively.
  - **`Paper-V1/`** is the same rules with the multiplier spelled over `S`, as `SHS' x⁻¹ x`, and 15 rules rather than 16: `(S • H) ^ 3 = ε` is a theorem here, not an axiom, because under that spelling `M₁` *is* that word and `M-power` at `k = 0` already gives it. `Iso` is the identity on words onto Paper-V0. `Lemmas/` carries only what that needs (`OneWire`, `GroupLike`, `XZ`) — the Ex-conjugation and three-wire layers it inherited from Paper-V0 were removed, since the isomorphism transports all of it.
  - **`Shared/PauliBase.agda`** is the relation-agnostic Pauli calculus, instantiated at whichever rule set needs it. `Calculus` rests on the axioms both spellings share; `BridgeCalc` adds `X • Z ≈ Z • X` as a *hypothesis* — the one fact whose proof genuinely differs between them — and builds the bridge between the R- and S-spellings of the multiplier, plus `MulZ`/`SemiMR` for carrying a Pauli across it.
  - **`Simplified-V2/`** transports the V1 theorem once more along an identity isomorphism. Nothing imports it.
- **`Groups/ProjectiveClifford/Qubit/`**: the qubit analogue (`CliffordExtension`, `Cocycle`, `ExtensionPresentation`, a `Selinger/` subtree). Self-contained — nothing outside the directory imports it.
- **`Amalgamations/CliffordT1.agda`**: the qubit Clifford+T gate set as an amalgamated product, ending in a monoid isomorphism.
- **`Amalgamations/QutritCliffordT1.agda`**: the qutrit Clifford+T analogue.
- **`Amalgamations/U33Di.agda`**: U₃(ℤ[½,i]) presented as a two-level amalgamated product.

## Key conventions

- `_===_` always means the raw relation (the axioms); `_≈_` always means the monoid congruence it generates (a congruence for `•`, closed under the monoid laws).
- `[_]ʷ` injects a generator into `Word`. `[_]ₗ`/`[_]ᵣ` are left/right embeddings in products.
- `(f ʷ)` extends `f : X → Word Y` to `Word X → Word Y` (postfix `_ʷ` = `wconcatmap`).
- `(h ᵗ)` extends a coset action `h : C → Y → Word X × C` to words, threading the coset.
- `nfp` (`NormalFormInjective`) and `nfp'` (`NormalForm`) are the standard names for normal-form witnesses.
- `by-equal-nf` proves `w ≈ v` from `nf w ≡ nf v`; `by-assoc` proves `w ≈ v` from `to-list w ≡ to-list v`; `by-passoc` re-brackets guided by pattern words built from `□`.
- Files follow the agda-stdlib style guide (see `style-guide.md`): 72-char banner headers with library line `-- Presentations of groups`, `{-# OPTIONS --safe #-}`, imports sorted with `using` lists, `private variable` blocks, sentence-case section separators.
- `MainTheorems.agda` is the style exemplar: it re-states the main theorems with definitions imported openly and proofs imported qualified, each section's banner naming the module the proof lives in. It is also the only façade — the per-development `Theorems.agda` layer was removed for the symmetric group, whose results MainTheorems now takes straight from `Presentation`, `UniqueNormalForm` and `SubPresentation/*`.

## Stdlib compatibility notes

- `Homomorphic₂` is imported from `Relation.Binary.Morphism.Definitions` (re-exported `Congruent`). That module is parameterised by `A B : Set`, so `A`/`B` are implicit at the call site — do **not** pass them explicitly.
- `IsMagmaHomomorphism` uses field `∙-homo` (renamed from `homo` in stdlib v3.0).
- `Data.Product.Relation.Binary.Pointwise.Dependent` is from stdlib master; it may not exist in older releases.
