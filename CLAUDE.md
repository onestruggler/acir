# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is the Agda formalisation accompanying the paper *"A Complete and Natural Rule Set for Multi-Qudit Clifford Circuits in All Odd Prime Dimensions"*. It is being prepared for submission to the Agda standard library. Tested with **Agda 2.8 + stdlib 2.3** (also works with Agda 2.7 + stdlib 2.2).

## Typechecking

```bash
# Typecheck via WSL (Agda 2.8, resolves dependencies automatically).
# These four roots cover the whole live library:
wsl --exec /home/onest/.cabal/bin/agda Examples/Groups/Symmetric/Theorems.agda
wsl --exec /home/onest/.cabal/bin/agda Examples/Amalgamations/CliffordT1.agda
wsl --exec /home/onest/.cabal/bin/agda Examples/Amalgamations/QutritCliffordT1.agda
wsl --exec /home/onest/.cabal/bin/agda Examples/Amalgamations/U33Di.agda
```

Use WSL Agda 2.8 (`wsl --exec /home/onest/.cabal/bin/agda`) for all files. The WSL install uses its own stdlib at `/home/onest/.agda/lib/agda-stdlib/`. The `.agda-lib` file (`qupit.agda-lib`) includes `.` and depends on `standard-library`.

**Always re-typecheck the four roots above after any edit to library files.** From PowerShell, invoke WSL directly (Git-Bash mangles the Linux path).

## Architecture

The library is layered bottom-up:

### Layer 0 — Notations (`Notations.agda`)
Numeral patterns `₀`–`₉`, successor patterns `₁₊`/`₂₊`/`₃₊`/`₄₊` (overloaded over ℕ and Fin), and the `auto` pattern (= `Eq.refl`).

### Layer 1 — Free monoid (`Word/`)
- **`Word/Base.agda`**: the `Word X` type (free monoid over generators `X`): constructors `[_]ʷ`, `ε`, `_•_`; powers `_^_`/`_^'_`; `wmap`, `wconcat`, `wconcatmap` and its postfix notation `_ʷ` (so `(f ʷ)` extends `f : X → Word Y` to words); folds `wfoldr`/`wfoldl`; the stateful traversals `_ᵗ`/`_ᵗ'` that drive coset enumeration; conjugation helpers `_ʰ`/`_ⁿ`/`_ʰ'`/`_ⁿ'`; `WRel X = Rel (Word X) 0ℓ`.
- **`Word/Properties.agda`**: `wmap`/`wconcat` fusion laws, `lemma-ʷ-∘`, `lemma-fʷ-w^n`, `wfoldr-cong`/`wfoldl-cong`, and `≡-dec` (decidable equality of words).

### Layer 2 — Group presentations (`Presentation/`)
- **`Base.agda`**: parameterised by `Γ : WRel X`. `_===_` is the raw relation; `_≈_` its congruence closure (refl/sym/trans/cong/assoc/left-unit/right-unit/axiom); `refl'` lifts `_≡_`; combinators `cleft_`, `cright_`, `_reversed`; `Alphabet = X`.
- **`Properties.agda`**: `≈-isEquivalence`, `word-setoid`, magma/semigroup/monoid structures and bundles; the associativity solvers (`to-list`/`from-list`, `mod-assoc`, `by-assoc`, `by-assoc-and`, and the pattern-guided `Pattern-Assoc.by-passoc`); word-power lemmas (`lemma-^-+`, `lemma-^^`, `word-comm`, …); `wfoldr`/`wfoldl` congruence lemmas.
- **`Definitions.agda`**: `_IsPresentationOf_` (group), `_IsMonoidPresentationOf_`, and `module SubPresentation` (`Soundness` & `Completeness` of a semantics ⟦_⟧ : Syn → Sem, i.e. ⟦_⟧ is a setoid embedding).
- **`GroupLike.agda`**: `Grouplike` (every generator has a left inverse) and `Group-Lemmas` (`_⁻¹`, cancellation, uniqueness of inverses, the group `•-ε-group`).
- **`Morphism.agda`**: parameterised by presentations `Γ`, `Δ`. Builders turning generator-level data into `IsMonoidHomomorphism`/`Monomorphism`/`Isomorphism` and the group versions, for both `(f ʷ)` and `wmap f`.

### Layer 3 — Constructions (`Presentation/Construct/`)
- **`Base.agda`**: amalgamated product `_⊕_` and related combinators on `WRel`.
- **`Properties/DirectProduct.agda`**, **`SemiDirectProduct.agda`**, **`SemiDirectProduct2.agda`**, **`NDirectProduct.agda`**, **`SugarProduct.agda`**: lift normal-form witnesses through the constructions.
- **`Properties/Amalgamation.agda`**: amalgamated free product with coset normal form (`AmalDataNF`, `ANF`).

### Layer — Circuits (`Circuit/`)
- **`Base.agda`**: parameterised by `Gate : ℕ → Set`. Wire-indexed generators `Gen`, `Circuit n = Word (Gen n)`, shifts `_↑`/`_↥ᵏ_`, and `Lift-Relation` extending any gate relation with the structural rules `cong↑`, `comm₁`, `comm₂`.

### Layer — Normalization (`Normalization/`)
- **`Base.agda`**: parameterised by `Γ : WRel X`. The normal-form witnesses `NormalFormWithoutInverse`, `NormalForm`, `BijectiveNormalForm`, `WeakNormalForm`; `UniqueNormalForm` and `by-normalization` (soundness + unique NF ⇒ completeness).
- **`Reidemeister-Schreier.agda`**: the injectivity/surjectivity engine. `Star-Injective-Simplified` proves `(f ʷ)` injective given a left inverse on generators; `Star-Injective-Full` (and its setoid variant) does coset enumeration and provides the Schreier section, right/left normal forms.
- **`CosetNF.agda`**: coset normal forms via Reidemeister–Schreier: `lemma-ᵗ-act` (letters-to-words action law), `module SingleLevel` (one level), `CosetTable` / `PackedCosetTable` (coset tables with a distinguished identity coset), `CosetTower` (iterate up an ℕ-indexed family).

### Layer 4 — Specific groups (`Presentation/Groups/`)
- **`Cyclic.agda`**: ℤ/nℤ presentation with `pres n`, `nfp n`, `nfp' n`.
- **`Sn.agda`**: symmetric group Sₙ via inductive Reidemeister–Schreier; exports `pres n`, `rel n`, `nfp n`, `nfp' n`.
- **`SnD.agda`**: the wreath product ℤ/4ℤ ≀ Sₙ as a semidirect product.
- **`Trivial.agda`**: the trivial group (two presentations, proved isomorphic).

### Layer 5 — Examples (`Examples/`)
- **`Groups/Symmetric/`**: completeness of the circuit presentation of Sₙ. `Theorems.agda` collects the main results (unique normal form, soundness, completeness for the loose endofunction semantics and the tight permutation semantics, and `IsPresentationOf`). Support: `Syntactics`, `Cosets`, `Normalization`, `Loose/*`, `Tight/*`.
- **`Amalgamations/CliffordT1.agda`**: the qubit Clifford+T gate set as an amalgamated product, ending in a monoid isomorphism.
- **`Amalgamations/QutritCliffordT1.agda`**: the qutrit Clifford+T analogue.
- **`Amalgamations/U33Di.agda`**: U₃(ℤ[½,i]) presented as a two-level amalgamated product.

## Key conventions

- `_===_` always means the raw relation (the axioms); `_≈_` always means the congruence closure.
- `[_]ʷ` injects a generator into `Word`. `[_]ₗ`/`[_]ᵣ` are left/right embeddings in products.
- `(f ʷ)` extends `f : X → Word Y` to `Word X → Word Y` (postfix `_ʷ` = `wconcatmap`).
- `(h ᵗ)` extends a coset action `h : C → Y → Word X × C` to words, threading the coset.
- `nfp` (`NormalFormWithoutInverse`) and `nfp'` (`NormalForm`) are the standard names for normal-form witnesses.
- `by-equal-nf` proves `w ≈ v` from `nf w ≡ nf v`; `by-assoc` proves `w ≈ v` from `to-list w ≡ to-list v`; `by-passoc` re-brackets guided by pattern words built from `□`.
- Files follow the agda-stdlib style guide (see `style-guide.md`): 72-char banner headers with library line `-- Presentations of groups`, `{-# OPTIONS --safe #-}`, imports sorted with `using` lists, `private variable` blocks, sentence-case section separators.
- `Examples/Groups/Symmetric/Theorems.agda` is the style exemplar: it re-states the main theorems with definitions imported openly and proofs imported qualified.

## Stdlib compatibility notes

- `Homomorphic₂` is imported from `Relation.Binary.Morphism.Definitions` (re-exported `Congruent`). That module is parameterised by `A B : Set`, so `A`/`B` are implicit at the call site — do **not** pass them explicitly.
- `IsMagmaHomomorphism` uses field `∙-homo` (renamed from `homo` in stdlib v3.0).
- `Data.Product.Relation.Binary.Pointwise.Dependent` is from stdlib master; it may not exist in older releases.
