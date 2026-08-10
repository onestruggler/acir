# Repo survey (P1) — verified facts for the paper
All claims below were verified on 2026-07-09/10 by reading the files and/or
typechecking with Agda 2.8 + stdlib 2.3 (WSL). Quote code only from here or by
re-reading the named files. NEVER cite the broken files as results.

## 0. Typecheck status map

GREEN (verified, citable as theorems):
- Examples/Groups/Symmetric/Theorems.agda   (standard root 1)
- Examples/Amalgamations/CliffordT1.agda    (root 2)
- Examples/Amalgamations/QutritCliffordT1.agda (root 3)
- Examples/Amalgamations/U33Di.agda         (root 4)
- Examples/Groups/ProjectivePauli/Presentation.agda   (EXIT=0 checked)
- Examples/Construct/SemiDirectProduct/SnD.agda (wreath; EXIT=0)
- Presentation/Construct/Properties/Extension.agda (EXIT=0; despite a stale
  "remaining goal" comment at line ~101 the file typechecks under --safe)
- Examples/Construct/DirectProduct/S3xC5/Semantic.agda (EXIT=0)
- Presentation/Groups/SnD.agda (old wreath-as-NF file; EXIT=0)
- Examples/Groups/Cyclic/Theorems.agda, Examples/Groups/Trivial.agda (in root closures)

STATUS FLIPS (2026-07-10, after user's Clifford-pres addition):
- Examples/Groups/ProjectivePauli/Semantics.agda — NOW GREEN (user fixed the metas).
- Examples/Groups/ProjectiveClifford/Qubit/Presentation.agda — NEW, GREEN (143 lines):
  Clifford-pres n = extension-presentation (Γ-H ⊕^ n) (n QRel,_===_) conj corr
  — the n-qubit Clifford relation set as a group extension (Selinger
  1310.6813 structure: 1 → phaseless Pauli → Clifford → Sp(2n,2) → 1);
  conj = vecToWord ∘ act1 ∘ genToVec (word-valued symplectic action);
  corr = p=2 cocycle: order-S ↦ Z₀, cong↑ r ↦ shiftPauli (corr r), _ ↦ ε
  (S² = Z is the only non-lifting relator; global phases die in phaseless
  Pauli; odd p splits → semidirect). Verified numerically per file header.
  This is a DEFINITION (relation set), not yet an IsPresentationOf theorem.
- Examples/Groups/Symplectic/{Symplectic-Derived,Action}.agda — green (in
  Clifford-pres closure). Symplectic gens: H-gen : ℤ₄ →, S-gen : ℤₚ →,
  CZ-gen : ℤₚ → (parameterized powers); QRel: order-S (S^p), order-H (H⁴),
  order-SH ((SH)³), comm-HHS, order-CZ, comm-CZ-S↓/↑, far-comm, cong↑.
- Examples/Groups/Symplectic/NF-Inj.agda — STILL RED (exit 42): the
  staircase normal-form tower remains WIP.
- Stats deltas: verified examples 32→35 files / 8,372→8,962 lines; WIP
  118/67,606; Zp (3/2,942) counted in the green closure; totals 191/89,355.

RED / WIP (do NOT claim; may mention as work-in-progress):
- Examples/Construct/DirectProduct/S3xC5/Presentation.agda — ParseError 47.40
  (presentation upgrade commented out; sub-presentation WIP)
- Examples/Groups/ProjectivePauli/Semantics.agda — UnsolvedMetaVariables 257–304
  (relating ⊗-group to the Vec-based Pauli carrier)
- Examples/Groups/Symplectic/** — 100+ files, depends on Pauli/Semantics →
  blocked. This is the in-progress multi-qudit Clifford/symplectic completeness
  (companion paper "A Complete and Natural Rule Set for Multi-Qudit Clifford
  Circuits in All Odd Prime Dimensions"). Symplectic/XZ.agda has an nfp'.

## 1. Size (wc -l, 2026-07-09)
- Total: 190 .agda files, 89,212 lines (excl. paper/).
- Core library: Word 2/265, Presentation 18/6912, Normalization 6/1639,
  Circuit 1/121, ForStdlib 7/865, Notations 1/43  → 35 files, 9,845 lines.
- Zp (modular arithmetic for qudits) 3/2942.
- Examples: 152 files / 76,425 lines, of which Symplectic+Pauli WIP tree is
  120 files / 68,053 lines. Verified examples ≈ 32 files / ~8.4k lines.
- Verified (green) closure ≈ 19k lines; WIP symplectic push ≈ 68k more.

## 2. Layer map with key definitions (all verified quotes)

### Word/Base.agda — free monoid
`data Word (X : Set) : Set where [_]ʷ : X → Word X ; ε : Word X ; _•_ : Word X → Word X → Word X`
- Powers `_^_` (right-assoc), `_^'_` (left-assoc); `wmap`, `wconcat`,
  `wconcatmap`; postfix `_ʷ = wconcatmap` "the unique monoid homomorphism
  extending f" (their comment).
- Stateful traversals (coset enumeration driver):
  `_ᵗ : (C → Y → Word X × C) → (C → Word Y → Word X × C)` threading the coset
  left-to-right; `_ᵗ'` right-to-left mirror.
- Conjugation helpers `_ʰ _ⁿ _ʰ' _ⁿ'` (element- and word-valued).
- `WRel X = Rel (Word X) 0ℓ`.

### Presentation/Base.agda — presented monoid (parameterised by Γ : WRel X)
`_===_ = Γ` (raw axioms) and THE core congruence (quote verbatim):
```agda
data _≈_ : WRel X where
  refl  : w ≈ w
  sym   : w ≈ v → v ≈ w
  trans : w ≈ v → v ≈ u → w ≈ u
  cong  : w ≈ w' → v ≈ v' → w • v ≈ w' • v'
  assoc      : (w • v) • u ≈ w • (v • u)
  left-unit  : ε • w ≈ w
  right-unit : w • ε ≈ w
  axiom      : w === v → w ≈ v
```
Plus `refl' : w ≡ v → w ≈ v`, combinators `cleft_`, `cright_`, `_reversed`.

### Presentation/Definitions.agda — presentation records
- `record _IsPresentationOf_ (_===_ : WRel X) (G : Group a ℓ)`: fields
  `gl : Grouplike _===_`, `⟦_⟧ : Word X → Group.Carrier G`,
  `iso : IsGroupIsomorphism` from the word group `GL.•-ε-group` (Word X / ≈
  with inverses from grouplike) to G. Similarly `_IsSubPresentationOf_` (mono),
  `_IsMonoidPresentationOf_` / `_IsSubMonoidPresentationOf_` (no gl needed).
- Upgrades: `isPresentationOf : sub → Surjective ⟦_⟧ → IsPresentationOf`;
  `monoidPresentation⇒presentation` (grouplike monoid presentation of
  Group.monoid G ⇒ group presentation — uses ForStdlib
  isMonoidHomomorphism⇒isGroupHomomorphism); `subMonoidPresentation⇒subPresentation`.

### Normalization/NormalForm/Setoid.agda — THE NF zoo (module params Γ, NF setoid)
Witnesses are stdlib Function.Bundles ON THE NOSE (their header comment):
- `NormalFormInjective` = `Injection word-setoid NF` (fields nf, nf-cong,
  nf-injective); derived `by-equal-nf : nf w ≈ₙ nf v → w ≈ v` and
  `≈-dec : Decidable _≈ₙ_ → Decidable _≈_` (via-injection) — DECIDES THE WORD
  PROBLEM.
- `NormalForm` = `RightInverse word-setoid NF` (nf + section inv-nf,
  inverseʳ); derives inv-nf∘nf=id, `normalize = inv-nf ∘ nf`,
  normalize-idempotent, nf-injective (so NormalForm ⇒ NormalFormInjective).
- `BijectiveNormalForm` = `Bijection`; yields NormalForm.
- `WeakNormalForm`: plain anf : Word X → |NF|, injective only, NO congruence.
- CONSTRUCTIVE-STRENGTH point for the paper (outline: "nf-injective is
  strictly weaker than section+retraction"): NormalForm ⇒ NormalFormInjective
  (proved, line ~105). Converse needs to REALIZE each normal form as a word —
  i.e. a section — which an Injection does not provide constructively (a
  surjection onto the image is not enough to choose representatives without
  choice). State carefully: over classical logic with choice, an injective nf
  with nf-image-decidability can be upgraded; in Agda's constructive setting
  the section is genuine extra data. (Write precise prose; do not overclaim a
  formal counterexample — the repo does not contain one.)
- `UniqueNormalForm` (over semantics ⟦_⟧ into setoid Sem, w.r.t. a NormalForm):
  field `unique : ⟦ inv-nf u ⟧ ≈₂ ⟦ inv-nf v ⟧ → u ≈ₙ v` — "normal forms with
  equal denotations are equal".
- `by-normalization : UniqueNormalForm nf → Congruent ⟦_⟧ → Injective ⟦_⟧`
  — SOUNDNESS + UNIQUE NF ⇒ COMPLETENESS (adequacy). THE central lemma.
- `SurjSem.by-normalization-wsurj`: ⟦_⟧∘inv-nf surjective + sound ⇒ ⟦_⟧
  surjective.
- `Propositional.agda` re-exports at `Eq.setoid B` for plain carriers.

### Normalization/Reidemeister-Schreier.agda (674 lines)
- `Star-Injective-Simplified Γ Δ` › `Reidemeister-Schreier-Simplified f g
  well-defined left-inv-gen`: if g : Y → Word X is a generator-level left
  inverse of f respecting Δ's axioms, then `(f ʷ)` is injective
  (`fʷ-inj`), `(g ʷ)` surjective. (Retraction argument, no cosets.)
- `Star-Injective-Full-Setoid Γ Δ Cₛ I` — coset enumeration with a SETOID of
  cosets; `Star-Injective-Full` = the ≡ special case, submodule
  `Reidemeister-Schreier-Full` + `RightAction` (Schreier section, left/right
  NFs). This is the monoid-level Reidemeister–Schreier engine.

### Normalization/CosetNF.agda (700+ lines)
- `module SingleLevel Γ Δ C I f h [_]` — data: subgroup pres Γ (letters X),
  group pres Δ (letters Y), coset set C, identity coset I, embedding
  f : X → Word Y, coset action/Schreier table h : C → Y → Word X × C, section
  [_] : C → Word Y. `module Transfer` takes THE FIVE HYPOTHESES (quote):
  (1) `h=⁻¹f-gen : ([ x ]ʷ , I) ~ (h ᵗ) I (f x)` (h inverts f at I);
  (2) `h-wd-ax` (h respects Δ-axioms, per coset);
  (3) `f-wd-ax` (f respects Γ-axioms);
  (4) `[I]≈ε`;
  (5) `h=ract : [ c ] • [ b ]ʷ ≈₂ (f ʷ)(h c b .proj₁) • [ h c b .proj₂ ]`.
  Yields: `nf = (h ᵗ) I : Word Y → Word X × C`, well-definedness, and the
  transports `nfp : NormalFormInjective Γ NF → NormalFormInjective Δ (NF × C)`,
  `nfp'` (same for NormalForm). KEY INTUITION: each level multiplies the
  normal form by one coset "digit".
- `CosetTable` + `record PackedCosetTable P₁ P₂` — same data with C ⊎ ⊤ cosets
  (distinguished identity coset), packaged as one value (fields C, f, h, [_]ₒ,
  hcme, htme, htme~, hcme~, h-wd-ax, f-wd-ax, h=ract).
- `module CosetTower X P Cᶜ` — ℕ-indexed family; `record Extension n` = one
  level of coset data P n → P (suc n) with the five hypotheses;
  `tower-carrier NF₀ (suc n) = tower-carrier NF₀ n × Cᶜ n` — the MIXED-RADIX
  carrier, one digit per level.

### Presentation/Construct/Base.agda — products of presentations
- Embeddings `[_]ₗ = wmap inj₁`, `[_]ᵣ = wmap inj₂`.
- `data _⋄_⋄_ Γ₁ Γ₂ Γ₃ : WRel (A ⊎ B)` with constructors left/right/mid —
  "the mixed component Γ₃ is what distinguishes the various products".
- Primitive mixed relations: `EmptyRel`; `TrivialRel` (everything ≈ ε);
  `CommRel` (comm : [a]ₗ•[b]ᵣ === [b]ᵣ•[a]ₗ); `ConjRel conj` (element-valued
  conjugation); `ConjRelʷ conj` (WORD-valued: [h]ᵣ•[n]ₗ === [conj h n]ₗ•[h]ᵣ);
  `AmalgRel f₁ f₂` (amal : [f₁ m]ₗ === [f₂ m]ᵣ); `SugarRel f`
  (desugar : [inj₁ m]ʷ === [f m]ᵣ — definitional extension).
- Products: free `Γ * Δ = Γ ⋄ Δ ⋄ EmptyRel`; direct `Γ ⊕ Δ = … CommRel`;
  n-fold `Γ ⊕^ n` over `A ⊎^ n`; semidirect `Γ ⋊ Δ ⋆ conj = … ConjRel conj`;
  amalgamated `Γ * Δ ⋆ f₁ ⋆ f₂ = … AmalgRel f₁ f₂`.
- `LeftRightCongruence`: lefts/rights lift factor congruences into the join.
- NF transport: `anfpₗ/ᵣ(')` (union), `mono-anfp`, `mono-nfp` (pull back along
  monoid mono), `iso-nfp'` (pull back NormalForm along monoid iso).

### Circuit/Base.agda (121 lines, parameterised by Gate : ℕ → Set)
```agda
data Gen : ℕ → Set where
  gate₁ : Gate 1 → Gen (₁₊ n)
  gate₂ : Gate 2 → Gen (₂₊ n)
  _↥   : Gen n → Gen (₁₊ n)
Circuit n = Word (Gen n)
```
- Design note IN THE FILE: "Indices begin with suc (no top-level addition) so
  Agda's coverage checker can solve unification goals by injectivity of ₁₊
  alone, avoiding stuck Diophantine equations of the form arity + k ≟ target."
  (proof-engineering point for the paper).
- `_↑ = wmap _↥` circuit shift; `_↥ᵏ_`, `_↑ᵏ_` (k on the LEFT of + to avoid
  n+0≢n); `module Lift-Relation SRel` adds the structural rules shared by all
  circuit presentations:
  `srel` (embed), `cong↑` (shift congruence), `comm₁`, `comm₂` (a gate at the
  bottom commutes with any generator shifted past its arity) — giving
  `_VRel,_===_`; `lemma-cong↑` lifts the whole congruence one wire up.

### Presentation/Properties.agda, Tactic/
- ≈-isEquivalence, word-setoid, •-ε-monoid; StarCongruence.fʷ-cong (extends
  f-wd-ax from axioms to the full congruence).
- Solvers: `by-assoc` (re-associate via to-list normalization: proves w ≈ v
  from to-list w ≡ to-list v — used HUNDREDS of times in the case studies),
  `by-passoc` (pattern-guided re-bracketing with □ patterns),
  AssociativitySolver module AS. GroupLike: `Grouplike Γ = every generator has
  a left inverse`, `Group-Lemmas` derive `_⁻¹` on words, cancellation,
  `•-ε-group` (the word group).
- Presentation/Morphism.agda: `StarIsomorphism Γ Δ f g fwd finv gwd ginv`
  builder → `isMonoidIsomorphism` for (f ʷ) — used as the last step of all
  three amalgamation case studies.
- Normalization/StarPresentation.agda: `MonoidSem mon ⟦_⟧₀` (Extend = free
  extension of generator semantics), `GroupSem grp ⟦_⟧₀`;
  `GetSubPresentation fʷ-cong-ax [grouplike] nfp unfp` builds
  `monoidSubPres : Γ IsSubMonoidPresentationOf mon` /
  `groupSubPres : Γ IsSubPresentationOf grp` — injectivity comes from
  by-normalization. I.e. UniqueNormalForm + soundness ⇒ sub-presentation;
  + surjectivity ⇒ presentation.

### ForStdlib/ — staged stdlib contributions (contribution 4), all --safe
1. Algebra.Construct.SemiDirectProduct — N ⋊ H; `record Action` (act, act-cong,
   act-ε-homo, act-∙-homo, act-identity, act-compose) = "exactly the laws
   needed to make the twisted multiplication associative and unital";
   rawMonoid/monoid/group builders, `(n,x)∙(m,y) = (n ∙ act x m , x ∙ y)`.
2. Algebra.Construct.Amalgamation — amalgamated free product M *_C N of
   MONOIDS as List-based words / least congruence; "the pushout M *_C N in the
   category of monoids" when φ, ψ are homs.
3. Algebra.Construct.Extension — group extensions as short exact sequences
   (record Extension N H: total, incl, proj, homos, exactness).
4. Algebra.Construct.SplitExtension — + homomorphic section; splitting-lemma
   relationship to ⋊ noted in header.
5. Algebra.Morphism.Consequences — isMonoidHomomorphism⇒isGroupHomomorphism
   ("the stdlib used to derive this only in the now-deprecated
   Algebra.Morphism").
6. Algebra.Morphism.Structures — IsMonoidEpimorphism (stdlib has mono/iso but
   not epi).
7. Data.Fin.Permutation.Properties — bundles stdlib's Permutation′ n as a
   Group (∘ₚ, id, flip) — "Permutation′-group n" used as the tight semantics
   of Sₙ.

## 3. THE CATALOGUE (for §Examples tables and MainTheorems.agda)

### General construction theorems (premises → presentation), all GREEN:
- DirectProduct (Presentation/Construct/Properties/DirectProduct.agda):
  * NFP: nfp-Γ, nfp-Δ NormalFormInjective ⇒
    `nfp : NormalFormInjective (Γ ⋄ Δ ⋄ CommRel) (NF₁ × NF₂)` (line 261);
    NFP': same for NormalForm (line 331).
  * module Presentation (line ~340): p1 : Γ IsPresentationOf G1, p2 : Δ ⇒
    `dpres : (Γ ⋄ Δ ⋄ CommRel) IsPresentationOf ADP.group G1 G2` (line 470).
- NDirectProduct (…/NDirectProduct.agda): ⊗-carrier; `nfp (n)`/`nfp' (n)` lift
  a factor NF to Γ ⊕^ n; module Presentation: `⊗-group : ℕ → Group` (trivial,
  G, ADP.group G (⊗-group n)); `presentation : (n : ℕ) → (Γ ⊕^ n)
  IsPresentationOf (⊗-group n)` (line 83).
- SemiDirectProduct (…/SemiDirectProduct.agda): ConjRel (element conj);
  nfp/nfp' with twist hypotheses (lines 346–414).
- SemiDirectProduct2 (…/SemiDirectProduct2.agda): ConjRelʷ (word-valued conj);
  premises conj-hyph, conj-hypn; nfp (354), nfp' (414); module Presentation
  (line ~437): p1, p2 ⇒ `dpres : (Γ ⋄ Δ ⋄ ConjRelʷ conj) IsPresentationOf
  G1⋊G2` (line 680) where G1⋊G2 = ForStdlib SDP.group G1 G2 φ.
- Amalgamation (…/Amalgamation.agda, 1800+ lines): `record AmalDataNF M P1 P2`
  = { P₀ : WRel M ; CA₁ : PackedCosetTable P₀ P1 ; CA₂ : PackedCosetTable P₀ P2 }.
  module ANF: NF carrier `amalNFC C D = (D ⊎ ⊤) × List (C × D) × (C ⊎ ⊤)`
  (alternating cosets — the classical amalgamated-free-product normal form);
  section [_]; coset action hh; ⇒ via SingleLevel: nfp, nfp' for
  `mypres = P₁ * P₂ ⋆ f₁ ⋆ f₂`. module Presentation (1548): G0,G1,G2 +
  p0,p1,p2 ⇒ φ, ψ induced amalgamating homs and (line 1785)
  `dpres : (P₁ * P₂ ⋆ f₁ ⋆ f₂) IsPresentationOf amalgamation` (target from
  ForStdlib.Algebra.Construct.Amalgamation).
- Extension (…/Extension.agda, GREEN): stated after "Proposition 2.55" (find
  source in P3 — likely a thesis/book numbering, maybe Bian's PhD thesis);
  `ext = S-rel ∪ conj-rel ∪ twisted-relator-lifts` presentation of an
  arbitrary (not nec. split) extension G of GQ by GN, premises: Extension
  record, pN, pQ, ⟦_⟧₀, sound-ax…, BijectiveNormalForm for both factors ⇒
  `ext IsPresentationOf G` (line 475). Note: RelTwist R̄ corr — each quotient
  relator r lifts with a correction word corr r ∈ Word N.
- SugarProduct (…/SugarProduct.agda): definitional extensions (SugarRel);
  used by U33Di. (Detail if needed in writing.)

### Concrete presentations (R IsPresentationOf G), all GREEN:
| # | Relations R | Group G | File |
|---|---|---|---|
| 1 | EmptyRel over ⊥ | Terminal.group (trivial) | Examples/Groups/Trivial.agda Empty.Presentation.presentation |
| 2 | TrivialRel over any A | Terminal.group | ibid. Universal.Presentation.presentation |
| 3 | (₁₊ n) Cn,_===_ (T^{n+1} = ε) | Cn-group (₁₊ n) (= ℤ/(n+1)ℤ on Fin) | Examples/Groups/Cyclic/Theorems.agda presentation (61) |
| 4 | n VRel,_===_ (circuit Coxeter: order, yang-baxter + cong↑/comm₂) | Permutation′-group n (stdlib permutations of Fin n) | Examples/Groups/Symmetric/Theorems.agda Tight.presentation (74) |
| 5 | Cₚ ⋄ Cₚ ⋄ CommRel | H-group = ℤ/p × ℤ/p | Examples/Groups/ProjectivePauli/Presentation.agda H-pres (58) |
| 6 | Γ-H ⊕^ n | Pauli-group n = (ℤ/p×ℤ/p)ⁿ | ibid. Pauli-presentation (71) — p an odd prime param (Prime (2+ p-2)) |
| 7 | (Γ₀ m ⊕^ n) ⋄ (n VRel,_===_) ⋄ ConjRelʷ conj | wreath-group = (ℤ/(m+1)ℤ)ⁿ ⋊ Sₙ = ℤ/(m+1)ℤ ≀ Sₙ | Examples/Construct/SemiDirectProduct/SnD.agda Wreath.presentation (337) — SIGNED PERMUTATIONS at m+1=2; generalized symmetric group G(N,1,n) generally |
plus the conditional construction theorems above (dpres for ⊕, ⋊, *⋆⋆, ext, ⊕^).

### Monoid isomorphisms (amalgamation case studies), all GREEN:
- CliffordT1 (Examples/Amalgamations/CliffordT1.agda:932):
  `CliffordT1-isomorphism : IsMonoidIsomorphism (rawMonoid m₁) (rawMonoid m₂) (f ʷ)`
  where m₁ = words over {T,H,S,ω} modulo
  { ω⁸=ε, T²=S, S⁴=ε, H²=ε, (S•H)³=ω, (T•X)²=ω (X:=H•S•S•H), ω central }
  and m₂ = TXSω * Clifford ⋆ f₁ ⋆ f₂ — the amalgamated free product of the
  T-extension and the H-extension over the common XSω subgroup presentation.
  TOWER: Sω = Cyclic.pres 8 ⊕ Cyclic.pres 4 (⟨ω⟩×⟨S⟩) →(2 cosets {ε,X})→
  XSω {ω⁸,S⁴,X²,(SX)²=ω²,ω central} →(3 cosets {I,H,HS})→ Clifford {…,(SH)³=ω,
  X=HSSH} and →(2 cosets {I,T})→ TXSω {…,T²=S,(TX)²=ω}. Each level a
  SingleLevel.Transfer with by-equal-nf discharging all table checks BY
  COMPUTATION (h-wd-ax cases are all `by-equal-nf Eq.refl`!).
- QutritCliffordT1 (…:2866): same statement shape for the qutrit gate set
  {T,H,S,ζ}: relations incl. ζ⁹=ε, S³=ζ⁶, H²? (order-H), T³=Z with
  Z=ζ³•S²•X²•S•X, comm-TS, comm-TX, (T•H•H)²=ε (order-THH), comm-HHSHHS…;
  TOWER: Cyclic 9 →(3 cosets)→ Sζ {ζ⁹,S³=ζ⁶} →(9 cosets!)→ SXζ {+X³,(SX)³,
  (XS)(SX)=ζ⁶(SX)(XS)} →(2 cosets)→ SXζHH {+HH²=ε, HH•X=X²•HH, HH•S=(S•Z)•HH}
  →amalgam→ CliffordTHH * CliffordH over SXζHH.
- U33Di (…:1391): `U33Di-isomorphism : IsMonoidIsomorphism (rawMonoid m₂)
  (rawMonoid m₁) (g ʷ)` — U₃(ℤ[½,i]) presented by generators
  {i₀, K₀₁, X₀₁, X₁₂} and relations [S1],[S3a],[S3b],[S4a],[S5a],[S9a],[S10],
  [S11],[S12],[S14],[S4b] (the "Simplified" module, from Bian–Selinger
  arXiv:2204.02217), shown isomorphic to a TWO-LEVEL amalgamated product;
  level 1: Ki (⟨K₀₁,i₀,i₁⟩, 6 cosets over C4⊕C4), Sim over C4⊕^3; uses
  SugarProduct (desugar) + Sn (S₃ enters via swap) + NDP + DP. 2869/1395-line
  files, biggest case studies.
- S3xC5/Semantic.agda (GREEN): S₃ × C₅ direct-product example; monoid-level
  iso/semantics for the composite (check exact final statement when quoting —
  file was trimmed this month).

### NF witnesses (concrete, GREEN):
- Trivial: nfp/nfp' : NormalForm(Injective) EmptyRel/TrivialRel ⊤ (+ unfp).
- Cyclic (Examples/Groups/Cyclic/Normalization.agda): NF n (= Fin-like carrier
  `Cn n`?verify when quoting), nfp n, nfp' n; unique-nf in Theorems.
- Sn (Presentation/Groups/Sn.agda): `NF zero = ⊤ ; NF (₁₊ n) = NF n × C (₁₊ n)`
  with `C n` = {ε, swap•ε, swap•swap•ε, …} — |C (₁₊ n)| = n+2 ⇒ |NF n| = n!
  FACTORIAL NUMBER SYSTEM. nfp via inductive R–S (p0/nfp-1 lines 418–427).
- Symmetric (circuit version, Examples/Groups/Symmetric/Normalization.agda):
  ract coset table for Gen (₂₊ n), racts = ract ᵗ; ract-sound; base0'/base1';
  exported `NF ; nfp'-t` used by Theorems.
- CliffordT1 Sω.nfp/nfp' : NormalForm(Pω ⊕ PS) (Cyclic.NF 8 × Cyclic.NF 4);
  each tower level's nfp/nfp' via Transfer; amalgam nfp/nfp' via ANF.
- UniqueNormalForm instances: Symmetric Loose (Endo-setoid n) + Tight
  (Permutation′-group setoid) [Theorems.agda 32–71]; Cyclic (Eq.setoid (Cn n))
  [Theorems 33]; Trivial (⊤).

### Semantics used
- Sₙ loose: Endo-setoid n (endofunctions on Fin n) — soundness + completeness.
- Sₙ tight: Permutation′-group n (ForStdlib bundling) — unique-nf +
  presentation.
- Cyclic: Cn n carrier with Eq.setoid.
- Products/wreath/Pauli/amalgamation: semantic groups BUILT from stdlib/
  ForStdlib constructions (ADP.group, SDP.group, Amalgamation monoid,
  Terminal.group) — "the semantic side exists thanks to ForStdlib".

## 4. Paper-facing observations (verified)
- The whole verified library is --safe (+ --cubical-compatible on the core);
  no postulates anywhere in the green closure.
- Circuit relations are INDUCTIVE FAMILIES indexed by wire count; the
  structural rules (cong↑, comm₁, comm₂) are added generically by
  Lift-Relation — "define only the group-specific axioms".
- Massive computational discharge: in the towers, h-wd-ax / h=⁻¹f-gen /
  hcme~ obligations are closed by `by-equal-nf Eq.refl` — the normal-form
  function COMPUTES both sides to the same value, so the proof is refl. This
  is the "completeness proofs involve a lot of computation" thesis: the
  computation is done by Agda's evaluator, not by hand. (e.g. QutritCliffordT1
  has ~100 such cases across 9-coset tables.)
- by-assoc discharges all re-bracketing (to-list ≡); the equational proofs in
  the case studies interleave by-assoc steps with single axiom applications —
  very close to pen-and-paper calculations.
- Honest example count: 7 nontrivial verified families: Cyclic, Sₙ (circuit),
  S₃×C₅, wreath ℤ/N≀Sₙ, Pauli (ℤ/p×ℤ/p)ⁿ, qubit Clifford+T, qutrit
  Clifford+T, U₃(ℤ[½,i]) — that's 8 + trivial group = 9 presentations;
  phrase as "a catalogue including …" and let the table speak. The outline
  says "7 examples … one published this year" — WITHOUT knowing the intended
  seven, present the table and in prose say "seven example families beyond
  the trivial group" if we pick: Cyclic, Symmetric, S3xC5, Wreath/SnD, Pauli,
  CliffordT1, QutritCliffordT1, U33Di = 8… SAFER: say "eight". Decide in P4;
  never claim Symplectic as done.
- "One published this year": U33Di ← arXiv 2204.02217 (published J. Math.
  Phys./…? verify year in P3); qutrit Clifford+T ← check for a 2025/2026
  publication (maybe the companion paper). Resolve in P3.

## 5. Open items forwarded to later phases
- P2: MainTheorems.agda collecting: presentations table (1–7 above),
  construction dpres theorems, the three monoid isos, NF/UniqueNF witnesses.
  Must NOT import any RED file. Note module parameters: Pauli needs
  (p-2, p-prime); wreath needs (n m); keep them as module params or re-export
  the modules qualified.
- P3: identify "Proposition 2.55" source (Extension.agda comment); actual
  titles of arXiv 2306.08530 / 2204.02217; Clément et al. ~300pp paper;
  Selinger n-qubit Clifford; qutrit Clifford+T paper; the companion multi-
  qudit paper (title in CLAUDE.md).
- P4 misc: LafontLP + qupit web tools (outline URLs); acknowledge Claude per
  outline; SnD.agda old vs new — old Presentation/Groups/SnD.agda is the
  NF-level wreath (ℤ/4≀Sₙ via SDP NF), new Examples/Construct/… is the
  group-level presentation. Both green; cite the new one.
