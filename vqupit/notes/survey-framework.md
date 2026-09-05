# Survey: generic framework (verified 2026-09-04 against working tree db998e6)

## Normalization/NormalForm/Uniqueness.agda (68 lines)
Module params: `{X} (Γ : WRel X) (NF : Setoid 0ℓ 0ℓ) {c d} (Sem : Setoid c d) (⟦_⟧ : Word X → Setoid.Carrier Sem)`.

```agda
record UniqueNormalForm (inv-nf : |NF| → Word X) : Set (c ⊔ d) where
  field
    unique : ∀ {u v : |NF|} → ⟦ inv-nf u ⟧ ≈₂ ⟦ inv-nf v ⟧ → u ≈ₙ v

by-normalization : {normalForm : NormalForm} → let open NormalForm normalForm in
                   UniqueNormalForm inv-nf  → Congruent _≈_ _≈₂_ ⟦_⟧ → Injective _≈_ _≈₂_ ⟦_⟧
by-normalization {normalForm} uni sound {x} {y} eq = nf-injective (unique claim)
  where
  claim : ⟦ inv-nf (nf x) ⟧ ≈₂ ⟦ inv-nf (nf y) ⟧
  claim = begin
    ⟦ inv-nf (nf x) ⟧ ≈⟨ sound inv-nf∘nf=id ⟩
    ⟦ x ⟧             ≈⟨ eq ⟩
    ⟦ y ⟧             ≈⟨ sym₂ (sound inv-nf∘nf=id) ⟩
    ⟦ inv-nf (nf y) ⟧ ∎

by-completeness : (∀ {u} → nf (inv-nf u) ≈ₙ u) → Injective _≈_ _≈₂_ ⟦_⟧ → UniqueNormalForm inv-nf
```
Setoid.agda: `NormalFormInjective = Injection word-setoid NF` (:54-58); `NormalForm = RightInverse` (:75-82); `BijectiveNormalForm = Bijection` (:117-123); `WeakNormalForm` (:201-208).

## Normalization/CosetNF.agda (775 lines)
```agda
module SingleLevel
  {X Y : Set}
  (Γ   : WRel X)               -- subgroup presentation  (letters X)
  (Δ   : WRel Y)               -- group presentation     (letters Y)
  (C   : Set)                  -- set of right cosets
  (I   : C)                    -- identity coset (that of the subgroup)
  (f   : X → Word Y)           -- generator embedding  H ↪ G
  (h   : C → Y → Word X × C)   -- coset action (Schreier table)
  ([_] : C → Word Y)           -- Schreier section
```
Transfer hypotheses (:133-148):
```agda
    (h=⁻¹f-gen : ∀ (x : X) → ([ x ]ʷ , I) ~ ((h ᵗ) I (f x)))
    (h-wd-ax : ∀ (c : C){u t : Word Y} → u ===₂ t → ((h ᵗ) c u) ~ ((h ᵗ) c t))
    (f-wd-ax : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
    ([I]≈ε : [ I ] ≈₂ ε)
    (h=ract :  ∀ c b → let (b' , c') = h c b in let [_]ₓ = f ʷ in
      [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
```
nf = (h ᵗ) I; inv-nf (w , c) = (f ʷ) w • [ c ]; transports nfp : NormalFormInjective Γ NF₁ → NormalFormInjective Δ (NF₁ × C), nfp' likewise (:216-272). `Transfer.Unique` (:294-345) gives exactness nf'∘gg=id.

CosetTower (:725-775): params `(X : ℕ → Set) (P : ∀ n → WRel (X n)) (Cᶜ : ℕ → Set)`; `record Extension (n : ℕ)` with fields I f h [_] + the 5 hypotheses; 
```agda
  tower-carrier : Set → ℕ → Set
  tower-carrier NF₀ zero    = NF₀
  tower-carrier NF₀ (suc n) = tower-carrier NF₀ n × Cᶜ n

    nfp'-tower : ∀ {NF₀} → NormalForm (P 0) NF₀ →
                 ∀ n → NormalForm (P n) (tower-carrier NF₀ n)
    nfp'-tower base zero    = base
    nfp'-tower base (suc n) = Extension.nfp' (ext n) (nfp'-tower base n)
```
PackedCosetTable (:659-708): C ⊎ ⊤ with identity coset inj₂ tt represented by ε on the nose.

## Presentation/Construct/Properties/SemiDirectProduct.agda (737 lines)
```agda
module Presentation.Construct.Properties.SemiDirectProduct
  {N H : Set} (Γ : WRel N) (Δ : WRel H) (conj : H → N → Word N) where
-- (:108-115)
module _
  (conj-hyph : ∀ {c d} n → c ===₂ d → (conj ʰ') c n ≈₁ (conj ʰ') d n)
  (conj-hypn : ∀ c {w v} → w ===₁ v → (conj ⁿ') c w ≈₁ (conj ⁿ') c v)
  where
-- (:444-449)
  module Presentation (G1 : Group 0ℓ 0ℓ) (G2 : Group 0ℓ 0ℓ)
    (p1 : Γ IsPresentationOf G1) (p2 : Δ IsPresentationOf G2) where
-- (:543-558) φ : SDP.Action ...; G1⋊G2 = SDP.group G1 G2 φ
-- act g x = ⟦ conjss (inv₂ g) (inv₁ x) ⟧₁   (:504-505)
-- (:689-690)
    dpres : (Γ ⋄ Δ ⋄ ConjRelʷ conj) IsPresentationOf G1⋊G2
```
NF side: `NFP.nfp : NormalFormInjective (Γ ⋄ Δ ⋄ ConjRelʷ conj) (NF₁ × NF₂)` (:362), `NFP'.nfp'` (:422-431); `LiftUNF` (:701-736). Cosets are words over the other factor up to ≈ (setoid cosets, `Cₛ = word-setoid₂`, :82-85). File header (:9-13): a generator-valued version was superseded because the Clifford scalar cocycle conjugates a generator to a word.

Construct/Base.agda:82-87
```agda
data ConjRelʷ {N H} (conj : H → N → Word N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) →
         ConjRelʷ conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ)
                  ([ conj h n ]ₗ • [ [ h ]ʷ ]ᵣ)
```
`_⋄_⋄_` at Base.agda:49-53.

## Presentation/Construct/Properties/Extension.agda (838 lines) — Prop 2.55
```agda
data RelTwist (R̄ : WRel X) (corr : ∀ {u v} → R̄ u v → Word N) : WRel (N ⊎ X) where
  tw : ∀ {u v} (r̄ : R̄ u v) → RelTwist R̄ corr [ u ]ᵣ ([ corr r̄ ]ₗ • [ v ]ᵣ)

extension-presentation : (S : WRel N) (R̄ : WRel X)
  (conj : X → N → Word N) (corr : ∀ {u v} → R̄ u v → Word N) → WRel (N ⊎ X)
extension-presentation S R̄ conj corr = S ⋄ EmptyRel ⋄ (ConjRelʷ conj ∪ RelTwist R̄ corr)
```
`module Presentation (GN GQ : Group 0ℓ 0ℓ) (et : Extension GN GQ) (pN : S IsPresentationOf GN) (pQ : R̄ IsPresentationOf GQ) (⟦_⟧₀ : (N ⊎ X) → Carrier G) {NFS NFQ} (nfpS : BijectiveNormalForm S NFS) (nfpQ : BijectiveNormalForm R̄ NFQ)` (:121-135).
```agda
    dpres : Realises → (sound-ax : ∀ {w v} → extp w v → Group._≈_ G ⟦ w ⟧ ⟦ v ⟧) →
      (sec-triv : Sec-trivial) → (conj-triv : Conj-trivial) →
      (real-Q : ∀ x → GQm._≈_ (proj ⟦ inj₂ x ⟧₀) ⟦ [ x ]ʷ ⟧Q) → ext IsPresentationOf G
```
Completed proof. Normalization/Construction.agda:140-167 upgrades to BijectiveNormalForm ext (NFS × NFQ) so extensions stack.

**Clifford/Qupit does NOT use Prop 2.55's dpres**: Clifford/Qupit/Semantics.agda imports ForStdlib.Algebra.Construct.Extension, ForStdlib.Algebra.Construct.CentralExtension as CE, Presentation.Construct.Properties.CocycleGen (Generator-Data). `Presented-Extension` is defined in Semantics.agda:636-639 (params g*, g-gen); `Presented-group n gd = CE.group (A n) (H n) (γᶜ n gd)` (:731-732); `Presented-extension n gd = CE.centralExtension ...` (:735-736). Clifford/Qupit/Presentation.agda uses only `Ext.tw` and `Ext.extp S Q QS.conj QS.corr` (:107, :202); header (:30-45) explains: Prop 2.55 demands a bijective NF for each factor and "for the qupit quotient no such normal form exists yet". Its theorem `presentation-exact` (:637-645) is a monoid presentation promoted by `monoidPresentation⇒presentation` (:521-533). Prop 2.55 IS instantiated in the qubit development (Clifford/Qubit/Presentation.agda:343; ProjectiveClifford/Qubit/ExtensionPresentation.agda).

## ForStdlib
SemiDirectProduct.agda:33-49 `record Action (N : RawMonoid) (H : RawMonoid)` fields act, act-cong, act-ε-homo, act-∙-homo, act-identity, act-compose. `group : (N H : Group) → Action → Group` (:136-138); `(n , x) ◦ (m , y) = n N.∙ act x m , x H.∙ y`.
Extension.agda:41-68 `record Extension (N H : Group)`: total, incl, proj, incl-homo, proj-homo, incl-injective, proj-surjective, proj-kills-incl, ker⊆im-incl. SplitExtension adds sect, sect-homo, proj-splits-sect. CentralExtension.agda (328 lines: Cocycle, group, centralExtension); FactorSetExtension.agda (696).

## ForStdlib/Data/Fin/Mod
`ℤ n = Fin n`; `ℤ* n@(₁₊ _) = Σ[ a ∈ ℤ n ] (a ≢ ₀)`. `module PrimeModulus (p-2 : ℕ) (p-prime : Prime (₂₊ p-2))`; `ₚ = ₁₊ (₁₊ p-2)`; inverse via Bézout `_⁻¹'` (Prime.agda:140-143). Fermat.agda: `module PrimeModulus' ... open PrimeModulus public`; `Fermat's-little-theorem : ∀ (a*@(a , nz) : ℤ* ₚ) → a ^′ p-1 ≡ ₁` (:220) proved by permutation-of-residues argument.
```agda
  module Primitive-Root-Modp'
    (g*@(g , g≠0) : ℤ* ₚ)
    (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k )
```
**Primitive root is a module parameter (existence not proved)**; only p = 2 instance discharged (Two.agda). Derived: `g^_ : ℤ ₚ → ℤ* ₚ`, `log : ℤ* ₚ → ℤ ₚ-₁`, `aux-g^′-%`.

## Presentation/Definitions.agda
```agda
record _IsPresentationOf_ (_===_ : WRel X) (G : Group a ℓ) : Set (a ⊔ ℓ) where
  field gl : Grouplike _===_
  module GL = Group-Lemmas _===_ gl
  open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup G)
  field
    ⟦_⟧ : Word X → Group.Carrier G
    iso : IsGroupIsomorphism ⟦_⟧
```
`_IsSubPresentationOf_` with `mono : IsGroupMonomorphism ⟦_⟧`; soundness/completeness = stdlib `Function.Congruent`/`Injective`. Upgrades: isPresentationOf (mono + surj ⇒ iso, :98-104), monoidPresentation⇒presentation (:135-147). Normalization/StarPresentation.agda:38-56 is where by-normalization becomes the `injective` field of every dpres.

## Circuit/Base.agda (239 lines) — `module Circuit.Base (Gate : ℕ → Set)`
```agda
data Gen : ℕ → Set where
  gate₀ : Gate 0 → Gen n
  gate₁ : Gate 1 → Gen (₁₊ n)
  gate₂ : Gate 2 → Gen (₂₊ n)
  _↥   : Gen n → Gen (₁₊ n)

Circuit : ℕ → Set
Circuit n = Word (Gen n)

module Lift-Relation (_SRel,_===_ : (n : ℕ) → CRel n) where
  data _VRel,_===_ : (n : ℕ) → CRel n where
    srel  : n SRel, w === v → n VRel, w === v
    cong↑ : n VRel, w === v → (₁₊ n) VRel, w ↑ === v ↑
    comm₀ : (h : Gate 0) (g : Gen n) → n VRel,
      [ g ]ʷ • [ gate₀ h ]ʷ === [ gate₀ h ]ʷ • [ g ]ʷ
    comm₁ : (h : Gate 1) (g : Gen n) → (₁₊ n) VRel,
      [ g ↥ ]ʷ • [ gate₁ h ]ʷ === [ gate₁ h ]ʷ • [ g ↥ ]ʷ
    comm₂ : (h : Gate 2) (g : Gen n) → (₂₊ n) VRel,
      [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ === [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ
    ω↑=ω : (ω : Gate 0) → (₁₊ n) VRel, [ gate₀ ω ]ʷ ↑ === [ gate₀ ω ]ʷ
```
gate₀ = global (scalar) gate; ω↑=ω identifies its shifts ("Selinger's Figure 8 carried it as cω↑").

## Line counts (framework)
Word 2/265; Presentation 18/7268 (Amalgamation 1732, Extension 838, SemiDirectProduct 737, CocycleGen 571, DirectProduct 514, CentralProduct 456, Tactic/Rewriting 432, ...); Circuit 3/525; Normalization 10/2172 (CosetNF 775, R-S 535); ForStdlib 21/4618 (Mod/Prime 789, FactorSetExtension 696, CentralProduct 420, CentralExtension 328, Fermat 306). Core subtotal 54 files / 14 848 lines. Examples 273 / 91 328. Repo total 329 / 106 388.
