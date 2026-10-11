# Survey: Examples/Groups/Symplectic (excluding Simplified) — 2026-09-04

Sizes: 111 files / 33 645 lines; Normalization/** 35 files / 8 352; BR/** 28 / 7 002.
Largest: Normalization/LMHeadInj.agda 1322; SoundnessDirect.agda 1109; Syntactics/Gates.agda 741; Pushing/SrelWDW1 766; SrelWDM 708.

## Syntactics (Gates.agda)
`module Examples.Groups.Symplectic.Syntactics (p-2 : ℕ) (p-prime : Prime (2+ p-2))`.
```agda
  data SympGate : ℕ → Set where
    H-gate  : SympGate 1
    S-gate  : SympGate 1
    CZ-gate : SympGate 2
  S = [ gate₁ S-gate ]ʷ ; S⁻¹ = S ^ p-1 ; H = [ gate₁ H-gate ]ʷ ; CZ = [ gate₂ CZ-gate ]ʷ
  CX = H ↓ ^ 3 • CZ • H ↓ ;  XC = H ↑ ^ 3 • CZ • H ↑ ; CX' = H ↓ • CZ • H ↓ ^ 3
  Ex = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑
  ₕ|ₕ = H ↓ • CZ • H ↓ ; ʰ|ʰ = H ↑ • CZ • H ↑ ; ⊥⊤ = ₕ|ₕ • ʰ|ʰ ; ⊤⊥ = ʰ|ʰ • ₕ|ₕ
  S^ k = S ^ toℕ k ; CZ^ k = CZ ^ toℕ k ; CX^ ...
  SHS : ℤ ₚ → ℤ ₚ → Word (Gen (₁₊ n)) ; SHS a b = S^ a • H • S^ b • H • S^ a • H
  ZM x' = SHS x x⁻¹ ; XM x' = SHS x⁻¹ x ; M = ZM ; M₁ = M ₁ₚ
```
Full symplectic axioms (Gates.agda:249-269) — **17 constructors**:
```agda
      data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where
        order-S    : ∀ {n} → (₁₊ n) SRel,  S ^ p === ε
        order-H    : ∀ {n} → (₁₊ n) SRel,  H ^ 4 === ε
        order-SH   : ∀ {n} → (₁₊ n) SRel,  (S • H) ^ 3 === ε
        comm-HHS   : ∀ {n} → (₁₊ n) SRel,  H • H • S === S • H • H
        M-mul      : ∀ {n} x y → (₁₊ n) SRel,  M x • M y === M (x *' y)
        semi-MS    : ∀ {n} x → (₁₊ n) SRel,  M x • S === S^ (x ^2) • M x
        semi-M↑CZ  : ∀ {n} x → (₂₊ n) SRel,  M x ↑ • CZ === CZ^ (x ^1) • M x ↑
        semi-M↓CZ  : ∀ {n} x → (₂₊ n) SRel,  M x ↓ • CZ === CZ^ (x ^1) • M x ↓
        order-CZ   : ∀ {n} → (₂₊ n) SRel,  CZ ^ p === ε
        comm-CZ-S↓ : ∀ {n} → (₂₊ n) SRel,  CZ • S ↓ === S ↓ • CZ
        comm-CZ-S↑ : ∀ {n} → (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
        selinger-c10 : ∀ {n} → (₂₊ n) SRel,  CZ • H ↑ • CZ === S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
        selinger-c11 : ∀ {n} → (₂₊ n) SRel,  CZ • H ↓ • CZ === S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
        selinger-c12 : ∀ {n} → (₃₊ n) SRel,  CZ ↑ • CZ === CZ • CZ ↑
        selinger-c13 : ∀ {n} → (₃₊ n) SRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
        selinger-c14 : ∀ {n} → (₃₊ n) SRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
        selinger-c15 : ∀ {n} → (₃₊ n) SRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
```
`_QRel,_===_ = LR._VRel,_===_` (Lift-Relation of the above). grouplike (Gates.agda:571-618): H⁻¹ = H^3, S⁻¹ = S^{p-1}, CZ⁻¹ = CZ^{p-1}.

## Semantics.agda — Sp(2n) as linear symplectic bijections of Pauli n = Vec (ℤ ₚ × ℤ ₚ) n
```agda
record Symplectic (n : ℕ) : Set where
  field
    ap        : Pauli n → Pauli n
    ap⁻¹      : Pauli n → Pauli n
    invˡ      : ∀ p → ap⁻¹ (ap p) ≡ p
    invʳ      : ∀ p → ap (ap⁻¹ p) ≡ p
    linear-+  : ∀ p q → ap (p +ₚ q) ≡ ap p +ₚ ap q
    linear-*  : ∀ k p → ap (k *ₚ p) ≡ k *ₚ ap p
    preserves : ∀ p q → sform (ap p) (ap q) ≡ sform p q
S ≈ˢ T = ap S ≗ ap T
```
εˢ, _∘ˢ_ (function composition; assoc/identity on the nose), _⁻¹ˢ; `Sp-group : Group 0ℓ 0ℓ` (Semantics.agda:132-157). Generator action (:356-374):
```agda
  actg : ∀ {n} → Gen n → Pauli n → Pauli n
  actg (gate₁ H-gate)  ((a , b) ∷ ps)             = (- b , a) ∷ ps
  actg (gate₁ S-gate)  ((a , b) ∷ ps)             = (a , b + a) ∷ ps
  actg (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) = (a , b + a') ∷ (a' , b' + a) ∷ ps
  actg (g ↥)           (x ∷ ps)                   = x ∷ actg g ps
  ⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ ; ⟦ ε ⟧ = εˢ ; ⟦ w • v ⟧ = ⟦ w ⟧ ∘ˢ ⟦ v ⟧
```
Sp-indexedGroup, lift₀ˢ (fix wire 0), Sp-embedding.

## Normalization/Boxes.agda (80 lines, data only)
```agda
A : Set ; A = Σ[ ab ∈ (ℤ ₚ × ℤ ₚ) ] (ab ≢ (₀ , ₀))
B = ℤ ₚ × ℤ ₚ ; D = ℤ ₚ × ℤ ₚ ; E = ℤ ₚ
L' 0 = ⊤ ; L' (₁₊ n) = Vec B n × A
M 0 = ⊤ ; M (₁₊ n) = Vec D n × E
ML' 0 = ⊤ ; ML' n@(₁₊ _) = M n × L' n
ML 0 = ⊤ ; ML 1 = ML' 1 ; ML (₂₊ n) = ML' (₂₊ n) ⊎ D × ML (₁₊ n)
NF 0 = ⊤ ; NF (₁₊ n) = NF n × ML (₁₊ n)
```
(also L, Lj, LE — an older j-indexed L). Double induction: ML = chain of bottom D boxes (inj₂) capped by an ML' (inj₁); NF = list of ML boxes of decreasing width.

## Normalization/Section.agda — boxes as circuits (section is `[_]`, not `[_]ⁿᶠ`)
```agda
[_]ᵃ {n} ((₀ , b@(₁₊ b-1)), pr) = XM (b , λ ())
[_]ᵃ {n} ((a@(₁₊ a-1) , b), pr) = XM (a , λ ()) • H • S^ -b/a      -- -b/a = - b * a⁻¹
[_]ᵇ {n} (₀ , b) = Ex • CX'^ b
[_]ᵇ {n} (a@(₁₊ a-1) , b) = Ex • CX'^ a • H ↑ • S^ -b/a ↑
[_]ᵈ {n} (₀ , b) = Ex • CZ^ (- b)
[_]ᵈ {n} (a@(₁₊ _) , b) = Ex • CZ^ (- a) • H • S^ -b/a
[_]ᵉ {n} b = S^ (- b)
[_]ᵛᵇ (x ∷ v) = [ v ]ᵛᵇ ↑ • [ x ]ᵇ        -- Vec B in circuit order
[_]ᵛᵈ (x ∷ v) = [ x ]ᵈ • [ v ]ᵛᵈ ↑
[_]ᵐ {₁₊ n} ([] , e) = [ e ]ᵉ ; [_]ᵐ {₁₊ n} (x ∷ vd , e) = [ x ]ᵈ • [ vd , e ]ᵐ ↑
[_]ˡ' {₁₊ n} (vb , a) = [ vb ]ᵛᵇ • [ a ]ᵃ
[_]ᵐˡ {₂₊ n} (inj₁ (m , l)) = [ m ]ᵐ • [ l ]ˡ'
[_]ᵐˡ {₂₊ n} (inj₂ (d , lm)) = [ d ]ᵈ • [ lm ]ᵐˡ ↑
[_] : ∀ {n} → NF n → Word (Gen n)
[_] {0} tt = ε
[_] {₁₊ n} (nf , lm) = [ nf ] ↑ • [ lm ]ᵐˡ
```

## Normalization.agda — coset tower
`C = ML` (:62); `[_]ᶜ = [_]ᵐˡ`;
```agda
ract : ∀ {n} → C (₁₊ n) → Gen (₁₊ n) → Circuit n × C (₁₊ n)      -- = PushML.ract
ract-sound : ∀ {n} c g → let (b' , c') = ract {n} c g in [ c ]ᶜ • [ g ]ʷ ≈ b' ↑ • [ c' ]ᶜ
```
PushML.ract dispatch (PushML.agda:85-117) by (inj₁ ML' / inj₂ D-spine) × (S, H, CZ, lifted g). Pushing/ 26 files 5 633 lines.
Word-level: `ract-sound-word` (SrelWDSem:91-94); well-definedness split into coset-wd (proved semantically via head-injectivity) and residual half (needs ↑-inj).
```agda
module T = CosetNF.CosetTower (λ k → Gen k) (λ k → k QRel,_===_) (λ k → C (₁₊ k))
ext k ↑inj = record { I = Iᶜ ; f = [_]ʷ ∘ _↥ ; h = ract ; [_] = [_]ᶜ ; h=⁻¹f-gen = ... ; h-wd-ax = ⁻¹[⇑]-wd'' ↑inj ; f-wd-ax = ... ; [I]≈ε = [I]≈ε' ; h=ract = ... }
Iᶜ {zero} = ([] , ₀) , ([] , Ia)  where Ia = (₀ , ₁) , λ ()
record TowerLevel (n : ℕ) : Set where
  field nfp' : NormalForm (n QRel,_===_) (NFᵗ n) ; agree : ∀ u → inv-nf nfp' u ≈ [ φ u ]
-- The induction.  Level (1+k) needs ↑-injectivity at k, which comes
-- from faithfulness at k, which comes from Level k — strictly below,
-- so the recursion is well founded.
tower : ∀ n → TowerLevel n
tower 0 = record { nfp' = base0' ; agree = λ _ → PB.refl }
tower (₁₊ k) = record { nfp' = nfp'₁ ; agree = agree₁ }
  where prev = tower k
        ↑inj = SemInj.Injectivity!.↑-inj-↑ k (FF.faithful-from′ k (TowerLevel.nfp' prev) φ φ-inj (TowerLevel.agree prev))
        nfp'₁ = T.Extension.nfp' (ext k ↑inj) (TowerLevel.nfp' prev)
nfp'-t : ∀ n → NormalForm (n QRel,_===_) (NFᵗ n)
nfp : (n : ℕ) → NormalFormInjective (n QRel,_===_) (NFᵗ n)
```
Loop (FaithfulFrom header): tower at width n ⟹ Faithful n ⟹ ↑-inj n ⟹ srel-wd n ⟹ tower at 1+n. Faithful1 bootstraps via Tower01.nfp1'.

## Box relations
No "67" anywhere in repo. Lemmas/BoxRelations.agda names 8 families: One: A←H, A←S, E←S; Two: B←H↑-S↑-S, D←H-S↑-S-CZ; Three: BB←CZ↑, B↑←CZ, DD←CZ. Each is a table (dir-of/d'-of) over gate × box-shape. E.g.
```agda
  A←H : ∀ (x : A) → let (dir , x') = OA.dir-and-A'-of x H-gen tt in [ x ]ᵃ • H ≈ dir • [ x' ]ᵃ
  D←H-S↑-S-CZ : ∀ (d : D) (g : Gen 2) (neq : g ≢ H-gen ↥) → let (e , dir) = TD.dir-of d g neq ; d' = TD.d'-of d g neq in
    [ d ]ᵈ • [ g ]ʷ ≈ S^ e  • dir ↑ • [ d' ]ᵈ
-- BR/Two/D.agda:102-133
d'-of (a , b) H-gen _       = (b , - a)
d'-of (a , b) S-gen _       = (a , b + - a)
d'-of (a , b) (S-gen ↥) _   = (a , b)
d'-of (a , b) CZ-gen _      = (a , b + - ₁)
dir-of (₀ , ₀)               H-gen neq = ₀ , H
dir-of (₀ , ₁₊ _)            H-gen neq = ₀ , ε
dir-of (₁₊ _ , ₀)            H-gate neq = ₀ , HH
dir-of (a@(₁₊ _) , b@(₁₊ _)) H-gen neq = ₀ , ZM a/b • S^ b/a
dir-of (₀ , b)               S-gen neq = ₀ , S
dir-of (₁₊ _ , b)            S-gen neq = ₀ , ε
dir-of (a , b)           (S-gen ↥) neq = ₁ , ε
dir-of (₀ , b)              CZ-gen neq = ₀ , ε
dir-of (a@(₁₊ _) , b)       CZ-gen neq = a , H • S^ (- a⁻¹) • H ^ 3
```
Proved lemma counts in BR: One/A 16, One/E 2, Two/B 20, Two/D 19, Two/L2-CZ 3, Two/ML'-Top 9, Three/BB-CZ 2, Three/B-CZ 10, Three/DD-CZ 10. CongDownK.cong↓ᵏ widens fixed-width relations (BB-CZ-n, DD-CZ-n).

## Uniqueness
NF-Inj.agda:74-79
```agda
act-nf : ∀ {n} → NF n → Pauli n → Pauli n
act-nf {0}    _        = id
act-nf {₁₊ n} (ih , lm) ps = head s ∷ act-nf ih (tail s)  where s = act [ lm ]ᵐˡ ps
lemma-nf-inj : ∀ {n} (nf₁ nf₂ : NF n) → act-nf nf₁ ≗ act-nf nf₂ → nf₁ ≡ nf₂
lemma-lm-head-inj : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
  (∀ (ps : Pauli (₁₊ n)) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) → lm₁ ≡ lm₂
lemma-lm-tail-surj : ∀ {n} (lm : ML (₁₊ n)) (qs : Pauli n) → ∃ λ (ps : Pauli (₁₊ n)) → tail (act [ lm ]ᵐˡ ps) ≡ qs
⟦[]⟧-injective : ∀ {n} (u v : NF n) → ⟦ [ u ] ⟧ ≈ˢ ⟦ [ v ] ⟧ → u ≡ v
```
LMHeadInj (1322 lines): induction on ML: base lemma-nf1-head-inj (4 A-shapes, closed-form actions from BoxAction); inj₁≁inj₂ separation; inj₂/inj₂: read d off by probing with pZ/pX prefixes at identity tail. Uniqueness.agda:248-260 obtains the same via generic Circuit.Uniqueness (`c-inj`, `c-surj`), and `unique-nf : ∀ n → NFU.UniqueNormalForm (n QRel,_===_) (NF n) Sem ⟦_⟧ (inv-nf {n})`. Uniqueness.agda header comment (:14-30) quotable ("The towers agree on the nose... States are Paulis, one per wire... ap is a LEFT action").
SemInj: `Faithful n = ∀ w v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧ → w ≈ v`; `Sem-↑-Inj`; `↑-inj-↑`. FaithfulFrom.faithful-from′.

## Presentation
Presentation.agda:175-188: `subpresentation : ∀ {n} → (n QRel,_===_) IsSubPresentationOf (Sp-group n)`; `Surjectivity n = ∀ (S : Symplectic n) → ∃ λ w → ⟦ w ⟧ ≈ˢ S`; `presentation-from : Surjectivity n → ... IsPresentationOf (Sp-group n)`. PresentationFull.agda:41-42 `presentation = presentation-from surj-nf`. Surjectivity.agda: `surj-nf` via `lemma-invnf` and `Theorem-LM : ∀ {n} (p q : Pauli n) → sform p q ≡ ₁ → ∃ λ (lm : ML n) → act [ lm ]ᵐˡ p ≡ pZ₀ × act [ lm ]ᵐˡ q ≡ pX₀` (TheoremLM.agda:128). SoundnessDirect.agda (1109): `sound-ax` one clause per axiom.

Other: Cosets.agda legacy vocab; CongDownK cong↓ᵏ; WordAction act≡ap; ABox/BBox/DBox clearing lemmas; BoxAction closed-form actions.
No postulates anywhere (stale comments say otherwise).
