# Survey: Symplectic/Simplified and box relations — 2026-09-04

Sizes: Simplified/ 7 files 1754 lines (Bijective 257, Iso 174, Lemmas 494, LemmasCZ 246, NfEps 72, Presentation 149, Syntactics 362); BR/ 28 / 7002; Lemmas/ 26 / 11159; Syntactics/ 3 / 1707; Symplectic total 118 / 35399.

## Simplified/Syntactics.agda
```agda
module Examples.Groups.Symplectic.Simplified.Syntactics
  (p-2 : ℕ) (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k )
  where
open Primitive-Root-Modp' g* g-gen
  M₋₁ = M -'₁ ; Mg = M g′ ; Mg^ k = Mg ^ toℕ k
  module SimBase where
    data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where
      order-S :           (₁₊ n) SRel,  S ^ p === ε
      order-H :           (₁₊ n) SRel,  H ^ 2 === M₋₁
      M-power :     ∀ k → (₁₊ n) SRel,  Mg^ k === M (g^ k)
      semi-MS :           (₁₊ n) SRel,  Mg • S === S^ (g * g) • Mg
      semi-M↑CZ :         (₂₊ n) SRel,  Mg ↑ • CZ === CZ^ g • Mg ↑
      semi-M↓CZ :         (₂₊ n) SRel,  Mg ↓ • CZ === CZ^ g • Mg ↓
      order-CZ :          (₂₊ n) SRel,  CZ ^ p === ε
      comm-CZ-S↓ :        (₂₊ n) SRel,  CZ • S ↓ === S ↓ • CZ
      comm-CZ-S↑ :        (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
      selinger-c10 :      (₂₊ n) SRel,  CZ • H ↑ • CZ === S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
      selinger-c11 :      (₂₊ n) SRel,  CZ • H ↓ • CZ === S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
      selinger-c12 :      (₃₊ n) SRel,  CZ ↑ • CZ === CZ • CZ ↑
      selinger-c13 :      (₃₊ n) SRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
      selinger-c14 :      (₃₊ n) SRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
      selinger-c15 :      (₃₊ n) SRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
  _QRel,_===_ = LR._VRel,_===_     -- Lift-Relation of SimBase
```
**15 group-specific (4 one-qudit, 7 two-qudit, 4 three-qudit) + 3 structural (cong↑, comm₁, comm₂) = 18.** M-power is a scheme over k : ℤ ₚ.

Full set (Gates.agda): 17 group-specific (+3 = 20). Differences: full has `order-H : H^4 = ε`, `M-mul x y`, `semi-MS x`, `semi-M↑CZ x`, `semi-M↓CZ x` (schemes over units x), `order-SH`, `comm-HHS`; simplified has `H^2 = M₋₁`, `M-power k`, and semi-rules at g only; order-SH and comm-HHS become theorems (Lemmas1.lemma-order-SH, Lemmas1b.lemma-comm-HHS).

## Simplified/Iso.agda — identity on words both ways
```agda
f-well-defined : ∀ {w v} → n QRel, w ===₁ v → id w ≈₂ id v   -- full axiom from simplified
g-well-defined : ∀ {u t} → n QRel, u ===₂ t → id u ≈₁ id t   -- simplified from full
Theorem-Sym-iso-Sim : ∀ {n} → IsGroupIsomorphism (rawGroup G1.•-ε-group) (rawGroup G2.•-ε-group) id
Theorem-Sym-iso-Sim' : (the converse, also id)
```
f table: order-H←Lemmas1.lemma-order-H; order-SH←lemma-order-SH; comm-HHS←Lemmas1b.lemma-comm-HHS; M-mul←Lemmas1.lemma-M-mul; semi-MS←lemma-semi-MS; semi-M↑CZ/↓CZ←Lemmas2. g: order-H←Derived.lemma-HH-M-1 (HH ≈ M -'₁); M-power←Derived.lemma-M-power; semi-* = full axiom at g.

## Simplified/Lemmas.agda (Lemmas1 n)
lemma-M1 : M₁ ≈ ε (:94); lemma-order-SH : (S • H) ^ 3 ≈ ε (:103); lemma-MgS^k; lemma-Mg^kS; lemma-semi-MS (:208); lemma-Mg^p-1=ε (via Fermat, :229); **lemma-M-mul : ∀ x y → M x • M y ≈ M (x *' y)** (:251-267: rewrite x = g^k, y = g^l by M-power twice, add exponents, reduce mod p-1 by Mg^{p-1} ≈ ε from Fermat, M-power again); lemma-M₋₁^2; lemma-order-H : H ^ 4 ≈ ε (:328). Lemmas1b: lemma-comm-HHS : H • H • S ≈ S • H • H (:473). LemmasCZ Lemmas2: lemma-semi-M↓CZ, lemma-semi-M↑CZ (M x • CZ ≈ CZ^ x' • M x).

## Simplified/Presentation.agda
```agda
_SRel,_===_ = _QRel,_===₂_       -- NOTE: lifted relation
subpresentation : ∀ {n} → (n QRel,_===₂_) IsSubPresentationOf (Sp-group n)
presentation : ∀ {n} → (n SRel,_===_) IsPresentationOf (Sp-group n)   -- = compose Theorem-Sym-iso-Sim' with PresentationFull.presentation via Algebra.Morphism.Construct.Composition
```
Header: "with the SAME interpretation ⟦_⟧: the underlying function on words is unchanged, only the congruence it is quotiented by is presented differently."
Bijective.agda: bijective₂ : BijectiveNormalForm (n QRel,_===₂_) (NF n), NF-dec, bijective₂ε/rep-ε (section patched so inv-nf (nf ε) ≡ ε) — consumed by semidirect. NfEps.agda: negative result nf-ε-positive : inv (nf ε) ≡ ε → ⊥ at width ≥ 1 (tower inverse is always a concatenation).

## Box relations
Derived from the FULL rule set (BR/** + Lemmas/** ≈ 18 000 lines); Simplified reaches them through Iso (≈ 900 lines).
Lemmas/BoxRelations.agda: One: A←H, A←S, E←S (E←S : ∀ b → [ b ]ᵉ • S ≈ [ b + - ₁ ]ᵉ); Two: B←H↑-S↑-S, D←H-S↑-S-CZ; Three: BB←CZ↑ (∀ vb : Vec B 2 → [ vb ]ᵛᵇ • CZ ↑ ≈ dir ⇣ • [ vb' ]ᵛᵇ), B↑←CZ ([ b ]ᵇ ↑ • CZ ≈ dir • [ b ]ᵇ ↑), DD←CZ. Plus L←CZ in BR/Two/L2-CZ.agda (lemma-dir-and-l'). Concrete dir-of cases: A←H 3, A←S 2, E←S 1, B← 9, D← 9, L←CZ 8, BB←CZ↑ 4, B↑←CZ 2, DD←CZ 4 = **42** (matches Cir2Tikz/src/NewBoxRel.hs: 42 relations + 8 box definitions = 50 pictures). "67" appears only in slides prose; paper says 66. Duality (Lemmas/Duality.agda, `dual`) proves each ↑/↓ pair once. BB-CZ-n/DD-CZ-n widen width-3 relations via CongDownK.cong↓ᵏ. Cir2Tikz/test3.tex: Layer 0 = 19 leaf lemmas, Layer 1 = 14 box relation subsections.
BR/Two/L2-CZ/Base.agda: "The preamble of L2-CZ costs about 9 CPU seconds".
Caveat: name `_SRel,_===_` overloaded (generator-level datatype vs lifted alias in Presentation.agda).
