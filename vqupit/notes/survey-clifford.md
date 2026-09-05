# Survey: ProjectivePauli, ProjectiveClifford/Qupit, Clifford/Qupit — 2026-09-04

## ProjectivePauli (1220 lines: Presentation-Alt 779, Semantics 369, Presentation 72)
Presentation-Alt.agda (circuit alphabet XZGate: X-gate, Z-gate : XZGate 1):
```agda
module Base where
  data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where
    order-X :  ∀ {n} → (₁₊ n) SRel,  X ^ p === ε
    order-Z :  ∀ {n} → (₁₊ n) SRel,  Z ^ p === ε
    comm-Z-X : ∀ {n} → (₁₊ n) SRel,  Z • X === X • Z
_QRel,_===_ = LR._VRel,_===_
presentation : ∀ {n} → (n QRel,_===_) IsPresentationOf (+ₚ-group n)   -- :775-779
```
Semantics.agda: `Pauli1 = ℤ ₚ × ℤ ₚ`; `Pauli n = Vec Pauli1 n`; `+ₚ-group n` from IsAbelianGroup (_≡_) _+ₚ_ pIₙ -ₚ_ (:181-204); sform/sform1 symplectic form; iso to iterated stdlib direct power. NF: X^a • Z^b per wire (:460-462); via StarPresentation; exports `sound`, `complete` (:766-773) consumed by ConjAction. Presentation.agda (72 lines) builds Pauli from Cyclic ⋄ Cyclic ⋄ CommRel then ⊕^ n — used only by the Qubit development.

## SemiDirect (978 lines: ConjAction 221, Presentation 223, Syntactics 534)
Syntactics.agda:267-288 (`Gen n = XZ.Gen n ⊎ Sym.Gen n`):
```agda
  conj : Sym.Gen n → XZ.Gen n → Word (XZ.Gen n)
  conj Sym.H-gen   XZ.X-gen           = XZ.Z
  conj Sym.H-gen   XZ.Z-gen           = XZ.X ^ p-1
  conj Sym.H-gen   (xz XZ.↥)          = [ xz ]ʷ XZ.↑
  conj Sym.S-gen   XZ.X-gen           = XZ.X • XZ.Z
  conj Sym.S-gen   XZ.Z-gen           = XZ.Z
  conj Sym.S-gen   (xz XZ.↥)          = [ xz ]ʷ XZ.↑
  conj Sym.CZ-gen  XZ.X-gen           = XZ.X • XZ.Z XZ.↑
  conj Sym.CZ-gen  XZ.Z-gen           = XZ.Z
  conj Sym.CZ-gen  (XZ.X-gen XZ.↥)    = XZ.X XZ.↑ • XZ.Z
  conj Sym.CZ-gen  (XZ.Z-gen XZ.↥)    = XZ.Z XZ.↑
  conj Sym.CZ-gen  (xz XZ.↥ XZ.↥)     = [ xz ]ʷ XZ.↑ XZ.↑
  conj (sym Sym.↥) XZ.X-gen           = XZ.X
  conj (sym Sym.↥) XZ.Z-gen           = XZ.Z
  conj (sym Sym.↥) (xz XZ.↥)          = conj sym xz XZ.↑
  _QRel,_===_ n = XZ._QRel,_===_ n ⋄ Sim._QRel,_===_ n ⋄ ConjRelʷ conj
```
ConjAction.agda: `conjw-sem : ∀ c w → sem ((conj ʰ') c w) ≡ ap ⟦ c ⟧ (sem w)`; 
```agda
respects-Γ : ∀ {n} (c : Gen n) {u v} → (n XZ.QRel, u === v) → PB._≈_ (XZ._QRel,_===_ n) ((conj ⁿ') c u) ((conj ⁿ') c v)
respects-Γ c ax = complete n (Eq.trans (conj-sem c u) (Eq.trans (Eq.cong (ap ⟦ c ⟧ᵍ) (sound-ax ax)) (Eq.sym (conj-sem c v))))
respects-Δ : ∀ {n} {c d : Word (Gen n)} (u : Word (XZ.Gen n)) → Sim._QRel,_===_ n c d → PB._≈_ (XZ._QRel,_===_ n) ((conj ʰ') c u) ((conj ʰ') d u)
```
Both via soundness+completeness of the factor presentations ("the long symplectic rules ... are never conjugated by hand").
Presentation.agda:83-115:
```agda
module Semidirect (n : ℕ) where
  Γ = XZ._QRel,_===_ n ; Δ = NSim.Simplified-Relations._QRel,_===_ n ; cj = SemiDirect.conj {n}
  private module SDP = SDP' Γ Δ cj
  private module P = SDP.Presentation (CA.respects-Δ {n}) (CA.respects-Γ {n}) (+ₚ-group n) (Sp-group n) (XZ.presentation {n}) (SimPres.presentation {n})
  Pauli⋊Sp : Group 0ℓ 0ℓ
  Pauli⋊Sp = P.G1⋊G2
  presentation : (SemiDirect._QRel,_===_ n) IsPresentationOf Pauli⋊Sp
  presentation = P.dpres
```
Unconditional ("no postulate, no hole, no hypothesis"). Pauli⋊Sp uses the transported action act g x = ⟦ conjss (inv₂ g) (inv₁ x) ⟧₁; `Pauli⋊Sp-group n` (Examples/Construct/SemiDirectProduct/Clifford.agda:66-77, Action with act = ap, act-∙-homo = linear-+) is the direct one; `act≡ap`, `∙-agrees` (abstract block; "a two-line lemma about Z ^ j went from 27 s to OOM at 12 GB").

## Simplified-V1 (7899 lines, 11 files) — 19 group-specific rules (Syntactics.agda:142-171)
```agda
      order-S :           ∀ {n} → (₁₊ n) SRel,  S ^ p === ε
      order-H :           ∀ {n} → (₁₊ n) SRel,  H ^ 2 === M₋₁
      M-power : ∀ {n} (k : ℤ ₚ) → (₁₊ n) SRel,  Mg^ k === M (g^ k)
      semi-MR :           ∀ {n} → (₁₊ n) SRel,  Mg • R === R^ (g * g) • Mg
      order-SH :          ∀ {n} → (₁₊ n) SRel,  (S • H) ^ 3 === ε
      comm-HHSHHS :       ∀ {n} → (₁₊ n) SRel,  H • H • S • H • H • S === S • H • H • S • H • H
      semi-M↑CZ :         ∀ {n} → (₂₊ n) SRel,  Mg ↑ • CZ === CZ^ g • Mg ↑
      semi-M↓CZ :         ∀ {n} → (₂₊ n) SRel,  Mg ↓ • CZ === CZ^ g • Mg ↓
      rel-X↑-CZ :         ∀ {n} → (₂₊ n) SRel,  CZ • X ↑ === X ↑ • Z ↓ • CZ
      rel-X↓-CZ :         ∀ {n} → (₂₊ n) SRel,  CZ • X ↓ === X ↓ • Z ↑ • CZ
      order-CZ :          ∀ {n} → (₂₊ n) SRel,  CZ ^ p === ε
      comm-CZ-S↓ :        ∀ {n} → (₂₊ n) SRel,  CZ • S ↓ === S ↓ • CZ
      comm-CZ-S↑ :        ∀ {n} → (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
      selinger-c10 :      ∀ {n} → (₂₊ n) SRel,  CZ • H ↑ • CZ === R ↑ ^ p-1 • H ↑ • R ↑ ^ p-1 • CZ • H ↑ • R ↑ ^ p-1 • R ↓ ^ p-1
      selinger-c11 :      ∀ {n} → (₂₊ n) SRel,  CZ • H ↓ • CZ === R ↓ ^ p-1 • H ↓ • R ↓ ^ p-1 • CZ • H ↓ • R ↓ ^ p-1 • R ↑ ^ p-1
      selinger-c12 :      ∀ {n} → (₃₊ n) SRel,  CZ ↑ • CZ === CZ • CZ ↑
      selinger-c13 :      ∀ {n} → (₃₊ n) SRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
      selinger-c14 :      ∀ {n} → (₃₊ n) SRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
      selinger-c15 :      ∀ {n} → (₃₊ n) SRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε
```
Words: Z = H • H • S • H • H • S⁻¹ ; X = H • S • H • H • S⁻¹ • H ; R = S • Z^ 1/2 ; M x' = R^ x • H • R^ x⁻¹ • H • R^ x • H ; Mg = M g′. `X • Z === Z • X` NOT an axiom (LemmasXZ.Lemmas1b.lemma-comm-X-Z).
Forward.agda:74-87:
```agda
  f : ∀ {n} -> SemiDirect.Gen n -> Word (Gen n)
  f SemiDirect.X-gen = Clifford.X
  f SemiDirect.Z-gen = Clifford.Z
  f SemiDirect.H-gen = Cli.H
  f SemiDirect.S-gen = Clifford.R
  f SemiDirect.CZ-gen = Cli.CZ
  f {₁₊ n} (inj₁ (x XZ.↥)) = f (inj₁ x) ↑
  f {₁₊ n} (inj₂ (y Sym.↥)) = f (inj₂ y) ↑
  h : ∀ {n} -> Cli.Gen n -> Word (SemiDirect.Gen n)
  h Cli.H-gen = SemiDirect.H
  h Cli.S-gen = SemiDirect.Z^ -1/2 • SemiDirect.S
  h Cli.CZ-gen = SemiDirect.CZ
  h (x Cli.↥) = (h x) SemiDirect.↑
```
Iso.agda:895-987: f-left-inv-gen, g-left-inv-gen, `Theorem-SemiDirect-iso-Clifford : IsGroupIsomorphism ... (f ʷ)` via StarGroupIsomorphism. Presentation.agda:153-161: `presentation : ∀ {n} → (Cli.Clifford-Relations._QRel,_===_ n) IsPresentationOf (SDPres.Semidirect.Pauli⋊Sp n)`.
Files: Lemmas 517 (Lemmas1: multiplier calculus, grouplike), Tactics 197 (CommData-Sim, Rewriting-Sim step function ~60 clauses), LemmasXZ 809 (Pauli conjugation calculus), LemmasCZ 726, SemiM 1154 (dead), ExRules 1390 (Paper-V0's seven Ex rules proved inside V1 by transport), Forward 594, Iso 987, Soundness 849 (scratch, dead), Syntactics 515, Presentation 161.

## Paper-V0 (5674: Syntactics 526, Lemmas 4754, Iso 255, Presentation 139) — 16 rules
```agda
      order-S :       (₁₊ n) SRel,  S ^ p === ε
      order-H :       (₁₊ n) SRel,  H ^ 2 === M₋₁
      M-power : ∀ k → (₁₊ n) SRel,  XMg^ k === XM (g^ k)
      semi-MR :       (₁₊ n) SRel,  XMg • R^  (g * g) === R • XMg
      order-SH :      (₁₊ n) SRel,  (S • H) ^ 3 === ε
      comm-HHSHHS :   (₁₊ n) SRel,  H • H • S • H • H • S === S • H • H • S • H • H
      order-CZ :      (₂₊ n) SRel,  CZ ^ p === ε
      order-Ex :      (₂₊ n) SRel,  Ex ^ 2 === ε
      comm-CZ-S↑ :    (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
      semi-M↑CZ :     (₂₊ n) SRel,  XMg ↑ • CZ^ g === CZ • XMg ↑
      semi-Ex-S↑ :    (₂₊ n) SRel,  Ex • S ↑ === S ↓ • Ex
      semi-Ex-H↑ :    (₂₊ n) SRel,  Ex • H ↑ === H ↓ • Ex
      blake-c12 :     (₂₊ n) SRel,  (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ
      yang-baxter :   (₃₊ n) SRel,  Ex ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • Ex ↓
      cz-slide :      (₃₊ n) SRel,  Ex ↓ • Ex ↑ • CZ === CZ ↑ • Ex ↓ • Ex ↑
      semi-CX↑-CZ↓ :  (₃₊ n) SRel,  CZ ↓ • CX ↑ === CZ02 • CX ↑ • CZ ↓
```
RHR a b = R^ a • H • R^ b • H • R^ a • H ; M x' = RHR x x⁻¹ ; XM x' = RHR x⁻¹ x ; XMg = XM g′. Swap–CZ commutation and both Pauli-vs-CZ rules are derived, not axioms. Iso: identity on words; `v1⇒pap : w ≈ v → w ≈' v` (Star-Congruence.lemma-id*-cong g-well-defined); `Theorem-PaperV0-iso-V1 : IsGroupIsomorphism ... id`. Ten axioms shared verbatim; 15 remaining: Paper-V0.Lemmas (8 V1-only + 2 Pauli-vs-CZ + 3 multiplier) and Simplified-V1.ExRules (7 Paper-V0-only). `presentation : ∀ (n : ℕ) → (n CRel,_===_) IsPresentationOf (Pauli⋊Sp n)`. Lemmas.agda: One-Wire, Paper-GroupLike (native, needs right-cancellation), Ex-Conjugation (:1010-3382; lemma-Ex-CZ, lemma-rel-X↓-CZ/X↑-CZ, lemma-selinger-c10 (:3280), c11 = c10 conjugated by swap), Down-Rules, Three-Wire (c12 by •-cancelʳ against Ex • Ex ↑; c13 both sides CZ02; c14 telescopes since ⊤⊥ ↑ has order 3; c15 = c14 transported along transposition of wires 0 and 2).

## Paper-V1 (2560) — 15 rules: Paper-V0 minus order-SH, semi-MR respelled:
```agda
      order-H :       (₁₊ n) SRel,  H ^ 2 === XM₋₁
      M-power : ∀ k → (₁₊ n) SRel,  XMg^ k === XM (g^ k)
      semi-MR :       (₁₊ n) SRel,  XMg • S^ (g * g) • Z^ ((g * g + - g) * 1/2) === S • XMg
  SHS' a b = Z^ ((b + - ₁) * 1/2) • X^ ((₁ + - a) * 1/2) • S^ b • H • S^ a • H • S^ b • H
  M x' = SHS' ((x' ⁻¹) .proj₁) (x' .proj₁) ; XM x' = SHS x' = SHS' x x⁻¹
```
(performance note: double inversion "makes even XM≡M⁻¹ take minutes"). Iso: identity on words; 11 axioms straight across; 4 (order-H, M-power, semi-MR, semi-M↑CZ) need R↔S bridge (Shared.PauliBase at Simplified-V1, transported by v1⇒pap); order-SH: `g-well-defined PapV0R.order-SH = PapL.One-Wire.lemma-order-SH n`.
OneWire.agda: lemma-M1 (:167), lemma-M1-unfold : M₁ ≈ (S • H) ^ 3 (:184-203, prefix exponents (1−1)·½ = 0 vanish), lemma-order-SH = trans (sym lemma-M1-unfold) lemma-M1 (:213). `presentation : ∀ (n : ℕ) → (n CRel,_===_) IsPresentationOf (Pauli⋊Sp n)` — exported by MainTheorems.clifford-presentation.

## Shared/PauliBase.agda (885)
`module Calculus (n) (Γ) (grouplike) (order-S' : S ^ p ≈ ε) (order-H4 : H ^ 4 ≈ ε) (order-SH' : (S • H) ^ 3 ≈ ε)`: S⁻¹S, lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹, lemma-HSH. `module BridgeCalc (n) (Γ) (order-X) (order-Z) (comm-Z-S) (comm-X-Z) (conj-H-X^k) (conj-X^k-H) (lemma-XS) (pow-mod) (induction) (inductionˡ)`: MulZ (Z-W : ∀ k → Z^ k • W ≈ W • Z^ (a * k)), SemiMR (S⇒R, R⇒S), Bridge (bridge : RHR a b ≈ SHS' a b).

## Clifford/Qupit (5029) — scalars
Syntactics.agda:130-197: `Scalar-relation = p Cn,_===_` (ω from Cyclic.Syntactics: renaming X to ScalarGen, T to ω); `conj _ _ = ω` (central); `sh-exponent = (p * p ∸ 1) / 8`; `ω^SH = ω ^ sh-exponent`; `srel-corr CB.order-SH = ω^SH ; srel-corr _ = ε`; `corr (CR.srel r) = srel-corr r ; corr (CR.cong↑ r) = corr r ; corr (comm₁) = ε ; corr (comm₂) = ε`;
```agda
_Exact,_===_ : (n : ℕ) → WRel (ScalarGen ⊎ Gen n)
_Exact,_===_ n = extension-presentation Scalar-relation (n CR.QRel,_===_) conj corr
```
Quotient = Paper-V0 (16 rules). Header: matrix conventions (δ_p), "exactly ONE of the sixteen ... fails on the nose, order-SH picks up ω^((p²-1)/8)"; residues p=3..47: 1,3,6,4,8,2,7,20,18,27,23,5,16,41. No matrices in Agda.
Semantics.agda: Model A (structural): `record Scalar` (ω^_ exponent : ℤ ₚ); `cocy (P , S) (Q , _) = 1/2 * sform P (ap S Q)`; `weyl : Cocycle Scalar-abelianGroup (Pauli⋊Sp-group n)`; `Clifford-group = CE.group Scalar-abelianGroup (Pauli⋊Sp-group n) weyl`; `Clifford-extension = CE.centralExtension ...`; multiplication (ω^e , g) ·ᶜ (ω^f , h) = (ω^(e + f + cocy g h) , g ∙ h); heisenberg law. Model B (Presented-Extension g* g-gen): `A n = CGn.K n` (scalars as words), `H n = CGn.Q n` (Paper-V0 word group), `φ n = trivialAction`; `record GeneratorData n` (G, G-cong, G-ε, f-axiom); `Presented-group n gd = CE.group (A n) (H n) (γᶜ n gd)`; `Presented-extension n gd = CE.centralExtension ...`; `Realises-corr = ∀ {u v} (r : QRel u v) → scal u ≈ QS.corr r • scal v`; split-forces (non-split since ω^((p²−1)/8) ≠ ε). **Model A vs Model B total groups not proved equal** (Semantics.agda:585-589).
Presentation.agda: `presentation-exact : ∀ (n : ℕ) → (n Exact,_===_) IsPresentationOf (PE.Presented-group n (exact-generator-data n))` (:641-645), unconditional; monoid presentation promoted. SemFE pulls weyl back along Paper-V0's presentation (generator-data); SemRealises reduces Realises to equations on phase Φ : Circuit n → ℤ/pℤ; SemShift (Φ-↑); SemLocal (one-wire phase calculus, has-SH3); SemZBlock (blake-c12 pure-Z); SemSHExp ((p²−1)/8 ≡ −⅛); SemSRel (dispatcher `realises`).
NOT formalised: link to unitary matrices; the "glue facts" (projective Clifford ≅ Pauli⋊Sp; Clifford = central extension) — the theorems are about the constructed groups; Model A ≠ Model B identification; Clifford/Qupit not reached from MainTheorems root (typechecks separately). Slides cite `Theorem-Clifford = CQP.presentation-exact`.

## Simplified-V2 (4132): fifth rule set (~24 constructors) with Pauli parts pushed right; identity iso onto V1; nothing imports it.
