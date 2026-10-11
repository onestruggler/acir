------------------------------------------------------------------------
-- Presentations of groups
--
-- Auxiliary equations on one and two qubits (Clément, Appendix B,
-- Figure 12: Equations (81) … (110)), derived from Figure 4
--
-- These are the identities the two-qubit completeness proof rewrites
-- with (Appendix C).  Each family of equations is derived once and
-- then transported along the conjugations of Conjugation: negating a
-- control (N↑, N↓) and swapping the wires (S).  The names follow the
-- paper's numbering where the equation is in Figure 12 (eq84, …);
-- the others are the images and intermediate forms named by their
-- content (CH-°CZ : CH • °CZ ≈ °CZ • CH, …).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.TwoQubit.Auxiliary where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- One wire: the box Z • Z° is central, and Z° = Z up to it

module _ {n : ℕ} where
  open Tools ((₁₊ n) VRel,_===_)

  private
    ZHZHZH : Circuit (₁₊ n)
    ZHZHZH = Z • H • Z • H • Z • H

    □HZ : (Z • Z°) • H • Z ≈ ZHZHZH
    □HZ = begin
      (Z • Z°) • H • Z
        ≈⟨ by-assoc Eq.refl ⟩
      (Z • H • Z • H • Z • H • Z) • (H • H) • Z
        ≈⟨ cancelᵐ _ _ H² ⟩
      (Z • H • Z • H • Z • H • Z) • Z
        ≈⟨ by-assoc Eq.refl ⟩
      ZHZHZH • (Z • Z)
        ≈⟨ cancelᵉ _ Z² ⟩
      ZHZHZH ∎

    HZ□ : H • Z • (Z • Z°) ≈ ZHZHZH
    HZ□ = begin
      H • Z • (Z • Z°)
        ≈⟨ by-assoc Eq.refl ⟩
      H • (Z • Z) • (H • Z • H • Z • H • Z • H)
        ≈⟨ cancelᵐ _ _ Z² ⟩
      H • (H • Z • H • Z • H • Z • H)
        ≈⟨ by-assoc Eq.refl ⟩
      (H • H) • ZHZHZH
        ≈⟨ cancelˢ _ H² ⟩
      ZHZHZH ∎

    HZ° : H • Z° ≈ ZHZHZH
    HZ° = begin
      H • Z°
        ≈⟨ by-assoc Eq.refl ⟩
      (H • H) • ZHZHZH
        ≈⟨ cancelˢ _ H² ⟩
      ZHZHZH ∎

  -- The box before H • Z is H • Z°, and it commutes with H • Z.
  □-HZ : (Z • Z°) • H • Z ≈ H • Z°
  □-HZ = trans □HZ (sym HZ°)

  HZ-□ : H • Z • (Z • Z°) ≈ (Z • Z°) • H • Z
  HZ-□ = trans HZ□ (sym □HZ)

------------------------------------------------------------------------
-- Two wires

module _ {n : ℕ} where
  open Tools ((₂₊ n) VRel,_===_)

  -- The one-wire facts on the upper wire.
  □-HZ↑ : (Z ↑ • Z° ↑) • H ↑ • Z ↑ ≈ H ↑ • Z° ↑
  □-HZ↑ = lemma-cong↑ ((Z • Z°) • H • Z) (H • Z°) □-HZ

  HZ-□↑ : H ↑ • Z ↑ • (Z ↑ • Z° ↑) ≈ (Z ↑ • Z° ↑) • H ↑ • Z ↑
  HZ-□↑ = lemma-cong↑ (H • Z • (Z • Z°)) ((Z • Z°) • H • Z) HZ-□

  ----------------------------------------------------------------------
  -- Merging controls: (6), (7) and their images

  CZ-°CZ : CZ • °CZ ≈ Z ↓
  CZ-°CZ = ax merge-CZ

  °CZ-CZ : °CZ • CZ ≈ Z ↓
  °CZ-CZ = N↑.⟪⟫-≈ CZ-°CZ (N↑.⟪⟫-•₂ refl N↑-°CZ) N↑-Z↓

  CZ-CZ° : CZ • CZ° ≈ Z ↑
  CZ-CZ° = S.⟪⟫-≈ CZ-°CZ (S.⟪⟫-•₂ S-CZ S-°CZ) S-Z↓

  CZ°-CZ : CZ° • CZ ≈ Z ↑
  CZ°-CZ = S.⟪⟫-≈ °CZ-CZ (S.⟪⟫-•₂ S-°CZ S-CZ) S-Z↓

  °CZ-°CZ° : °CZ • °CZ° ≈ Z° ↑
  °CZ-°CZ° = N↑.⟪⟫-≈ CZ-CZ° (N↑.⟪⟫-•₂ refl N↑-CZ°) refl

  °CZ°-°CZ : °CZ° • °CZ ≈ Z° ↑
  °CZ°-°CZ = N↑.⟪⟫-≈ CZ°-CZ (N↑.⟪⟫-•₂ N↑-CZ° refl) refl

  CZ°-°CZ° : CZ° • °CZ° ≈ Z° ↓
  CZ°-°CZ° = N↓.⟪⟫-≈ CZ-°CZ (N↓.⟪⟫-•₂ refl N↓-°CZ) refl

  °CZ°-CZ° : °CZ° • CZ° ≈ Z° ↓
  °CZ°-CZ° = N↓.⟪⟫-≈ °CZ-CZ (N↓.⟪⟫-•₂ N↓-°CZ refl) refl

  -- (90), (91), and the doubly negated form.
  eq90 : CZ • °CZ ≈ °CZ • CZ
  eq90 = trans CZ-°CZ (sym °CZ-CZ)

  eq91 : CZ • CZ° ≈ CZ° • CZ
  eq91 = trans CZ-CZ° (sym CZ°-CZ)

  °CZ°-°CZ-comm : °CZ° • °CZ ≈ °CZ • °CZ°
  °CZ°-°CZ-comm = trans °CZ°-°CZ (sym °CZ-°CZ°)

  CH-°CH : CH • °CH ≈ H ↓
  CH-°CH = ax merge-CH

  °CH-CH : °CH • CH ≈ H ↓
  °CH-CH = N↑.⟪⟫-≈ CH-°CH (N↑.⟪⟫-•₂ refl N↑-°CH) N↑-H↓

  HC-HC° : HC • HC° ≈ H ↑
  HC-HC° = S.⟪⟫-≈ CH-°CH (S.⟪⟫-•₂ refl S-°CH) S-H↓

  HC°-HC : HC° • HC ≈ H ↑
  HC°-HC = S.⟪⟫-≈ °CH-CH (S.⟪⟫-•₂ S-°CH refl) S-H↓

  -- (92)
  eq92 : CH • °CH ≈ °CH • CH
  eq92 = trans CH-°CH (sym °CH-CH)

  ----------------------------------------------------------------------
  -- Involutions

  °CZ² : °CZ • °CZ ≈ ε
  °CZ² = N↑.⟪⟫-invol CZ²

  CZ°² : CZ° • CZ° ≈ ε
  CZ°² = N↓.⟪⟫-invol CZ²

  °CZ°² : °CZ° • °CZ° ≈ ε
  °CZ°² = trans (cong (sym N↓-°CZ) (sym N↓-°CZ)) (N↓.⟪⟫-invol °CZ²)

  °CH² : °CH • °CH ≈ ε
  °CH² = N↑.⟪⟫-invol CH²

  HC² : HC • HC ≈ ε
  HC² = S.⟪⟫-invol CH²

  HC°² : HC° • HC° ≈ ε
  HC°² = N↓.⟪⟫-invol HC²

  -- (82), (83)
  CX² : CX • CX ≈ ε
  CX² = conj-invol H² CZ²

  °CX² : °CX • °CX ≈ ε
  °CX² = N↑.⟪⟫-invol CX²

  XC² : XC • XC ≈ ε
  XC² = S.⟪⟫-invol CX²

  XC°² : XC° • XC° ≈ ε
  XC°² = N↓.⟪⟫-invol XC²

  ----------------------------------------------------------------------
  -- (93): CH absorbs H on its target, becoming °CH

  CH-H↓ : CH • H ↓ ≈ °CH
  CH-H↓ = trans (back _ (sym CH-°CH)) (cancelˡ _ CH²)

  H↓-CH : H ↓ • CH ≈ °CH
  H↓-CH = trans (front _ (sym °CH-CH)) (cancelʳ _ CH²)

  °CH-H↓ : °CH • H ↓ ≈ CH
  °CH-H↓ = trans (back _ (sym °CH-CH)) (cancelˡ _ °CH²)

  H↓-°CH : H ↓ • °CH ≈ CH
  H↓-°CH = trans (front _ (sym CH-°CH)) (cancelʳ _ °CH²)

  eq93 : CH • H ↓ ≈ H ↓ • CH
  eq93 = trans CH-H↓ (sym H↓-CH)

  ----------------------------------------------------------------------
  -- (10) and its images

  CH-°CZ : CH • °CZ ≈ °CZ • CH
  CH-°CZ = ax comm-CH-°CZ

  °CH-CZ : °CH • CZ ≈ CZ • °CH
  °CH-CZ = N↑.⟪⟫-≈ CH-°CZ (N↑.⟪⟫-•₂ refl N↑-°CZ) (N↑.⟪⟫-•₂ N↑-°CZ refl)

  HC-CZ° : HC • CZ° ≈ CZ° • HC
  HC-CZ° = S.⟪⟫-≈ CH-°CZ (S.⟪⟫-•₂ refl S-°CZ) (S.⟪⟫-•₂ S-°CZ refl)

  HC°-CZ : HC° • CZ ≈ CZ • HC°
  HC°-CZ = S.⟪⟫-≈ °CH-CZ (S.⟪⟫-•₂ S-°CH S-CZ) (S.⟪⟫-•₂ S-CZ S-°CH)

  ----------------------------------------------------------------------
  -- The CNOTs as conjugates of CZ

  °CX-alt : °CX ≈ H ↓ • °CZ • H ↓
  °CX-alt = N↑.⟪⟫-•₃ N↑-H↓ refl N↑-H↓

  XC-alt : XC ≈ H ↑ • CZ • H ↑
  XC-alt = S.⟪⟫-•₃ S-H↓ S-CZ S-H↓

  XC°-alt : XC° ≈ H ↑ • CZ° • H ↑
  XC°-alt = N↓.⟪⟫-≈ˡ XC-alt (N↓.⟪⟫-•₃ N↓-H↑ refl N↓-H↑)

  -- CX = CH • CZ • CH, and so (103).
  CX-alt : CX ≈ CH • CZ • CH
  CX-alt = begin
    H ↓ • CZ • H ↓
      ≈⟨ cong (sym CH-°CH) (back _ (sym °CH-CH)) ⟩
    (CH • °CH) • CZ • (°CH • CH)
      ≈⟨ by-assoc Eq.refl ⟩
    CH • (°CH • CZ) • °CH • CH
      ≈⟨ mid _ _ °CH-CZ ⟩
    CH • (CZ • °CH) • °CH • CH
      ≈⟨ by-assoc Eq.refl ⟩
    (CH • CZ) • (°CH • °CH) • CH
      ≈⟨ cancelᵐ _ _ °CH² ⟩
    (CH • CZ) • CH
      ≈⟨ assoc ⟩
    CH • CZ • CH ∎

  eq103 : CH • CX • CH ≈ CZ
  eq103 = trans (mid _ _ CX-alt) (unconj CH²)

  ----------------------------------------------------------------------
  -- (94)–(96): controlled gates on different controls commute

  eq94 : CH • °CX ≈ °CX • CH
  eq94 = begin
    CH • °CX
      ≈⟨ back _ °CX-alt ⟩
    CH • (H ↓ • °CZ • H ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    (CH • H ↓) • °CZ • H ↓
      ≈⟨ front _ eq93 ⟩
    (H ↓ • CH) • °CZ • H ↓
      ≈⟨ by-assoc Eq.refl ⟩
    H ↓ • (CH • °CZ) • H ↓
      ≈⟨ mid _ _ CH-°CZ ⟩
    H ↓ • (°CZ • CH) • H ↓
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • °CZ) • (CH • H ↓)
      ≈⟨ back _ eq93 ⟩
    (H ↓ • °CZ) • (H ↓ • CH)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • °CZ • H ↓) • CH
      ≈⟨ front _ (sym °CX-alt) ⟩
    °CX • CH ∎

  eq95 : °CH • CX ≈ CX • °CH
  eq95 = N↑.⟪⟫-≈ eq94 (N↑.⟪⟫-•₂ refl N↑-°CX) (N↑.⟪⟫-•₂ N↑-°CX refl)

  HC°-XC : HC° • XC ≈ XC • HC°
  HC°-XC = S.⟪⟫-≈ eq95 (S.⟪⟫-•₂ S-°CH refl) (S.⟪⟫-•₂ refl S-°CH)

  HC-XC° : HC • XC° ≈ XC° • HC
  HC-XC° = S.⟪⟫-≈ eq94 (S.⟪⟫-•₂ refl S-°CX) (S.⟪⟫-•₂ S-°CX refl)

  eq96 : CX • °CZ ≈ °CZ • CX
  eq96 = begin
    CX • °CZ
      ≈⟨ front _ CX-alt ⟩
    (CH • CZ • CH) • °CZ
      ≈⟨ by-assoc Eq.refl ⟩
    (CH • CZ) • (CH • °CZ)
      ≈⟨ back _ CH-°CZ ⟩
    (CH • CZ) • (°CZ • CH)
      ≈⟨ by-assoc Eq.refl ⟩
    CH • (CZ • °CZ) • CH
      ≈⟨ mid _ _ eq90 ⟩
    CH • (°CZ • CZ) • CH
      ≈⟨ by-assoc Eq.refl ⟩
    (CH • °CZ) • CZ • CH
      ≈⟨ front _ CH-°CZ ⟩
    (°CZ • CH) • CZ • CH
      ≈⟨ by-assoc Eq.refl ⟩
    °CZ • (CH • CZ • CH)
      ≈⟨ back _ (sym CX-alt) ⟩
    °CZ • CX ∎

  °CX-CZ : °CX • CZ ≈ CZ • °CX
  °CX-CZ = N↑.⟪⟫-≈ eq96 (N↑.⟪⟫-•₂ refl N↑-°CZ) (N↑.⟪⟫-•₂ N↑-°CZ refl)

  XC-CZ° : XC • CZ° ≈ CZ° • XC
  XC-CZ° = S.⟪⟫-≈ eq96 (S.⟪⟫-•₂ refl S-°CZ) (S.⟪⟫-•₂ S-°CZ refl)

  XC°-CZ : XC° • CZ ≈ CZ • XC°
  XC°-CZ = S.⟪⟫-≈ °CX-CZ (S.⟪⟫-•₂ S-°CX S-CZ) (S.⟪⟫-•₂ S-CZ S-°CX)

  ----------------------------------------------------------------------
  -- (84), (85), (88), (89), (100), (101): CNOT and its negation

  eq84 : CX • °CX ≈ X ↓
  eq84 = begin
    CX • °CX
      ≈⟨ back _ °CX-alt ⟩
    (H ↓ • CZ • H ↓) • (H ↓ • °CZ • H ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ) • (H ↓ • H ↓) • (°CZ • H ↓)
      ≈⟨ cancelᵐ _ _ H² ⟩
    (H ↓ • CZ) • (°CZ • H ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    H ↓ • (CZ • °CZ) • H ↓
      ≈⟨ mid _ _ CZ-°CZ ⟩
    H ↓ • Z ↓ • H ↓ ∎

  °CX-CX : °CX • CX ≈ X ↓
  °CX-CX = N↑.⟪⟫-≈ eq84 (N↑.⟪⟫-•₂ refl N↑-°CX) N↑-X↓

  eq85 : CX • °CX ≈ °CX • CX
  eq85 = trans eq84 (sym °CX-CX)

  eq88 : CX • X ↓ ≈ °CX
  eq88 = trans (back _ (sym eq84)) (cancelˡ _ CX²)

  eq89 : °CX • X ↓ ≈ CX
  eq89 = trans (back _ (sym °CX-CX)) (cancelˡ _ °CX²)

  X↓-CX : X ↓ • CX ≈ °CX
  X↓-CX = trans (front _ (sym °CX-CX)) (cancelʳ _ CX²)

  X↓-°CX : X ↓ • °CX ≈ CX
  X↓-°CX = trans (front _ (sym eq84)) (cancelʳ _ °CX²)

  eq100 : CX • X ↓ ≈ X ↓ • CX
  eq100 = trans eq88 (sym X↓-CX)

  eq101 : X ↓ • CX • X ↓ ≈ CX
  eq101 = N↓.⟪⟫-fix (sym eq100)

  °CX-X↓-comm : °CX • X ↓ ≈ X ↓ • °CX
  °CX-X↓-comm = N↑.⟪⟫-≈ eq100 (N↑.⟪⟫-•₂ refl N↑-X↓) (N↑.⟪⟫-•₂ N↑-X↓ refl)

  N↓-°CX : X ↓ • °CX • X ↓ ≈ °CX
  N↓-°CX = N↓.⟪⟫-fix (sym °CX-X↓-comm)

  -- The swapped forms: XC commutes with X on the upper wire, and
  -- absorbs it into a negated control.
  XC-X↑-comm : XC • X ↑ ≈ X ↑ • XC
  XC-X↑-comm = S.⟪⟫-≈ eq100 (S.⟪⟫-•₂ refl S-X↓) (S.⟪⟫-•₂ S-X↓ refl)

  XC°-X↑-comm : XC° • X ↑ ≈ X ↑ • XC°
  XC°-X↑-comm = S.⟪⟫-≈ °CX-X↓-comm (S.⟪⟫-•₂ S-°CX S-X↓) (S.⟪⟫-•₂ S-X↓ S-°CX)

  N↑-XC : X ↑ • XC • X ↑ ≈ XC
  N↑-XC = N↑.⟪⟫-fix (sym XC-X↑-comm)

  N↑-XC° : X ↑ • XC° • X ↑ ≈ XC°
  N↑-XC° = N↑.⟪⟫-fix (sym XC°-X↑-comm)

  XC-X↑ : XC • X ↑ ≈ XC°
  XC-X↑ = S.⟪⟫-≈ eq88 (S.⟪⟫-•₂ refl S-X↓) S-°CX

  X↑-XC : X ↑ • XC ≈ XC°
  X↑-XC = S.⟪⟫-≈ X↓-CX (S.⟪⟫-•₂ S-X↓ refl) S-°CX

  XC°-X↑ : XC° • X ↑ ≈ XC
  XC°-X↑ = S.⟪⟫-≈ eq89 (S.⟪⟫-•₂ S-°CX S-X↓) refl

  X↑-XC° : X ↑ • XC° ≈ XC
  X↑-XC° = S.⟪⟫-≈ X↓-°CX (S.⟪⟫-•₂ S-X↓ S-°CX) refl

  ----------------------------------------------------------------------
  -- (97), (98): CNOT moves the control of CZ

  eq97 : CX • CZ ≈ CZ° • CX
  eq97 = begin
    CX • CZ
      ≈⟨ front _ (sym X↓-°CX) ⟩
    (X ↓ • °CX) • CZ
      ≈⟨ assoc ⟩
    X ↓ • (°CX • CZ)
      ≈⟨ back _ °CX-CZ ⟩
    X ↓ • (CZ • °CX)
      ≈⟨ back _ (back _ (insertˡ _ X²)) ⟩
    X ↓ • (CZ • (X ↓ • X ↓ • °CX))
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↓ • CZ • X ↓) • (X ↓ • °CX)
      ≈⟨ back _ X↓-°CX ⟩
    CZ° • CX ∎

  eq98 : CX • CZ • CX ≈ CZ°
  eq98 = trans (sym assoc) (trans (front _ eq97) (cancelʳ _ CX²))

  XC-CZ-XC : XC • CZ • XC ≈ °CZ
  XC-CZ-XC = S.⟪⟫-≈ eq98 (S.⟪⟫-•₃ refl S-CZ refl) S-CZ°

  ----------------------------------------------------------------------
  -- (99): HC° commutes with °CZ, and CH with Z on its control

  eq99 : HC° • °CZ ≈ °CZ • HC°
  eq99 = begin
    HC° • °CZ
      ≈⟨ back _ (sym XC-CZ-XC) ⟩
    HC° • (XC • CZ • XC)
      ≈⟨ by-assoc Eq.refl ⟩
    (HC° • XC) • CZ • XC
      ≈⟨ front _ HC°-XC ⟩
    (XC • HC°) • CZ • XC
      ≈⟨ by-assoc Eq.refl ⟩
    XC • (HC° • CZ) • XC
      ≈⟨ mid _ _ HC°-CZ ⟩
    XC • (CZ • HC°) • XC
      ≈⟨ by-assoc Eq.refl ⟩
    (XC • CZ) • (HC° • XC)
      ≈⟨ back _ HC°-XC ⟩
    (XC • CZ) • (XC • HC°)
      ≈⟨ by-assoc Eq.refl ⟩
    (XC • CZ • XC) • HC°
      ≈⟨ front _ XC-CZ-XC ⟩
    °CZ • HC° ∎

  °CH-CZ° : °CH • CZ° ≈ CZ° • °CH
  °CH-CZ° = S.⟪⟫-≈ eq99 (S.⟪⟫-•₂ S-HC° S-°CZ) (S.⟪⟫-•₂ S-°CZ S-HC°)

  CH-°CZ° : CH • °CZ° ≈ °CZ° • CH
  CH-°CZ° = N↑.⟪⟫-≈ °CH-CZ° (N↑.⟪⟫-•₂ N↑-°CH N↑-CZ°) (N↑.⟪⟫-•₂ N↑-CZ° N↑-°CH)

  °CH-Z↑ : °CH • Z ↑ ≈ Z ↑ • °CH
  °CH-Z↑ = begin
    °CH • Z ↑           ≈⟨ back _ (sym CZ-CZ°) ⟩
    °CH • (CZ • CZ°)    ≈⟨ sym assoc ⟩
    (°CH • CZ) • CZ°    ≈⟨ front _ °CH-CZ ⟩
    (CZ • °CH) • CZ°    ≈⟨ assoc ⟩
    CZ • (°CH • CZ°)    ≈⟨ back _ °CH-CZ° ⟩
    CZ • (CZ° • °CH)    ≈⟨ sym assoc ⟩
    (CZ • CZ°) • °CH    ≈⟨ front _ CZ-CZ° ⟩
    Z ↑ • °CH ∎

  CH-Z°↑ : CH • Z° ↑ ≈ Z° ↑ • CH
  CH-Z°↑ = N↑.⟪⟫-≈ °CH-Z↑ (N↑.⟪⟫-•₂ N↑-°CH refl) (N↑.⟪⟫-•₂ refl N↑-°CH)

  CH-Z↑ : CH • Z ↑ ≈ Z ↑ • CH
  CH-Z↑ = begin
    CH • Z ↑            ≈⟨ front _ (sym H↓-°CH) ⟩
    (H ↓ • °CH) • Z ↑   ≈⟨ assoc ⟩
    H ↓ • (°CH • Z ↑)   ≈⟨ back _ °CH-Z↑ ⟩
    H ↓ • (Z ↑ • °CH)   ≈⟨ sym assoc ⟩
    (H ↓ • Z ↑) • °CH   ≈⟨ front _ H↓-Z↑ ⟩
    (Z ↑ • H ↓) • °CH   ≈⟨ assoc ⟩
    Z ↑ • (H ↓ • °CH)   ≈⟨ back _ H↓-°CH ⟩
    Z ↑ • CH ∎

  °CH-Z°↑ : °CH • Z° ↑ ≈ Z° ↑ • °CH
  °CH-Z°↑ = N↑.⟪⟫-≈ CH-Z↑ (N↑.⟪⟫-•₂ refl refl) (N↑.⟪⟫-•₂ refl refl)

  -- (109)
  eq109 : (Z • Z°) ↑ • CH ≈ CH • (Z • Z°) ↑
  eq109 = begin
    (Z ↑ • Z° ↑) • CH   ≈⟨ assoc ⟩
    Z ↑ • (Z° ↑ • CH)   ≈⟨ back _ (sym CH-Z°↑) ⟩
    Z ↑ • (CH • Z° ↑)   ≈⟨ sym assoc ⟩
    (Z ↑ • CH) • Z° ↑   ≈⟨ front _ (sym CH-Z↑) ⟩
    (CH • Z ↑) • Z° ↑   ≈⟨ assoc ⟩
    CH • (Z ↑ • Z° ↑) ∎

  ----------------------------------------------------------------------
  -- (110): Equation (11) with the negated forms

  -- (11) with Z° in place of Z.
  private
    eq11° : CH • H ↑ • Z° ↑ • CH • H ↑ ≈ H ↑ • Z° ↑ • CH • H ↑ • CH
    eq11° = begin
      CH • H ↑ • Z° ↑ • CH • H ↑
        ≈⟨ back _ (back _ (front _ (insertˡ _ Z²↑))) ⟩
      CH • H ↑ • (Z ↑ • Z ↑ • Z° ↑) • CH • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      CH • (H ↑ • Z ↑ • (Z ↑ • Z° ↑)) • CH • H ↑
        ≈⟨ mid _ _ HZ-□↑ ⟩
      CH • ((Z ↑ • Z° ↑) • H ↑ • Z ↑) • CH • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      (CH • (Z ↑ • Z° ↑)) • H ↑ • Z ↑ • CH • H ↑
        ≈⟨ front _ (sym eq109) ⟩
      ((Z ↑ • Z° ↑) • CH) • H ↑ • Z ↑ • CH • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      (Z ↑ • Z° ↑) • (CH • H ↑ • Z ↑ • CH • H ↑)
        ≈⟨ back _ (ax slide-CH) ⟩
      (Z ↑ • Z° ↑) • (H ↑ • Z ↑ • CH • H ↑ • CH)
        ≈⟨ by-assoc Eq.refl ⟩
      ((Z ↑ • Z° ↑) • H ↑ • Z ↑) • CH • H ↑ • CH
        ≈⟨ front _ □-HZ↑ ⟩
      (H ↑ • Z° ↑) • CH • H ↑ • CH
        ≈⟨ assoc ⟩
      H ↑ • Z° ↑ • CH • H ↑ • CH ∎

    -- Both sides of (110) with °CH = CH • H ↓ = H ↓ • CH unfolded.
    eq110ˡ : °CH • H ↑ • Z° ↑ • °CH • H ↑ ≈ CH • H ↑ • Z° ↑ • CH • H ↑
    eq110ˡ = begin
      °CH • H ↑ • Z° ↑ • °CH • H ↑
        ≈⟨ cong (sym CH-H↓) (back _ (back _ (front _ (sym H↓-CH)))) ⟩
      (CH • H ↓) • H ↑ • Z° ↑ • (H ↓ • CH) • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      CH • (H ↓ • H ↑) • Z° ↑ • H ↓ • CH • H ↑
        ≈⟨ mid _ _ H↓-H↑ ⟩
      CH • (H ↑ • H ↓) • Z° ↑ • H ↓ • CH • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      (CH • H ↑) • (H ↓ • Z° ↑) • H ↓ • CH • H ↑
        ≈⟨ mid _ _ H↓-Z°↑ ⟩
      (CH • H ↑) • (Z° ↑ • H ↓) • H ↓ • CH • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      (CH • H ↑ • Z° ↑) • (H ↓ • H ↓) • CH • H ↑
        ≈⟨ cancelᵐ _ _ H² ⟩
      (CH • H ↑ • Z° ↑) • CH • H ↑
        ≈⟨ by-assoc Eq.refl ⟩
      CH • H ↑ • Z° ↑ • CH • H ↑ ∎

    eq110ʳ : H ↑ • Z° ↑ • °CH • H ↑ • °CH ≈ H ↑ • Z° ↑ • CH • H ↑ • CH
    eq110ʳ = begin
      H ↑ • Z° ↑ • °CH • H ↑ • °CH
        ≈⟨ back _ (back _ (cong (sym CH-H↓) (back _ (sym H↓-CH)))) ⟩
      H ↑ • Z° ↑ • (CH • H ↓) • H ↑ • (H ↓ • CH)
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↑ • Z° ↑ • CH) • (H ↓ • H ↑) • H ↓ • CH
        ≈⟨ mid _ _ H↓-H↑ ⟩
      (H ↑ • Z° ↑ • CH) • (H ↑ • H ↓) • H ↓ • CH
        ≈⟨ by-assoc Eq.refl ⟩
      (H ↑ • Z° ↑ • CH • H ↑) • (H ↓ • H ↓) • CH
        ≈⟨ cancelᵐ _ _ H² ⟩
      (H ↑ • Z° ↑ • CH • H ↑) • CH
        ≈⟨ by-assoc Eq.refl ⟩
      H ↑ • Z° ↑ • CH • H ↑ • CH ∎

  eq110 : °CH • H ↑ • Z° ↑ • °CH • H ↑ ≈ H ↑ • Z° ↑ • °CH • H ↑ • °CH
  eq110 = trans eq110ˡ (trans eq11° (sym eq110ʳ))

  ----------------------------------------------------------------------
  -- (86), (87), (104): the swap as three CNOTs

  eq86 : Ex ≈ CX • XC • CX
  eq86 = begin
    Ex
      ≈⟨ moveʳ H²↑ Ex-H↑ ⟩
    (H ↓ • Ex) • H ↑
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ) • (H ↓ • H ↑) • (CZ • H ↓ • H ↑ • H ↑)
      ≈⟨ mid _ _ H↓-H↑ ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ) • (H ↑ • H ↓) • (CZ • H ↓ • H ↑ • H ↑)
      ≈⟨ by-assoc Eq.refl ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • (H ↑ • H ↑)
      ≈⟨ cancelᵉ _ H²↑ ⟩
    H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓
      ≈⟨ by-assoc Eq.refl ⟩
    CX • (H ↑ • CZ • H ↑) • CX
      ≈⟨ mid _ _ (sym XC-alt) ⟩
    CX • XC • CX ∎

  eq86ˢ : Ex ≈ XC • CX • XC
  eq86ˢ = S.⟪⟫-≈ eq86 S-Ex (S.⟪⟫-•₃ refl S-XC refl)

  eq87 : CX • Ex ≈ XC • CX
  eq87 = trans (back _ eq86) (cancelˡ _ CX²)

  eq104 : CX • Ex • CX ≈ XC
  eq104 = trans (mid _ _ eq86) (unconj CX²)

  XC-Ex : XC • Ex ≈ CX • XC
  XC-Ex = trans (back _ eq86ˢ) (cancelˡ _ XC²)

  XC-CX-XC : XC • CX • XC ≈ Ex
  XC-CX-XC = sym eq86ˢ

  ----------------------------------------------------------------------
  -- (102), (105)–(108): conjugating controlled-H by CNOTs

  eq102 : CX • CH • CX ≈ X ↓ • CH • X ↓
  eq102 = begin
    CX • CH • CX
      ≈⟨ front _ (sym X↓-°CX) ⟩
    (X ↓ • °CX) • CH • CX
      ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • (°CX • CH) • CX
      ≈⟨ mid _ _ (sym eq94) ⟩
    X ↓ • (CH • °CX) • CX
      ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • CH • (°CX • CX)
      ≈⟨ back _ (back _ °CX-CX) ⟩
    X ↓ • CH • X ↓ ∎

  eq105 : XC • °CH • XC ≈ CX • HC° • CX
  eq105 = begin
    XC • °CH • XC
      ≈⟨ cong (sym eq104) (back _ (sym eq104)) ⟩
    (CX • Ex • CX) • °CH • (CX • Ex • CX)
      ≈⟨ by-assoc Eq.refl ⟩
    (CX • Ex) • (CX • °CH) • CX • Ex • CX
      ≈⟨ mid _ _ (sym eq95) ⟩
    (CX • Ex) • (°CH • CX) • CX • Ex • CX
      ≈⟨ by-assoc Eq.refl ⟩
    (CX • Ex • °CH) • (CX • CX) • (Ex • CX)
      ≈⟨ cancelᵐ _ _ CX² ⟩
    (CX • Ex • °CH) • (Ex • CX)
      ≈⟨ by-assoc Eq.refl ⟩
    CX • (Ex • °CH • Ex) • CX
      ≈⟨ mid _ _ S-°CH ⟩
    CX • HC° • CX ∎

  eq106 : X ↑ • (CX • HC • CX) • X ↑ ≈ X ↓ • (XC • CH • XC) • X ↓
  eq106 = begin
    X ↑ • (CX • HC • CX) • X ↑
      ≈⟨ by-assoc Eq.refl ⟩
    X ↑ • CX • HC • CX • X ↑
      ≈⟨ back _ (back _ (front _ (sym N↓-HC°))) ⟩
    X ↑ • CX • (X ↓ • HC° • X ↓) • CX • X ↑
      ≈⟨ by-assoc Eq.refl ⟩
    X ↑ • (CX • X ↓) • HC° • (X ↓ • CX) • X ↑
      ≈⟨ back _ (cong eq100 (back _ (front _ (sym eq100)))) ⟩
    X ↑ • (X ↓ • CX) • HC° • (CX • X ↓) • X ↑
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↑ • X ↓) • (CX • HC° • CX) • (X ↓ • X ↑)
      ≈⟨ cong (sym X↓-X↑) (cong (sym eq105) X↓-X↑) ⟩
    (X ↓ • X ↑) • (XC • °CH • XC) • (X ↑ • X ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • (X ↑ • XC) • °CH • (XC • X ↑) • X ↓
      ≈⟨ back _ (cong (sym XC-X↑-comm) (back _ (front _ XC-X↑-comm))) ⟩
    X ↓ • (XC • X ↑) • °CH • (X ↑ • XC) • X ↓
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↓ • XC) • (X ↑ • °CH • X ↑) • (XC • X ↓)
      ≈⟨ mid _ _ N↑-°CH ⟩
    (X ↓ • XC) • CH • (XC • X ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • (XC • CH • XC) • X ↓ ∎

  eq107 : XC° • (CX • HC • CX) • XC° ≈ X ↓ • °CH • X ↓
  eq107 = begin
    XC° • (CX • HC • CX) • XC°
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↓ • XC) • (X ↓ • CX) • HC • (CX • X ↓) • XC • X ↓
      ≈⟨ back _ (cong (sym eq100) (back _ (front _ eq100))) ⟩
    (X ↓ • XC) • (CX • X ↓) • HC • (X ↓ • CX) • XC • X ↓
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↓ • XC) • (CX • HC° • CX) • (XC • X ↓)
      ≈⟨ mid _ _ (sym eq105) ⟩
    (X ↓ • XC) • (XC • °CH • XC) • (XC • X ↓)
      ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • (XC • XC) • (°CH • (XC • XC) • X ↓)
      ≈⟨ cancelᵐ _ _ XC² ⟩
    X ↓ • (°CH • (XC • XC) • X ↓)
      ≈⟨ back _ (cancelᵐ _ _ XC²) ⟩
    X ↓ • °CH • X ↓ ∎

  eq108 : °CX • (X ↓ • (XC • CH • XC) • X ↓) • °CX ≈ X ↑ • HC • X ↑
  eq108 = begin
    °CX • (X ↓ • (XC • CH • XC) • X ↓) • °CX
      ≈⟨ mid _ _ (sym eq106) ⟩
    °CX • (X ↑ • (CX • HC • CX) • X ↑) • °CX
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↑ • CX) • (X ↑ • X ↑) • (CX • HC • CX • (X ↑ • X ↑) • CX • X ↑)
      ≈⟨ cancelᵐ _ _ X²↑ ⟩
    (X ↑ • CX) • (CX • HC • CX • (X ↑ • X ↑) • CX • X ↑)
      ≈⟨ back _ (by-assoc Eq.refl) ⟩
    (X ↑ • CX) • ((CX • HC • CX) • (X ↑ • X ↑) • (CX • X ↑))
      ≈⟨ back _ (cancelᵐ _ _ X²↑) ⟩
    (X ↑ • CX) • ((CX • HC • CX) • (CX • X ↑))
      ≈⟨ by-assoc Eq.refl ⟩
    X ↑ • (CX • CX) • (HC • (CX • CX) • X ↑)
      ≈⟨ cancelᵐ _ _ CX² ⟩
    X ↑ • (HC • (CX • CX) • X ↑)
      ≈⟨ back _ (cancelᵐ _ _ CX²) ⟩
    X ↑ • HC • X ↑ ∎
