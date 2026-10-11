------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding respects the auxiliary theory (Clément, Appendix C:
-- Lemmas 7.4 and 7.5)
--
-- Lemma 7.4: decoding the encoding of a gate gives the gate back.
-- Lemma 7.5: the decoding D sends each equation of Figure 7 (at N = 4)
-- to a derivable equation of circuits.  The paper's Table 1 lists,
-- for each pair of a two-level matrix X_[b,c] and H_[a,c], which
-- auxiliary equation shows that conjugating D(H_[a,c]) by D(X_[b,c])
-- gives D(H_[a,b]); here the same is organised by conjugation: the
-- six CNOT-like circuits D(X_[b,c]) are, up to the conjugations of
-- Conjugation, the one CNOT, so each family of cases is one case
-- transported.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.TwoQubit.Decoding where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Auxiliary
open import Examples.Groups.Real-Clifford+CH.TwoQubit using (e ; d)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])

open Tools (2 VRel,_===_)

------------------------------------------------------------------------
-- The decoded generators

dZ : Fin 4 → Circuit 2
dZ a = d −1[ a ]

dX dH : Fin 4 → Fin 4 → Circuit 2
dX a b = d X[ a , b ]
dH a b = d H[ a , b ]

-- The three conjugations act on the basis indices: X on the upper wire
-- flips the bit of weight 2, X on the lower wire the bit of weight 1,
-- and the swap exchanges the two bits.
flip↑ flip↓ sw : Fin 4 → Fin 4
flip↑ ₀ = ₂
flip↑ ₁ = ₃
flip↑ ₂ = ₀
flip↑ ₃ = ₁
flip↓ ₀ = ₁
flip↓ ₁ = ₀
flip↓ ₂ = ₃
flip↓ ₃ = ₂
sw ₀ = ₀
sw ₁ = ₂
sw ₂ = ₁
sw ₃ = ₃

------------------------------------------------------------------------
-- Lemma 7.4

lemma-7-4 : ∀ g → 2 ⊢ [ g ]ʷ ≈ (d ʷ) (e g)
lemma-7-4 (gate₀ ())
lemma-7-4 H-gen        = sym °CH-CH
lemma-7-4 Z-gen        = sym °CZ-CZ
lemma-7-4 CZ-gen       = refl
lemma-7-4 CH-gen       = refl
lemma-7-4 (H-gen ↥)    = sym HC°-HC
lemma-7-4 (Z-gen ↥)    = sym CZ°-CZ
lemma-7-4 (gate₀ () ↥)
lemma-7-4 (gate₀ () ↥ ↥)

------------------------------------------------------------------------
-- The conjugations act on the decoded generators by renaming

-- The two decodings that are not conjugates by definition.
private
  N↑-H12 : X ↑ • dH ₁ ₂ • X ↑ ≈ dH ₃ ₀
  N↑-H12 = trans (N↑.⟪⟫-•₃ refl refl refl) (conj-sym °CX² eq108)

  N↓-H12 : X ↓ • dH ₁ ₂ • X ↓ ≈ dH ₀ ₃
  N↓-H12 = trans (N↓.⟪⟫-•₃ eq101 refl eq101) (sym eq105)

N↑-dZ : ∀ a → X ↑ • dZ a • X ↑ ≈ dZ (flip↑ a)
N↑-dZ ₀ = N↑-°CZ°
N↑-dZ ₁ = N↑-°CZ
N↑-dZ ₂ = N↑-CZ°
N↑-dZ ₃ = refl

N↓-dZ : ∀ a → X ↓ • dZ a • X ↓ ≈ dZ (flip↓ a)
N↓-dZ ₀ = N↓-°CZ°
N↓-dZ ₁ = N↓-°CZ
N↓-dZ ₂ = N↓-CZ°
N↓-dZ ₃ = refl

S-dZ : ∀ a → Ex • dZ a • Ex ≈ dZ (sw a)
S-dZ ₀ = S-°CZ°
S-dZ ₁ = S-°CZ
S-dZ ₂ = S-CZ°
S-dZ ₃ = S-CZ

N↑-dH : ∀ a b → X ↑ • dH a b • X ↑ ≈ dH (flip↑ a) (flip↑ b)
N↑-dH ₀ ₀ = N↑.⟪⟫-ε
N↑-dH ₁ ₁ = N↑.⟪⟫-ε
N↑-dH ₂ ₂ = N↑.⟪⟫-ε
N↑-dH ₃ ₃ = N↑.⟪⟫-ε
N↑-dH ₂ ₃ = refl
N↑-dH ₀ ₁ = N↑-°CH
N↑-dH ₀ ₂ = refl
N↑-dH ₂ ₀ = N↑.⟪⟫-⟪⟫ HC°
N↑-dH ₁ ₃ = refl
N↑-dH ₃ ₁ = N↑.⟪⟫-⟪⟫ HC
N↑-dH ₃ ₂ = N↑-N↓ CH
N↑-dH ₁ ₀ = trans (N↑-N↓ °CH) (mid _ _ N↑-°CH)
N↑-dH ₂ ₁ = N↑.⟪⟫-•₃ N↑-XC refl N↑-XC
N↑-dH ₀ ₃ = N↑.⟪⟫-•₃ N↑-XC N↑-°CH N↑-XC
N↑-dH ₁ ₂ = N↑-H12
N↑-dH ₃ ₀ = conj-sym X²↑ N↑-H12

N↓-dH : ∀ a b → X ↓ • dH a b • X ↓ ≈ dH (flip↓ a) (flip↓ b)
N↓-dH ₀ ₀ = N↓.⟪⟫-ε
N↓-dH ₁ ₁ = N↓.⟪⟫-ε
N↓-dH ₂ ₂ = N↓.⟪⟫-ε
N↓-dH ₃ ₃ = N↓.⟪⟫-ε
N↓-dH ₂ ₃ = refl
N↓-dH ₃ ₂ = N↓.⟪⟫-⟪⟫ CH
N↓-dH ₀ ₁ = refl
N↓-dH ₁ ₀ = N↓.⟪⟫-⟪⟫ °CH
N↓-dH ₀ ₂ = N↓-HC°
N↓-dH ₁ ₃ = refl
N↓-dH ₂ ₀ = trans (N↓-N↑ HC°) (mid _ _ N↓-HC°)
N↓-dH ₃ ₁ = N↓-N↑ HC
N↓-dH ₂ ₁ = refl
N↓-dH ₃ ₀ = N↓.⟪⟫-⟪⟫ (XC • CH • XC)
N↓-dH ₁ ₂ = N↓-H12
N↓-dH ₀ ₃ = conj-sym X² N↓-H12

S-dH : ∀ a b → Ex • dH a b • Ex ≈ dH (sw a) (sw b)
S-dH ₀ ₀ = S.⟪⟫-ε
S-dH ₁ ₁ = S.⟪⟫-ε
S-dH ₂ ₂ = S.⟪⟫-ε
S-dH ₃ ₃ = S.⟪⟫-ε
S-dH ₂ ₃ = refl
S-dH ₁ ₃ = S-HC
S-dH ₀ ₁ = S-°CH
S-dH ₀ ₂ = S-HC°
S-dH ₃ ₂ = S-N↓ CH HC refl
S-dH ₃ ₁ = S-N↑ HC CH S-HC
S-dH ₁ ₀ = S-N↓ °CH HC° S-°CH
S-dH ₂ ₀ = S-N↑ HC° °CH S-HC°
S-dH ₂ ₁ = S.⟪⟫-•₃ S-XC refl S-XC
S-dH ₁ ₂ = S.⟪⟫-•₃ refl S-HC refl
S-dH ₀ ₃ = trans (S.⟪⟫-•₃ S-XC S-°CH S-XC) (sym eq105)
S-dH ₃ ₀ = trans (S-N↓ (XC • CH • XC) (CX • HC • CX) (S.⟪⟫-•₃ S-XC refl S-XC)) eq106

------------------------------------------------------------------------
-- Conjugating by the decoded X_[b,c]
--
-- Each D(X_[b,c]) is the CNOT conjugated: °CX = N↑ CX, XC = S CX,
-- XC° = N↓ XC, and D(X_[0,3]) = Ex • X ↑ • X ↓ conjugates as S ∘ N↑ ∘ N↓.
-- So conjugating by it is conjugating by CX between two renamings.

via-N↑ : ∀ {w w₁ w₂ w′} → X ↑ • w • X ↑ ≈ w₁ → CX • w₁ • CX ≈ w₂ →
         X ↑ • w₂ • X ↑ ≈ w′ → °CX • w • °CX ≈ w′
via-N↑ {w} p h k =
  trans (N↑.⟪⟫-sandwich CX w) (trans (N↑.⟪⟫-cong (trans (mid _ _ p) h)) k)

via-S : ∀ {w w₁ w₂ w′} → Ex • w • Ex ≈ w₁ → CX • w₁ • CX ≈ w₂ →
        Ex • w₂ • Ex ≈ w′ → XC • w • XC ≈ w′
via-S {w} p h k =
  trans (S.⟪⟫-sandwich CX w) (trans (S.⟪⟫-cong (trans (mid _ _ p) h)) k)

via-N↓ : ∀ {w w₁ w₂ w′} → X ↓ • w • X ↓ ≈ w₁ → XC • w₁ • XC ≈ w₂ →
         X ↓ • w₂ • X ↓ ≈ w′ → XC° • w • XC° ≈ w′
via-N↓ {w} p h k =
  trans (N↓.⟪⟫-sandwich XC w) (trans (N↓.⟪⟫-cong (trans (mid _ _ p) h)) k)

-- Conjugating by Ex • X ↑ • X ↓ is conjugating by X ↓, X ↑, then Ex.
private
  E-conj : ∀ w → (Ex • X ↑ • X ↓) • w • (Ex • X ↑ • X ↓) ≈
                 Ex • (X ↑ • (X ↓ • w • X ↓) • X ↑) • Ex
  E-conj w = trans (back _ (back _ Ex-XX))
    (by-passoc ((□ • (□ • □)) • (□ • (□ • (□ • □))))
               (□ • ((□ • ((□ • (□ • □)) • □)) • □)) Eq.refl)

via-E : ∀ {w w₁ w₂ w′} → X ↓ • w • X ↓ ≈ w₁ → X ↑ • w₁ • X ↑ ≈ w₂ →
        Ex • w₂ • Ex ≈ w′ → (Ex • X ↑ • X ↓) • w • (Ex • X ↑ • X ↓) ≈ w′
via-E {w} p q k =
  trans (E-conj w) (trans (S.⟪⟫-cong (trans (N↑.⟪⟫-cong p) q)) k)

-- The decoded X_[b,c] are involutions.
E² : (Ex • X ↑ • X ↓) • (Ex • X ↑ • X ↓) ≈ ε
E² = begin
  (Ex • X ↑ • X ↓) • (Ex • X ↑ • X ↓)
    ≈⟨ back _ Ex-XX ⟩
  (Ex • X ↑ • X ↓) • (X ↓ • X ↑ • Ex)
    ≈⟨ by-assoc Eq.refl ⟩
  (Ex • X ↑) • (X ↓ • X ↓) • (X ↑ • Ex)
    ≈⟨ cancelᵐ _ _ X² ⟩
  (Ex • X ↑) • (X ↑ • Ex)
    ≈⟨ by-assoc Eq.refl ⟩
  Ex • (X ↑ • X ↑) • Ex
    ≈⟨ cancelᵐ _ _ X²↑ ⟩
  Ex • Ex
    ≈⟨ Ex² ⟩
  ε ∎

dX² : ∀ a b → dX a b • dX a b ≈ ε
dX² ₀ ₀ = left-unit
dX² ₁ ₁ = left-unit
dX² ₂ ₂ = left-unit
dX² ₃ ₃ = left-unit
dX² ₂ ₃ = CX²
dX² ₃ ₂ = CX²
dX² ₀ ₁ = °CX²
dX² ₁ ₀ = °CX²
dX² ₀ ₂ = XC°²
dX² ₂ ₀ = XC°²
dX² ₁ ₃ = XC²
dX² ₃ ₁ = XC²
dX² ₁ ₂ = Ex²
dX² ₂ ₁ = Ex²
dX² ₀ ₃ = E²
dX² ₃ ₀ = E²

dH² : ∀ a b → dH a b • dH a b ≈ ε
dH² ₀ ₀ = left-unit
dH² ₁ ₁ = left-unit
dH² ₂ ₂ = left-unit
dH² ₃ ₃ = left-unit
dH² ₂ ₃ = CH²
dH² ₀ ₁ = °CH²
dH² ₀ ₂ = HC°²
dH² ₁ ₃ = HC²
dH² ₃ ₂ = conj-invol X² CH²
dH² ₁ ₀ = conj-invol X² °CH²
dH² ₂ ₀ = conj-invol X²↑ HC°²
dH² ₃ ₁ = conj-invol X²↑ HC²
dH² ₂ ₁ = conj-invol XC² CH²
dH² ₁ ₂ = conj-invol CX² HC²
dH² ₀ ₃ = conj-invol XC² °CH²
dH² ₃ ₀ = conj-invol X² (conj-invol XC² CH²)

------------------------------------------------------------------------
-- Conjugating the decoded (−1)_[a] and H_[a,b] by the decoded X_[b,c]

-- By CX: the two cases of Table 1's first column that genuinely use
-- the auxiliary equations, and the others.
private
  CX-Z2 : CX • dZ ₂ • CX ≈ dZ ₃
  CX-Z2 = conj-sym CX² eq98

  CX-Z3 : CX • dZ ₃ • CX ≈ dZ ₂
  CX-Z3 = eq98

  CX-H02 : CX • dH ₀ ₂ • CX ≈ dH ₀ ₃
  CX-H02 = sym eq105

  CX-H03 : CX • dH ₀ ₃ • CX ≈ dH ₀ ₂
  CX-H03 = conj-sym CX² (sym eq105)

  CX-H12 : CX • dH ₁ ₂ • CX ≈ dH ₁ ₃
  CX-H12 = unconj CX²

  CX-H13 : CX • dH ₁ ₃ • CX ≈ dH ₁ ₂
  CX-H13 = refl

  CX-H32 : CX • dH ₃ ₂ • CX ≈ dH ₂ ₃
  CX-H32 = conj-sym CX² eq102

  CX-H23 : CX • dH ₂ ₃ • CX ≈ dH ₃ ₂
  CX-H23 = eq102

  -- By XC (needed again for XC°).
  XC-Z1 : XC • dZ ₁ • XC ≈ dZ ₃
  XC-Z1 = via-S (S-dZ ₁) CX-Z2 (S-dZ ₃)

  XC-Z3 : XC • dZ ₃ • XC ≈ dZ ₁
  XC-Z3 = via-S (S-dZ ₃) CX-Z3 (S-dZ ₂)

  XC-H03 : XC • dH ₀ ₃ • XC ≈ dH ₀ ₁
  XC-H03 = via-S (S-dH ₀ ₃) CX-H03 (S-dH ₀ ₂)

  XC-H01 : XC • dH ₀ ₁ • XC ≈ dH ₀ ₃
  XC-H01 = via-S (S-dH ₀ ₁) CX-H02 (S-dH ₀ ₃)

  XC-H23 : XC • dH ₂ ₃ • XC ≈ dH ₂ ₁
  XC-H23 = via-S (S-dH ₂ ₃) CX-H13 (S-dH ₁ ₂)

  XC-H21 : XC • dH ₂ ₁ • XC ≈ dH ₂ ₃
  XC-H21 = via-S (S-dH ₂ ₁) CX-H12 (S-dH ₁ ₃)

  XC-H31 : XC • dH ₃ ₁ • XC ≈ dH ₁ ₃
  XC-H31 = via-S (S-dH ₃ ₁) CX-H32 (S-dH ₂ ₃)

  XC-H13 : XC • dH ₁ ₃ • XC ≈ dH ₃ ₁
  XC-H13 = via-S (S-dH ₁ ₃) CX-H23 (S-dH ₃ ₂)

-- X_[a,b] conjugates (−1)_[a] to (−1)_[b].
cX-Z : ∀ a b → a ≢ b → dX a b • dZ a • dX a b ≈ dZ b
cX-Z ₂ ₃ _ = CX-Z2
cX-Z ₃ ₂ _ = CX-Z3
cX-Z ₀ ₁ _ = via-N↑ (N↑-dZ ₀) CX-Z2 (N↑-dZ ₃)
cX-Z ₁ ₀ _ = via-N↑ (N↑-dZ ₁) CX-Z3 (N↑-dZ ₂)
cX-Z ₁ ₃ _ = XC-Z1
cX-Z ₃ ₁ _ = XC-Z3
cX-Z ₀ ₂ _ = via-N↓ (N↓-dZ ₀) XC-Z1 (N↓-dZ ₃)
cX-Z ₂ ₀ _ = via-N↓ (N↓-dZ ₂) XC-Z3 (N↓-dZ ₁)
cX-Z ₁ ₂ _ = S-dZ ₁
cX-Z ₂ ₁ _ = S-dZ ₂
cX-Z ₀ ₃ _ = via-E (N↓-dZ ₀) (N↑-dZ ₁) (S-dZ ₃)
cX-Z ₃ ₀ _ = via-E (N↓-dZ ₃) (N↑-dZ ₂) (S-dZ ₀)
cX-Z ₀ ₀ p = ⊥-elim (p Eq.refl)
cX-Z ₁ ₁ p = ⊥-elim (p Eq.refl)
cX-Z ₂ ₂ p = ⊥-elim (p Eq.refl)
cX-Z ₃ ₃ p = ⊥-elim (p Eq.refl)

-- X_[b,c] conjugates H_[a,c] to H_[a,b] (a, b, c distinct).
cX-H : ∀ a b c → a ≢ b → a ≢ c → b ≢ c → dX b c • dH a c • dX b c ≈ dH a b
cX-H ₀ ₂ ₃ _ _ _ = CX-H03
cX-H ₀ ₃ ₂ _ _ _ = CX-H02
cX-H ₁ ₂ ₃ _ _ _ = CX-H13
cX-H ₁ ₃ ₂ _ _ _ = CX-H12
cX-H ₂ ₀ ₁ _ _ _ = via-N↑ (N↑-dH ₂ ₁) CX-H03 (N↑-dH ₀ ₂)
cX-H ₂ ₁ ₀ _ _ _ = via-N↑ (N↑-dH ₂ ₀) CX-H02 (N↑-dH ₀ ₃)
cX-H ₃ ₀ ₁ _ _ _ = via-N↑ (N↑-dH ₃ ₁) CX-H13 (N↑-dH ₁ ₂)
cX-H ₃ ₁ ₀ _ _ _ = via-N↑ (N↑-dH ₃ ₀) CX-H12 (N↑-dH ₁ ₃)
cX-H ₀ ₁ ₃ _ _ _ = XC-H03
cX-H ₀ ₃ ₁ _ _ _ = XC-H01
cX-H ₂ ₁ ₃ _ _ _ = XC-H23
cX-H ₂ ₃ ₁ _ _ _ = XC-H21
cX-H ₁ ₀ ₂ _ _ _ = via-N↓ (N↓-dH ₁ ₂) XC-H03 (N↓-dH ₀ ₁)
cX-H ₁ ₂ ₀ _ _ _ = via-N↓ (N↓-dH ₁ ₀) XC-H01 (N↓-dH ₀ ₃)
cX-H ₃ ₀ ₂ _ _ _ = via-N↓ (N↓-dH ₃ ₂) XC-H23 (N↓-dH ₂ ₁)
cX-H ₃ ₂ ₀ _ _ _ = via-N↓ (N↓-dH ₃ ₀) XC-H21 (N↓-dH ₂ ₃)
cX-H ₀ ₁ ₂ _ _ _ = S-dH ₀ ₂
cX-H ₀ ₂ ₁ _ _ _ = S-dH ₀ ₁
cX-H ₃ ₁ ₂ _ _ _ = S-dH ₃ ₂
cX-H ₃ ₂ ₁ _ _ _ = S-dH ₃ ₁
cX-H ₁ ₀ ₃ _ _ _ = via-E (N↓-dH ₁ ₃) (N↑-dH ₀ ₂) (S-dH ₂ ₀)
cX-H ₁ ₃ ₀ _ _ _ = via-E (N↓-dH ₁ ₀) (N↑-dH ₀ ₁) (S-dH ₂ ₃)
cX-H ₂ ₀ ₃ _ _ _ = via-E (N↓-dH ₂ ₃) (N↑-dH ₃ ₂) (S-dH ₁ ₀)
cX-H ₂ ₃ ₀ _ _ _ = via-E (N↓-dH ₂ ₀) (N↑-dH ₃ ₁) (S-dH ₁ ₃)
cX-H ₀ ₀ _ p _ _ = ⊥-elim (p Eq.refl)
cX-H ₁ ₁ _ p _ _ = ⊥-elim (p Eq.refl)
cX-H ₂ ₂ _ p _ _ = ⊥-elim (p Eq.refl)
cX-H ₃ ₃ _ p _ _ = ⊥-elim (p Eq.refl)
cX-H ₀ _ ₀ _ q _ = ⊥-elim (q Eq.refl)
cX-H ₁ _ ₁ _ q _ = ⊥-elim (q Eq.refl)
cX-H ₂ _ ₂ _ q _ = ⊥-elim (q Eq.refl)
cX-H ₃ _ ₃ _ q _ = ⊥-elim (q Eq.refl)
cX-H _ ₀ ₀ _ _ r = ⊥-elim (r Eq.refl)
cX-H _ ₁ ₁ _ _ r = ⊥-elim (r Eq.refl)
cX-H _ ₂ ₂ _ _ r = ⊥-elim (r Eq.refl)
cX-H _ ₃ ₃ _ _ r = ⊥-elim (r Eq.refl)

-- X_[b,c] conjugates H_[c,b] to H_[b,c].
cX-H′ : ∀ b c → b ≢ c → dX b c • dH c b • dX b c ≈ dH b c
cX-H′ ₂ ₃ _ = CX-H32
cX-H′ ₃ ₂ _ = CX-H23
cX-H′ ₀ ₁ _ = via-N↑ (N↑-dH ₁ ₀) CX-H32 (N↑-dH ₂ ₃)
cX-H′ ₁ ₀ _ = via-N↑ (N↑-dH ₀ ₁) CX-H23 (N↑-dH ₃ ₂)
cX-H′ ₁ ₃ _ = XC-H31
cX-H′ ₃ ₁ _ = XC-H13
cX-H′ ₀ ₂ _ = via-N↓ (N↓-dH ₂ ₀) XC-H31 (N↓-dH ₁ ₃)
cX-H′ ₂ ₀ _ = via-N↓ (N↓-dH ₀ ₂) XC-H13 (N↓-dH ₃ ₁)
cX-H′ ₁ ₂ _ = S-dH ₂ ₁
cX-H′ ₂ ₁ _ = S-dH ₁ ₂
cX-H′ ₀ ₃ _ = via-E (N↓-dH ₃ ₀) (N↑-dH ₂ ₁) (S-dH ₀ ₃)
cX-H′ ₃ ₀ _ = via-E (N↓-dH ₀ ₃) (N↑-dH ₁ ₂) (S-dH ₃ ₀)
cX-H′ ₀ ₀ p = ⊥-elim (p Eq.refl)
cX-H′ ₁ ₁ p = ⊥-elim (p Eq.refl)
cX-H′ ₂ ₂ p = ⊥-elim (p Eq.refl)
cX-H′ ₃ ₃ p = ⊥-elim (p Eq.refl)

------------------------------------------------------------------------
-- (d2): (−1)_[b] • H_[a,b] = H_[a,b] • X_[a,b]

private
  d2-23 : dZ ₃ • dH ₂ ₃ ≈ dH ₂ ₃ • dX ₂ ₃
  d2-23 = trans (front _ (sym eq103)) (trans (by-assoc Eq.refl) (cancelᵉ _ CH²))

  d2-01 : dZ ₁ • dH ₀ ₁ ≈ dH ₀ ₁ • dX ₀ ₁
  d2-01 = N↑.⟪⟫-≈ d2-23 (N↑.⟪⟫-•₂ refl refl) (N↑.⟪⟫-•₂ refl refl)

  d2-13 : dZ ₃ • dH ₁ ₃ ≈ dH ₁ ₃ • dX ₁ ₃
  d2-13 = S.⟪⟫-≈ d2-23 (S.⟪⟫-•₂ S-CZ refl) (S.⟪⟫-•₂ refl refl)

  d2-02 : dZ ₂ • dH ₀ ₂ ≈ dH ₀ ₂ • dX ₀ ₂
  d2-02 = S.⟪⟫-≈ d2-01 (S.⟪⟫-•₂ S-°CZ S-°CH) (S.⟪⟫-•₂ S-°CH S-°CX)

  d2-32 : dZ ₂ • dH ₃ ₂ ≈ dH ₃ ₂ • dX ₃ ₂
  d2-32 = N↓.⟪⟫-≈ d2-23 (N↓.⟪⟫-•₂ refl refl) (N↓.⟪⟫-•₂ refl eq101)

  d2-10 : dZ ₀ • dH ₁ ₀ ≈ dH ₁ ₀ • dX ₁ ₀
  d2-10 = N↓.⟪⟫-≈ d2-01 (N↓.⟪⟫-•₂ N↓-°CZ refl) (N↓.⟪⟫-•₂ refl N↓-°CX)

  d2-31 : dZ ₁ • dH ₃ ₁ ≈ dH ₃ ₁ • dX ₃ ₁
  d2-31 = N↑.⟪⟫-≈ d2-13 (N↑.⟪⟫-•₂ refl refl) (N↑.⟪⟫-•₂ refl N↑-XC)

  d2-20 : dZ ₀ • dH ₂ ₀ ≈ dH ₂ ₀ • dX ₂ ₀
  d2-20 = N↑.⟪⟫-≈ d2-02 (N↑.⟪⟫-•₂ N↑-CZ° refl) (N↑.⟪⟫-•₂ refl N↑-XC°)

  d2-21 : dZ ₁ • dH ₂ ₁ ≈ dH ₂ ₁ • dX ₂ ₁
  d2-21 = begin
    °CZ • (XC • CH • XC)
      ≈⟨ front _ (sym XC-CZ-XC) ⟩
    (XC • CZ • XC) • (XC • CH • XC)
      ≈⟨ by-assoc Eq.refl ⟩
    (XC • CZ) • (XC • XC) • (CH • XC)
      ≈⟨ cancelᵐ _ _ XC² ⟩
    (XC • CZ) • (CH • XC)
      ≈⟨ by-assoc Eq.refl ⟩
    XC • (CZ • CH) • XC
      ≈⟨ mid _ _ d2-23 ⟩
    XC • (CH • CX) • XC
      ≈⟨ by-assoc Eq.refl ⟩
    (XC • CH) • (CX • XC)
      ≈⟨ back _ (sym XC-Ex) ⟩
    (XC • CH) • (XC • Ex)
      ≈⟨ by-assoc Eq.refl ⟩
    (XC • CH • XC) • Ex ∎

  d2-12 : dZ ₂ • dH ₁ ₂ ≈ dH ₁ ₂ • dX ₁ ₂
  d2-12 = S.⟪⟫-≈ d2-21 (S.⟪⟫-•₂ S-°CZ (S.⟪⟫-•₃ S-XC refl S-XC))
                       (S.⟪⟫-•₂ (S.⟪⟫-•₃ S-XC refl S-XC) S-Ex)

  d2-03 : dZ ₃ • dH ₀ ₃ ≈ dH ₀ ₃ • dX ₀ ₃
  d2-03 = N↑.⟪⟫-≈ d2-21 (N↑.⟪⟫-•₂ N↑-°CZ (N↑.⟪⟫-•₃ N↑-XC refl N↑-XC))
                        (N↑.⟪⟫-•₂ (N↑.⟪⟫-•₃ N↑-XC refl N↑-XC) N↑-Ex)

  d2-30 : dZ ₀ • dH ₃ ₀ ≈ dH ₃ ₀ • dX ₃ ₀
  d2-30 = N↓.⟪⟫-≈ d2-21 (N↓.⟪⟫-•₂ N↓-°CZ refl) (N↓.⟪⟫-•₂ refl N↓-Ex)

d2ᵈ : ∀ a b → a ≢ b → dZ b • dH a b ≈ dH a b • dX a b
d2ᵈ ₂ ₃ _ = d2-23
d2ᵈ ₀ ₁ _ = d2-01
d2ᵈ ₁ ₃ _ = d2-13
d2ᵈ ₀ ₂ _ = d2-02
d2ᵈ ₃ ₂ _ = d2-32
d2ᵈ ₁ ₀ _ = d2-10
d2ᵈ ₃ ₁ _ = d2-31
d2ᵈ ₂ ₀ _ = d2-20
d2ᵈ ₂ ₁ _ = d2-21
d2ᵈ ₁ ₂ _ = d2-12
d2ᵈ ₀ ₃ _ = d2-03
d2ᵈ ₃ ₀ _ = d2-30
d2ᵈ ₀ ₀ p = ⊥-elim (p Eq.refl)
d2ᵈ ₁ ₁ p = ⊥-elim (p Eq.refl)
d2ᵈ ₂ ₂ p = ⊥-elim (p Eq.refl)
d2ᵈ ₃ ₃ p = ⊥-elim (p Eq.refl)

------------------------------------------------------------------------
-- (d3*): Equation (110) with the controls commuted past Z°

private
  d3ᵈ : °CH • HC° • HC • °CH • °CZ° • °CZ • HC° • HC ≈
        HC° • HC • °CH • °CZ° • °CZ • HC° • HC • °CH
  d3ᵈ = begin
    °CH • HC° • HC • °CH • °CZ° • °CZ • HC° • HC
      ≈⟨ by-assoc Eq.refl ⟩
    °CH • (HC° • HC) • °CH • (°CZ° • °CZ) • (HC° • HC)
      ≈⟨ back _ (cong HC°-HC (back _ (cong °CZ°-°CZ HC°-HC))) ⟩
    °CH • H ↑ • °CH • Z° ↑ • H ↑
      ≈⟨ by-assoc Eq.refl ⟩
    (°CH • H ↑) • (°CH • Z° ↑) • H ↑
      ≈⟨ mid _ _ °CH-Z°↑ ⟩
    (°CH • H ↑) • (Z° ↑ • °CH) • H ↑
      ≈⟨ by-assoc Eq.refl ⟩
    °CH • H ↑ • Z° ↑ • °CH • H ↑
      ≈⟨ eq110 ⟩
    H ↑ • Z° ↑ • °CH • H ↑ • °CH
      ≈⟨ by-assoc Eq.refl ⟩
    H ↑ • (Z° ↑ • °CH) • H ↑ • °CH
      ≈⟨ mid _ _ (sym °CH-Z°↑) ⟩
    H ↑ • (°CH • Z° ↑) • H ↑ • °CH
      ≈⟨ by-assoc Eq.refl ⟩
    H ↑ • °CH • Z° ↑ • H ↑ • °CH
      ≈⟨ cong (sym HC°-HC) (back _ (cong (sym °CZ°-°CZ) (front _ (sym HC°-HC)))) ⟩
    (HC° • HC) • °CH • (°CZ° • °CZ) • (HC° • HC) • °CH
      ≈⟨ by-assoc Eq.refl ⟩
    HC° • HC • °CH • °CZ° • °CZ • HC° • HC • °CH ∎

------------------------------------------------------------------------
-- Lemma 7.5

lemma-7-5 : ∀ {u t} → 4 G.G, u === t → 2 ⊢ (d ʷ) u ≈ (d ʷ) t
lemma-7-5 G.a1*                  = °CZ°²
lemma-7-5 (G.a2 {a = a} {b = b} _)       = dX² a b
lemma-7-5 (G.a3 {a = a} {b = b} _)       = dH² a b
lemma-7-5 G.b1*                  = °CZ°-°CZ-comm
lemma-7-5 G.b4*                  = sym eq99
lemma-7-5 G.b6*                  = sym eq92
lemma-7-5 (G.c1 {a = a} {b = b} p)       = conj-comm (dX² a b) (cX-Z a b p)
lemma-7-5 (G.c5 {a = a} {b = b} {c = c} p q r) = conj-comm (dX² b c) (cX-H a b c p q r)
lemma-7-5 (G.d2 {a = a} {b = b} p)       = d2ᵈ a b p
lemma-7-5 G.d3*                  = d3ᵈ
lemma-7-5 (G.e2* {b = b} {c = c} p)      = conj-comm (dX² b c) (cX-H′ b c p)
