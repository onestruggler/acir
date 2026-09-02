{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Ex-conjugation calculus, part 1 of 3: the swap as an involution,
-- conjugation of single gates and their powers, and the multiplier
-- versus CZ.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ< ; toℕ-injective)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ExConjA
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
open Lemmas-Clifford
  using (lemma-↑^ ; lemma-Induction ; lemma-Inductionˡ
        ; lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Hᵏ-w↑
        ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑ ; lemma-comm-CZ-w↑)

private
  variable
    n : ℕ

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ p-3 p-prime g* g-gen

module Ex-Conjugation-A (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ ; •-cancelˡ)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₁ = PB ((₁₊ n) QRel,_===_)

  -- semi-M↑CZ, back in the Mg spelling.  Like semi-MR one wire down, the
  -- axiom is stated over XMg = Mg ⁻¹ and says conjugation by it takes
  -- CZ ^ g to CZ; inserting XMg ↑ • Mg ↑ = ε and cancelling turns that
  -- into the original rule.  The two inverse facts are the one-wire ones
  -- lifted, since Mg and XMg both live on wire 1 here.
  private
    Mg↑XMg↑ : Mg ↑ • XMg ↑ ≈ ε
    Mg↑XMg↑ = lemma-cong↑ _ _ (One-Wire.lemma-Mg-XMg n)

    XMg↑Mg↑ : XMg ↑ • Mg ↑ ≈ ε
    XMg↑Mg↑ = lemma-cong↑ _ _ (One-Wire.lemma-XMg-Mg n)

  lemma-semi-M↑CZ : Mg ↑ • CZ ≈ CZ^ g • Mg ↑
  lemma-semi-M↑CZ = begin
    Mg ↑ • CZ
      ≈⟨ sym right-unit ⟩
    (Mg ↑ • CZ) • ε
      ≈⟨ cright sym XMg↑Mg↑ ⟩
    (Mg ↑ • CZ) • (XMg ↑ • Mg ↑)
      ≈⟨ assoc ⟩
    Mg ↑ • (CZ • (XMg ↑ • Mg ↑))
      ≈⟨ cright sym assoc ⟩
    Mg ↑ • ((CZ • XMg ↑) • Mg ↑)
      ≈⟨ cright cleft sym (axiom semi-M↑CZ) ⟩
    Mg ↑ • ((XMg ↑ • CZ^ g) • Mg ↑)
      ≈⟨ cright assoc ⟩
    Mg ↑ • (XMg ↑ • (CZ^ g • Mg ↑))
      ≈⟨ sym assoc ⟩
    (Mg ↑ • XMg ↑) • (CZ^ g • Mg ↑)
      ≈⟨ cleft Mg↑XMg↑ ⟩
    ε • (CZ^ g • Mg ↑)
      ≈⟨ left-unit ⟩
    CZ^ g • Mg ↑ ∎

  -- order-Ex with the power unfolded: Ex ^ 2 is Ex • (Ex ^ 1) is
  -- Ex • Ex definitionally, so this is the axiom itself.
  lemma-Ex-Ex : Ex • Ex ≈ ε
  lemma-Ex-Ex = axiom order-Ex

  -- Cancelling a trailing Ex • Ex.
  lemma-cancel-Ex : ∀ {w} → w • Ex • Ex ≈ w
  lemma-cancel-Ex {w} = begin
    w • Ex • Ex ≈⟨ cright lemma-Ex-Ex ⟩
    w • ε       ≈⟨ right-unit ⟩
    w ∎

  ------------------------------------------------------------------------
  -- The two axioms, and their opposites
  --
  -- Conjugating by an involution is symmetric: from Ex • H ↑ ≈ H • Ex we
  -- get Ex • H ≈ H ↑ • Ex by inserting Ex • Ex on the right, pushing the
  -- axiom through backwards, and cancelling the pair on the left.

  lemma-Ex-H↑ : Ex • H ↑ ≈ H • Ex
  lemma-Ex-H↑ = axiom semi-Ex-H↑

  lemma-Ex-S↑ : Ex • S ↑ ≈ S • Ex
  lemma-Ex-S↑ = axiom semi-Ex-S↑

  lemma-Ex-H : Ex • H ≈ H ↑ • Ex
  lemma-Ex-H = begin
    Ex • H                 ≈⟨ sym lemma-cancel-Ex ⟩
    (Ex • H) • Ex • Ex     ≈⟨ by-assoc auto ⟩
    Ex • (H • Ex) • Ex     ≈⟨ cright cleft sym lemma-Ex-H↑ ⟩
    Ex • (Ex • H ↑) • Ex   ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • H ↑ • Ex   ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • H ↑ • Ex           ≈⟨ left-unit ⟩
    H ↑ • Ex ∎

  lemma-Ex-S : Ex • S ≈ S ↑ • Ex
  lemma-Ex-S = begin
    Ex • S                 ≈⟨ sym lemma-cancel-Ex ⟩
    (Ex • S) • Ex • Ex     ≈⟨ by-assoc auto ⟩
    Ex • (S • Ex) • Ex     ≈⟨ cright cleft sym lemma-Ex-S↑ ⟩
    Ex • (Ex • S ↑) • Ex   ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • S ↑ • Ex   ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • S ↑ • Ex           ≈⟨ left-unit ⟩
    S ↑ • Ex ∎

  ------------------------------------------------------------------------
  -- Two-sided conjugation
  --
  -- The form the later derivations actually use: Ex • g • Ex is g with
  -- its wire flipped.

  lemma-conj-Ex-H↑ : Ex • H ↑ • Ex ≈ H
  lemma-conj-Ex-H↑ = begin
    Ex • H ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • H ↑) • Ex ≈⟨ cleft lemma-Ex-H↑ ⟩
    (H • Ex) • Ex   ≈⟨ assoc ⟩
    H • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    H ∎

  lemma-conj-Ex-S↑ : Ex • S ↑ • Ex ≈ S
  lemma-conj-Ex-S↑ = begin
    Ex • S ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • S ↑) • Ex ≈⟨ cleft lemma-Ex-S↑ ⟩
    (S • Ex) • Ex   ≈⟨ assoc ⟩
    S • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    S ∎

  lemma-conj-Ex-H : Ex • H • Ex ≈ H ↑
  lemma-conj-Ex-H = begin
    Ex • H • Ex     ≈⟨ sym assoc ⟩
    (Ex • H) • Ex   ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • Ex ≈⟨ assoc ⟩
    H ↑ • Ex • Ex   ≈⟨ lemma-cancel-Ex ⟩
    H ↑ ∎

  lemma-conj-Ex-S : Ex • S • Ex ≈ S ↑
  lemma-conj-Ex-S = begin
    Ex • S • Ex     ≈⟨ sym assoc ⟩
    (Ex • S) • Ex   ≈⟨ cleft lemma-Ex-S ⟩
    (S ↑ • Ex) • Ex ≈⟨ assoc ⟩
    S ↑ • Ex • Ex   ≈⟨ lemma-cancel-Ex ⟩
    S ↑ ∎

  ------------------------------------------------------------------------
  -- Powers
  --
  -- Conjugation is a homomorphism, so it passes through a power one
  -- factor at a time.

  lemma-Ex-Hᵏ : ∀ k → Ex • H ^ k ≈ (H ↑) ^ k • Ex
  lemma-Ex-Hᵏ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Hᵏ ₁ = lemma-Ex-H
  lemma-Ex-Hᵏ (₂₊ k) = begin
    Ex • H ^ ₂₊ k            ≈⟨ sym assoc ⟩
    (Ex • H) • H ^ ₁₊ k      ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • H ^ ₁₊ k    ≈⟨ assoc ⟩
    H ↑ • Ex • H ^ ₁₊ k      ≈⟨ cright lemma-Ex-Hᵏ (₁₊ k) ⟩
    H ↑ • (H ↑) ^ ₁₊ k • Ex  ≈⟨ sym assoc ⟩
    (H ↑) ^ ₂₊ k • Ex ∎

  lemma-Ex-Sᵏ : ∀ k → Ex • S ^ k ≈ (S ↑) ^ k • Ex
  lemma-Ex-Sᵏ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Sᵏ ₁ = lemma-Ex-S
  lemma-Ex-Sᵏ (₂₊ k) = begin
    Ex • S ^ ₂₊ k            ≈⟨ sym assoc ⟩
    (Ex • S) • S ^ ₁₊ k      ≈⟨ cleft lemma-Ex-S ⟩
    (S ↑ • Ex) • S ^ ₁₊ k    ≈⟨ assoc ⟩
    S ↑ • Ex • S ^ ₁₊ k      ≈⟨ cright lemma-Ex-Sᵏ (₁₊ k) ⟩
    S ↑ • (S ↑) ^ ₁₊ k • Ex  ≈⟨ sym assoc ⟩
    (S ↑) ^ ₂₊ k • Ex ∎

  lemma-Ex-Hᵏ↑ : ∀ k → Ex • (H ↑) ^ k ≈ H ^ k • Ex
  lemma-Ex-Hᵏ↑ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Hᵏ↑ ₁ = lemma-Ex-H↑
  lemma-Ex-Hᵏ↑ (₂₊ k) = begin
    Ex • (H ↑) ^ ₂₊ k          ≈⟨ sym assoc ⟩
    (Ex • H ↑) • (H ↑) ^ ₁₊ k  ≈⟨ cleft lemma-Ex-H↑ ⟩
    (H • Ex) • (H ↑) ^ ₁₊ k    ≈⟨ assoc ⟩
    H • Ex • (H ↑) ^ ₁₊ k      ≈⟨ cright lemma-Ex-Hᵏ↑ (₁₊ k) ⟩
    H • H ^ ₁₊ k • Ex          ≈⟨ sym assoc ⟩
    H ^ ₂₊ k • Ex ∎

  lemma-Ex-Sᵏ↑ : ∀ k → Ex • (S ↑) ^ k ≈ S ^ k • Ex
  lemma-Ex-Sᵏ↑ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Sᵏ↑ ₁ = lemma-Ex-S↑
  lemma-Ex-Sᵏ↑ (₂₊ k) = begin
    Ex • (S ↑) ^ ₂₊ k          ≈⟨ sym assoc ⟩
    (Ex • S ↑) • (S ↑) ^ ₁₊ k  ≈⟨ cleft lemma-Ex-S↑ ⟩
    (S • Ex) • (S ↑) ^ ₁₊ k    ≈⟨ assoc ⟩
    S • Ex • (S ↑) ^ ₁₊ k      ≈⟨ cright lemma-Ex-Sᵏ↑ (₁₊ k) ⟩
    S • S ^ ₁₊ k • Ex          ≈⟨ sym assoc ⟩
    S ^ ₂₊ k • Ex ∎

  ------------------------------------------------------------------------
  -- Conjugation is a monoid homomorphism
  --
  -- Stated as "Ex • u ≈ u' • Ex", the form the chains below compose in.
  -- These two are what lift the gate-level axioms to the derived words Z,
  -- R, M and Mg, which are just products and powers of S and H.

  lemma-Ex-• : ∀ {u u' v v'} → Ex • u ≈ u' • Ex → Ex • v ≈ v' • Ex →
               Ex • (u • v) ≈ (u' • v') • Ex
  lemma-Ex-• {u} {u'} {v} {v'} eu ev = begin
    Ex • (u • v)   ≈⟨ sym assoc ⟩
    (Ex • u) • v   ≈⟨ cleft eu ⟩
    (u' • Ex) • v  ≈⟨ assoc ⟩
    u' • Ex • v    ≈⟨ cright ev ⟩
    u' • v' • Ex   ≈⟨ sym assoc ⟩
    (u' • v') • Ex ∎

  lemma-Ex-pow : ∀ {u u'} → Ex • u ≈ u' • Ex → ∀ k → Ex • u ^ k ≈ u' ^ k • Ex
  lemma-Ex-pow e ₀      = trans right-unit (sym left-unit)
  lemma-Ex-pow e ₁      = e
  lemma-Ex-pow e (₂₊ k) = lemma-Ex-• e (lemma-Ex-pow e (₁₊ k))

  ------------------------------------------------------------------------
  -- CZ is symmetric in its two wires, so the swap leaves it alone
  --
  -- This is Lemma 2 of ProgressReport14, which shows the swap-vs-CZ
  -- commutation (its C12) is derivable and need not be an axiom.  The
  -- argument turns on the two ways of writing the swap.  Write A = H • H↑
  -- for the Hadamard on both wires.  A commutes with Ex, because Ex
  -- carries each Hadamard to the other wire (Lemma 1 = lemma-Ex-H, itself
  -- just semi-Ex-H↑ conjugated) and the two Hadamards commute with each
  -- other; cancelling one A then rewrites
  --
  --     Ex = CZ • A • CZ • A • CZ • A      (the definition here)
  --     Ex = A • CZ • A • CZ • A • CZ      (the report's D4)
  --
  -- and with both in hand the commutation is pure associativity: the CZ
  -- at the right end of the first form is the CZ at the left end of the
  -- second.

  lemma-Ex-A : Ex • (H • H ↑) ≈ (H • H ↑) • Ex
  lemma-Ex-A = begin
    Ex • (H • H ↑)  ≈⟨ sym assoc ⟩
    (Ex • H) • H ↑  ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • H ↑ ≈⟨ assoc ⟩
    H ↑ • (Ex • H ↑) ≈⟨ cright lemma-Ex-H↑ ⟩
    H ↑ • (H • Ex)  ≈⟨ sym assoc ⟩
    (H ↑ • H) • Ex  ≈⟨ cleft axiom comm-H ⟩
    (H • H ↑) • Ex ∎

  -- The report's D4: the same swap with the Hadamards leading.
  lemma-D4 : Ex ≈ (H • H ↑) • CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ))
  lemma-D4 = •-cancelʳ {h = H • H ↑} (begin
    Ex • (H • H ↑)
      ≈⟨ lemma-Ex-A ⟩
    (H • H ↑) • Ex
      ≈⟨ by-assoc auto ⟩
    ((H • H ↑) • CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ))) • (H • H ↑) ∎)

  lemma-Ex-CZ : Ex • CZ ≈ CZ • Ex
  lemma-Ex-CZ = begin
    Ex • CZ
      ≈⟨ by-assoc auto ⟩
    CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ)))
      ≈⟨ cright sym lemma-D4 ⟩
    CZ • Ex ∎

  lemma-Ex-CZᵏ : ∀ k → Ex • CZ ^ k ≈ CZ ^ k • Ex
  lemma-Ex-CZᵏ = lemma-Ex-pow lemma-Ex-CZ

  lemma-conj-Ex-CZ : Ex • CZ • Ex ≈ CZ
  lemma-conj-Ex-CZ = begin
    Ex • CZ • Ex    ≈⟨ sym assoc ⟩
    (Ex • CZ) • Ex  ≈⟨ cleft lemma-Ex-CZ ⟩
    (CZ • Ex) • Ex  ≈⟨ assoc ⟩
    CZ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    CZ ∎

  ------------------------------------------------------------------------
  -- The derived one-wire words, carried from the upper wire to the lower
  --
  -- Each is a product of powers of S and H, so it is assembled from the
  -- two axioms by lemma-Ex-• and lemma-Ex-pow.  The `refl'` steps are
  -- the shift commuting with a power — definitional for a literal
  -- exponent, but p-1 and toℕ k are symbolic, so lemma-↑^ is needed.

  lemma-Ex-S⁻¹↑ : Ex • S⁻¹ ↑ ≈ S⁻¹ • Ex
  lemma-Ex-S⁻¹↑ = begin
    Ex • S⁻¹ ↑          ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ p-1 S)) ⟩
    Ex • (S ↑) ^ p-1    ≈⟨ lemma-Ex-Sᵏ↑ p-1 ⟩
    S⁻¹ • Ex ∎

  lemma-Ex-Z↑ : Ex • Z ↑ ≈ Z • Ex
  lemma-Ex-Z↑ =
    lemma-Ex-• lemma-Ex-H↑
      (lemma-Ex-• lemma-Ex-H↑
        (lemma-Ex-• lemma-Ex-S↑
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• lemma-Ex-H↑ lemma-Ex-S⁻¹↑))))

  lemma-Ex-Z^↑ : ∀ k → Ex • (Z^ k) ↑ ≈ Z^ k • Ex
  lemma-Ex-Z^↑ k = begin
    Ex • (Z ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) Z)) ⟩
    Ex • (Z ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-Z↑ (toℕ k) ⟩
    Z ^ toℕ k • Ex ∎

  lemma-Ex-R↑ : Ex • R ↑ ≈ R • Ex
  lemma-Ex-R↑ = lemma-Ex-• lemma-Ex-S↑ (lemma-Ex-Z^↑ 1/2)

  lemma-Ex-R^↑ : ∀ k → Ex • (R^ k) ↑ ≈ R^ k • Ex
  lemma-Ex-R^↑ k = begin
    Ex • (R ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) R)) ⟩
    Ex • (R ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-R↑ (toℕ k) ⟩
    R ^ toℕ k • Ex ∎

  -- X on the upper wire.  This used to sit below, next to lemma-Ex-X;
  -- the SHS spelling of M carries a Pauli prefix, so lemma-Ex-M↑ needs
  -- it here.  Its factors — H ↑, S ↑ and S⁻¹ ↑ — are all above, so it
  -- moves on its own (lemma-Ex-X, which needs lemma-Ex-S⁻¹, stays put).
  lemma-Ex-X↑ : Ex • X ↑ ≈ X • Ex
  lemma-Ex-X↑ =
    lemma-Ex-• lemma-Ex-H↑
      (lemma-Ex-• lemma-Ex-S↑
        (lemma-Ex-• lemma-Ex-H↑
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• lemma-Ex-S⁻¹↑ lemma-Ex-H↑))))

  lemma-Ex-X^↑ : ∀ k → Ex • (X^ k) ↑ ≈ X^ k • Ex
  lemma-Ex-X^↑ k = begin
    Ex • (X ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) X)) ⟩
    Ex • (X ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-X↑ (toℕ k) ⟩
    X ^ toℕ k • Ex ∎

  lemma-Ex-S^↑ : ∀ k → Ex • (S^ k) ↑ ≈ S^ k • Ex
  lemma-Ex-S^↑ k = begin
    Ex • (S ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) S)) ⟩
    Ex • (S ↑) ^ toℕ k       ≈⟨ lemma-Ex-Sᵏ↑ (toℕ k) ⟩
    S ^ toℕ k • Ex ∎

  -- Eight factors now rather than six: the Pauli prefix Z^ • X^ in front
  -- of the S-spelled SHS.  Each is a power of a one-wire word, so the
  -- assembly is the same lemma-Ex-• chain, two links longer.
  lemma-Ex-M↑ : ∀ (x' : ℤ* ₚ) → Ex • M x' ↑ ≈ M x' • Ex
  lemma-Ex-M↑ x' =
    lemma-Ex-• (lemma-Ex-Z^↑ ((x + - ₁) * 1/2))
      (lemma-Ex-• (lemma-Ex-X^↑ ((₁ + - x⁻¹) * 1/2))
        (lemma-Ex-• (lemma-Ex-S^↑ x)
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• (lemma-Ex-S^↑ x⁻¹)
              (lemma-Ex-• lemma-Ex-H↑
                (lemma-Ex-• (lemma-Ex-S^↑ x) lemma-Ex-H↑))))))
    where
    x   = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁)

  lemma-Ex-Mg↑ : Ex • Mg ↑ ≈ Mg • Ex
  lemma-Ex-Mg↑ = lemma-Ex-M↑ g′

  -- …and the same three, in the other direction: a lower-wire word goes
  -- up.  c11 is c10 conjugated by the swap, and these are the factors of
  -- c10 that travel that way.

  lemma-Ex-S⁻¹ : Ex • S⁻¹ ≈ S⁻¹ ↑ • Ex
  lemma-Ex-S⁻¹ = begin
    Ex • S ^ p-1      ≈⟨ lemma-Ex-Sᵏ p-1 ⟩
    (S ↑) ^ p-1 • Ex  ≈⟨ refl' (Eq.cong (_• Ex) (Eq.sym (lemma-↑^ p-1 S))) ⟩
    S⁻¹ ↑ • Ex ∎

  lemma-Ex-Z : Ex • Z ≈ Z ↑ • Ex
  lemma-Ex-Z =
    lemma-Ex-• lemma-Ex-H
      (lemma-Ex-• lemma-Ex-H
        (lemma-Ex-• lemma-Ex-S
          (lemma-Ex-• lemma-Ex-H
            (lemma-Ex-• lemma-Ex-H lemma-Ex-S⁻¹))))

  -- The other Pauli, both ways.  X = H • S • H • H • S ⁻¹ • H, so these
  -- are the same six factors as for Z in a different order.

  lemma-Ex-X : Ex • X ≈ X ↑ • Ex
  lemma-Ex-X =
    lemma-Ex-• lemma-Ex-H
      (lemma-Ex-• lemma-Ex-S
        (lemma-Ex-• lemma-Ex-H
          (lemma-Ex-• lemma-Ex-H
            (lemma-Ex-• lemma-Ex-S⁻¹ lemma-Ex-H))))

  -- (lemma-Ex-X↑ is above, next to lemma-Ex-M↑, which needs it.)

  ------------------------------------------------------------------------
  -- Transporting a whole relation along the swap
  --
  -- Ex is an involution, so a relation between two words is equivalent to
  -- the relation between their conjugates.  This is used twice: here for
  -- the upper Pauli rule, and much later to turn c10 into c11.

  -- (exported, not private: later parts of the split use these)
  transport-Ex : ∀ {u u' v v'} →
                 Ex • u ≈ u' • Ex → Ex • v ≈ v' • Ex → u ≈ v → u' ≈ v'
  transport-Ex {u} {u'} {v} {v'} eu ev eq = begin
    u'              ≈⟨ sym lemma-cancel-Ex ⟩
    u' • Ex • Ex    ≈⟨ sym assoc ⟩
    (u' • Ex) • Ex  ≈⟨ cleft sym eu ⟩
    (Ex • u) • Ex   ≈⟨ cleft cright eq ⟩
    (Ex • v) • Ex   ≈⟨ cleft ev ⟩
    (v' • Ex) • Ex  ≈⟨ assoc ⟩
    v' • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    v' ∎

  -- (The two Pauli-versus-CZ rules are proved much further down, once the
  -- multiplier calculus and blake-c12 are both available: see
  -- lemma-rel-X↓-CZ and lemma-rel-X↑-CZ.  transport-Ex is declared here
  -- because it is what carries the lower rule to the upper one, and
  -- because c10 needs it too.)

  lemma-Ex-Z^ : ∀ k → Ex • Z^ k ≈ (Z^ k) ↑ • Ex
  lemma-Ex-Z^ k = begin
    Ex • Z ^ toℕ k      ≈⟨ lemma-Ex-pow lemma-Ex-Z (toℕ k) ⟩
    (Z ↑) ^ toℕ k • Ex  ≈⟨ refl' (Eq.cong (_• Ex) (Eq.sym (lemma-↑^ (toℕ k) Z))) ⟩
    (Z ^ toℕ k) ↑ • Ex ∎

  lemma-Ex-R : Ex • R ≈ R ↑ • Ex
  lemma-Ex-R = lemma-Ex-• lemma-Ex-S (lemma-Ex-Z^ 1/2)

  ------------------------------------------------------------------------
  -- The controlled-X and its mirror
  --
  -- CX = H ↓ ^ 3 • CZ • H ↓ conjugates CZ by an H on wire 0, so its
  -- target is wire 0 and its control wire 1; XC = H ↑ ^ 3 • CZ • H ↑ is
  -- the same with the wires exchanged.  Conjugating by the swap therefore
  -- exchanges the two, and since CZ is symmetric the proof is just the
  -- homomorphism applied to the three factors.

  lemma-Ex-CX : Ex • CX ≈ XC • Ex
  lemma-Ex-CX = lemma-Ex-• (lemma-Ex-Hᵏ 3) (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H)

  lemma-Ex-XC : Ex • XC ≈ CX • Ex
  lemma-Ex-XC = lemma-Ex-• (lemma-Ex-Hᵏ↑ 3) (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H↑)

  lemma-conj-Ex-CX : Ex • CX • Ex ≈ XC
  lemma-conj-Ex-CX = begin
    Ex • CX • Ex    ≈⟨ sym assoc ⟩
    (Ex • CX) • Ex  ≈⟨ cleft lemma-Ex-CX ⟩
    (XC • Ex) • Ex  ≈⟨ assoc ⟩
    XC • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    XC ∎

  lemma-conj-Ex-XC : Ex • XC • Ex ≈ CX
  lemma-conj-Ex-XC = begin
    Ex • XC • Ex    ≈⟨ sym assoc ⟩
    (Ex • XC) • Ex  ≈⟨ cleft lemma-Ex-XC ⟩
    (CX • Ex) • Ex  ≈⟨ assoc ⟩
    CX • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    CX ∎

  -- …and on to powers, which is the form blake-c12 needs (it writes
  -- CX ^ p-1 for the inverse).
  lemma-Ex-CXᵏ : ∀ k → Ex • CX ^ k ≈ XC ^ k • Ex
  lemma-Ex-CXᵏ = lemma-Ex-pow lemma-Ex-CX

  lemma-Ex-XCᵏ : ∀ k → Ex • XC ^ k ≈ CX ^ k • Ex
  lemma-Ex-XCᵏ = lemma-Ex-pow lemma-Ex-XC

  ------------------------------------------------------------------------
  -- The half-swaps, and ⊤⊥ / ⊥⊤
  --
  -- ₕ|ₕ = H ↓ • CZ • H ↓ and ʰ|ʰ = H ↑ • CZ • H ↑ are the same word on
  -- the two wires, so the swap exchanges them; ⊥⊤ = ₕ|ₕ • ʰ|ʰ and
  -- ⊤⊥ = ʰ|ʰ • ₕ|ₕ are their two orders, so the swap exchanges those
  -- too.  Selinger's c13, c14 and c15 are all stated over ⊤⊥ / ⊥⊤, and
  -- c14 and c15 are mirror images of one another.

  lemma-Ex-ₕ|ₕ : Ex • ₕ|ₕ ≈ ʰ|ʰ • Ex
  lemma-Ex-ₕ|ₕ = lemma-Ex-• lemma-Ex-H (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H)

  lemma-Ex-ʰ|ʰ : Ex • ʰ|ʰ ≈ ₕ|ₕ • Ex
  lemma-Ex-ʰ|ʰ = lemma-Ex-• lemma-Ex-H↑ (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H↑)

  lemma-Ex-⊥⊤ : Ex • ⊥⊤ ≈ ⊤⊥ • Ex
  lemma-Ex-⊥⊤ = lemma-Ex-• lemma-Ex-ₕ|ₕ lemma-Ex-ʰ|ʰ

  lemma-Ex-⊤⊥ : Ex • ⊤⊥ ≈ ⊥⊤ • Ex
  lemma-Ex-⊤⊥ = lemma-Ex-• lemma-Ex-ʰ|ʰ lemma-Ex-ₕ|ₕ

  lemma-conj-Ex-⊥⊤ : Ex • ⊥⊤ • Ex ≈ ⊤⊥
  lemma-conj-Ex-⊥⊤ = begin
    Ex • ⊥⊤ • Ex    ≈⟨ sym assoc ⟩
    (Ex • ⊥⊤) • Ex  ≈⟨ cleft lemma-Ex-⊥⊤ ⟩
    (⊤⊥ • Ex) • Ex  ≈⟨ assoc ⟩
    ⊤⊥ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    ⊤⊥ ∎

  lemma-conj-Ex-⊤⊥ : Ex • ⊤⊥ • Ex ≈ ⊥⊤
  lemma-conj-Ex-⊤⊥ = begin
    Ex • ⊤⊥ • Ex    ≈⟨ sym assoc ⟩
    (Ex • ⊤⊥) • Ex  ≈⟨ cleft lemma-Ex-⊤⊥ ⟩
    (⊥⊤ • Ex) • Ex  ≈⟨ assoc ⟩
    ⊥⊤ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    ⊥⊤ ∎

  ------------------------------------------------------------------------
  -- Three half-swaps make the swap
  --
  --     ₕ|ₕ • ʰ|ʰ • ₕ|ₕ  ≈  H • Ex • (H ↑) ^ 3
  --
  -- the classical "SWAP is three CNOTs", in the form the two rule sets
  -- actually write.  Both sides are the same nine letters
  -- H CZ H H↑ CZ H H↑ CZ H once the H's are sorted: on the left the
  -- adjacent H↑ • H is flipped by the structural comm-H, and on the right
  -- Ex's trailing H↑ absorbs the (H ↑) ^ 3 into (H ↑) ^ 4 ≈ ε.
  --
  -- This is the dictionary c13, c14 and c15 need, since those are stated
  -- over ⊤⊥ / ⊥⊤ while Paper-V1's own three-wire axioms are stated over
  -- Ex.

  lemma-order-H↑ : (H ↑) ^ 4 ≈ ε
  lemma-order-H↑ = lemma-cong↑ _ _ (One-Wire.lemma-order-H n)

  lemma-half-swaps : ₕ|ₕ • ʰ|ʰ • ₕ|ₕ ≈ H • Ex • (H ↑) ^ 3
  lemma-half-swaps = begin
    ₕ|ₕ • ʰ|ʰ • ₕ|ₕ
      ≈⟨ by-assoc auto ⟩
    (H • CZ • H • H ↑ • CZ) • (H ↑ • H) • CZ • H
      ≈⟨ cright cleft axiom comm-H ⟩
    (H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H
      ≈⟨ sym right-unit ⟩
    ((H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H) • ε
      ≈⟨ cright sym lemma-order-H↑ ⟩
    ((H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H) • (H ↑) ^ 4
      ≈⟨ by-assoc auto ⟩
    H • Ex • (H ↑) ^ 3 ∎

  ------------------------------------------------------------------------
  -- A half-swap times a swap has order 3
  --
  -- Ex carries ₕ|ₕ to ʰ|ʰ, so ⊥⊤ = ₕ|ₕ • ʰ|ʰ is (ₕ|ₕ • Ex) squared, and
  -- ⊤⊥ is the same element conjugated.  Cubing that element is
  -- ⊥⊤ • ₕ|ₕ • Ex, which lemma-half-swaps rewrites to H • Ex • (H ↑)³ • Ex;
  -- the two swaps then cancel and H ⁴ is ε.
  --
  -- Both c14 and c15 assert that an element cubes to ε, and Paper-V1's
  -- axioms supply exactly two such elements: this one and the 3-cycle of
  -- lemma-σ³.

  lemma-ʰ|ʰ-conj : Ex • (ₕ|ₕ • Ex) ≈ ʰ|ʰ
  lemma-ʰ|ʰ-conj = begin
    Ex • (ₕ|ₕ • Ex)  ≈⟨ sym assoc ⟩
    (Ex • ₕ|ₕ) • Ex  ≈⟨ cleft lemma-Ex-ₕ|ₕ ⟩
    (ʰ|ʰ • Ex) • Ex  ≈⟨ assoc ⟩
    ʰ|ʰ • (Ex • Ex)  ≈⟨ cright lemma-Ex-Ex ⟩
    ʰ|ʰ • ε          ≈⟨ right-unit ⟩
    ʰ|ʰ ∎

  lemma-⊥⊤-square : ⊥⊤ ≈ (ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)
  lemma-⊥⊤-square = begin
    ₕ|ₕ • ʰ|ʰ                    ≈⟨ cright sym lemma-ʰ|ʰ-conj ⟩
    ₕ|ₕ • (Ex • (ₕ|ₕ • Ex))      ≈⟨ sym assoc ⟩
    (ₕ|ₕ • Ex) • (ₕ|ₕ • Ex) ∎

  lemma-half-swap-cube : ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex) ≈ ε
  lemma-half-swap-cube = begin
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)
      ≈⟨ cleft sym lemma-⊥⊤-square ⟩
    ⊥⊤ • (ₕ|ₕ • Ex)
      ≈⟨ by-assoc auto ⟩
    (ₕ|ₕ • ʰ|ʰ • ₕ|ₕ) • Ex
      ≈⟨ cleft lemma-half-swaps ⟩
    (H • Ex • (H ↑) ^ 3) • Ex
      ≈⟨ by-assoc auto ⟩
    H • Ex • ((H ↑) ^ 3 • Ex)
      ≈⟨ cright cright sym (lemma-Ex-Hᵏ 3) ⟩
    H • Ex • (Ex • H ^ 3)
      ≈⟨ by-assoc auto ⟩
    H • (Ex • Ex) • H ^ 3
      ≈⟨ cright cleft lemma-Ex-Ex ⟩
    H • ε • H ^ 3
      ≈⟨ cright left-unit ⟩
    H • H ^ 3
      ≈⟨ by-assoc auto ⟩
    H ^ 4
      ≈⟨ One-Wire.lemma-order-H (₁₊ n) ⟩
    ε ∎

  -- The same on the other side.  ⊤⊥ is what c14 is stated over, and it is
  -- the square of Ex • ₕ|ₕ, which is the previous element conjugated by
  -- the swap — so its cube is ε for the same reason, with no second
  -- appeal to lemma-half-swaps.

  lemma-UUₕ|ₕ : ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ ≈ Ex
  lemma-UUₕ|ₕ = begin
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ
      ≈⟨ sym right-unit ⟩
    (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ) • ε
      ≈⟨ cright sym lemma-Ex-Ex ⟩
    (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ) • (Ex • Ex)
      ≈⟨ by-assoc auto ⟩
    (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)) • Ex
      ≈⟨ cleft lemma-half-swap-cube ⟩
    ε • Ex
      ≈⟨ left-unit ⟩
    Ex ∎

  lemma-⊤⊥-square : ⊤⊥ ≈ (Ex • ₕ|ₕ) • (Ex • ₕ|ₕ)
  lemma-⊤⊥-square = begin
    ʰ|ʰ • ₕ|ₕ                        ≈⟨ cleft sym lemma-ʰ|ʰ-conj ⟩
    (Ex • (ₕ|ₕ • Ex)) • ₕ|ₕ          ≈⟨ by-assoc auto ⟩
    (Ex • ₕ|ₕ) • (Ex • ₕ|ₕ) ∎

  lemma-⊤⊥-cube : ((Ex • ₕ|ₕ) • (Ex • ₕ|ₕ)) • (Ex • ₕ|ₕ) ≈ ε
  lemma-⊤⊥-cube = begin
    ((Ex • ₕ|ₕ) • (Ex • ₕ|ₕ)) • (Ex • ₕ|ₕ)
      ≈⟨ by-assoc auto ⟩
    Ex • (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ)
      ≈⟨ cright lemma-UUₕ|ₕ ⟩
    Ex • Ex
      ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  lemma-conj-Ex-Mg↑ : Ex • Mg ↑ • Ex ≈ Mg
  lemma-conj-Ex-Mg↑ = begin
    Ex • Mg ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • Mg ↑) • Ex ≈⟨ cleft lemma-Ex-Mg↑ ⟩
    (Mg • Ex) • Ex   ≈⟨ assoc ⟩
    Mg • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    Mg ∎

  ------------------------------------------------------------------------
  -- The ↓-rules, obtained by conjugating the ↑-rules
  --
  -- This is what the new comm-Ex-CZ axiom buys.  Each proof is the same
  -- three moves: replace the lower-wire word by its Ex-conjugate, push
  -- the CZ through both copies of Ex, and apply the ↑-rule in the middle.

  lemma-comm-CZ-S : CZ • S ≈ S • CZ
  lemma-comm-CZ-S = begin
    CZ • S                ≈⟨ cright sym lemma-conj-Ex-S↑ ⟩
    CZ • (Ex • S ↑ • Ex)  ≈⟨ by-assoc auto ⟩
    (CZ • Ex) • S ↑ • Ex  ≈⟨ cleft sym lemma-Ex-CZ ⟩
    (Ex • CZ) • S ↑ • Ex  ≈⟨ by-assoc auto ⟩
    Ex • (CZ • S ↑) • Ex  ≈⟨ cright cleft axiom comm-CZ-S↑ ⟩
    Ex • (S ↑ • CZ) • Ex  ≈⟨ by-assoc auto ⟩
    (Ex • S ↑) • CZ • Ex  ≈⟨ cright sym lemma-Ex-CZ ⟩
    (Ex • S ↑) • Ex • CZ  ≈⟨ by-assoc auto ⟩
    (Ex • S ↑ • Ex) • CZ  ≈⟨ cleft lemma-conj-Ex-S↑ ⟩
    S • CZ ∎

  -- Every re-bracketing here is an explicit assoc rather than by-assoc:
  -- the tactic compares to-list, and to-list is stuck on CZ^ g = CZ ^ toℕ g,
  -- whose exponent is symbolic.
  lemma-semi-Mg-CZ : Mg • CZ ≈ CZ^ g • Mg
  lemma-semi-Mg-CZ = begin
    Mg • CZ                       ≈⟨ cleft sym lemma-conj-Ex-Mg↑ ⟩
    (Ex • (Mg ↑ • Ex)) • CZ       ≈⟨ assoc ⟩
    Ex • ((Mg ↑ • Ex) • CZ)       ≈⟨ cright assoc ⟩
    Ex • (Mg ↑ • (Ex • CZ))       ≈⟨ cright cright lemma-Ex-CZ ⟩
    Ex • (Mg ↑ • (CZ • Ex))       ≈⟨ cright sym assoc ⟩
    Ex • ((Mg ↑ • CZ) • Ex)       ≈⟨ cright cleft lemma-semi-M↑CZ ⟩
    Ex • ((CZ^ g • Mg ↑) • Ex)    ≈⟨ cright assoc ⟩
    Ex • (CZ^ g • (Mg ↑ • Ex))    ≈⟨ sym assoc ⟩
    (Ex • CZ^ g) • (Mg ↑ • Ex)    ≈⟨ cleft lemma-Ex-CZᵏ (toℕ g) ⟩
    (CZ^ g • Ex) • (Mg ↑ • Ex)    ≈⟨ assoc ⟩
    CZ^ g • (Ex • (Mg ↑ • Ex))    ≈⟨ cright lemma-conj-Ex-Mg↑ ⟩
    CZ^ g • Mg ∎

  ------------------------------------------------------------------------
  -- Pushing the multiplier past a CZ power rescales the exponent
  --
  -- Iterating the rule over the power multiplies the exponent by g.  The
  -- product is taken in ℕ, so lemma-pow-mod brings it back into range and
  -- lemma-toℕ-% identifies it with the product in ℤ/pℤ.

  lemma-Mg-CZ^ : ∀ (a : ℤ ₚ) → Mg • CZ^ a ≈ CZ^ (g * a) • Mg
  lemma-Mg-CZ^ a = begin
    Mg • CZ ^ toℕ a
      ≈⟨ lemma-Induction lemma-semi-Mg-CZ (toℕ a) ⟩
    (CZ ^ toℕ g) ^ toℕ a • Mg
      ≈⟨ cleft (^^ CZ (toℕ g) (toℕ a)) ⟩
    CZ ^ (toℕ g Nat.* toℕ a) • Mg
      ≈⟨ cleft (lemma-pow-mod (axiom order-CZ) (toℕ g Nat.* toℕ a)) ⟩
    CZ ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg
      ≈⟨ cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% g a)) ⟩
    CZ ^ toℕ (g * a) • Mg ∎

  -- Mg ^ j rescales by g ^′ j.  The induction costs only associativity,
  -- since x ^′ (suc k) is x * (x ^′ k) definitionally; the ₀/₁/₂₊ split
  -- is forced by w ^ 1 being w rather than w • w ^ 0.
  lemma-Mgᵏ-CZ : ∀ j → Mg ^ j • CZ ≈ CZ ^ toℕ (g ^′ j) • Mg ^ j
  lemma-Mgᵏ-CZ ₀ = begin
    ε • CZ  ≈⟨ left-unit ⟩
    CZ      ≈⟨ sym right-unit ⟩
    CZ • ε ∎
  lemma-Mgᵏ-CZ ₁ = begin
    Mg • CZ                ≈⟨ lemma-semi-Mg-CZ ⟩
    CZ ^ toℕ g • Mg
      ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • Mg) (Eq.sym (lemma-x^′1=x g)) ⟩
    CZ ^ toℕ (g ^′ 1) • Mg ∎
  lemma-Mgᵏ-CZ (₂₊ j) = begin
    (Mg • Mg ^ ₁₊ j) • CZ
      ≈⟨ assoc ⟩
    Mg • (Mg ^ ₁₊ j • CZ)
      ≈⟨ cright lemma-Mgᵏ-CZ (₁₊ j) ⟩
    Mg • (CZ ^ toℕ (g ^′ ₁₊ j) • Mg ^ ₁₊ j)
      ≈⟨ sym assoc ⟩
    (Mg • CZ ^ toℕ (g ^′ ₁₊ j)) • Mg ^ ₁₊ j
      ≈⟨ cleft lemma-Mg-CZ^ (g ^′ ₁₊ j) ⟩
    (CZ ^ toℕ (g * (g ^′ ₁₊ j)) • Mg) • Mg ^ ₁₊ j
      ≈⟨ assoc ⟩
    CZ ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg • Mg ^ ₁₊ j) ∎

  ------------------------------------------------------------------------
  -- The same chain one wire up
  --
  -- semi-M↑CZ is an axiom, so the wire-1 multiplier needs no derivation
  -- for its base case; from there the induction is word-for-word the
  -- wire-0 one.  A multiplier on either wire of a CZ rescales it by the
  -- same factor, which is what makes c14's cancellation work.

  lemma-Mg↑-CZ^ : ∀ (a : ℤ ₚ) → Mg ↑ • CZ^ a ≈ CZ^ (g * a) • Mg ↑
  lemma-Mg↑-CZ^ a = begin
    Mg ↑ • CZ ^ toℕ a
      ≈⟨ lemma-Induction lemma-semi-M↑CZ (toℕ a) ⟩
    (CZ ^ toℕ g) ^ toℕ a • Mg ↑
      ≈⟨ cleft (^^ CZ (toℕ g) (toℕ a)) ⟩
    CZ ^ (toℕ g Nat.* toℕ a) • Mg ↑
      ≈⟨ cleft (lemma-pow-mod (axiom order-CZ) (toℕ g Nat.* toℕ a)) ⟩
    CZ ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg ↑
      ≈⟨ cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% g a)) ⟩
    CZ ^ toℕ (g * a) • Mg ↑ ∎

  lemma-Mgᵏ↑-CZ : ∀ j → (Mg ↑) ^ j • CZ ≈ CZ ^ toℕ (g ^′ j) • (Mg ↑) ^ j
  lemma-Mgᵏ↑-CZ ₀ = begin
    ε • CZ  ≈⟨ left-unit ⟩
    CZ      ≈⟨ sym right-unit ⟩
    CZ • ε ∎
  lemma-Mgᵏ↑-CZ ₁ = begin
    Mg ↑ • CZ            ≈⟨ lemma-semi-M↑CZ ⟩
    CZ ^ toℕ g • Mg ↑
      ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • Mg ↑) (Eq.sym (lemma-x^′1=x g)) ⟩
    CZ ^ toℕ (g ^′ 1) • Mg ↑ ∎
  lemma-Mgᵏ↑-CZ (₂₊ j) = begin
    (Mg ↑ • (Mg ↑) ^ ₁₊ j) • CZ
      ≈⟨ assoc ⟩
    Mg ↑ • ((Mg ↑) ^ ₁₊ j • CZ)
      ≈⟨ cright lemma-Mgᵏ↑-CZ (₁₊ j) ⟩
    Mg ↑ • (CZ ^ toℕ (g ^′ ₁₊ j) • (Mg ↑) ^ ₁₊ j)
      ≈⟨ sym assoc ⟩
    (Mg ↑ • CZ ^ toℕ (g ^′ ₁₊ j)) • (Mg ↑) ^ ₁₊ j
      ≈⟨ cleft lemma-Mg↑-CZ^ (g ^′ ₁₊ j) ⟩
    (CZ ^ toℕ (g * (g ^′ ₁₊ j)) • Mg ↑) • (Mg ↑) ^ ₁₊ j
      ≈⟨ assoc ⟩
    CZ ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg ↑ • (Mg ↑) ^ ₁₊ j) ∎

  ------------------------------------------------------------------------
  -- (moved below, after the multiplier lemmas it depends on)

  -- (exported, not private: later parts of the split use these)
  -- The power of g that is -1, and M₋₁ as that power of Mg, taken from
  -- One-Wire at both widths: as it stands for the wire-0 multiplier,
  -- and lifted for the wire-1 one.
  j₋ : ℕ
  j₋ = One-Wire.j₋ n

  e₋ : (g^ (One-Wire.k₋ n)) .proj₁ ≡ -'₁ .proj₁
  e₋ = One-Wire.e₋ n

  Mg^j₋≈M₋₁ : Mg ^ j₋ ≈ M₋₁
  Mg^j₋≈M₋₁ = One-Wire.lemma-M₋₁-pow (₁₊ n)

  lemma-M₋₁-CZ : M₋₁ • CZ ≈ CZ ^ toℕ (-'₁ .proj₁) • M₋₁
  lemma-M₋₁-CZ = begin
    M₋₁ • CZ                        ≈⟨ cleft sym Mg^j₋≈M₋₁ ⟩
    Mg ^ j₋ • CZ                    ≈⟨ lemma-Mgᵏ-CZ j₋ ⟩
    CZ ^ toℕ (g ^′ j₋) • Mg ^ j₋    ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • Mg ^ j₋) e₋ ⟩
    CZ ^ toℕ (-'₁ .proj₁) • Mg ^ j₋ ≈⟨ cright Mg^j₋≈M₋₁ ⟩
    CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ∎

  -- The same, one wire up.  M-power and aux-M≡M are one-wire facts, so
  -- the ↑ version is the ↓ one lifted, modulo (Mg ^ j) ↑ ≡ (Mg ↑) ^ j.
  Mg↑^j₋≈M₋₁↑ : (Mg ↑) ^ j₋ ≈ M₋₁ ↑
  Mg↑^j₋≈M₋₁↑ = begin
    (Mg ↑) ^ j₋  ≡⟨ Eq.sym (lemma-↑^ j₋ Mg) ⟩
    (Mg ^ j₋) ↑  ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-M₋₁-pow n) ⟩
    M₋₁ ↑ ∎

  -- Exposed rather than private: Three-Wire needs this one for c14.
  lemma-M₋₁↑-CZ : M₋₁ ↑ • CZ ≈ CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑
  lemma-M₋₁↑-CZ = begin
    M₋₁ ↑ • CZ                       ≈⟨ cleft sym Mg↑^j₋≈M₋₁↑ ⟩
    (Mg ↑) ^ j₋ • CZ                 ≈⟨ lemma-Mgᵏ↑-CZ j₋ ⟩
    CZ ^ toℕ (g ^′ j₋) • (Mg ↑) ^ j₋
      ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • (Mg ↑) ^ j₋) e₋ ⟩
    CZ ^ toℕ (-'₁ .proj₁) • (Mg ↑) ^ j₋ ≈⟨ cright Mg↑^j₋≈M₋₁↑ ⟩
    CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑ ∎

  -- CZ • CZ⁻¹ is CZ ^ p.  Exposed rather than private: Three-Wire needs
  -- it for c14, where the same cancellation closes the chain.
  lemma-CZ-CZ₋₁ : CZ • CZ ^ toℕ (-'₁ .proj₁) ≈ ε
  lemma-CZ-CZ₋₁ = begin
    CZ • CZ ^ toℕ (-'₁ .proj₁)
      ≡⟨ Eq.cong (λ m → CZ • CZ ^ m) lemma-toℕ-1ₚ ⟩
    CZ • CZ ^ p-1        ≈⟨ sym (^-+ CZ 1 p-1) ⟩
    CZ ^ (1 Nat.+ p-1)   ≈⟨ axiom order-CZ ⟩
    ε ∎

  lemma-ₕ|ₕ-invol : ₕ|ₕ • ₕ|ₕ ≈ ε
  lemma-ₕ|ₕ-invol = begin
    (H • CZ • H) • (H • CZ • H)
      ≈⟨ by-assoc auto ⟩
    H • CZ • (H ^ 2 • (CZ • H))
      ≈⟨ cright cright cleft axiom order-H ⟩
    H • CZ • (M₋₁ • (CZ • H))
      ≈⟨ cright cright sym assoc ⟩
    H • CZ • ((M₋₁ • CZ) • H)
      ≈⟨ cright cright cleft lemma-M₋₁-CZ ⟩
    H • CZ • ((CZ ^ toℕ (-'₁ .proj₁) • M₋₁) • H)
      -- explicit assoc, not by-assoc: to-list is stuck on the symbolic
      -- exponent of CZ ^ toℕ (-'₁ .proj₁)
      ≈⟨ cright cright assoc ⟩
    H • CZ • (CZ ^ toℕ (-'₁ .proj₁) • (M₋₁ • H))
      ≈⟨ cright sym assoc ⟩
    H • ((CZ • CZ ^ toℕ (-'₁ .proj₁)) • (M₋₁ • H))
      ≈⟨ cright cleft lemma-CZ-CZ₋₁ ⟩
    H • (ε • (M₋₁ • H))
      ≈⟨ cright left-unit ⟩
    H • (M₋₁ • H)
      ≈⟨ cright cleft sym (axiom order-H) ⟩
    H • (H ^ 2 • H)
      ≈⟨ by-assoc auto ⟩
    H ^ 4
      ≈⟨ One-Wire.lemma-order-H (₁₊ n) ⟩
    ε ∎

  lemma-ʰ|ʰ-invol : ʰ|ʰ • ʰ|ʰ ≈ ε
  lemma-ʰ|ʰ-invol = begin
    ʰ|ʰ • ʰ|ʰ
      ≈⟨ cong (sym lemma-ʰ|ʰ-conj) (sym lemma-ʰ|ʰ-conj) ⟩
    (Ex • (ₕ|ₕ • Ex)) • (Ex • (ₕ|ₕ • Ex))
      ≈⟨ by-assoc auto ⟩
    Ex • (ₕ|ₕ • ((Ex • Ex) • (ₕ|ₕ • Ex)))
      ≈⟨ cright cright cleft lemma-Ex-Ex ⟩
    Ex • (ₕ|ₕ • (ε • (ₕ|ₕ • Ex)))
      ≈⟨ cright cright left-unit ⟩
    Ex • (ₕ|ₕ • (ₕ|ₕ • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((ₕ|ₕ • ₕ|ₕ) • Ex)
      ≈⟨ cright cleft lemma-ₕ|ₕ-invol ⟩
    Ex • (ε • Ex)
      ≈⟨ cright left-unit ⟩
    Ex • Ex
      ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  -- ⊥⊤ and ⊤⊥ are the two products of the same pair of involutions.
  lemma-⊥⊤-⊤⊥ : ⊥⊤ • ⊤⊥ ≈ ε
  lemma-⊥⊤-⊤⊥ = begin
    (ₕ|ₕ • ʰ|ʰ) • (ʰ|ʰ • ₕ|ₕ)
      ≈⟨ by-assoc auto ⟩
    ₕ|ₕ • ((ʰ|ʰ • ʰ|ʰ) • ₕ|ₕ)
      ≈⟨ cright cleft lemma-ʰ|ʰ-invol ⟩
    ₕ|ₕ • (ε • ₕ|ₕ)
      ≈⟨ cright left-unit ⟩
    ₕ|ₕ • ₕ|ₕ
      ≈⟨ lemma-ₕ|ₕ-invol ⟩
    ε ∎

  -- With both involutions in hand the two half-swap words collapse to a
  -- single half-swap times a swap: ⊥⊤ • (Ex • ₕ|ₕ) is ₕ|ₕ • ₕ|ₕ after the
  -- two swaps cancel, and likewise on the other side.  These are the
  -- forms c13 is proved in.
  lemma-⊥⊤-simple : ⊥⊤ ≈ Ex • ₕ|ₕ
  lemma-⊥⊤-simple = •-cancelˡ {g = ₕ|ₕ • Ex} (begin
    (ₕ|ₕ • Ex) • ⊥⊤
      ≈⟨ cright lemma-⊥⊤-square ⟩
    (ₕ|ₕ • Ex) • ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex))
      ≈⟨ sym assoc ⟩
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)
      ≈⟨ lemma-half-swap-cube ⟩
    ε
      ≈⟨ sym lemma-ₕ|ₕ-invol ⟩
    ₕ|ₕ • ₕ|ₕ
      ≈⟨ by-assoc auto ⟩
    ₕ|ₕ • (ε • ₕ|ₕ)
      ≈⟨ cright cleft sym lemma-Ex-Ex ⟩
    ₕ|ₕ • ((Ex • Ex) • ₕ|ₕ)
      ≈⟨ by-assoc auto ⟩
    (ₕ|ₕ • Ex) • (Ex • ₕ|ₕ) ∎)

  lemma-⊤⊥-⊥⊤ : ⊤⊥ • ⊥⊤ ≈ ε
  lemma-⊤⊥-⊥⊤ = begin
    (ʰ|ʰ • ₕ|ₕ) • (ₕ|ₕ • ʰ|ʰ)
      ≈⟨ by-assoc auto ⟩
    ʰ|ʰ • ((ₕ|ₕ • ₕ|ₕ) • ʰ|ʰ)
      ≈⟨ cright cleft lemma-ₕ|ₕ-invol ⟩
    ʰ|ʰ • (ε • ʰ|ʰ)
      ≈⟨ cright left-unit ⟩
    ʰ|ʰ • ʰ|ʰ
      ≈⟨ lemma-ʰ|ʰ-invol ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- The half-swap is a multiplier times a CX
  --
  -- CX is H ^ 3 • CZ • H by definition, so M₋₁ • CX is H ^ 5 • CZ • H,
  -- and H ^ 4 ≈ ε leaves H • CZ • H, which is ₕ|ₕ.  Purely syntactic —
  -- it needs only the definition of CX, order-H and lemma-M₋₁^2.
  --
  -- This is the bridge to C18: C18 tells us how CX ↑ moves across a CZ,
  -- and this lemma turns that into a statement about the half-swap, which
  -- is what c14 is stated over.

  lemma-ₕ|ₕ-CX : M₋₁ • CX ≈ ₕ|ₕ
  lemma-ₕ|ₕ-CX = begin
    M₋₁ • CX
      ≈⟨ cleft sym (axiom order-H) ⟩
    H ^ 2 • CX
      ≈⟨ by-assoc auto ⟩
    (H ^ 4 • H) • (CZ • H)
      ≈⟨ cleft cleft One-Wire.lemma-order-H (₁₊ n) ⟩
    (ε • H) • (CZ • H)
      ≈⟨ cleft left-unit ⟩
    H • (CZ • H) ∎

  lemma-⊤⊥-simple : ⊤⊥ ≈ ₕ|ₕ • Ex
  lemma-⊤⊥-simple = •-cancelʳ {h = ⊥⊤} (begin
    ⊤⊥ • ⊥⊤                  ≈⟨ lemma-⊤⊥-⊥⊤ ⟩
    ε                        ≈⟨ sym lemma-ₕ|ₕ-invol ⟩
    ₕ|ₕ • ₕ|ₕ                ≈⟨ by-assoc auto ⟩
    ₕ|ₕ • (ε • ₕ|ₕ)          ≈⟨ cright cleft sym lemma-Ex-Ex ⟩
    ₕ|ₕ • ((Ex • Ex) • ₕ|ₕ)  ≈⟨ by-assoc auto ⟩
    (ₕ|ₕ • Ex) • (Ex • ₕ|ₕ)  ≈⟨ cright sym lemma-⊥⊤-simple ⟩
    (ₕ|ₕ • Ex) • ⊥⊤ ∎)

  -- The cube, stated over ⊤⊥ itself rather than over ₕ|ₕ • Ex.
  ------------------------------------------------------------------------
  -- CZ against H ↑
  --
  -- XC is H ↑ ^ 3 • CZ • H ↑ by definition, so H ↑ • XC is CZ • H ↑ once
  -- H ↑ ^ 4 ≈ ε closes the loop.  This is what peels a leading H ↑ off
  -- both sides of c10, leaving the reduced core
  --
  --     XC • CZ ≈ R ↑ • XC • R ↑ ⁻¹ • R ↓ ⁻¹.
  --
  -- (The swap-dual of CX that the core then needs is already available:
  -- lemma-conj-Ex-CX turns blake-c12 into its XC form.)

