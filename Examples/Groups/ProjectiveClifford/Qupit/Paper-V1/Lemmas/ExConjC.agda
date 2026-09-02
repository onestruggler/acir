{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Ex-conjugation calculus, part 3 of 3: the Pauli-versus-CZ rules,
-- the XC flip, and Selinger's c10 / c11.
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


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ExConjC
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
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ExConjB p-3 p-prime g* g-gen as B

module Ex-Conjugation-C (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ ; •-cancelˡ)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₁ = PB ((₁₊ n) QRel,_===_)


  open B.Ex-Conjugation-B n public

  lemma-rel-X↓-CZ : CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
  lemma-rel-X↓-CZ = Derive.lemma-rel-X↓-CZ

  -- …and the upper one, which is the lower one conjugated by the swap.
  -- Ex fixes CZ (lemma-Ex-CZ) and exchanges the wires, so transporting
  -- CZ • X ↓ ≈ X ↓ • Z ↑ • CZ across it gives CZ • X ↑ ≈ X ↑ • Z ↓ • CZ.
  lemma-rel-X↑-CZ : CZ • X ↑ ≈ X ↑ • (Z • CZ)
  lemma-rel-X↑-CZ = transport-Ex lhs rhs lemma-rel-X↓-CZ
    where
    lhs : Ex • (CZ • X) ≈ (CZ • X ↑) • Ex
    lhs = lemma-Ex-• lemma-Ex-CZ lemma-Ex-X

    rhs : Ex • (X • (Z ↑ • CZ)) ≈ (X ↑ • (Z • CZ)) • Ex
    rhs = lemma-Ex-• lemma-Ex-X (lemma-Ex-• lemma-Ex-Z↑ lemma-Ex-CZ)

  ------------------------------------------------------------------------
  -- A power of the upper X across CZ
  --
  -- rel-X↑-CZ moves one X ↑ across CZ at the cost of a Z on wire 0.
  -- Iterating collects one Z per crossing; the Z's slide back past the
  -- remaining X ↑ because they sit on different wires (lemma-comm-Z-w↑),
  -- so the corrections gather into a single power.

  lemma-CZ-X↑ᵏ : ∀ m → CZ • (X ↑) ^ m ≈ (X ↑) ^ m • ((Z ↓) ^ m • CZ)
  lemma-CZ-X↑ᵏ ₀ = begin
    CZ • ε              ≈⟨ right-unit ⟩
    CZ                  ≈⟨ sym left-unit ⟩
    ε • CZ              ≈⟨ sym left-unit ⟩
    ε • (ε • CZ) ∎
  lemma-CZ-X↑ᵏ ₁ = lemma-rel-X↑-CZ
  lemma-CZ-X↑ᵏ (₂₊ k) = begin
    CZ • (X ↑ • (X ↑) ^ ₁₊ k)
      ≈⟨ sym assoc ⟩
    (CZ • X ↑) • (X ↑) ^ ₁₊ k
      ≈⟨ cleft lemma-rel-X↑-CZ ⟩
    (X ↑ • (Z ↓ • CZ)) • (X ↑) ^ ₁₊ k
      ≈⟨ assoc ⟩
    X ↑ • ((Z ↓ • CZ) • (X ↑) ^ ₁₊ k)
      ≈⟨ cright assoc ⟩
    X ↑ • (Z ↓ • (CZ • (X ↑) ^ ₁₊ k))
      ≈⟨ cright cright lemma-CZ-X↑ᵏ (₁₊ k) ⟩
    X ↑ • (Z ↓ • ((X ↑) ^ ₁₊ k • ((Z ↓) ^ ₁₊ k • CZ)))
      ≈⟨ cright sym assoc ⟩
    X ↑ • ((Z ↓ • (X ↑) ^ ₁₊ k) • ((Z ↓) ^ ₁₊ k • CZ))
      ≈⟨ cright cleft slide ⟩
    X ↑ • (((X ↑) ^ ₁₊ k • Z ↓) • ((Z ↓) ^ ₁₊ k • CZ))
      ≈⟨ cright assoc ⟩
    X ↑ • ((X ↑) ^ ₁₊ k • (Z ↓ • ((Z ↓) ^ ₁₊ k • CZ)))
      ≈⟨ sym assoc ⟩
    (X ↑ • (X ↑) ^ ₁₊ k) • (Z ↓ • ((Z ↓) ^ ₁₊ k • CZ))
      ≈⟨ cright sym assoc ⟩
    (X ↑ • (X ↑) ^ ₁₊ k) • ((Z ↓ • (Z ↓) ^ ₁₊ k) • CZ) ∎
    where
    slide : Z ↓ • (X ↑) ^ ₁₊ k ≈ (X ↑) ^ ₁₊ k • Z ↓
    slide = begin
      Z ↓ • (X ↑) ^ ₁₊ k  ≡⟨ Eq.cong (λ w → Z ↓ • w) (Eq.sym (lemma-↑^ (₁₊ k) X)) ⟩
      Z ↓ • (X ^ ₁₊ k) ↑  ≈⟨ lemma-comm-Z-w↑ (X ^ ₁₊ k) ⟩
      (X ^ ₁₊ k) ↑ • Z ↓  ≡⟨ Eq.cong (λ w → w • Z ↓) (lemma-↑^ (₁₊ k) X) ⟩
      (X ↑) ^ ₁₊ k • Z ↓ ∎

  ------------------------------------------------------------------------
  -- A Pauli across a power of CZ
  --
  -- rel-X↑-CZ iterated in the CZ exponent.  The Z's the crossings emit
  -- gather into a single power, since they pass the CZ's still to come.

  -- (_↓ is the identity on circuits — it only pins a wire count — so the
  -- Z ↓ the axiom emits *is* the wire-0 Z, with no conversion needed.)
  lemma-CZᵏ-X↑ : ∀ j → CZ ^ j • X ↑ ≈ X ↑ • (Z ^ j • CZ ^ j)
  lemma-CZᵏ-X↑ ₀ = begin
    ε • X ↑        ≈⟨ left-unit ⟩
    X ↑            ≈⟨ sym right-unit ⟩
    X ↑ • ε        ≈⟨ cright sym left-unit ⟩
    X ↑ • (ε • ε) ∎
  lemma-CZᵏ-X↑ ₁ = lemma-rel-X↑-CZ
  lemma-CZᵏ-X↑ (₂₊ j) = begin
    (CZ • CZ ^ ₁₊ j) • X ↑
      ≈⟨ assoc ⟩
    CZ • (CZ ^ ₁₊ j • X ↑)
      ≈⟨ cright lemma-CZᵏ-X↑ (₁₊ j) ⟩
    CZ • (X ↑ • (Z ^ ₁₊ j • CZ ^ ₁₊ j))
      ≈⟨ sym assoc ⟩
    (CZ • X ↑) • (Z ^ ₁₊ j • CZ ^ ₁₊ j)
      ≈⟨ cleft lemma-CZᵏ-X↑ 1 ⟩
    (X ↑ • (Z • CZ)) • (Z ^ ₁₊ j • CZ ^ ₁₊ j)
      ≈⟨ assoc ⟩
    X ↑ • ((Z • CZ) • (Z ^ ₁₊ j • CZ ^ ₁₊ j))
      ≈⟨ cright assoc ⟩
    X ↑ • (Z • (CZ • (Z ^ ₁₊ j • CZ ^ ₁₊ j)))
      ≈⟨ cright cright sym assoc ⟩
    X ↑ • (Z • ((CZ • Z ^ ₁₊ j) • CZ ^ ₁₊ j))
      ≈⟨ cright cright cleft comm⇒pow-comm 1 (₁₊ j) lemma-comm-CZ-Z ⟩
    X ↑ • (Z • ((Z ^ ₁₊ j • CZ) • CZ ^ ₁₊ j))
      ≈⟨ cright cright assoc ⟩
    X ↑ • (Z • (Z ^ ₁₊ j • (CZ • CZ ^ ₁₊ j)))
      ≈⟨ cright sym assoc ⟩
    X ↑ • ((Z • Z ^ ₁₊ j) • (CZ • CZ ^ ₁₊ j)) ∎

  private
    Zᵖ : Z ^ p-1 • Z ≈ ε
    Zᵖ = begin
      Z ^ p-1 • Z        ≈⟨ sym (^-+ Z p-1 1) ⟩
      Z ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (Z ^_) (NP.+-comm p-1 1) ⟩
      Z ^ p              ≈⟨ One-Wire.lemma-order-Z (₁₊ n) ⟩
      ε ∎

  -- The same crossing read the other way at the exponent p-1: the p-1
  -- Z's the crossings emit complete to a full p-th power against the one
  -- carried in, so exactly one Z is left over.
  lemma-X↑-CZᵖ⁻¹ : X ↑ • CZ ^ p-1 ≈ CZ ^ p-1 • (X ↑ • Z)
  lemma-X↑-CZᵖ⁻¹ = sym (begin
    CZ ^ p-1 • (X ↑ • Z)
      ≈⟨ sym assoc ⟩
    (CZ ^ p-1 • X ↑) • Z
      ≈⟨ cleft lemma-CZᵏ-X↑ p-1 ⟩
    (X ↑ • (Z ^ p-1 • CZ ^ p-1)) • Z
      ≈⟨ assoc ⟩
    X ↑ • ((Z ^ p-1 • CZ ^ p-1) • Z)
      ≈⟨ cright assoc ⟩
    X ↑ • (Z ^ p-1 • (CZ ^ p-1 • Z))
      ≈⟨ cright cright comm⇒pow-comm p-1 1 lemma-comm-CZ-Z ⟩
    X ↑ • (Z ^ p-1 • (Z • CZ ^ p-1))
      ≈⟨ cright sym assoc ⟩
    X ↑ • ((Z ^ p-1 • Z) • CZ ^ p-1)
      ≈⟨ cright cleft Zᵖ ⟩
    X ↑ • (ε • CZ ^ p-1)
      ≈⟨ cright left-unit ⟩
    X ↑ • CZ ^ p-1 ∎)

  ------------------------------------------------------------------------
  -- The Pauli-versus-XC rule
  --
  -- XC = H ↑ ^ 3 • CZ • H ↑ has its control on wire 0 and its target on
  -- wire 1, so it conjugates a Z on wire 1 to Z ↑ • Z.  Every crossing is
  -- now available: lemma-Z-conj and lemma-X-H³ take the Pauli across the
  -- two H ↑ factors, and lemma-X↑-CZᵖ⁻¹ takes it across the CZ between
  -- them.  Nothing here has a negative exponent — the H-crossings were
  -- chosen in the directions that emit positive powers.
  --
  -- This is exactly the gap between the S-spelling of the commutator,
  -- which blake-c12 gives, and the R-spelling that c10 is stated in:
  -- R = S • Z ^ ½, so the two differ by this Pauli and by nothing else.

  private
    H↑³H↑ : (H ↑) ^ 3 • H ↑ ≈ ε
    H↑³H↑ = begin
      (H ↑) ^ 3 • H ↑  ≈⟨ sym (^-+ (H ↑) 3 1) ⟩
      (H ↑) ^ 4        ≈⟨ lemma-order-H↑ ⟩
      ε ∎

    H↑⁶ : (H ↑) ^ 3 • (H ↑) ^ 3 ≈ M₋₁ ↑
    H↑⁶ = begin
      (H ↑) ^ 3 • (H ↑) ^ 3  ≈⟨ sym (^-+ (H ↑) 3 3) ⟩
      (H ↑) ^ 6              ≈⟨ ^-+ (H ↑) 4 2 ⟩
      (H ↑) ^ 4 • (H ↑) ^ 2  ≈⟨ cleft lemma-order-H↑ ⟩
      ε • (H ↑) ^ 2          ≈⟨ left-unit ⟩
      (H ↑) ^ 2              ≈⟨ lemma-cong↑ _ _ (PB₁.axiom order-H) ⟩
      M₋₁ ↑ ∎

    M₋₁↑H↑ : M₋₁ ↑ • H ↑ ≈ (H ↑) ^ 3
    M₋₁↑H↑ = begin
      M₋₁ ↑ • H ↑      ≈⟨ cleft sym (lemma-cong↑ _ _ (PB₁.axiom order-H)) ⟩
      (H ↑) ^ 2 • H ↑  ≈⟨ sym (^-+ (H ↑) 2 1) ⟩
      (H ↑) ^ 3 ∎

    lemma-M₋₁↑-CZ' : M₋₁ ↑ • CZ ≈ CZ ^ p-1 • M₋₁ ↑
    lemma-M₋₁↑-CZ' = begin
      M₋₁ ↑ • CZ       ≈⟨ lemma-M₋₁↑-CZ ⟩
      CZ ^ e₁ • M₋₁ ↑  ≡⟨ Eq.cong (λ m → CZ ^ m • M₋₁ ↑) lemma-toℕ-1ₚ ⟩
      CZ ^ p-1 • M₋₁ ↑ ∎

  -- XC read from the other side.  The two spellings of the conjugation
  -- differ by an H ↑ ^ 2, which is the multiplier by −1 and inverts the
  -- CZ it passes.
  lemma-XC-flip : H ↑ • (CZ ^ p-1 • (H ↑) ^ 3) ≈ XC
  lemma-XC-flip = •-cancelˡ {g = (H ↑) ^ 3} (begin
    (H ↑) ^ 3 • (H ↑ • (CZ ^ p-1 • (H ↑) ^ 3))
      ≈⟨ sym assoc ⟩
    ((H ↑) ^ 3 • H ↑) • (CZ ^ p-1 • (H ↑) ^ 3)
      ≈⟨ cleft H↑³H↑ ⟩
    ε • (CZ ^ p-1 • (H ↑) ^ 3)
      ≈⟨ left-unit ⟩
    CZ ^ p-1 • (H ↑) ^ 3
      ≈⟨ cright sym M₋₁↑H↑ ⟩
    CZ ^ p-1 • (M₋₁ ↑ • H ↑)
      ≈⟨ sym assoc ⟩
    (CZ ^ p-1 • M₋₁ ↑) • H ↑
      ≈⟨ cleft sym lemma-M₋₁↑-CZ' ⟩
    (M₋₁ ↑ • CZ) • H ↑
      ≈⟨ cleft cleft sym H↑⁶ ⟩
    (((H ↑) ^ 3 • (H ↑) ^ 3) • CZ) • H ↑
      ≈⟨ cleft assoc ⟩
    ((H ↑) ^ 3 • ((H ↑) ^ 3 • CZ)) • H ↑
      ≈⟨ assoc ⟩
    (H ↑) ^ 3 • (((H ↑) ^ 3 • CZ) • H ↑)
      ≈⟨ cright assoc ⟩
    (H ↑) ^ 3 • ((H ↑) ^ 3 • (CZ • H ↑)) ∎)

  lemma-conj-XC-Z↑ : Z ↑ • XC ≈ XC • (Z ↑ • Z)
  lemma-conj-XC-Z↑ = begin
    Z ↑ • XC
      ≈⟨ cleft (lemma-cong↑ _ _ (One-Wire-Group.lemma-Z-conj n)) ⟩
    (H ↑ • (X ↑ • (H ↑) ^ 3)) • ((H ↑) ^ 3 • (CZ • H ↑))
      ≈⟨ assoc ⟩
    H ↑ • ((X ↑ • (H ↑) ^ 3) • ((H ↑) ^ 3 • (CZ • H ↑)))
      ≈⟨ cright assoc ⟩
    H ↑ • (X ↑ • ((H ↑) ^ 3 • ((H ↑) ^ 3 • (CZ • H ↑))))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (X ↑ • (((H ↑) ^ 3 • (H ↑) ^ 3) • (CZ • H ↑)))
      ≈⟨ cright cright cleft H↑⁶ ⟩
    H ↑ • (X ↑ • (M₋₁ ↑ • (CZ • H ↑)))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (X ↑ • ((M₋₁ ↑ • CZ) • H ↑))
      ≈⟨ cright cright cleft lemma-M₋₁↑-CZ' ⟩
    H ↑ • (X ↑ • ((CZ ^ p-1 • M₋₁ ↑) • H ↑))
      ≈⟨ cright cright assoc ⟩
    H ↑ • (X ↑ • (CZ ^ p-1 • (M₋₁ ↑ • H ↑)))
      ≈⟨ cright cright cright M₋₁↑H↑ ⟩
    H ↑ • (X ↑ • (CZ ^ p-1 • (H ↑) ^ 3))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((X ↑ • CZ ^ p-1) • (H ↑) ^ 3)
      ≈⟨ cright cleft lemma-X↑-CZᵖ⁻¹ ⟩
    H ↑ • ((CZ ^ p-1 • (X ↑ • Z)) • (H ↑) ^ 3)
      ≈⟨ cright assoc ⟩
    H ↑ • (CZ ^ p-1 • ((X ↑ • Z) • (H ↑) ^ 3))
      ≈⟨ cright cright assoc ⟩
    H ↑ • (CZ ^ p-1 • (X ↑ • (Z • (H ↑) ^ 3)))
      ≈⟨ cright cright cright lemma-comm-Z-w↑ (H ^ 3) ⟩
    H ↑ • (CZ ^ p-1 • (X ↑ • ((H ↑) ^ 3 • Z)))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (CZ ^ p-1 • ((X ↑ • (H ↑) ^ 3) • Z))
      ≈⟨ cright cright cleft (lemma-cong↑ _ _ (One-Wire-Group.lemma-X-H³ n)) ⟩
    H ↑ • (CZ ^ p-1 • (((H ↑) ^ 3 • Z ↑) • Z))
      ≈⟨ cright cright assoc ⟩
    H ↑ • (CZ ^ p-1 • ((H ↑) ^ 3 • (Z ↑ • Z)))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((CZ ^ p-1 • (H ↑) ^ 3) • (Z ↑ • Z))
      ≈⟨ sym assoc ⟩
    (H ↑ • (CZ ^ p-1 • (H ↑) ^ 3)) • (Z ↑ • Z)
      ≈⟨ cleft lemma-XC-flip ⟩
    XC • (Z ↑ • Z) ∎

  lemma-conj-XC-Z↑ᵏ : ∀ k → (Z ↑) ^ k • XC ≈ XC • ((Z ↑) ^ k • Z ^ k)
  lemma-conj-XC-Z↑ᵏ k = begin
    (Z ↑) ^ k • XC
      ≈⟨ lemma-Inductionˡ lemma-conj-XC-Z↑ k ⟩
    XC • (Z ↑ • Z) ^ k
      ≈⟨ cright ^-• (Z ↑) Z k (sym (lemma-comm-Z-w↑ Z)) ⟩
    XC • ((Z ↑) ^ k • Z ^ k) ∎

  ------------------------------------------------------------------------
  -- The commutator of XC with the upper R
  --
  -- lemma-comm-XC-S↑ is stated with the p-1 power in front, because
  -- blake-c12 is; flipping it needs XC ^ p ≈ ε, which holds because XC is
  -- a CZ conjugated by H ↑.  Substituting R = S • Z ^ ½ then splits the
  -- conjugation into the S part, which is that commutator, and the Pauli
  -- part, which is lemma-conj-XC-Z↑ᵏ.

  private
    h : ℕ
    h = toℕ 1/2

    lemma-XCᵏ : ∀ k → XC ^ k ≈ (H ↑) ^ 3 • (CZ ^ k • H ↑)
    lemma-XCᵏ ₀ = begin
      ε                      ≈⟨ sym H↑³H↑ ⟩
      (H ↑) ^ 3 • H ↑        ≈⟨ cright sym left-unit ⟩
      (H ↑) ^ 3 • (ε • H ↑) ∎
    lemma-XCᵏ ₁ = refl
    lemma-XCᵏ (₂₊ k) = begin
      XC • XC ^ ₁₊ k
        ≈⟨ cright lemma-XCᵏ (₁₊ k) ⟩
      ((H ↑) ^ 3 • (CZ • H ↑)) • ((H ↑) ^ 3 • (CZ ^ ₁₊ k • H ↑))
        ≈⟨ assoc ⟩
      (H ↑) ^ 3 • ((CZ • H ↑) • ((H ↑) ^ 3 • (CZ ^ ₁₊ k • H ↑)))
        ≈⟨ cright assoc ⟩
      (H ↑) ^ 3 • (CZ • (H ↑ • ((H ↑) ^ 3 • (CZ ^ ₁₊ k • H ↑))))
        ≈⟨ cright cright sym assoc ⟩
      (H ↑) ^ 3 • (CZ • ((H ↑ • (H ↑) ^ 3) • (CZ ^ ₁₊ k • H ↑)))
        ≈⟨ cright cright cleft lemma-order-H↑ ⟩
      (H ↑) ^ 3 • (CZ • (ε • (CZ ^ ₁₊ k • H ↑)))
        ≈⟨ cright cright left-unit ⟩
      (H ↑) ^ 3 • (CZ • (CZ ^ ₁₊ k • H ↑))
        ≈⟨ cright sym assoc ⟩
      (H ↑) ^ 3 • ((CZ • CZ ^ ₁₊ k) • H ↑) ∎

    lemma-order-XC : XC ^ p ≈ ε
    lemma-order-XC = begin
      XC ^ p                      ≈⟨ lemma-XCᵏ p ⟩
      (H ↑) ^ 3 • (CZ ^ p • H ↑)  ≈⟨ cright cleft axiom order-CZ ⟩
      (H ↑) ^ 3 • (ε • H ↑)       ≈⟨ cright left-unit ⟩
      (H ↑) ^ 3 • H ↑             ≈⟨ H↑³H↑ ⟩
      ε ∎

    XCᵖ⁻¹XC : XC ^ p-1 • XC ≈ ε
    XCᵖ⁻¹XC = begin
      XC ^ p-1 • XC       ≈⟨ sym (^-+ XC p-1 1) ⟩
      XC ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (XC ^_) (NP.+-comm p-1 1) ⟩
      XC ^ p              ≈⟨ lemma-order-XC ⟩
      ε ∎

    S-Z↑ʰ : S • (Z ↑) ^ h ≈ (Z ↑) ^ h • S
    S-Z↑ʰ = begin
      S • (Z ↑) ^ h  ≡⟨ Eq.cong (S •_) (Eq.sym (lemma-↑^ h Z)) ⟩
      S • (Z ^ h) ↑  ≈⟨ lemma-comm-S-w↑ (Z ^ h) ⟩
      (Z ^ h) ↑ • S  ≡⟨ Eq.cong (_• S) (lemma-↑^ h Z) ⟩
      (Z ↑) ^ h • S ∎

  lemma-comm-XC-S↑' : S ↑ • XC ≈ XC • (S ↑ • (S • CZ))
  lemma-comm-XC-S↑' = •-cancelˡ {g = XC ^ p-1} (begin
    XC ^ p-1 • (S ↑ • XC)
      ≈⟨ lemma-comm-XC-S↑ ⟩
    S ↑ • (S • CZ)
      ≈⟨ sym left-unit ⟩
    ε • (S ↑ • (S • CZ))
      ≈⟨ cleft sym XCᵖ⁻¹XC ⟩
    (XC ^ p-1 • XC) • (S ↑ • (S • CZ))
      ≈⟨ assoc ⟩
    XC ^ p-1 • (XC • (S ↑ • (S • CZ))) ∎)

  lemma-comm-XC-R↑ : R ↑ • XC ≈ XC • (R ↑ • (R • CZ))
  lemma-comm-XC-R↑ = begin
    R ↑ • XC
      ≡⟨ Eq.cong (λ w → (S ↑ • w) • XC) (lemma-↑^ h Z) ⟩
    (S ↑ • (Z ↑) ^ h) • XC
      ≈⟨ assoc ⟩
    S ↑ • ((Z ↑) ^ h • XC)
      ≈⟨ cright lemma-conj-XC-Z↑ᵏ h ⟩
    S ↑ • (XC • ((Z ↑) ^ h • Z ^ h))
      ≈⟨ sym assoc ⟩
    (S ↑ • XC) • ((Z ↑) ^ h • Z ^ h)
      ≈⟨ cleft lemma-comm-XC-S↑' ⟩
    (XC • (S ↑ • (S • CZ))) • ((Z ↑) ^ h • Z ^ h)
      ≈⟨ assoc ⟩
    XC • ((S ↑ • (S • CZ)) • ((Z ↑) ^ h • Z ^ h))
      ≈⟨ cright rearrange ⟩
    XC • ((S ↑ • (Z ↑) ^ h) • ((S • Z ^ h) • CZ))
      ≡⟨ Eq.sym (Eq.cong (λ w → XC • ((S ↑ • w) • ((S • Z ^ h) • CZ))) (lemma-↑^ h Z)) ⟩
    XC • (R ↑ • (R • CZ)) ∎
    where
    rearrange : (S ↑ • (S • CZ)) • ((Z ↑) ^ h • Z ^ h)
              ≈ (S ↑ • (Z ↑) ^ h) • ((S • Z ^ h) • CZ)
    rearrange = begin
      (S ↑ • (S • CZ)) • ((Z ↑) ^ h • Z ^ h)
        ≈⟨ assoc ⟩
      S ↑ • ((S • CZ) • ((Z ↑) ^ h • Z ^ h))
        ≈⟨ cright assoc ⟩
      S ↑ • (S • (CZ • ((Z ↑) ^ h • Z ^ h)))
        ≈⟨ cright cright sym assoc ⟩
      S ↑ • (S • ((CZ • (Z ↑) ^ h) • Z ^ h))
        ≈⟨ cright cright cleft comm⇒pow-comm 1 h lemma-comm-CZ-Z↑ ⟩
      S ↑ • (S • (((Z ↑) ^ h • CZ) • Z ^ h))
        ≈⟨ cright cright assoc ⟩
      S ↑ • (S • ((Z ↑) ^ h • (CZ • Z ^ h)))
        ≈⟨ cright cright cright comm⇒pow-comm 1 h lemma-comm-CZ-Z ⟩
      S ↑ • (S • ((Z ↑) ^ h • (Z ^ h • CZ)))
        ≈⟨ cright sym assoc ⟩
      S ↑ • ((S • (Z ↑) ^ h) • (Z ^ h • CZ))
        ≈⟨ cright cleft S-Z↑ʰ ⟩
      S ↑ • (((Z ↑) ^ h • S) • (Z ^ h • CZ))
        ≈⟨ cright assoc ⟩
      S ↑ • ((Z ↑) ^ h • (S • (Z ^ h • CZ)))
        ≈⟨ cright cright sym assoc ⟩
      S ↑ • ((Z ↑) ^ h • ((S • Z ^ h) • CZ))
        ≈⟨ sym assoc ⟩
      (S ↑ • (Z ↑) ^ h) • ((S • Z ^ h) • CZ) ∎

  ------------------------------------------------------------------------
  -- Selinger's c10
  --
  -- Both sides shed a leading H ↑ — the left by lemma-CZ-H↑, the right
  -- because R ↑ ⁻¹ • H ↑ • R ↑ ⁻¹ is H ↑ • R ↑ • H ↑ ⁻¹ by the Euler
  -- decomposition of the multiplier by −1 (lemma-M₋₁-R).  What is left is
  --
  --     XC • CZ ≈ R ↑ • XC • R ↑ ⁻¹ • R ↓ ⁻¹,
  --
  -- i.e. the conjugation rule lemma-comm-XC-R↑, with the CZ it emits
  -- surviving and the two R's cancelling the two inverse powers.

  private
    A₋ : Word (Gen (₂₊ n))
    A₋ = (R ↑) ^ p-1

    lemma-comm-CZ-R : CZ • R ≈ R • CZ
    lemma-comm-CZ-R = begin
      CZ • (S • Z ^ h)  ≈⟨ sym assoc ⟩
      (CZ • S) • Z ^ h  ≈⟨ cleft lemma-comm-CZ-S ⟩
      (S • CZ) • Z ^ h  ≈⟨ assoc ⟩
      S • (CZ • Z ^ h)  ≈⟨ cright comm⇒pow-comm 1 h lemma-comm-CZ-Z ⟩
      S • (Z ^ h • CZ)  ≈⟨ sym assoc ⟩
      (S • Z ^ h) • CZ ∎

    lemma-comm-CZ-R↑ : CZ • R ↑ ≈ R ↑ • CZ
    lemma-comm-CZ-R↑ = begin
      CZ • R ↑
        ≡⟨ Eq.cong (λ w → CZ • (S ↑ • w)) (lemma-↑^ h Z) ⟩
      CZ • (S ↑ • (Z ↑) ^ h)
        ≈⟨ sym assoc ⟩
      (CZ • S ↑) • (Z ↑) ^ h
        ≈⟨ cleft axiom comm-CZ-S↑ ⟩
      (S ↑ • CZ) • (Z ↑) ^ h
        ≈⟨ assoc ⟩
      S ↑ • (CZ • (Z ↑) ^ h)
        ≈⟨ cright comm⇒pow-comm 1 h lemma-comm-CZ-Z↑ ⟩
      S ↑ • ((Z ↑) ^ h • CZ)
        ≈⟨ sym assoc ⟩
      (S ↑ • (Z ↑) ^ h) • CZ
        ≡⟨ Eq.sym (Eq.cong (λ w → (S ↑ • w) • CZ) (lemma-↑^ h Z)) ⟩
      R ↑ • CZ ∎

    lemma-comm-R-w↑ : ∀ (w : Word (Gen (₁₊ n))) → R • w ↑ ≈ w ↑ • R
    lemma-comm-R-w↑ w = begin
      (S • Z ^ h) • w ↑  ≈⟨ assoc ⟩
      S • (Z ^ h • w ↑)  ≈⟨ cright lemma-Inductionˡ (lemma-comm-Z-w↑ w) h ⟩
      S • (w ↑ • Z ^ h)  ≈⟨ sym assoc ⟩
      (S • w ↑) • Z ^ h  ≈⟨ cleft lemma-comm-S-w↑ w ⟩
      (w ↑ • S) • Z ^ h  ≈⟨ assoc ⟩
      w ↑ • (S • Z ^ h) ∎

    R-A₋ : R • A₋ ≈ A₋ • R
    R-A₋ = begin
      R • A₋           ≡⟨ Eq.cong (R •_) (Eq.sym (lemma-↑^ p-1 R)) ⟩
      R • (R ^ p-1) ↑  ≈⟨ lemma-comm-R-w↑ (R ^ p-1) ⟩
      (R ^ p-1) ↑ • R  ≡⟨ Eq.cong (_• R) (lemma-↑^ p-1 R) ⟩
      A₋ • R ∎

    R↑-A₋ : R ↑ • A₋ ≈ ε
    R↑-A₋ = begin
      R ↑ • (R ↑) ^ p-1      ≈⟨ sym (^-+ (R ↑) 1 p-1) ⟩
      (R ↑) ^ (1 Nat.+ p-1)  ≡⟨ Eq.sym (lemma-↑^ p R) ⟩
      (R ^ p) ↑              ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-R n) ⟩
      ε ∎

    R-Rᵖ⁻¹ : R • R ^ p-1 ≈ ε
    R-Rᵖ⁻¹ = begin
      R • R ^ p-1        ≈⟨ sym (^-+ R 1 p-1) ⟩
      R ^ (1 Nat.+ p-1)  ≈⟨ One-Wire.lemma-order-R (₁₊ n) ⟩
      ε ∎

    euler↑ : A₋ • (H ↑ • (A₋ • (H ↑ • (A₋ • H ↑)))) ≈ (H ↑) ^ 2
    euler↑ = begin
      A₋ • (H ↑ • (A₋ • (H ↑ • (A₋ • H ↑))))
        ≡⟨ Eq.sym (Eq.cong (λ w → w • (H ↑ • (w • (H ↑ • (w • H ↑)))))
                           (lemma-↑^ p-1 R)) ⟩
      (R ^ p-1) ↑ • (H ↑ • ((R ^ p-1) ↑ • (H ↑ • ((R ^ p-1) ↑ • H ↑))))
        ≈⟨ lemma-cong↑ _ _ (One-Wire-Group.lemma-M₋₁-R n) ⟩
      (H ↑) ^ 2 ∎

    -- The Euler decomposition, rearranged: conjugating H ↑ by R ↑ ⁻¹ the
    -- one way is conjugating R ↑ by H ↑ the other.
    lemma-ABA : A₋ • (H ↑ • A₋) ≈ H ↑ • (R ↑ • (H ↑) ^ 3)
    lemma-ABA = •-cancelʳ {h = H ↑ • (A₋ • H ↑)} (trans left-half (sym right-half))
      where
      -- Both sides, multiplied by H ↑ • (A₋ • H ↑), come to H ↑ ^ 2:
      -- the left by the Euler decomposition itself, the right because
      -- the two H ↑ powers and the two R ↑ powers each cancel.
      left-half : (A₋ • (H ↑ • A₋)) • (H ↑ • (A₋ • H ↑)) ≈ (H ↑) ^ 2
      left-half = begin
        (A₋ • (H ↑ • A₋)) • (H ↑ • (A₋ • H ↑))
          ≈⟨ assoc ⟩
        A₋ • ((H ↑ • A₋) • (H ↑ • (A₋ • H ↑)))
          ≈⟨ cright assoc ⟩
        A₋ • (H ↑ • (A₋ • (H ↑ • (A₋ • H ↑))))
          ≈⟨ euler↑ ⟩
        (H ↑) ^ 2 ∎

      right-half : (H ↑ • (R ↑ • (H ↑) ^ 3)) • (H ↑ • (A₋ • H ↑)) ≈ (H ↑) ^ 2
      right-half = begin
        (H ↑ • (R ↑ • (H ↑) ^ 3)) • (H ↑ • (A₋ • H ↑))
          ≈⟨ assoc ⟩
        H ↑ • ((R ↑ • (H ↑) ^ 3) • (H ↑ • (A₋ • H ↑)))
          ≈⟨ cright assoc ⟩
        H ↑ • (R ↑ • ((H ↑) ^ 3 • (H ↑ • (A₋ • H ↑))))
          ≈⟨ cright cright sym assoc ⟩
        H ↑ • (R ↑ • (((H ↑) ^ 3 • H ↑) • (A₋ • H ↑)))
          ≈⟨ cright cright cleft H↑³H↑ ⟩
        H ↑ • (R ↑ • (ε • (A₋ • H ↑)))
          ≈⟨ cright cright left-unit ⟩
        H ↑ • (R ↑ • (A₋ • H ↑))
          ≈⟨ cright sym assoc ⟩
        H ↑ • ((R ↑ • A₋) • H ↑)
          ≈⟨ cright cleft R↑-A₋ ⟩
        H ↑ • (ε • H ↑)
          ≈⟨ cright left-unit ⟩
        H ↑ • H ↑ ∎

  lemma-selinger-c10 :
    CZ • H ↑ • CZ ≈ R ↑ ^ p-1 • H ↑ • R ↑ ^ p-1 • CZ • H ↑ • R ↑ ^ p-1 • R ↓ ^ p-1
  lemma-selinger-c10 = sym (begin
    A₋ • (H ↑ • (A₋ • (CZ • (H ↑ • (A₋ • R ^ p-1)))))
      ≈⟨ cright sym assoc ⟩
    A₋ • ((H ↑ • A₋) • (CZ • (H ↑ • (A₋ • R ^ p-1))))
      ≈⟨ sym assoc ⟩
    (A₋ • (H ↑ • A₋)) • (CZ • (H ↑ • (A₋ • R ^ p-1)))
      ≈⟨ cleft lemma-ABA ⟩
    (H ↑ • (R ↑ • (H ↑) ^ 3)) • (CZ • (H ↑ • (A₋ • R ^ p-1)))
      ≈⟨ assoc ⟩
    H ↑ • ((R ↑ • (H ↑) ^ 3) • (CZ • (H ↑ • (A₋ • R ^ p-1))))
      ≈⟨ cright assoc ⟩
    H ↑ • (R ↑ • ((H ↑) ^ 3 • (CZ • (H ↑ • (A₋ • R ^ p-1)))))
      ≈⟨ cright cright cright sym assoc ⟩
    H ↑ • (R ↑ • ((H ↑) ^ 3 • ((CZ • H ↑) • (A₋ • R ^ p-1))))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (R ↑ • (((H ↑) ^ 3 • (CZ • H ↑)) • (A₋ • R ^ p-1)))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((R ↑ • XC) • (A₋ • R ^ p-1))
      ≈⟨ cright cleft lemma-comm-XC-R↑ ⟩
    H ↑ • ((XC • (R ↑ • (R • CZ))) • (A₋ • R ^ p-1))
      ≈⟨ cright assoc ⟩
    H ↑ • (XC • ((R ↑ • (R • CZ)) • (A₋ • R ^ p-1)))
      ≈⟨ cright cright collapse ⟩
    H ↑ • (XC • CZ)
      ≈⟨ sym assoc ⟩
    (H ↑ • XC) • CZ
      ≈⟨ cleft sym lemma-CZ-H↑ ⟩
    (CZ • H ↑) • CZ
      ≈⟨ assoc ⟩
    CZ • (H ↑ • CZ) ∎)
    where
    collapse : (R ↑ • (R • CZ)) • (A₋ • R ^ p-1) ≈ CZ
    collapse = begin
      (R ↑ • (R • CZ)) • (A₋ • R ^ p-1)
        ≈⟨ assoc ⟩
      R ↑ • ((R • CZ) • (A₋ • R ^ p-1))
        ≈⟨ cright assoc ⟩
      R ↑ • (R • (CZ • (A₋ • R ^ p-1)))
        ≈⟨ cright cright sym assoc ⟩
      R ↑ • (R • ((CZ • A₋) • R ^ p-1))
        ≈⟨ cright cright cleft comm⇒pow-comm 1 p-1 lemma-comm-CZ-R↑ ⟩
      R ↑ • (R • ((A₋ • CZ) • R ^ p-1))
        ≈⟨ cright cright assoc ⟩
      R ↑ • (R • (A₋ • (CZ • R ^ p-1)))
        ≈⟨ cright cright cright comm⇒pow-comm 1 p-1 lemma-comm-CZ-R ⟩
      R ↑ • (R • (A₋ • (R ^ p-1 • CZ)))
        ≈⟨ cright sym assoc ⟩
      R ↑ • ((R • A₋) • (R ^ p-1 • CZ))
        ≈⟨ cright cleft R-A₋ ⟩
      R ↑ • ((A₋ • R) • (R ^ p-1 • CZ))
        ≈⟨ cright assoc ⟩
      R ↑ • (A₋ • (R • (R ^ p-1 • CZ)))
        ≈⟨ sym assoc ⟩
      (R ↑ • A₋) • (R • (R ^ p-1 • CZ))
        ≈⟨ cleft R↑-A₋ ⟩
      ε • (R • (R ^ p-1 • CZ))
        ≈⟨ left-unit ⟩
      R • (R ^ p-1 • CZ)
        ≈⟨ sym assoc ⟩
      (R • R ^ p-1) • CZ
        ≈⟨ cleft R-Rᵖ⁻¹ ⟩
      ε • CZ
        ≈⟨ left-unit ⟩
      CZ ∎

  ------------------------------------------------------------------------
  -- Selinger's c11, by conjugating c10 with the swap
  --
  -- Ex exchanges the two wires and fixes CZ, so it carries each factor of
  -- c10 to the corresponding factor of c11.  Nothing is reproved here:
  -- the statement is transported, factor by factor, by lemma-Ex-•.
  -- (transport-Ex itself is declared much earlier, since rel-X↑-CZ is
  -- transported the same way and is needed long before this.)

  lemma-selinger-c11 :
    CZ • H ↓ • CZ ≈ R ↓ ^ p-1 • H ↓ • R ↓ ^ p-1 • CZ • H ↓ • R ↓ ^ p-1 • R ↑ ^ p-1
  lemma-selinger-c11 = transport-Ex lhs rhs lemma-selinger-c10
    where
    lhs : Ex • (CZ • (H ↑ • CZ)) ≈ (CZ • (H • CZ)) • Ex
    lhs = lemma-Ex-• lemma-Ex-CZ (lemma-Ex-• lemma-Ex-H↑ lemma-Ex-CZ)

    rhs : Ex • (A₋ • (H ↑ • (A₋ • (CZ • (H ↑ • (A₋ • R ^ p-1))))))
        ≈ (R ^ p-1 • (H • (R ^ p-1 • (CZ • (H • (R ^ p-1 • A₋)))))) • Ex
    rhs = lemma-Ex-• (lemma-Ex-pow lemma-Ex-R↑ p-1)
            (lemma-Ex-• lemma-Ex-H↑
              (lemma-Ex-• (lemma-Ex-pow lemma-Ex-R↑ p-1)
                (lemma-Ex-• lemma-Ex-CZ
                  (lemma-Ex-• lemma-Ex-H↑
                    (lemma-Ex-• (lemma-Ex-pow lemma-Ex-R↑ p-1)
                                (lemma-Ex-pow lemma-Ex-R p-1))))))

  lemma-⊤⊥-cube3 : (⊤⊥ • ⊤⊥) • ⊤⊥ ≈ ε
  lemma-⊤⊥-cube3 = begin
    (⊤⊥ • ⊤⊥) • ⊤⊥
      ≈⟨ cong (cong lemma-⊤⊥-simple lemma-⊤⊥-simple) lemma-⊤⊥-simple ⟩
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)
      ≈⟨ lemma-half-swap-cube ⟩
    ε ∎


