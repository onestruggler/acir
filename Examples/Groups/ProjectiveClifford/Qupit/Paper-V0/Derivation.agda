{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- rel-X↓-CZ derived from the other sixteen axioms
--
-- Paper-V0.Redundancy shows the rule is redundant and reduces it to one
-- equation about CZ • H • CZ ⁻¹, which it cannot close.  This module
-- closes it, by conjugating in the OTHER direction.
--
-- The rule says what CZ costs when it crosses X.  Read it as
--
--     X • CZ ≈ (X • CZ • X ⁻¹) • X
--
-- and push the two-wire gate leftwards through X's six letters, one at a
-- time.  Each letter conjugates whatever two-wire word has accumulated,
-- and the point is that the accumulated word never leaves the set
--
--     { CZ ^ a , CX ^ b , S ↑ }
--
-- because of three facts:
--
--   * H conjugates CZ to CX ⁻¹ and CX to CZ.  Both are immediate from
--     CX = H ³ • CZ • H and H ⁴ ≈ ε — no Pauli-versus-CZ rule needed.
--
--   * S conjugates CX to CX • S ↑ • CZ.  This is blake-c12, which is
--     exactly a statement about S crossing CX, rearranged (blake-A).
--
--   * S ↑ lives on the other wire from every letter of X, so the letters
--     pass it for free.  That is why no rule for H ↑ against CX is ever
--     needed, and it is what makes the whole calculation finite.
--
-- Six crossings later the accumulated word is
--
--     D₀ = S ↑ • CX • CZ • S ↑ • CX ⁻¹
--
-- and the rule is D₀ ≈ Z ↑ ⁻¹ • CZ.  Collapsing D₀ needs blake once more,
-- read the other way round: what S does to CX ⁻¹ rather than to CX.  That
-- is blake-c12 conjugated by the multiplier by −1 on wire 1, which sends
-- CX to CX ⁻¹, CZ to CZ ⁻¹, fixes S, and sends S ↑ to S ↑ • Z ↑ — the last
-- being Z's definition read backwards (Z-split).  The stray Z ↑ that this
-- introduces IS the Z ↑ of the rule.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Derivation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  p-3 p-prime g* g-gen
  using (module One-Wire ; module Paper-GroupLike ; module Ex-Conjugation)

open Clifford-Relations
open Lemmas-Clifford
  using ( lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Hᵏ-w↑
        ; lemma-comm-X-w↑ ; lemma-Induction ; lemma-↑^ )

------------------------------------------------------------------------
-- One wire: what the multiplier by −1 does to a phase gate
--
-- Conjugating S by M₋₁ produces a Z.  This is Z's own definition —
-- Z = H ² • S • H ² • S ⁻¹ — read as a statement about M₋₁ • S • M₋₁,
-- and it is the only place a Pauli enters the whole derivation.  It is
-- proved one wire down so that lemma-cong↑ can lift it to wire 1, which
-- is where the derivation needs it.

module Wire-0 (m : ℕ) where

  open PB ((₁₊ m) QRel,_===_)
  open PP ((₁₊ m) QRel,_===_)
  open SR word-setoid
  open One-Wire m
    using (lemma-M₋₁^2 ; lemma-order-S ; lemma-comm-Z-S)

  private
    S⁻¹S : S ^ p-1 • S ≈ ε
    S⁻¹S = begin
      S ^ p-1 • S        ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p              ≈⟨ lemma-order-S ⟩
      ε ∎

    -- Z is two multipliers and two phase gates.
    Z-split : Z ≈ M₋₁ • (S • (M₋₁ • S ^ p-1))
    Z-split = begin
      H • (H • (S • (H • (H • S ^ p-1))))
        ≈⟨ sym assoc ⟩
      (H • H) • (S • (H • (H • S ^ p-1)))
        ≈⟨ cright cright sym assoc ⟩
      (H • H) • (S • ((H • H) • S ^ p-1))
        ≈⟨ cong (axiom order-H) (cright cleft axiom order-H) ⟩
      M₋₁ • (S • (M₋₁ • S ^ p-1)) ∎

    -- …so the S ⁻¹ cancels and M₋₁ • S • M₋₁ is Z • S.
    lemma-ZS : M₋₁ • (S • M₋₁) ≈ Z • S
    lemma-ZS = sym (begin
      Z • S
        ≈⟨ cleft Z-split ⟩
      (M₋₁ • (S • (M₋₁ • S ^ p-1))) • S
        ≈⟨ assoc ⟩
      M₋₁ • ((S • (M₋₁ • S ^ p-1)) • S)
        ≈⟨ cright assoc ⟩
      M₋₁ • (S • ((M₋₁ • S ^ p-1) • S))
        ≈⟨ cright cright assoc ⟩
      M₋₁ • (S • (M₋₁ • (S ^ p-1 • S)))
        ≈⟨ cright cright cright S⁻¹S ⟩
      M₋₁ • (S • (M₋₁ • ε))
        ≈⟨ cright cright right-unit ⟩
      M₋₁ • (S • M₋₁) ∎)

  -- The multiplier by −1 conjugates S into S • Z.
  lemma-M₋₁-S : M₋₁ • S ≈ (S • Z) • M₋₁
  lemma-M₋₁-S = begin
    M₋₁ • S
      ≈⟨ sym right-unit ⟩
    (M₋₁ • S) • ε
      ≈⟨ cright sym lemma-M₋₁^2 ⟩
    (M₋₁ • S) • (M₋₁ • M₋₁)
      ≈⟨ sym assoc ⟩
    ((M₋₁ • S) • M₋₁) • M₋₁
      ≈⟨ cleft assoc ⟩
    (M₋₁ • (S • M₋₁)) • M₋₁
      ≈⟨ cleft lemma-ZS ⟩
    (Z • S) • M₋₁
      ≈⟨ cleft lemma-comm-Z-S ⟩
    (S • Z) • M₋₁ ∎

------------------------------------------------------------------------
-- Two wires: the derivation

module Derivation (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelˡ ; •-cancelʳ)
  open Ex-Conjugation n
    using (lemma-comm-CZ-S ; lemma-comm-CZ-Z↑ ; lemma-CZ-M₋₁
          ; lemma-M₋₁↑-CZ ; e₁)

  private
    module CL = One-Wire (₁₊ n)
    module W0 = Wire-0 n

  ----------------------------------------------------------------------
  -- Two combinators
  --
  -- Everything below is of the form "a crosses u, leaving u′ behind".
  -- crossW composes such facts in the thing being crossed, slide in the
  -- thing doing the crossing; between them they build the whole chain
  -- with no associativity bookkeeping at the call sites.

  crossW : ∀ {a u u' v v'} → a • u ≈ u' • a → a • v ≈ v' • a
         → a • (u • v) ≈ (u' • v') • a
  crossW {a} {u} {u'} {v} {v'} eu ev = begin
    a • (u • v)    ≈⟨ sym assoc ⟩
    (a • u) • v    ≈⟨ cleft eu ⟩
    (u' • a) • v   ≈⟨ assoc ⟩
    u' • (a • v)   ≈⟨ cright ev ⟩
    u' • (v' • a)  ≈⟨ sym assoc ⟩
    (u' • v') • a ∎

  slide : ∀ {l V D D' D''} → V • D ≈ D' • V → l • D' ≈ D'' • l
        → (l • V) • D ≈ D'' • (l • V)
  slide {l} {V} {D} {D'} {D''} eV el = begin
    (l • V) • D    ≈⟨ assoc ⟩
    l • (V • D)    ≈⟨ cright eV ⟩
    l • (D' • V)   ≈⟨ sym assoc ⟩
    (l • D') • V   ≈⟨ cleft el ⟩
    (D'' • l) • V  ≈⟨ assoc ⟩
    D'' • (l • V) ∎

  ----------------------------------------------------------------------
  -- Orders and inverses used throughout

  private
    H⁴ : H ^ 4 ≈ ε
    H⁴ = CL.lemma-order-H

    H³H : H ^ 3 • H ≈ ε
    H³H = begin
      H ^ 3 • H        ≈⟨ sym (^-+ H 3 1) ⟩
      H ^ 4            ≈⟨ H⁴ ⟩
      ε ∎

    -- H ⁵ is H, so a multiplier absorbed into an H ³ leaves a single H.
    H²H³ : M₋₁ • H ^ 3 ≈ H
    H²H³ = begin
      M₋₁ • H ^ 3       ≈⟨ cleft sym (axiom order-H) ⟩
      H ^ 2 • H ^ 3     ≈⟨ sym (^-+ H 2 3) ⟩
      H ^ 5             ≈⟨ cright H⁴ ⟩
      H • ε             ≈⟨ right-unit ⟩
      H ∎

    H³H² : H ^ 3 • M₋₁ ≈ H
    H³H² = begin
      H ^ 3 • M₋₁       ≈⟨ cright sym (axiom order-H) ⟩
      H ^ 3 • H ^ 2     ≈⟨ sym (^-+ H 3 2) ⟩
      H ^ 5             ≈⟨ cright H⁴ ⟩
      H • ε             ≈⟨ right-unit ⟩
      H ∎

    CZ⁻CZ : CZ ^ p-1 • CZ ≈ ε
    CZ⁻CZ = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p              ≈⟨ axiom order-CZ ⟩
      ε ∎

    S⁻S : S ^ p-1 • S ≈ ε
    S⁻S = begin
      S ^ p-1 • S        ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p              ≈⟨ CL.lemma-order-S ⟩
      ε ∎

    SS⁻ : S • S ^ p-1 ≈ ε
    SS⁻ = CL.lemma-order-S

    order-S↑ : S ↑ ^ p ≈ ε
    order-S↑ = begin
      S ↑ ^ p    ≡⟨ Eq.sym (lemma-↑^ p S) ⟩
      (S ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-S n) ⟩
      ε ∎

    S↑⁻S↑ : S ↑ ^ p-1 • S ↑ ≈ ε
    S↑⁻S↑ = begin
      S ↑ ^ p-1 • S ↑        ≈⟨ sym (^-+ (S ↑) p-1 1) ⟩
      S ↑ ^ (p-1 Nat.+ 1)    ≡⟨ Eq.cong (S ↑ ^_) (NP.+-comm p-1 1) ⟩
      S ↑ ^ p                ≈⟨ order-S↑ ⟩
      ε ∎

    S↑S↑⁻ : S ↑ • S ↑ ^ p-1 ≈ ε
    S↑S↑⁻ = order-S↑

    Z↑Z↑⁻ : Z ↑ • Z ↑ ^ p-1 ≈ ε
    Z↑Z↑⁻ = begin
      Z ↑ ^ p    ≡⟨ Eq.sym (lemma-↑^ p Z) ⟩
      (Z ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-Z n) ⟩
      ε ∎

  ----------------------------------------------------------------------
  -- The multiplier by −1 inverts the CZ it passes
  --
  -- lemma-CZ-M₋₁ is exposed by Lemmas; this is the same fact read from
  -- the other side, got by conjugating with M₋₁ (an involution).

  private
    M₋₁M₋₁ : M₋₁ • M₋₁ ≈ ε
    M₋₁M₋₁ = CL.lemma-M₋₁^2

    CZᵉ : CZ ^ e₁ ≈ CZ ^ p-1
    CZᵉ = refl' (Eq.cong (CZ ^_) lemma-toℕ-1ₚ)

    lemma-M₋₁-CZ : M₋₁ • CZ ≈ CZ ^ p-1 • M₋₁
    lemma-M₋₁-CZ = begin
      M₋₁ • CZ
        ≈⟨ sym right-unit ⟩
      (M₋₁ • CZ) • ε
        ≈⟨ cright sym M₋₁M₋₁ ⟩
      (M₋₁ • CZ) • (M₋₁ • M₋₁)
        ≈⟨ sym assoc ⟩
      ((M₋₁ • CZ) • M₋₁) • M₋₁
        ≈⟨ cleft assoc ⟩
      (M₋₁ • (CZ • M₋₁)) • M₋₁
        ≈⟨ cleft cright lemma-CZ-M₋₁ ⟩
      (M₋₁ • (M₋₁ • CZ ^ e₁)) • M₋₁
        ≈⟨ cleft sym assoc ⟩
      ((M₋₁ • M₋₁) • CZ ^ e₁) • M₋₁
        ≈⟨ cleft cleft M₋₁M₋₁ ⟩
      (ε • CZ ^ e₁) • M₋₁
        ≈⟨ cleft left-unit ⟩
      CZ ^ e₁ • M₋₁
        ≈⟨ cleft CZᵉ ⟩
      CZ ^ p-1 • M₋₁ ∎

  ----------------------------------------------------------------------
  -- The CZ / CX quartet
  --
  -- CX is CZ conjugated by an H on wire 0, so conjugating by H again
  -- must come back to CZ — with a sign, because H ² is the multiplier by
  -- −1 and that inverts the CZ it passes.  Naming CX ⁻¹ as a word (the
  -- same conjugation with the H's swapped) keeps every exponent
  -- positive.

  CX⁻ : Word (Gen (₂₊ n))
  CX⁻ = H • (CZ • H ^ 3)

  cH-CX : H • CX ≈ CZ • H
  cH-CX = begin
    H • (H ^ 3 • (CZ • H))   ≈⟨ sym assoc ⟩
    (H • H ^ 3) • (CZ • H)   ≈⟨ cleft H⁴ ⟩
    ε • (CZ • H)             ≈⟨ left-unit ⟩
    CZ • H ∎

  cH-CZ : H • CZ ≈ CX⁻ • H
  cH-CZ = sym (begin
    (H • (CZ • H ^ 3)) • H   ≈⟨ assoc ⟩
    H • ((CZ • H ^ 3) • H)   ≈⟨ cright assoc ⟩
    H • (CZ • (H ^ 3 • H))   ≈⟨ cright cright H³H ⟩
    H • (CZ • ε)             ≈⟨ cright right-unit ⟩
    H • CZ ∎)

  cH-CX⁻ : H • CX⁻ ≈ CZ ^ p-1 • H
  cH-CX⁻ = begin
    H • (H • (CZ • H ^ 3))
      ≈⟨ sym assoc ⟩
    (H • H) • (CZ • H ^ 3)
      ≈⟨ cleft axiom order-H ⟩
    M₋₁ • (CZ • H ^ 3)
      ≈⟨ sym assoc ⟩
    (M₋₁ • CZ) • H ^ 3
      ≈⟨ cleft lemma-M₋₁-CZ ⟩
    (CZ ^ p-1 • M₋₁) • H ^ 3
      ≈⟨ assoc ⟩
    CZ ^ p-1 • (M₋₁ • H ^ 3)
      ≈⟨ cright H²H³ ⟩
    CZ ^ p-1 • H ∎

  cH-CZ⁻ : H • CZ ^ p-1 ≈ CX • H
  cH-CZ⁻ = sym (begin
    (H ^ 3 • (CZ • H)) • H
      ≈⟨ assoc ⟩
    H ^ 3 • ((CZ • H) • H)
      ≈⟨ cright assoc ⟩
    H ^ 3 • (CZ • (H • H))
      ≈⟨ cright cright axiom order-H ⟩
    H ^ 3 • (CZ • M₋₁)
      ≈⟨ cright lemma-CZ-M₋₁ ⟩
    H ^ 3 • (M₋₁ • CZ ^ e₁)
      ≈⟨ cright cright CZᵉ ⟩
    H ^ 3 • (M₋₁ • CZ ^ p-1)
      ≈⟨ sym assoc ⟩
    (H ^ 3 • M₋₁) • CZ ^ p-1
      ≈⟨ cleft H³H² ⟩
    H • CZ ^ p-1 ∎)

  -- CX ⁻¹ really is the inverse: conjugating by H is injective, and it
  -- sends both CX ^ (p-1) and CX⁻ to CZ ^ (p-1).
  CX⁻≈ : CX ^ p-1 ≈ CX⁻
  CX⁻≈ = •-cancelˡ {g = H} (begin
    H • CX ^ p-1      ≈⟨ lemma-Induction cH-CX p-1 ⟩
    CZ ^ p-1 • H      ≈⟨ sym cH-CX⁻ ⟩
    H • CX⁻ ∎)

  private
    CX-CX⁻ : CX • CX⁻ ≈ ε
    CX-CX⁻ = begin
      (H ^ 3 • (CZ • H)) • (H • (CZ • H ^ 3))
        ≈⟨ assoc ⟩
      H ^ 3 • ((CZ • H) • (H • (CZ • H ^ 3)))
        ≈⟨ cright assoc ⟩
      H ^ 3 • (CZ • (H • (H • (CZ • H ^ 3))))
        ≈⟨ cright cright cH-CX⁻ ⟩
      H ^ 3 • (CZ • (CZ ^ p-1 • H))
        ≈⟨ cright sym assoc ⟩
      H ^ 3 • ((CZ • CZ ^ p-1) • H)
        ≈⟨ cright cleft (axiom order-CZ) ⟩
      H ^ 3 • (ε • H)
        ≈⟨ cright left-unit ⟩
      H ^ 3 • H
        ≈⟨ H³H ⟩
      ε ∎

    -- H ⁶ is the multiplier by −1 again.
    H³H³ : H ^ 3 • H ^ 3 ≈ M₋₁
    H³H³ = begin
      H ^ 3 • H ^ 3   ≈⟨ sym (^-+ H 3 3) ⟩
      H ^ 6           ≈⟨ ^-+ H 4 2 ⟩
      H ^ 4 • H ^ 2   ≈⟨ cleft H⁴ ⟩
      ε • H ^ 2       ≈⟨ left-unit ⟩
      H ^ 2           ≈⟨ axiom order-H ⟩
      M₋₁ ∎

    CX⁻-CX : CX⁻ • CX ≈ ε
    CX⁻-CX = begin
      (H • (CZ • H ^ 3)) • (H ^ 3 • (CZ • H))
        ≈⟨ assoc ⟩
      H • ((CZ • H ^ 3) • (H ^ 3 • (CZ • H)))
        ≈⟨ cright assoc ⟩
      H • (CZ • (H ^ 3 • (H ^ 3 • (CZ • H))))
        ≈⟨ cright cright sym assoc ⟩
      H • (CZ • ((H ^ 3 • H ^ 3) • (CZ • H)))
        ≈⟨ cright cright cleft H³H³ ⟩
      H • (CZ • (M₋₁ • (CZ • H)))
        ≈⟨ cright cright sym assoc ⟩
      H • (CZ • ((M₋₁ • CZ) • H))
        ≈⟨ cright cright cleft lemma-M₋₁-CZ ⟩
      H • (CZ • ((CZ ^ p-1 • M₋₁) • H))
        ≈⟨ cright cright assoc ⟩
      H • (CZ • (CZ ^ p-1 • (M₋₁ • H)))
        ≈⟨ cright sym assoc ⟩
      H • ((CZ • CZ ^ p-1) • (M₋₁ • H))
        ≈⟨ cright cleft (axiom order-CZ) ⟩
      H • (ε • (M₋₁ • H))
        ≈⟨ cright left-unit ⟩
      H • (M₋₁ • H)
        ≈⟨ sym assoc ⟩
      (H • M₋₁) • H
        ≈⟨ cleft cright sym (axiom order-H) ⟩
      H ^ 3 • H
        ≈⟨ H³H ⟩
      ε ∎

  ----------------------------------------------------------------------
  -- blake-c12 as a crossing rule
  --
  -- The axiom is exactly "what S costs when it crosses CX", written with
  -- everything moved to one side.  Moving it back is pure cancellation.

  private
    blake₀ : S ↑ ^ p-1 • (S ^ p-1 • (CX⁻ • (S • CX))) ≈ CZ
    blake₀ = begin
      S ↑ ^ p-1 • (S ^ p-1 • (CX⁻ • (S • CX)))
        ≈⟨ cright cright cleft sym CX⁻≈ ⟩
      S ↑ ^ p-1 • (S ^ p-1 • (CX ^ p-1 • (S • CX)))
        ≡⟨ Eq.cong (λ w → w • (S ^ p-1 • (CX ^ p-1 • (S • CX))))
                   (Eq.sym (lemma-↑^ p-1 S)) ⟩
      (S ^ p-1) ↑ • (S ^ p-1 • (CX ^ p-1 • (S • CX)))
        ≈⟨ axiom blake-c12 ⟩
      CZ ∎

  blake-A : CX⁻ • (S • CX) ≈ S • (S ↑ • CZ)
  blake-A = •-cancelˡ {g = S ↑ ^ p-1 • S ^ p-1} (begin
    (S ↑ ^ p-1 • S ^ p-1) • (CX⁻ • (S • CX))
      ≈⟨ assoc ⟩
    S ↑ ^ p-1 • (S ^ p-1 • (CX⁻ • (S • CX)))
      ≈⟨ blake₀ ⟩
    CZ
      ≈⟨ sym left-unit ⟩
    ε • CZ
      ≈⟨ cleft sym S↑⁻S↑ ⟩
    (S ↑ ^ p-1 • S ↑) • CZ
      ≈⟨ assoc ⟩
    S ↑ ^ p-1 • (S ↑ • CZ)
      ≈⟨ cright sym left-unit ⟩
    S ↑ ^ p-1 • (ε • (S ↑ • CZ))
      ≈⟨ cright cleft sym S⁻S ⟩
    S ↑ ^ p-1 • ((S ^ p-1 • S) • (S ↑ • CZ))
      ≈⟨ cright assoc ⟩
    S ↑ ^ p-1 • (S ^ p-1 • (S • (S ↑ • CZ)))
      ≈⟨ sym assoc ⟩
    (S ↑ ^ p-1 • S ^ p-1) • (S • (S ↑ • CZ)) ∎)

  -- What S costs crossing CX: it leaves an S ↑ and a CZ behind.
  cS-CX : S • CX ≈ (CX • (S ↑ • CZ)) • S
  cS-CX = begin
    S • CX
      ≈⟨ sym left-unit ⟩
    ε • (S • CX)
      ≈⟨ cleft sym CX-CX⁻ ⟩
    (CX • CX⁻) • (S • CX)
      ≈⟨ assoc ⟩
    CX • (CX⁻ • (S • CX))
      ≈⟨ cright blake-A ⟩
    CX • (S • (S ↑ • CZ))
      ≈⟨ cright sym assoc ⟩
    CX • ((S • S ↑) • CZ)
      ≈⟨ cright cleft lemma-comm-S-w↑ S ⟩
    CX • ((S ↑ • S) • CZ)
      ≈⟨ cright assoc ⟩
    CX • (S ↑ • (S • CZ))
      ≈⟨ cright cright sym lemma-comm-CZ-S ⟩
    CX • (S ↑ • (CZ • S))
      ≈⟨ cright sym assoc ⟩
    CX • ((S ↑ • CZ) • S)
      ≈⟨ sym assoc ⟩
    (CX • (S ↑ • CZ)) • S ∎

  -- The same for S ⁻¹ crossing CX ⁻¹, which is what X's fifth letter
  -- needs.  blake-A with the CX moved to the other side, then flipped.
  private
    blake-B : CX⁻ • S ≈ S • (S ↑ • (CZ • CX⁻))
    blake-B = begin
      CX⁻ • S
        ≈⟨ sym right-unit ⟩
      (CX⁻ • S) • ε
        ≈⟨ cright sym CX-CX⁻ ⟩
      (CX⁻ • S) • (CX • CX⁻)
        ≈⟨ assoc ⟩
      CX⁻ • (S • (CX • CX⁻))
        ≈⟨ cright sym assoc ⟩
      CX⁻ • ((S • CX) • CX⁻)
        ≈⟨ sym assoc ⟩
      (CX⁻ • (S • CX)) • CX⁻
        ≈⟨ cleft blake-A ⟩
      (S • (S ↑ • CZ)) • CX⁻
        ≈⟨ assoc ⟩
      S • ((S ↑ • CZ) • CX⁻)
        ≈⟨ cright assoc ⟩
      S • (S ↑ • (CZ • CX⁻)) ∎

  cS⁻-CX⁻ : S ^ p-1 • CX⁻ ≈ (S ↑ • (CZ • CX⁻)) • S ^ p-1
  cS⁻-CX⁻ = •-cancelˡ {g = S} (begin
    S • (S ^ p-1 • CX⁻)
      ≈⟨ sym assoc ⟩
    (S • S ^ p-1) • CX⁻
      ≈⟨ cleft SS⁻ ⟩
    ε • CX⁻
      ≈⟨ left-unit ⟩
    CX⁻
      ≈⟨ sym right-unit ⟩
    CX⁻ • ε
      ≈⟨ cright sym SS⁻ ⟩
    CX⁻ • (S • S ^ p-1)
      ≈⟨ sym assoc ⟩
    (CX⁻ • S) • S ^ p-1
      ≈⟨ cleft blake-B ⟩
    (S • (S ↑ • (CZ • CX⁻))) • S ^ p-1
      ≈⟨ assoc ⟩
    S • ((S ↑ • (CZ • CX⁻)) • S ^ p-1) ∎)

  ----------------------------------------------------------------------
  -- blake read the other way, by the multiplier on wire 1
  --
  -- Conjugating by M₋₁ ↑ swaps CX with CX ⁻¹ and CZ with CZ ⁻¹, fixes S
  -- (other wire) and sends S ↑ to S ↑ • Z ↑.  Applying it to blake-A
  -- therefore gives what S does to CX ⁻¹ — and the Z ↑ it drops is the
  -- Z ↑ the rule is about.

  private
    mu-S : M₋₁ ↑ • S ≈ S • M₋₁ ↑
    mu-S = sym (lemma-comm-S-w↑ M₋₁)

    mu-H : M₋₁ ↑ • H ≈ H • M₋₁ ↑
    mu-H = sym (lemma-comm-H-w↑ M₋₁)

    mu-H³ : M₋₁ ↑ • H ^ 3 ≈ H ^ 3 • M₋₁ ↑
    mu-H³ = sym (lemma-comm-Hᵏ-w↑ 3 M₋₁)

    mu-CZ : M₋₁ ↑ • CZ ≈ CZ ^ p-1 • M₋₁ ↑
    mu-CZ = trans lemma-M₋₁↑-CZ (cleft CZᵉ)

    mu-S↑ : M₋₁ ↑ • S ↑ ≈ (S ↑ • Z ↑) • M₋₁ ↑
    mu-S↑ = lemma-cong↑ _ _ (W0.lemma-M₋₁-S)

    mu-CX : M₋₁ ↑ • CX ≈ CX⁻ • M₋₁ ↑
    mu-CX = begin
      M₋₁ ↑ • (H ^ 3 • (CZ • H))
        ≈⟨ crossW mu-H³ (crossW mu-CZ mu-H) ⟩
      (H ^ 3 • (CZ ^ p-1 • H)) • M₋₁ ↑
        ≈⟨ cleft cright sym cH-CX⁻ ⟩
      (H ^ 3 • (H • CX⁻)) • M₋₁ ↑
        ≈⟨ cleft sym assoc ⟩
      ((H ^ 3 • H) • CX⁻) • M₋₁ ↑
        ≈⟨ cleft cleft H³H ⟩
      (ε • CX⁻) • M₋₁ ↑
        ≈⟨ cleft left-unit ⟩
      CX⁻ • M₋₁ ↑ ∎

    mu-CX⁻ : M₋₁ ↑ • CX⁻ ≈ CX • M₋₁ ↑
    mu-CX⁻ = begin
      M₋₁ ↑ • (H • (CZ • H ^ 3))
        ≈⟨ crossW mu-H (crossW mu-CZ mu-H³) ⟩
      (H • (CZ ^ p-1 • H ^ 3)) • M₋₁ ↑
        ≈⟨ cleft sym assoc ⟩
      ((H • CZ ^ p-1) • H ^ 3) • M₋₁ ↑
        ≈⟨ cleft cleft cH-CZ⁻ ⟩
      ((CX • H) • H ^ 3) • M₋₁ ↑
        ≈⟨ cleft assoc ⟩
      (CX • (H • H ^ 3)) • M₋₁ ↑
        ≈⟨ cleft cright H⁴ ⟩
      (CX • ε) • M₋₁ ↑
        ≈⟨ cleft right-unit ⟩
      CX • M₋₁ ↑ ∎

  blake-flip : CX • (S • CX⁻) ≈ S • (S ↑ • (Z ↑ • CZ ^ p-1))
  blake-flip = •-cancelʳ {h = M₋₁ ↑} (begin
    (CX • (S • CX⁻)) • M₋₁ ↑
      ≈⟨ sym (crossW mu-CX⁻ (crossW mu-S mu-CX)) ⟩
    M₋₁ ↑ • (CX⁻ • (S • CX))
      ≈⟨ cright blake-A ⟩
    M₋₁ ↑ • (S • (S ↑ • CZ))
      ≈⟨ crossW mu-S (crossW mu-S↑ mu-CZ) ⟩
    (S • ((S ↑ • Z ↑) • CZ ^ p-1)) • M₋₁ ↑
      ≈⟨ cleft cright assoc ⟩
    (S • (S ↑ • (Z ↑ • CZ ^ p-1))) • M₋₁ ↑ ∎)

  -- …and the same with S ⁻¹, which is the form the collapse needs.  Both
  -- sides are inverse to CX • (S • CX⁻), and inverses are unique.
  blake-flip⁻ : CX • (S ^ p-1 • CX⁻)
              ≈ CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))
  blake-flip⁻ = •-cancelˡ {g = CX • (S • CX⁻)} (trans left right)
    where
    left : (CX • (S • CX⁻)) • (CX • (S ^ p-1 • CX⁻)) ≈ ε
    left = begin
      (CX • (S • CX⁻)) • (CX • (S ^ p-1 • CX⁻))
        ≈⟨ assoc ⟩
      CX • ((S • CX⁻) • (CX • (S ^ p-1 • CX⁻)))
        ≈⟨ cright assoc ⟩
      CX • (S • (CX⁻ • (CX • (S ^ p-1 • CX⁻))))
        ≈⟨ cright cright sym assoc ⟩
      CX • (S • ((CX⁻ • CX) • (S ^ p-1 • CX⁻)))
        ≈⟨ cright cright cleft CX⁻-CX ⟩
      CX • (S • (ε • (S ^ p-1 • CX⁻)))
        ≈⟨ cright cright left-unit ⟩
      CX • (S • (S ^ p-1 • CX⁻))
        ≈⟨ cright sym assoc ⟩
      CX • ((S • S ^ p-1) • CX⁻)
        ≈⟨ cright cleft SS⁻ ⟩
      CX • (ε • CX⁻)
        ≈⟨ cright left-unit ⟩
      CX • CX⁻
        ≈⟨ CX-CX⁻ ⟩
      ε ∎

    -- Nothing needs commuting here: the four cancellations are already
    -- nested one inside the next.
    right : ε ≈ (CX • (S • CX⁻)) • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
    right = sym (begin
      (CX • (S • CX⁻)) • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
        ≈⟨ cleft blake-flip ⟩
      (S • (S ↑ • (Z ↑ • CZ ^ p-1))) • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
        ≈⟨ assoc ⟩
      S • ((S ↑ • (Z ↑ • CZ ^ p-1)) • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))
        ≈⟨ cright assoc ⟩
      S • (S ↑ • ((Z ↑ • CZ ^ p-1) • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))))
        ≈⟨ cright cright assoc ⟩
      S • (S ↑ • (Z ↑ • (CZ ^ p-1 • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))))
        ≈⟨ cright cright cright sym assoc ⟩
      S • (S ↑ • (Z ↑ • ((CZ ^ p-1 • CZ) • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))))
        ≈⟨ cright cright cright cleft CZ⁻CZ ⟩
      S • (S ↑ • (Z ↑ • (ε • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))))
        ≈⟨ cright cright cright left-unit ⟩
      S • (S ↑ • (Z ↑ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))
        ≈⟨ cright cright sym assoc ⟩
      S • (S ↑ • ((Z ↑ • Z ↑ ^ p-1) • (S ↑ ^ p-1 • S ^ p-1)))
        ≈⟨ cright cright cleft Z↑Z↑⁻ ⟩
      S • (S ↑ • (ε • (S ↑ ^ p-1 • S ^ p-1)))
        ≈⟨ cright cright left-unit ⟩
      S • (S ↑ • (S ↑ ^ p-1 • S ^ p-1))
        ≈⟨ cright sym assoc ⟩
      S • ((S ↑ • S ↑ ^ p-1) • S ^ p-1)
        ≈⟨ cright cleft S↑S↑⁻ ⟩
      S • (ε • S ^ p-1)
        ≈⟨ cright left-unit ⟩
      S • S ^ p-1
        ≈⟨ SS⁻ ⟩
      ε ∎)

  ----------------------------------------------------------------------
  -- The six crossings
  --
  -- X = H • S • H • H • S ⁻¹ • H, read right to left.  Each letter
  -- conjugates the accumulated two-wire word; S ↑ is inert because every
  -- letter of X is on wire 0.

  private
    cH-S↑ : H • S ↑ ≈ S ↑ • H
    cH-S↑ = lemma-comm-H-w↑ S

    cS-S↑ : S • S ↑ ≈ S ↑ • S
    cS-S↑ = lemma-comm-S-w↑ S

    cS-CZ⁻ : S • CZ ^ p-1 ≈ CZ ^ p-1 • S
    cS-CZ⁻ = comm⇒pow-comm 1 p-1 (sym lemma-comm-CZ-S)

    c₁ : H • CZ ≈ CX⁻ • H
    c₁ = cH-CZ

    c₂ : S ^ p-1 • CX⁻ ≈ (S ↑ • (CZ • CX⁻)) • S ^ p-1
    c₂ = cS⁻-CX⁻

    c₃ : H • (S ↑ • (CZ • CX⁻)) ≈ (S ↑ • (CX⁻ • CZ ^ p-1)) • H
    c₃ = crossW cH-S↑ (crossW cH-CZ cH-CX⁻)

    c₄ : H • (S ↑ • (CX⁻ • CZ ^ p-1)) ≈ (S ↑ • (CZ ^ p-1 • CX)) • H
    c₄ = crossW cH-S↑ (crossW cH-CX⁻ cH-CZ⁻)

    c₅ : S • (S ↑ • (CZ ^ p-1 • CX))
       ≈ (S ↑ • (CZ ^ p-1 • (CX • (S ↑ • CZ)))) • S
    c₅ = crossW cS-S↑ (crossW cS-CZ⁻ cS-CX)

    c₆ : H • (S ↑ • (CZ ^ p-1 • (CX • (S ↑ • CZ))))
       ≈ (S ↑ • (CX • (CZ • (S ↑ • CX⁻)))) • H
    c₆ = crossW cH-S↑ (crossW cH-CZ⁻ (crossW cH-CX (crossW cH-S↑ cH-CZ)))

  -- What X conjugates CZ into.
  D₀ : Word (Gen (₂₊ n))
  D₀ = S ↑ • (CX • (CZ • (S ↑ • CX⁻)))

  lemma-chain : X • CZ ≈ D₀ • X
  lemma-chain = slide (slide (slide (slide (slide c₁ c₂) c₃) c₄) c₅) c₆

  ----------------------------------------------------------------------
  -- …and D₀ collapses
  --
  -- Fold CX • S ↑ • CZ back into S • CX • S ⁻¹ (blake, cS-CX), leaving
  -- CX • S ⁻¹ • CX ⁻¹ — which is blake-flip⁻.  Everything then cancels
  -- except the Z ↑ ⁻¹ the flip introduced.

  private
    -- S and S ↑ both commute with CZ and with Z ↑ ^ (p-1), so the block
    -- S ↑ • S passes them and meets its own inverse.
    W : Word (Gen (₂₊ n))
    W = S ↑ • S

    -- Moving something that commutes with the head out of the way.
    pull : ∀ {a u v} → a • u ≈ u • a → a • (u • v) ≈ u • (a • v)
    pull e = trans (sym assoc) (trans (cleft e) assoc)

    W-CZ : W • CZ ≈ CZ • W
    W-CZ = slide (sym lemma-comm-CZ-S) (sym (axiom comm-CZ-S↑))

    comm-S↑-Z↑ : S ↑ • Z ↑ ^ p-1 ≈ Z ↑ ^ p-1 • S ↑
    comm-S↑-Z↑ = comm⇒pow-comm 1 p-1
      (sym (lemma-cong↑ _ _ (One-Wire.lemma-comm-Z-S n)))

    comm-S-Z↑ : S • Z ↑ ^ p-1 ≈ Z ↑ ^ p-1 • S
    comm-S-Z↑ = comm⇒pow-comm 1 p-1 (lemma-comm-S-w↑ Z)

    W-Z↑ : W • Z ↑ ^ p-1 ≈ Z ↑ ^ p-1 • W
    W-Z↑ = slide comm-S-Z↑ comm-S↑-Z↑

    W-kill : W • (S ↑ ^ p-1 • S ^ p-1) ≈ ε
    W-kill = begin
      (S ↑ • S) • (S ↑ ^ p-1 • S ^ p-1)
        ≈⟨ assoc ⟩
      S ↑ • (S • (S ↑ ^ p-1 • S ^ p-1))
        ≈⟨ cright sym assoc ⟩
      S ↑ • ((S • S ↑ ^ p-1) • S ^ p-1)
        ≈⟨ cright cleft comm⇒pow-comm 1 p-1 (lemma-comm-S-w↑ S) ⟩
      S ↑ • ((S ↑ ^ p-1 • S) • S ^ p-1)
        ≈⟨ cright assoc ⟩
      S ↑ • (S ↑ ^ p-1 • (S • S ^ p-1))
        ≈⟨ cright cright SS⁻ ⟩
      S ↑ • (S ↑ ^ p-1 • ε)
        ≈⟨ cright right-unit ⟩
      S ↑ • S ↑ ^ p-1
        ≈⟨ S↑S↑⁻ ⟩
      ε ∎

  lemma-D₀ : D₀ ≈ Z ↑ ^ p-1 • CZ
  lemma-D₀ = begin
    S ↑ • (CX • (CZ • (S ↑ • CX⁻)))
      ≈⟨ cright cright sym assoc ⟩
    S ↑ • (CX • ((CZ • S ↑) • CX⁻))
      ≈⟨ cright cright cleft (axiom comm-CZ-S↑) ⟩
    S ↑ • (CX • ((S ↑ • CZ) • CX⁻))
      ≈⟨ cright sym assoc ⟩
    S ↑ • ((CX • (S ↑ • CZ)) • CX⁻)
      ≈⟨ cright cleft sym unfold ⟩
    S ↑ • ((S • (CX • S ^ p-1)) • CX⁻)
      ≈⟨ cright assoc ⟩
    S ↑ • (S • ((CX • S ^ p-1) • CX⁻))
      ≈⟨ cright cright assoc ⟩
    S ↑ • (S • (CX • (S ^ p-1 • CX⁻)))
      ≈⟨ cright cright blake-flip⁻ ⟩
    S ↑ • (S • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))
      ≈⟨ sym assoc ⟩
    W • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
      ≈⟨ pull W-CZ ⟩
    CZ • (W • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
      ≈⟨ cright pull W-Z↑ ⟩
    CZ • (Z ↑ ^ p-1 • (W • (S ↑ ^ p-1 • S ^ p-1)))
      ≈⟨ cright cright W-kill ⟩
    CZ • (Z ↑ ^ p-1 • ε)
      ≈⟨ cright right-unit ⟩
    CZ • Z ↑ ^ p-1
      ≈⟨ comm⇒pow-comm 1 p-1 lemma-comm-CZ-Z↑ ⟩
    Z ↑ ^ p-1 • CZ ∎
    where
    -- cS-CX with the trailing S moved across: S • CX • S ⁻¹.
    unfold : S • (CX • S ^ p-1) ≈ CX • (S ↑ • CZ)
    unfold = begin
      S • (CX • S ^ p-1)
        ≈⟨ sym assoc ⟩
      (S • CX) • S ^ p-1
        ≈⟨ cleft cS-CX ⟩
      ((CX • (S ↑ • CZ)) • S) • S ^ p-1
        ≈⟨ assoc ⟩
      (CX • (S ↑ • CZ)) • (S • S ^ p-1)
        ≈⟨ cright SS⁻ ⟩
      (CX • (S ↑ • CZ)) • ε
        ≈⟨ right-unit ⟩
      CX • (S ↑ • CZ) ∎

  ----------------------------------------------------------------------
  -- The axiom

  lemma-rel-X↓-CZ : CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
  lemma-rel-X↓-CZ = sym (begin
    X • (Z ↑ • CZ)
      ≈⟨ sym assoc ⟩
    (X • Z ↑) • CZ
      ≈⟨ cleft (lemma-comm-X-w↑ Z) ⟩
    (Z ↑ • X) • CZ
      ≈⟨ assoc ⟩
    Z ↑ • (X • CZ)
      ≈⟨ cright lemma-chain ⟩
    Z ↑ • (D₀ • X)
      ≈⟨ cright cleft lemma-D₀ ⟩
    Z ↑ • ((Z ↑ ^ p-1 • CZ) • X)
      ≈⟨ sym assoc ⟩
    (Z ↑ • (Z ↑ ^ p-1 • CZ)) • X
      ≈⟨ cleft sym assoc ⟩
    ((Z ↑ • Z ↑ ^ p-1) • CZ) • X
      ≈⟨ cleft cleft Z↑Z↑⁻ ⟩
    (ε • CZ) • X
      ≈⟨ cleft left-unit ⟩
    CZ • X ∎)
