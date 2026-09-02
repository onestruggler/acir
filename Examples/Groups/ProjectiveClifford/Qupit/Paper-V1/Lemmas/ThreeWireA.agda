{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The remote CZ at three wires, part 1 of 2.
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


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ThreeWireA
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
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.ExConj p-3 p-prime g* g-gen

------------------------------------------------------------------------
-- The remote CZ, at three wires
--
-- CZ02 is *defined* as Ex • CZ ↑ • Ex — the CZ on wires 1-2 carried onto
-- wires 0-2 by the swap of wires 0-1 — so conjugation facts about it are
-- definitional, and its order follows from the order of CZ.
--
-- This is the correction term of the paper's C18
-- (semi-CX↑-CZ↓ : CX ↑ • CZ ↓ === CZ ↓ • CZ02 • CX ↑): CX ↑ retargets
-- wire 1, which is what a CZ on wires 0-1 reads, so pushing that CZ
-- through picks up a CZ on wires 0-2.  Deriving selinger-c12 turns on
-- those corrections cancelling, and they cancel because CX ↑ occurs in
-- the C6-expansion of a CZ with total exponent 1 + (p-1) = p, leaving
-- CZ02 ^ p ≈ ε.

module Three-Wire-A (n : ℕ) where

  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation (₁₊ n)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₂ = PB ((₂₊ n) QRel,_===_)

  open Group-Lemmas ((₃₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₃₊ n})
    using (•-cancelʳ ; •-cancelˡ)

  -- CZ on the upper pair has order p, inherited from order-CZ one wire
  -- down.  (ε ↑ is ε definitionally, so the shift leaves no residue.)
  lemma-order-CZ↑ : (CZ ↑) ^ p ≈ ε
  lemma-order-CZ↑ = begin
    (CZ ↑) ^ p  ≈⟨ refl' (Eq.sym (lemma-↑^ p CZ)) ⟩
    (CZ ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (PB₂.axiom order-CZ) ⟩
    ε ∎

  -- Conjugation commutes with powers.  Stated over an arbitrary u so it
  -- serves CZ02 and anything else conjugated by the swap.
  lemma-conj-pow : ∀ (u : Word (Gen (₃₊ n))) k →
                   (Ex • (u • Ex)) ^ k ≈ Ex • (u ^ k • Ex)
  lemma-conj-pow u ₀ = begin
    ε              ≈⟨ sym lemma-Ex-Ex ⟩
    Ex • Ex        ≈⟨ cright sym left-unit ⟩
    Ex • (ε • Ex) ∎
  lemma-conj-pow u ₁ = refl
  lemma-conj-pow u (₂₊ k) = begin
    (Ex • (u • Ex)) • (Ex • (u • Ex)) ^ ₁₊ k
      ≈⟨ cright lemma-conj-pow u (₁₊ k) ⟩
    (Ex • (u • Ex)) • (Ex • (u ^ ₁₊ k • Ex))
      ≈⟨ assoc ⟩
    Ex • ((u • Ex) • (Ex • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright assoc ⟩
    Ex • (u • (Ex • (Ex • (u ^ ₁₊ k • Ex))))
      ≈⟨ cright cright sym assoc ⟩
    Ex • (u • ((Ex • Ex) • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright cright cleft lemma-Ex-Ex ⟩
    Ex • (u • (ε • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright cright left-unit ⟩
    Ex • (u • (u ^ ₁₊ k • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((u • u ^ ₁₊ k) • Ex) ∎

  -- The remote CZ has order p as well: p copies of it are p copies of
  -- CZ ↑ with the two swaps cancelling.
  lemma-order-CZ02 : CZ02 ^ p ≈ ε
  lemma-order-CZ02 = begin
    CZ02 ^ p                ≈⟨ lemma-conj-pow (CZ ↑) p ⟩
    Ex • ((CZ ↑) ^ p • Ex)  ≈⟨ cright cleft lemma-order-CZ↑ ⟩
    Ex • (ε • Ex)           ≈⟨ cright left-unit ⟩
    Ex • Ex                 ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- The multiplier commutes with anything on the wires above it
  --
  -- Mg is a product of powers of S, H and Z on wire 0, and each of those
  -- commutes with a shifted word; the two combinators below lift that
  -- through the products and powers Mg is built from.  Taking w = CX
  -- gives what the rescaled C18 needs.

  -- (exported, not private: the other half of the split uses these)
  comm-• : ∀ {u v} {w : Word (Gen (₂₊ n))} →
           u • w ↑ ≈ w ↑ • u → v • w ↑ ≈ w ↑ • v →
           (u • v) • w ↑ ≈ w ↑ • (u • v)
  comm-• {u} {v} {w} cu cv = begin
    (u • v) • w ↑  ≈⟨ assoc ⟩
    u • (v • w ↑)  ≈⟨ cright cv ⟩
    u • (w ↑ • v)  ≈⟨ sym assoc ⟩
    (u • w ↑) • v  ≈⟨ cleft cu ⟩
    (w ↑ • u) • v  ≈⟨ assoc ⟩
    w ↑ • (u • v) ∎

  comm-pow : ∀ {u} {w : Word (Gen (₂₊ n))} →
             u • w ↑ ≈ w ↑ • u → ∀ k → u ^ k • w ↑ ≈ w ↑ • u ^ k
  comm-pow cu ₀      = trans left-unit (sym right-unit)
  comm-pow cu ₁      = cu
  comm-pow cu (₂₊ k) = comm-• cu (comm-pow cu (₁₊ k))

  lemma-Mg-w↑ : ∀ (w : Word (Gen (₂₊ n))) → Mg • w ↑ ≈ w ↑ • Mg
  lemma-Mg-w↑ w =
    comm-• cZ^ (comm-• cX^ (comm-• cS^ (comm-• cH
      (comm-• cS^' (comm-• cH (comm-• cS^ cH))))))
    where
    g⁻¹  = ((g′ ⁻¹) .proj₁)
    cH   = lemma-comm-H-w↑ w
    cZ^  = comm-pow (lemma-comm-Z-w↑ w) (toℕ ((g + - ₁) * 1/2))
    cX^  = comm-pow (lemma-comm-X-w↑ w) (toℕ ((₁ + - g⁻¹) * 1/2))
    cS^  = comm-pow (lemma-comm-S-w↑ w) (toℕ g)
    cS^' = comm-pow (lemma-comm-S-w↑ w) (toℕ g⁻¹)

  lemma-Mg-CX↑ : Mg • CX ↑ ≈ CX ↑ • Mg
  lemma-Mg-CX↑ = lemma-Mg-w↑ CX

  ------------------------------------------------------------------------
  -- The multiplier on wire 0 rescales the remote CZ too
  --
  -- CZ02 is Ex • CZ ↑ • Ex, so the multiplier passes onto the upper wire
  -- with the swap, rescales there against CZ ↑, and comes back; the
  -- power is carried through the swap by lemma-conj-pow.

  -- (exported, not private: the other half of the split uses these)
  -- semi-M↓CZ one wire up: Mg on wire 1 against CZ on wires 1-2.
  -- The instance one wire down, so that cong↑ lands at this width.
  semi↑ : Mg ↑ • CZ ↑ ≈ (CZ ↑) ^ toℕ g • Mg ↑
  semi↑ = trans (lemma-cong↑ _ _ (Ex-Conjugation.lemma-semi-Mg-CZ n))
                (refl' (Eq.cong (_• Mg ↑) (lemma-↑^ (toℕ g) CZ)))

  -- The swap carries the multiplier from wire 1 down to wire 0.
  mg↑Ex : Mg ↑ • Ex ≈ Ex • Mg
  mg↑Ex = begin
    Mg ↑ • Ex               ≈⟨ sym left-unit ⟩
    ε • (Mg ↑ • Ex)         ≈⟨ cleft sym lemma-Ex-Ex ⟩
    (Ex • Ex) • (Mg ↑ • Ex) ≈⟨ assoc ⟩
    Ex • (Ex • (Mg ↑ • Ex)) ≈⟨ cright lemma-conj-Ex-Mg↑ ⟩
    Ex • Mg ∎

  lemma-Mg-CZ02 : Mg • CZ02 ≈ CZ02 ^ toℕ g • Mg
  lemma-Mg-CZ02 = begin
    Mg • (Ex • (CZ ↑ • Ex))
      ≈⟨ sym assoc ⟩
    (Mg • Ex) • (CZ ↑ • Ex)
      ≈⟨ cleft sym lemma-Ex-Mg↑ ⟩
    (Ex • Mg ↑) • (CZ ↑ • Ex)
      ≈⟨ assoc ⟩
    Ex • (Mg ↑ • (CZ ↑ • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((Mg ↑ • CZ ↑) • Ex)
      ≈⟨ cright cleft semi↑ ⟩
    Ex • (((CZ ↑) ^ toℕ g • Mg ↑) • Ex)
      ≈⟨ cright assoc ⟩
    Ex • ((CZ ↑) ^ toℕ g • (Mg ↑ • Ex))
      ≈⟨ cright cright mg↑Ex ⟩
    Ex • ((CZ ↑) ^ toℕ g • (Ex • Mg))
      ≈⟨ cright sym assoc ⟩
    Ex • (((CZ ↑) ^ toℕ g • Ex) • Mg)
      ≈⟨ sym assoc ⟩
    (Ex • ((CZ ↑) ^ toℕ g • Ex)) • Mg
      ≈⟨ cleft sym (lemma-conj-pow (CZ ↑) (toℕ g)) ⟩
    CZ02 ^ toℕ g • Mg ∎

  ------------------------------------------------------------------------
  -- Iterating the multiplier: from the fixed generator to any unit
  --
  -- Mg ^ j rescales by g ^′ j.  The induction costs only associativity,
  -- because x ^′ (suc k) is x * (x ^′ k) definitionally; the ₀/₁/₂₊ split
  -- is forced by w ^ 1 being w rather than w • w ^ 0.

  ------------------------------------------------------------------------
  -- The transposition of wires 0 and 2
  --
  -- Ex swaps wires 0-1 and Ex ↑ swaps 1-2, so Ex • Ex ↑ • Ex transposes
  -- 0 and 2.  It carries CZ (wires 0-1) to CZ ↑ (wires 1-2), which is the
  -- transport between the progress report's form of C15 —
  -- CZ₁₂ • CZ₀₂ = CZ₀₂ • CZ₁₂, stated "up to qubit wire permutation" —
  -- and selinger-c12 as Simplified-V1 states it.  It is also the mirror
  -- that exchanges c14 and c15, since it swaps ⊤⊥ ↑ with ⊥⊤ as well.
  --
  -- Note Ex ↓ is Ex definitionally: _↓ maps every gate to itself and Ex
  -- is a word of gate letters with no symbolic power, so cz-slide can be
  -- used against Ex directly.

  ------------------------------------------------------------------------
  -- Iterating C18
  --
  -- Each CZ pushed leftwards through CX ↑ leaves a CZ02 behind, so a
  -- power of CZ leaves the alternating product (CZ • CZ02) ^ k.  No
  -- commutation between CZ and CZ02 is assumed — the two stay
  -- interleaved, which is the whole point: comparing this against the
  -- multiplier-rescaled form of the same word is what proves they
  -- commute.

  -- C18 read with CX ↑ on the left of the CZ.  The axiom as stated emits
  -- its CZ02 on the far left when a CZ crosses CX ↑ leftwards; read the
  -- other way it emits CZ02 ⁻¹, and it is that form the iteration needs,
  -- because the emitted factor lands outside CX ↑ and so does not block
  -- the next step.  (The axiom used to be stated in circuit order, which
  -- is the reverse of Word order; this is the same relation read the
  -- right way round.)

  -- (exported, not private: the other half of the split uses these)
  CZ02⁻ : Word (Gen (₃₊ n))
  CZ02⁻ = CZ02 ^ p-1

  lemma-CZ02-CZ02⁻ : CZ02 • CZ02⁻ ≈ ε
  lemma-CZ02-CZ02⁻ = begin
    CZ02 • CZ02 ^ p-1     ≈⟨ sym (^-+ CZ02 1 p-1) ⟩
    CZ02 ^ (1 Nat.+ p-1)  ≈⟨ lemma-order-CZ02 ⟩
    ε ∎

  lemma-C18' : CX ↑ • CZ ≈ (CZ02⁻ • CZ) • CX ↑
  lemma-C18' = •-cancelˡ {g = CZ02} (begin
    CZ02 • (CX ↑ • CZ)
      ≈⟨ sym (axiom semi-CX↑-CZ↓) ⟩
    CZ • CX ↑
      ≈⟨ cleft sym left-unit ⟩
    (ε • CZ) • CX ↑
      ≈⟨ cleft cleft sym lemma-CZ02-CZ02⁻ ⟩
    ((CZ02 • CZ02⁻) • CZ) • CX ↑
      ≈⟨ cleft assoc ⟩
    (CZ02 • (CZ02⁻ • CZ)) • CX ↑
      ≈⟨ assoc ⟩
    CZ02 • ((CZ02⁻ • CZ) • CX ↑) ∎)

  lemma-C18ᵏ : ∀ k → CX ↑ • CZ ^ k ≈ (CZ02⁻ • CZ) ^ k • CX ↑
  lemma-C18ᵏ ₀ = trans right-unit (sym left-unit)
  lemma-C18ᵏ ₁ = lemma-C18'
  lemma-C18ᵏ (₂₊ k) = begin
    CX ↑ • (CZ • CZ ^ ₁₊ k)
      ≈⟨ sym assoc ⟩
    (CX ↑ • CZ) • CZ ^ ₁₊ k
      ≈⟨ cleft lemma-C18' ⟩
    ((CZ02⁻ • CZ) • CX ↑) • CZ ^ ₁₊ k
      ≈⟨ assoc ⟩
    (CZ02⁻ • CZ) • (CX ↑ • CZ ^ ₁₊ k)
      ≈⟨ cright lemma-C18ᵏ (₁₊ k) ⟩
    (CZ02⁻ • CZ) • ((CZ02⁻ • CZ) ^ ₁₊ k • CX ↑)
      ≈⟨ sym assoc ⟩
    ((CZ02⁻ • CZ) • (CZ02⁻ • CZ) ^ ₁₊ k) • CX ↑ ∎

  ------------------------------------------------------------------------
  -- The alternating product has order p as well
  --
  -- CX ↑ • CZ ^ p is CX ↑ on the nose, so lemma-C18ᵏ at p says
  -- (CZ02 ⁻¹ • CZ) ^ p • CX ↑ is too, and CX ↑ cancels on the right.

  lemma-order-CZ·CZ02 : (CZ02⁻ • CZ) ^ p ≈ ε
  lemma-order-CZ·CZ02 = •-cancelʳ {h = CX ↑} (begin
    (CZ02⁻ • CZ) ^ p • CX ↑ ≈⟨ sym (lemma-C18ᵏ p) ⟩
    CX ↑ • CZ ^ p           ≈⟨ cright axiom order-CZ ⟩
    CX ↑ • ε                ≈⟨ right-unit ⟩
    CX ↑                    ≈⟨ sym left-unit ⟩
    ε • CX ↑ ∎)

  ------------------------------------------------------------------------
  -- The rescaled C18, and the exponent identity it forces
  --
  -- Conjugating C18 by Mg ^ j — which commutes with CX ↑ and rescales
  -- both CZ and CZ02 by g ^′ j — gives (A).  Comparing it against the
  -- interleaved form (B) of lemma-C18ᵏ at the same exponent, and
  -- cancelling CX ↑, leaves (C): the two CZs distribute over that power.

  lemma-Mg-CZ02^ : ∀ (a : ℤ ₚ) → Mg • CZ02 ^ toℕ a ≈ CZ02 ^ toℕ (g * a) • Mg
  lemma-Mg-CZ02^ a = begin
    Mg • CZ02 ^ toℕ a
      ≈⟨ lemma-Induction lemma-Mg-CZ02 (toℕ a) ⟩
    (CZ02 ^ toℕ g) ^ toℕ a • Mg
      ≈⟨ cleft (^^ CZ02 (toℕ g) (toℕ a)) ⟩
    CZ02 ^ (toℕ g Nat.* toℕ a) • Mg
      ≈⟨ cleft (lemma-pow-mod lemma-order-CZ02 (toℕ g Nat.* toℕ a)) ⟩
    CZ02 ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg
      ≈⟨ cleft refl' (Eq.cong (CZ02 ^_) (lemma-toℕ-% g a)) ⟩
    CZ02 ^ toℕ (g * a) • Mg ∎

  lemma-Mgᵏ-CZ02 : ∀ j → Mg ^ j • CZ02 ≈ CZ02 ^ toℕ (g ^′ j) • Mg ^ j
  lemma-Mgᵏ-CZ02 ₀ = begin
    ε • CZ02  ≈⟨ left-unit ⟩
    CZ02      ≈⟨ sym right-unit ⟩
    CZ02 • ε ∎
  lemma-Mgᵏ-CZ02 ₁ = begin
    Mg • CZ02             ≈⟨ lemma-Mg-CZ02 ⟩
    CZ02 ^ toℕ g • Mg
      ≡⟨ Eq.cong (λ z → CZ02 ^ toℕ z • Mg) (Eq.sym (lemma-x^′1=x g)) ⟩
    CZ02 ^ toℕ (g ^′ 1) • Mg ∎
  lemma-Mgᵏ-CZ02 (₂₊ j) = begin
    (Mg • Mg ^ ₁₊ j) • CZ02
      ≈⟨ assoc ⟩
    Mg • (Mg ^ ₁₊ j • CZ02)
      ≈⟨ cright lemma-Mgᵏ-CZ02 (₁₊ j) ⟩
    Mg • (CZ02 ^ toℕ (g ^′ ₁₊ j) • Mg ^ ₁₊ j)
      ≈⟨ sym assoc ⟩
    (Mg • CZ02 ^ toℕ (g ^′ ₁₊ j)) • Mg ^ ₁₊ j
      ≈⟨ cleft lemma-Mg-CZ02^ (g ^′ ₁₊ j) ⟩
    (CZ02 ^ toℕ (g * (g ^′ ₁₊ j)) • Mg) • Mg ^ ₁₊ j
      ≈⟨ assoc ⟩
    CZ02 ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg • Mg ^ ₁₊ j) ∎

  lemma-Mgᵏ-CX↑ : ∀ j → Mg ^ j • CX ↑ ≈ CX ↑ • Mg ^ j
  lemma-Mgᵏ-CX↑ = comm-pow lemma-Mg-CX↑

  -- (A): C18 with every CZ exponent rescaled by g ^′ j.  The multiplier
  -- rescales the emitted CZ02 ⁻¹ too, so its exponent picks up the same
  -- factor: CZ02 ^ (p-1) becomes CZ02 ^ ((p-1) * e).
  lemma-A : ∀ j → let e = toℕ (g ^′ j) in
            CX ↑ • CZ ^ e ≈ (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑
  lemma-A j = •-cancelʳ {h = Mg ^ j} (begin
    (CX ↑ • CZ ^ e) • Mg ^ j
      ≈⟨ assoc ⟩
    CX ↑ • (CZ ^ e • Mg ^ j)
      ≈⟨ cright sym (lemma-Mgᵏ-CZ j) ⟩
    CX ↑ • (Mg ^ j • CZ)
      ≈⟨ sym assoc ⟩
    (CX ↑ • Mg ^ j) • CZ
      ≈⟨ cleft sym (lemma-Mgᵏ-CX↑ j) ⟩
    (Mg ^ j • CX ↑) • CZ
      ≈⟨ assoc ⟩
    Mg ^ j • (CX ↑ • CZ)
      ≈⟨ cright lemma-C18' ⟩
    Mg ^ j • ((CZ02⁻ • CZ) • CX ↑)
      ≈⟨ sym assoc ⟩
    (Mg ^ j • (CZ02⁻ • CZ)) • CX ↑
      ≈⟨ cleft sym assoc ⟩
    ((Mg ^ j • CZ02⁻) • CZ) • CX ↑
      ≈⟨ cleft cleft rescale ⟩
    ((CZ02 ^ (p-1 Nat.* e) • Mg ^ j) • CZ) • CX ↑
      ≈⟨ cleft assoc ⟩
    (CZ02 ^ (p-1 Nat.* e) • (Mg ^ j • CZ)) • CX ↑
      ≈⟨ cleft cright (lemma-Mgᵏ-CZ j) ⟩
    (CZ02 ^ (p-1 Nat.* e) • (CZ ^ e • Mg ^ j)) • CX ↑
      ≈⟨ cleft sym assoc ⟩
    ((CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • Mg ^ j) • CX ↑
      ≈⟨ assoc ⟩
    (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • (Mg ^ j • CX ↑)
      ≈⟨ cright (lemma-Mgᵏ-CX↑ j) ⟩
    (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • (CX ↑ • Mg ^ j)
      ≈⟨ sym assoc ⟩
    ((CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑) • Mg ^ j ∎)
    where
    e = toℕ (g ^′ j)
    rescale : Mg ^ j • CZ02⁻ ≈ CZ02 ^ (p-1 Nat.* e) • Mg ^ j
    rescale = begin
      Mg ^ j • CZ02 ^ p-1
        ≈⟨ lemma-Induction (lemma-Mgᵏ-CZ02 j) p-1 ⟩
      (CZ02 ^ e) ^ p-1 • Mg ^ j
        ≈⟨ cleft (^^ CZ02 e p-1) ⟩
      CZ02 ^ (e Nat.* p-1) • Mg ^ j
        ≡⟨ Eq.cong (λ m → CZ02 ^ m • Mg ^ j) (NP.*-comm e p-1) ⟩
      CZ02 ^ (p-1 Nat.* e) • Mg ^ j ∎

  -- (C): the two CZs distribute over the rescaled power.
  lemma-C : ∀ j → let e = toℕ (g ^′ j) in
            (CZ02⁻ • CZ) ^ e ≈ CZ02 ^ (p-1 Nat.* e) • CZ ^ e
  lemma-C j = •-cancelʳ {h = CX ↑} (begin
    (CZ02⁻ • CZ) ^ e • CX ↑                 ≈⟨ sym (lemma-C18ᵏ e) ⟩
    CX ↑ • CZ ^ e                           ≈⟨ lemma-A j ⟩
    (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑ ∎)
    where e = toℕ (g ^′ j)

  ------------------------------------------------------------------------
  -- The two CZs sharing a wire commute
  --
  -- This is the progress report's C15, its Lemma 9.  Since g generates
  -- the units, some power of it is 2, and (C) at that exponent reads
  --
  --     (CZ • CZ02) • (CZ • CZ02)  ≈  (CZ • CZ) • (CZ02 • CZ02)
  --
  -- Cancelling a CZ on the left and a CZ02 on the right is the whole of
  -- the rest.  Nothing here is circular: the multiplier rescaling is an
  -- input from outside the CZ/CZ02 family, which is exactly why the
  -- report inserts M₂ • M½.

  -- (exported, not private: the other half of the split uses these)
  ₂ᵤ : ℤ* ₚ
  ₂ᵤ = (2ₚ , λ ())
    where
    2ₚ : ℤ ₚ
    2ₚ = ₂

  -- The power of g that is 2.
  j₂ : ℕ
  j₂ = toℕ (g-gen ₂ᵤ .proj₁)

  e₂ : toℕ (g ^′ j₂) ≡ 2
  e₂ = Eq.cong toℕ (Eq.sym (g-gen ₂ᵤ .proj₂))

  -- (C) with the exponent evaluated.
  lemma-C₂ : (CZ02⁻ • CZ) • (CZ02⁻ • CZ) ≈ (CZ02⁻ • CZ02⁻) • (CZ • CZ)
  lemma-C₂ = begin
    (CZ02⁻ • CZ) • (CZ02⁻ • CZ)
      ≡⟨ Eq.cong ((CZ02⁻ • CZ) ^_) (Eq.sym e₂) ⟩
    (CZ02⁻ • CZ) ^ toℕ (g ^′ j₂)
      ≈⟨ lemma-C j₂ ⟩
    CZ02 ^ (p-1 Nat.* toℕ (g ^′ j₂)) • CZ ^ toℕ (g ^′ j₂)
      ≡⟨ Eq.cong₂ (λ a b → CZ02 ^ (p-1 Nat.* a) • CZ ^ b) e₂ e₂ ⟩
    CZ02 ^ (p-1 Nat.* 2) • (CZ • CZ)
      ≈⟨ cleft sym (^^ CZ02 p-1 2) ⟩
    (CZ02⁻ • CZ02⁻) • (CZ • CZ) ∎

  -- Cancelling one CZ02 ⁻¹ on the left and one CZ on the right.  All
  -- explicit assoc: CZ02 ⁻¹ is a symbolic power, so to-list is stuck.
  lemma-comm-CZ-CZ02⁻ : CZ • CZ02⁻ ≈ CZ02⁻ • CZ
  lemma-comm-CZ-CZ02⁻ =
    •-cancelˡ {g = CZ02⁻} (•-cancelʳ {h = CZ} (begin
      (CZ02⁻ • (CZ • CZ02⁻)) • CZ
        ≈⟨ cleft sym assoc ⟩
      ((CZ02⁻ • CZ) • CZ02⁻) • CZ
        ≈⟨ assoc ⟩
      (CZ02⁻ • CZ) • (CZ02⁻ • CZ)
        ≈⟨ lemma-C₂ ⟩
      (CZ02⁻ • CZ02⁻) • (CZ • CZ)
        ≈⟨ assoc ⟩
      CZ02⁻ • (CZ02⁻ • (CZ • CZ))
        ≈⟨ cright sym assoc ⟩
      CZ02⁻ • ((CZ02⁻ • CZ) • CZ)
        ≈⟨ sym assoc ⟩
      (CZ02⁻ • (CZ02⁻ • CZ)) • CZ ∎))

  lemma-CZ02⁻-CZ02 : CZ02⁻ • CZ02 ≈ ε
  lemma-CZ02⁻-CZ02 = begin
    CZ02 ^ p-1 • CZ02
      ≈⟨ sym (^-+ CZ02 p-1 1) ⟩
    CZ02 ^ (p-1 Nat.+ 1)
      ≡⟨ Eq.cong (CZ02 ^_) (NP.+-comm p-1 1) ⟩
    CZ02 ^ (1 Nat.+ p-1)
      ≈⟨ lemma-order-CZ02 ⟩
    ε ∎

  -- CZ commutes with CZ02 ⁻¹, hence with CZ02.
  lemma-comm-CZ-CZ02 : CZ • CZ02 ≈ CZ02 • CZ
  lemma-comm-CZ-CZ02 = begin
    CZ • CZ02
      ≈⟨ cleft sym left-unit ⟩
    (ε • CZ) • CZ02
      ≈⟨ cleft cleft sym lemma-CZ02-CZ02⁻ ⟩
    ((CZ02 • CZ02⁻) • CZ) • CZ02
      ≈⟨ cleft assoc ⟩
    (CZ02 • (CZ02⁻ • CZ)) • CZ02
      ≈⟨ cleft cright sym lemma-comm-CZ-CZ02⁻ ⟩
    (CZ02 • (CZ • CZ02⁻)) • CZ02
      ≈⟨ cleft sym assoc ⟩
    ((CZ02 • CZ) • CZ02⁻) • CZ02
      ≈⟨ assoc ⟩
    (CZ02 • CZ) • (CZ02⁻ • CZ02)
      ≈⟨ cright lemma-CZ02⁻-CZ02 ⟩
    (CZ02 • CZ) • ε
      ≈⟨ right-unit ⟩
    CZ02 • CZ ∎

  T : Word (Gen (₃₊ n))
  T = Ex • Ex ↑ • Ex

  lemma-Ex↑-Ex↑ : Ex ↑ • Ex ↑ ≈ ε
  lemma-Ex↑-Ex↑ = lemma-cong↑ _ _ (PB₂.axiom order-Ex)

  ------------------------------------------------------------------------
  -- The swaps generate S₃
  --
  -- order-Ex makes each swap an involution and yang-baxter is the braid
  -- relation, so the 3-cycle σ = Ex • Ex ↑ has order 3.  Both c14 and c15
  -- assert that some element cubes to ε, so this is the shape they have
  -- to be matched against.

  lemma-σ³ : ((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑) ≈ ε
  lemma-σ³ = begin
    ((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑)
      ≈⟨ by-assoc auto ⟩
    Ex • (Ex ↑ • Ex • Ex ↑) • (Ex • Ex ↑)
      ≈⟨ cright cleft axiom yang-baxter ⟩
    Ex • (Ex ↓ • Ex ↑ • Ex ↓) • (Ex • Ex ↑)
      ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • Ex ↑ • (Ex • Ex) • Ex ↑
      ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • Ex ↑ • (Ex • Ex) • Ex ↑
      ≈⟨ left-unit ⟩
    Ex ↑ • (Ex • Ex) • Ex ↑
      ≈⟨ cright cleft lemma-Ex-Ex ⟩
    Ex ↑ • ε • Ex ↑
      ≈⟨ cright left-unit ⟩
    Ex ↑ • Ex ↑
      ≈⟨ lemma-Ex↑-Ex↑ ⟩
    ε ∎

  lemma-T-T : T • T ≈ ε
  lemma-T-T = begin
    (Ex • Ex ↑ • Ex) • (Ex • Ex ↑ • Ex)  ≈⟨ by-assoc auto ⟩
    (Ex • Ex ↑) • (Ex • Ex) • (Ex ↑ • Ex) ≈⟨ cright cleft lemma-Ex-Ex ⟩
    (Ex • Ex ↑) • ε • (Ex ↑ • Ex)         ≈⟨ cright left-unit ⟩
    (Ex • Ex ↑) • (Ex ↑ • Ex)             ≈⟨ by-assoc auto ⟩
    Ex • (Ex ↑ • Ex ↑) • Ex               ≈⟨ cright cleft lemma-Ex↑-Ex↑ ⟩
    Ex • ε • Ex                           ≈⟨ cright left-unit ⟩
    Ex • Ex                               ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  lemma-T-CZ : T • CZ • T ≈ CZ ↑
  lemma-T-CZ = begin
    (Ex • Ex ↑ • Ex) • CZ • (Ex • Ex ↑ • Ex)
      ≈⟨ by-assoc auto ⟩
    (Ex • Ex ↑) • (Ex • CZ) • (Ex • Ex ↑ • Ex)
      ≈⟨ cright cleft lemma-Ex-CZ ⟩
    (Ex • Ex ↑) • (CZ • Ex) • (Ex • Ex ↑ • Ex)
      ≈⟨ by-assoc auto ⟩
    (Ex ↓ • Ex ↑ • CZ) • (Ex • Ex) • (Ex ↑ • Ex)
      ≈⟨ cleft axiom cz-slide ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • (Ex • Ex) • (Ex ↑ • Ex)
      ≈⟨ cright cleft lemma-Ex-Ex ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • ε • (Ex ↑ • Ex)
      ≈⟨ cright left-unit ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • (Ex ↑ • Ex)
      ≈⟨ by-assoc auto ⟩
    CZ ↑ • Ex • (Ex ↑ • Ex ↑) • Ex
      ≈⟨ cright cright cleft lemma-Ex↑-Ex↑ ⟩
    CZ ↑ • Ex • ε • Ex
      ≈⟨ cright cright left-unit ⟩
    CZ ↑ • Ex • Ex
      ≈⟨ cright lemma-Ex-Ex ⟩
    CZ ↑ • ε
      ≈⟨ right-unit ⟩
    CZ ↑ ∎

  ------------------------------------------------------------------------
  -- selinger-c12, by moving the commutation onto the other pair
  --
  -- Simplified-V1 states c12 over the CZs sharing wire 1, whereas
  -- lemma-comm-CZ-CZ02 has the pair sharing wire 0.  The 3-cycle
  -- σ = Ex • Ex ↑ carries one to the other: cz-slide IS the statement
  -- that σ conjugates CZ to CZ ↑, and the companion fact — that it
  -- conjugates CZ02 back to CZ — follows once CZ02 is rewritten with the
  -- other swap, which is again cz-slide.

  -- (exported, not private: later parts of the split use these)
  -- CZ02 through the upper swap rather than the lower one.
  lemma-CZ02' : Ex ↑ • (CZ • Ex ↑) ≈ CZ02
  lemma-CZ02' = •-cancelˡ {g = Ex} (begin
    Ex • (Ex ↑ • (CZ • Ex ↑))   ≈⟨ by-assoc auto ⟩
    (Ex ↓ • Ex ↑ • CZ) • Ex ↑   ≈⟨ cleft axiom cz-slide ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • Ex ↑ ≈⟨ by-assoc auto ⟩
    (CZ ↑ • Ex) • (Ex ↑ • Ex ↑) ≈⟨ cright lemma-Ex↑-Ex↑ ⟩
    (CZ ↑ • Ex) • ε             ≈⟨ right-unit ⟩
    CZ ↑ • Ex                   ≈⟨ sym left-unit ⟩
    ε • (CZ ↑ • Ex)             ≈⟨ cleft sym lemma-Ex-Ex ⟩
    (Ex • Ex) • (CZ ↑ • Ex)     ≈⟨ assoc ⟩
    Ex • (Ex • (CZ ↑ • Ex)) ∎)

  -- The 3-cycle sends the remote CZ back to the lower pair.
  lemma-σ-CZ02 : (Ex • Ex ↑) • CZ02 ≈ CZ • (Ex • Ex ↑)
  lemma-σ-CZ02 = begin
    (Ex • Ex ↑) • CZ02
      ≈⟨ cright sym lemma-CZ02' ⟩
    (Ex • Ex ↑) • (Ex ↑ • (CZ • Ex ↑))
      ≈⟨ by-assoc auto ⟩
    Ex • ((Ex ↑ • Ex ↑) • (CZ • Ex ↑))
      ≈⟨ cright cleft lemma-Ex↑-Ex↑ ⟩
    Ex • (ε • (CZ • Ex ↑))
      ≈⟨ cright left-unit ⟩
    Ex • (CZ • Ex ↑)
      ≈⟨ sym assoc ⟩
    (Ex • CZ) • Ex ↑
      ≈⟨ cleft lemma-Ex-CZ ⟩
    (CZ • Ex) • Ex ↑
      ≈⟨ assoc ⟩
    CZ • (Ex • Ex ↑) ∎

  aux-left : (Ex • Ex ↑) • (CZ • CZ02) ≈ (CZ ↑ • CZ) • (Ex • Ex ↑)
  aux-left = begin
    (Ex • Ex ↑) • (CZ • CZ02)     ≈⟨ sym assoc ⟩
    ((Ex • Ex ↑) • CZ) • CZ02     ≈⟨ cleft by-assoc auto ⟩
    (Ex ↓ • Ex ↑ • CZ) • CZ02     ≈⟨ cleft axiom cz-slide ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • CZ02   ≈⟨ cleft by-assoc auto ⟩
    (CZ ↑ • (Ex • Ex ↑)) • CZ02   ≈⟨ assoc ⟩
    CZ ↑ • ((Ex • Ex ↑) • CZ02)   ≈⟨ cright lemma-σ-CZ02 ⟩
    CZ ↑ • (CZ • (Ex • Ex ↑))     ≈⟨ sym assoc ⟩
    (CZ ↑ • CZ) • (Ex • Ex ↑) ∎

  aux-right : (Ex • Ex ↑) • (CZ02 • CZ) ≈ (CZ • CZ ↑) • (Ex • Ex ↑)
  aux-right = begin
    (Ex • Ex ↑) • (CZ02 • CZ)     ≈⟨ sym assoc ⟩
    ((Ex • Ex ↑) • CZ02) • CZ     ≈⟨ cleft lemma-σ-CZ02 ⟩
    (CZ • (Ex • Ex ↑)) • CZ       ≈⟨ assoc ⟩
    CZ • ((Ex • Ex ↑) • CZ)       ≈⟨ cright by-assoc auto ⟩
    CZ • (Ex ↓ • Ex ↑ • CZ)       ≈⟨ cright axiom cz-slide ⟩
    CZ • (CZ ↑ • Ex ↓ • Ex ↑)     ≈⟨ cright by-assoc auto ⟩
    CZ • (CZ ↑ • (Ex • Ex ↑))     ≈⟨ sym assoc ⟩
    (CZ • CZ ↑) • (Ex • Ex ↑) ∎

  lemma-selinger-c12 : CZ ↑ • CZ ≈ CZ • CZ ↑
  lemma-selinger-c12 = •-cancelʳ {h = Ex • Ex ↑} (begin
    (CZ ↑ • CZ) • (Ex • Ex ↑)   ≈⟨ sym aux-left ⟩
    (Ex • Ex ↑) • (CZ • CZ02)   ≈⟨ cright lemma-comm-CZ-CZ02 ⟩
    (Ex • Ex ↑) • (CZ02 • CZ)   ≈⟨ aux-right ⟩
    (CZ • CZ ↑) • (Ex • Ex ↑) ∎)

  ------------------------------------------------------------------------
  -- The third commuting pair, by conjugating c12 with the 3-cycle
  --
  -- σ = Ex • Ex ↑ conjugates CZ to CZ ↑ (that is cz-slide) and CZ02 back
  -- to CZ (lemma-σ-CZ02).  Since σ ³ ≈ ε, the missing third leg follows:
  -- σ carries CZ ↑ to CZ02, because two steps forward is one step back.
  -- Conjugating c12 by σ then turns "CZ ↑ against CZ" into "CZ02 against
  -- CZ ↑", the pair the other half of c13 needs.

  -- (exported, not private: the other half of the split uses these)
  lemma-σ-CZ : (Ex • Ex ↑) • CZ ≈ CZ ↑ • (Ex • Ex ↑)
  lemma-σ-CZ = begin
    (Ex • Ex ↑) • CZ    ≈⟨ by-assoc auto ⟩
    Ex ↓ • Ex ↑ • CZ    ≈⟨ axiom cz-slide ⟩
    CZ ↑ • Ex ↓ • Ex ↑  ≈⟨ by-assoc auto ⟩
    CZ ↑ • (Ex • Ex ↑) ∎

  lemma-σ-CZ↑ : (Ex • Ex ↑) • CZ ↑ ≈ CZ02 • (Ex • Ex ↑)
  lemma-σ-CZ↑ =
    •-cancelʳ {h = (Ex • Ex ↑) • (Ex • Ex ↑)} (begin
      ((Ex • Ex ↑) • CZ ↑) • ((Ex • Ex ↑) • (Ex • Ex ↑))
        ≈⟨ by-assoc auto ⟩
      (Ex • Ex ↑) • (((CZ ↑ • (Ex • Ex ↑))) • (Ex • Ex ↑))
        ≈⟨ cright cleft sym lemma-σ-CZ ⟩
      (Ex • Ex ↑) • (((Ex • Ex ↑) • CZ) • (Ex • Ex ↑))
        ≈⟨ cright assoc ⟩
      (Ex • Ex ↑) • ((Ex • Ex ↑) • (CZ • (Ex • Ex ↑)))
        ≈⟨ cright cright sym lemma-σ-CZ02 ⟩
      (Ex • Ex ↑) • ((Ex • Ex ↑) • ((Ex • Ex ↑) • CZ02))
        ≈⟨ by-assoc auto ⟩
      (((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑)) • CZ02
        ≈⟨ cleft lemma-σ³ ⟩
      ε • CZ02
        ≈⟨ left-unit ⟩
      CZ02
        ≈⟨ sym right-unit ⟩
      CZ02 • ε
        ≈⟨ cright sym lemma-σ³ ⟩
      CZ02 • (((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑))
        ≈⟨ by-assoc auto ⟩
      (CZ02 • (Ex • Ex ↑)) • ((Ex • Ex ↑) • (Ex • Ex ↑)) ∎)

  lemma-comm-CZ↑-CZ02 : CZ ↑ • CZ02 ≈ CZ02 • CZ ↑
  lemma-comm-CZ↑-CZ02 = •-cancelʳ {h = Ex • Ex ↑} (begin
    (CZ ↑ • CZ02) • (Ex • Ex ↑)
      ≈⟨ assoc ⟩
    CZ ↑ • (CZ02 • (Ex • Ex ↑))
      ≈⟨ cright sym lemma-σ-CZ↑ ⟩
    CZ ↑ • ((Ex • Ex ↑) • CZ ↑)
      ≈⟨ sym assoc ⟩
    (CZ ↑ • (Ex • Ex ↑)) • CZ ↑
      ≈⟨ cleft sym lemma-σ-CZ ⟩
    ((Ex • Ex ↑) • CZ) • CZ ↑
      ≈⟨ assoc ⟩
    (Ex • Ex ↑) • (CZ • CZ ↑)
      ≈⟨ cright sym lemma-selinger-c12 ⟩
    (Ex • Ex ↑) • (CZ ↑ • CZ)
      ≈⟨ sym assoc ⟩
    ((Ex • Ex ↑) • CZ ↑) • CZ
      ≈⟨ cleft lemma-σ-CZ↑ ⟩
    (CZ02 • (Ex • Ex ↑)) • CZ
      ≈⟨ assoc ⟩
    CZ02 • ((Ex • Ex ↑) • CZ)
      ≈⟨ cright lemma-σ-CZ ⟩
    CZ02 • (CZ ↑ • (Ex • Ex ↑))
      ≈⟨ sym assoc ⟩
    (CZ02 • CZ ↑) • (Ex • Ex ↑) ∎)

  ------------------------------------------------------------------------
  -- The lower half-swap commutes with the upper CZ
  --
  -- ₕ|ₕ is H • CZ • H, all on wires 0 and 1.  The H commutes with CZ ↑
  -- structurally — it is a one-wire gate against a gate shifted off wire
  -- 0 — and the two CZs commute by c12, which is now available.  This is
  -- what makes c13 collapse.

  lemma-comm-ₕ|ₕ-CZ↑ : ₕ|ₕ • CZ ↑ ≈ CZ ↑ • ₕ|ₕ
  lemma-comm-ₕ|ₕ-CZ↑ = begin
    (H • CZ • H) • CZ ↑
      ≈⟨ by-assoc auto ⟩
    H • (CZ • (H • CZ ↑))
      ≈⟨ cright cright sym (axiom comm-H) ⟩
    H • (CZ • (CZ ↑ • H))
      ≈⟨ cright sym assoc ⟩
    H • ((CZ • CZ ↑) • H)
      ≈⟨ cright cleft sym lemma-selinger-c12 ⟩
    H • ((CZ ↑ • CZ) • H)
      ≈⟨ by-assoc auto ⟩
    (H • CZ ↑) • (CZ • H)
      ≈⟨ cleft sym (axiom comm-H) ⟩
    (CZ ↑ • H) • (CZ • H)
      ≈⟨ by-assoc auto ⟩
    CZ ↑ • (H • CZ • H) ∎

  ------------------------------------------------------------------------
  -- Half of c13: conjugating the upper CZ by the half-swaps gives CZ02
  --
  -- With ⊥⊤ = Ex • ₕ|ₕ and ⊤⊥ = ₕ|ₕ • Ex, the word ⊥⊤ • CZ ↑ • ⊤⊥ is
  -- Ex • (ₕ|ₕ • CZ ↑ • ₕ|ₕ) • Ex; the previous lemma moves CZ ↑ out
  -- through one ₕ|ₕ, the involution kills the pair, and what is left is
  -- Ex • CZ ↑ • Ex, which is CZ02 by definition.
  --
  -- Semantically both sides of c13 are CZ02 — that is how this shape was
  -- found — so the other half is the same statement about the upper pair.

