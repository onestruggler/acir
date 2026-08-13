{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The rest of the one-wire Pauli calculus, ported from
-- Simplified-V1.LemmasXZ.
--
-- Paper-V0 and Simplified-V1 have the SAME six one-wire axioms —
-- order-S, order-H, M-power, semi-MR, order-SH, comm-HHSHHS — so every
-- one-wire lemma of V1 holds here by the same proof.  Paper-V0.Lemmas
-- already ports the ones its two-wire chains needed; this file ports the
-- remainder, up to
--
--     conj-S-X       : S • X ≈ (X • Z) • S
--     lemma-comm-X-Z : X • Z ≈ Z • X
--
-- which is where the interesting content is.  X and Z commuting is NOT
-- an axiom of either rule set: it comes out of order-SH together with
-- M-power, which make both (S • H) ^ 3 and (R • H) ^ 3 trivial for the
-- two elements S and R = S • Z ^ ½ that differ by a Pauli.  Cancelling
-- the (S • H) ^ 3 out of the second leaves a residue in which Z ^ ½ and
-- X ^ ½ commute, and X, Z are their squares.
--
-- Proof terms are V1's, unchanged, except for one step of lemma-SX that
-- used V1's Sim-Rewriting tactic to replace H by H ^ 5; aux-H⁵ does that
-- by hand instead, so this file needs no tactic module.
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

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.LemmasXZ
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
  using (module One-Wire ; module One-Wire-Group ; module Paper-GroupLike
        ; lemma-pow-mod)

open Clifford-Relations
open Lemmas-Clifford using (lemma-Induction ; lemma-Inductionˡ)

module Lemmas1b (n : ℕ) where

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open One-Wire n
  open One-Wire-Group n
  open Group-Lemmas ((₁₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₁₊ n})
    using (•-cancelʳ ; •-cancelˡ ; inverseˡ)
  open Basis-Change _ ((₁₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₁₊ n})

  ----------------------------------------------------------------------
  -- Inverses of the Paulis

  aux-Z⁻¹⁻¹ : Z⁻¹ ^ p-1 ≈ Z
  aux-Z⁻¹⁻¹ = •-cancelʳ {h = Z⁻¹} aux00
    where
    aux00 : Z⁻¹ ^ p-1 • Z⁻¹ ≈ Z • Z⁻¹
    aux00 = begin
      Z⁻¹ ^ p-1 • Z⁻¹    ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
      Z⁻¹ • Z⁻¹ ^ p-1    ≈⟨ refl ⟩
      Z⁻¹ ^ p            ≈⟨ ^^ Z p-1 p ⟩
      Z ^ (p-1 Nat.* p)  ≡⟨ Eq.cong (Z ^_) (NP.*-comm p-1 p) ⟩
      Z ^ (p Nat.* p-1)  ≈⟨ sym (^^ Z p p-1) ⟩
      (Z ^ p) ^ p-1      ≈⟨ ^-cong (Z ^ p) ε p-1 lemma-order-Z ⟩
      ε ^ p-1            ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε                  ≈⟨ sym lemma-order-Z ⟩
      Z • Z⁻¹ ∎

  aux-X⁻¹⁻¹ : X⁻¹ ^ p-1 ≈ X
  aux-X⁻¹⁻¹ = •-cancelʳ {h = X⁻¹} aux00
    where
    aux00 : X⁻¹ ^ p-1 • X⁻¹ ≈ X • X⁻¹
    aux00 = begin
      X⁻¹ ^ p-1 • X⁻¹    ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
      X⁻¹ • X⁻¹ ^ p-1    ≈⟨ refl ⟩
      X⁻¹ ^ p            ≈⟨ ^^ X p-1 p ⟩
      X ^ (p-1 Nat.* p)  ≡⟨ Eq.cong (X ^_) (NP.*-comm p-1 p) ⟩
      X ^ (p Nat.* p-1)  ≈⟨ sym (^^ X p p-1) ⟩
      (X ^ p) ^ p-1      ≈⟨ ^-cong (X ^ p) ε p-1 lemma-order-X ⟩
      ε ^ p-1            ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε                  ≈⟨ sym lemma-order-X ⟩
      X • X⁻¹ ∎

  ----------------------------------------------------------------------
  -- The Euler decomposition of S, and how S moves a Pauli

  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹
  lemma-SHSH = bbc ε (S • H) claim
    where
    claim : ε • (S • H • S • H) • S • H ≈ ε • (H ^ 3 • S⁻¹) • S • H
    claim = begin
      ε • (S • H • S • H) • S • H  ≈⟨ left-unit ⟩
      (S • H • S • H) • S • H      ≈⟨ by-passoc (□ ^ 4 • □ ^ 2) ((□ ^ 2) ^ 3) auto ⟩
      (S • H) ^ 3                  ≈⟨ axiom order-SH ⟩
      ε                            ≈⟨ sym inverseˡ ⟩
      (H ^ 3 • S⁻¹) • S • H        ≈⟨ sym left-unit ⟩
      ε • (H ^ 3 • S⁻¹) • S • H ∎

  lemma-HSHSH : H • S • H • S • H ≈ S⁻¹
  lemma-HSHSH = bbc S ε claim
    where
    claim : S • (H • S • H • S • H) • ε ≈ S • S⁻¹ • ε
    claim = begin
      S • (H • S • H • S • H) • ε  ≈⟨ by-assoc auto ⟩
      (S • H) ^ 3                  ≈⟨ axiom order-SH ⟩
      ε                            ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹                      ≈⟨ sym (cong refl right-unit) ⟩
      S • S⁻¹ • ε ∎

  lemma-HSH : H • S • H ≈ S⁻¹ • H ^ 3 • S⁻¹
  lemma-HSH = bbc S ε claim
    where
    claim : S • (H • S • H) • ε ≈ S • (S⁻¹ • H ^ 3 • S⁻¹) • ε
    claim = begin
      S • (H • S • H) • ε        ≈⟨ cong refl right-unit ⟩
      S • (H • S • H)            ≈⟨ lemma-SHSH ⟩
      H ^ 3 • S⁻¹                ≈⟨ sym left-unit ⟩
      ε • H ^ 3 • S⁻¹            ≈⟨ cleft sym (axiom order-S) ⟩
      (S • S⁻¹) • H ^ 3 • S⁻¹    ≈⟨ assoc ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹)    ≈⟨ sym (cong refl right-unit) ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) • ε ∎

  -- V1 does this step with its Sim-Rewriting tactic; H ^ 5 is H • H ^ 4.
  private
    aux-H⁵ : H ≈ H ^ 5
    aux-H⁵ = begin
      H          ≈⟨ sym right-unit ⟩
      H • ε      ≈⟨ cright sym lemma-order-H ⟩
      H ^ 5 ∎

  lemma-SX : S • X ≈ X • Z • S
  lemma-SX = begin
    S • H • S • H • H • S⁻¹ • H
      ≈⟨ by-passoc (□ ^ 7) (□ ^ 4 • □ ^ 3) auto ⟩
    (S • H • S • H) • H • S⁻¹ • H
      ≈⟨ cleft lemma-SHSH ⟩
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H
      ≈⟨ cright cleft aux-H⁵ ⟩
    (H ^ 3 • S⁻¹) • H ^ 5 • S⁻¹ • H
      ≈⟨ sym (by-passoc (□ ^ 5 • □ • □ ^ 3 • □ ^ 2) ((□ ^ 3 • □) • □ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H)
      ≈⟨ cleft (cright sym left-unit) ⟩
    (H • ε • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H)
      ≈⟨ cleft cright cleft sym (axiom order-S) ⟩
    (H • (S • S⁻¹) • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H)
      ≈⟨ by-passoc ((□ • □ ^ 2 • □ ^ 4) • □ ^ 4) (□ ^ 2 • □ ^ 6 • □ ^ 3) auto ⟩
    (H • S) • (S⁻¹ • H • H • S⁻¹ • H • H) • H ^ 3 • S⁻¹ • H
      ≈⟨ cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH p-1) ⟩
    (H • S) • ((H • H • S⁻¹ • H • H) • S⁻¹) • H ^ 3 • S⁻¹ • H
      ≈⟨ by-passoc (□ ^ 2 • (□ ^ 5 • □) • □ ^ 3) (□ ^ 6 • □ • □ ^ 3 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • H • (S⁻¹ • H ^ 3 • S⁻¹) • H
      ≈⟨ cright cright cleft sym lemma-HSH ⟩
    (H • S • H • H • S⁻¹ • H) • H • (H • S • H) • H
      ≈⟨ by-passoc (□ ^ 6 • □ • □ ^ 3 • □) (□ ^ 6 • □ ^ 5) auto ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H)
      ≈⟨ cright sym right-unit ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • ε
      ≈⟨ cright cright sym (axiom order-S) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S • S⁻¹
      ≈⟨ cright cright comm⇒pow-comm 1 p-1 refl ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S⁻¹ • S
      ≈⟨ cright by-passoc (□ ^ 5 • □ ^ 2) (□ ^ 6 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • S ∎

  conj-S-X : S • X ≈ (X • Z) • S
  conj-S-X = begin
    S • X          ≈⟨ lemma-SX ⟩
    X • Z • S      ≈⟨ sym assoc ⟩
    (X • Z) • S ∎

  ----------------------------------------------------------------------
  -- Moving a Pauli rightward past S and past H

  comm-Z^k-S : ∀ k → Z ^ k • S ≈ S • Z ^ k
  comm-Z^k-S k = lemma-Inductionˡ lemma-comm-Z-S k

  lemma-Z-Z⁻¹ : Z • Z⁻¹ ≈ ε
  lemma-Z-Z⁻¹ = lemma-order-Z

  lemma-XS : X • S ≈ S • X • Z⁻¹
  lemma-XS = sym (begin
    S • X • Z⁻¹          ≈⟨ sym assoc ⟩
    (S • X) • Z⁻¹        ≈⟨ cleft conj-S-X ⟩
    ((X • Z) • S) • Z⁻¹  ≈⟨ assoc ⟩
    (X • Z) • S • Z⁻¹    ≈⟨ cright sym (comm-Z^k-S p-1) ⟩
    (X • Z) • Z⁻¹ • S    ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    X • (Z • Z⁻¹) • S    ≈⟨ cright cleft lemma-Z-Z⁻¹ ⟩
    X • ε • S            ≈⟨ cright left-unit ⟩
    X • S ∎)

  aux-X^-₁ : X^ (- ₁) ≈ X⁻¹
  aux-X^-₁ = refl' (Eq.cong (X ^_)
               (Eq.trans (Eq.cong toℕ (Eq.sym p-1=-1ₚ)) lemma-toℕ-ₚ₋₁))

  aux-X-X⁻¹ : X • X⁻¹ ≈ ε
  aux-X-X⁻¹ = lemma-order-X

  aux-Z⁻¹-Z : Z⁻¹ • Z ≈ ε
  aux-Z⁻¹-Z = begin
    Z⁻¹ • Z  ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
    Z • Z⁻¹  ≈⟨ lemma-Z-Z⁻¹ ⟩
    ε ∎

  lemma-XH : X • H ≈ H • Z⁻¹
  lemma-XH = bbc ε Z claim
    where
    claim : ε • (X • H) • Z ≈ ε • (H • Z⁻¹) • Z
    claim = begin
      ε • (X • H) • Z     ≈⟨ left-unit ⟩
      (X • H) • Z         ≈⟨ assoc ⟩
      X • (H • Z)         ≈⟨ cright conj-H-Z ⟩
      X • (X^ (- ₁) • H)  ≈⟨ cright cleft aux-X^-₁ ⟩
      X • (X⁻¹ • H)       ≈⟨ sym assoc ⟩
      (X • X⁻¹) • H       ≈⟨ cleft aux-X-X⁻¹ ⟩
      ε • H               ≈⟨ left-unit ⟩
      H                   ≈⟨ sym right-unit ⟩
      H • ε               ≈⟨ cright sym aux-Z⁻¹-Z ⟩
      H • Z⁻¹ • Z         ≈⟨ sym assoc ⟩
      (H • Z⁻¹) • Z       ≈⟨ sym left-unit ⟩
      ε • (H • Z⁻¹) • Z ∎

  conj-X^k-H : ∀ k → X ^ k • H ≈ H • Z⁻¹ ^ k
  conj-X^k-H k = lemma-Inductionˡ lemma-XH k

  ----------------------------------------------------------------------
  -- Half-powers
  --
  -- ½ as a natural exponent, and the fact that a ½-power squares to the
  -- word itself.

  half : ℕ
  half = toℕ 1/2

  private
    aux-k+k : ∀ (k : ℕ) → k Nat.+ k ≡ k Nat.* 2
    aux-k+k k = Eq.trans
      (Eq.cong₂ Nat._+_ (Eq.sym (NP.*-identityʳ k)) (Eq.sym (NP.*-identityʳ k)))
      (Eq.sym (NP.*-distribˡ-+ k 1 1))

    -- (2ₚ — the modulus of a bare ₂ pinned down — comes from One-Wire.)
    aux-half*2 : 1/2 * 2ₚ ≡ ₁
    aux-half*2 = lemma-⁻¹ˡ 2ₚ {{nztoℕ {y = 2ₚ} {neq0 = λ ()}}}

    aux-half+half : (half Nat.+ half) Nat.% p ≡ 1
    aux-half+half = Eq.trans (Eq.cong (Nat._% p) (aux-k+k half))
                    (Eq.trans (lemma-toℕ-% 1/2 2ₚ) (Eq.cong toℕ aux-half*2))

  aux-half-square : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → w ^ half • w ^ half ≈ w
  aux-half-square w ord = begin
    w ^ half • w ^ half              ≈⟨ sym (^-+ w half half) ⟩
    w ^ (half Nat.+ half)            ≈⟨ lemma-pow-mod ord (half Nat.+ half) ⟩
    w ^ ((half Nat.+ half) Nat.% p)  ≡⟨ Eq.cong (w ^_) aux-half+half ⟩
    w ∎

  aux-order-Z⁻¹ : Z⁻¹ ^ p ≈ ε
  aux-order-Z⁻¹ = lemma-order-w^k Z p p-1 lemma-order-Z

  aux-order-X⁻¹ : X⁻¹ ^ p ≈ ε
  aux-order-X⁻¹ = lemma-order-w^k X p p-1 lemma-order-X

  aux-pow-inverseˡ : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ k →
                     (w ^ p-1) ^ k • w ^ k ≈ ε
  aux-pow-inverseˡ w ord k = begin
    (w ^ p-1) ^ k • w ^ k    ≈⟨ cleft ^^' w p-1 k ⟩
    (w ^ k) ^ p-1 • w ^ k    ≈⟨ sym (^-+ (w ^ k) p-1 1) ⟩
    (w ^ k) ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong ((w ^ k) ^_) (NP.+-comm p-1 1) ⟩
    (w ^ k) ^ p              ≈⟨ lemma-order-w^k w p k ord ⟩
    ε ∎

  aux-pow-inverseʳ : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ k →
                     w ^ k • (w ^ p-1) ^ k ≈ ε
  aux-pow-inverseʳ w ord k = begin
    w ^ k • (w ^ p-1) ^ k  ≈⟨ cright ^^' w p-1 k ⟩
    w ^ k • (w ^ k) ^ p-1  ≈⟨ sym (^-+ (w ^ k) 1 p-1) ⟩
    (w ^ k) ^ p            ≈⟨ lemma-order-w^k w p k ord ⟩
    ε ∎

  ----------------------------------------------------------------------
  -- Conjugation by S • H permutes the three Paulis X, Z ⁻¹ • X ⁻¹, Z

  conj-SH-X : X • (S • H) ≈ (S • H) • (Z⁻¹ • X⁻¹)
  conj-SH-X = begin
    X • (S • H)            ≈⟨ sym assoc ⟩
    (X • S) • H            ≈⟨ cleft lemma-XS ⟩
    (S • X • Z⁻¹) • H      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) auto ⟩
    S • X • Z⁻¹ • H        ≈⟨ cright cright sym (conj-H-X^k p-1) ⟩
    S • X • H • X⁻¹        ≈⟨ cright sym assoc ⟩
    S • (X • H) • X⁻¹      ≈⟨ cright cleft lemma-XH ⟩
    S • (H • Z⁻¹) • X⁻¹    ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) auto ⟩
    (S • H) • (Z⁻¹ • X⁻¹) ∎

  aux-X-SHSH : X • ((S • H) • (S • H)) ≈ ((S • H) • (S • H)) • Z
  aux-X-SHSH = begin
    X • ((S • H) • (S • H))
      ≈⟨ cright by-passoc ((□ • □) • (□ • □)) (□ • □ • □ • □) auto ⟩
    X • (S • H • S • H)  ≈⟨ cright lemma-SHSH ⟩
    X • (H ^ 3 • S⁻¹)    ≈⟨ sym assoc ⟩
    (X • H ^ 3) • S⁻¹    ≈⟨ cleft lemma-X-H³ ⟩
    (H ^ 3 • Z) • S⁻¹    ≈⟨ assoc ⟩
    H ^ 3 • (Z • S⁻¹)    ≈⟨ cright comm⇒pow-comm 1 p-1 lemma-comm-Z-S ⟩
    H ^ 3 • (S⁻¹ • Z)    ≈⟨ sym assoc ⟩
    (H ^ 3 • S⁻¹) • Z    ≈⟨ cleft sym lemma-SHSH ⟩
    (S • H • S • H) • Z
      ≈⟨ cleft by-passoc (□ • □ • □ • □) ((□ • □) • (□ • □)) auto ⟩
    ((S • H) • (S • H)) • Z ∎

  conj-SH-Y : (Z⁻¹ • X⁻¹) • (S • H) ≈ (S • H) • Z
  conj-SH-Y = bbc (S • H) ε claim
    where
    claim : (S • H) • (((Z⁻¹ • X⁻¹) • (S • H)) • ε) ≈ (S • H) • (((S • H) • Z) • ε)
    claim = begin
      (S • H) • (((Z⁻¹ • X⁻¹) • (S • H)) • ε)  ≈⟨ cright right-unit ⟩
      (S • H) • ((Z⁻¹ • X⁻¹) • (S • H))        ≈⟨ sym assoc ⟩
      ((S • H) • (Z⁻¹ • X⁻¹)) • (S • H)        ≈⟨ cleft sym conj-SH-X ⟩
      (X • (S • H)) • (S • H)                  ≈⟨ assoc ⟩
      X • ((S • H) • (S • H))                  ≈⟨ aux-X-SHSH ⟩
      ((S • H) • (S • H)) • Z                  ≈⟨ assoc ⟩
      (S • H) • ((S • H) • Z)                  ≈⟨ cright sym right-unit ⟩
      (S • H) • (((S • H) • Z) • ε) ∎

  conj-SH-X^k : ∀ k → X ^ k • (S • H) ≈ (S • H) • (Z⁻¹ • X⁻¹) ^ k
  conj-SH-X^k = lemma-Inductionˡ conj-SH-X

  conj-SH-Y^k : ∀ k → (Z⁻¹ • X⁻¹) ^ k • (S • H) ≈ (S • H) • Z ^ k
  conj-SH-Y^k = lemma-Inductionˡ conj-SH-Y

  aux-order-Y : (Z⁻¹ • X⁻¹) ^ p ≈ ε
  aux-order-Y = bbc (S • H) ε claim
    where
    claim : (S • H) • ((Z⁻¹ • X⁻¹) ^ p • ε) ≈ (S • H) • (ε • ε)
    claim = begin
      (S • H) • ((Z⁻¹ • X⁻¹) ^ p • ε)  ≈⟨ cright right-unit ⟩
      (S • H) • (Z⁻¹ • X⁻¹) ^ p        ≈⟨ sym (conj-SH-X^k p) ⟩
      X ^ p • (S • H)                  ≈⟨ cleft lemma-order-X ⟩
      ε • (S • H)                      ≈⟨ left-unit ⟩
      S • H                            ≈⟨ sym right-unit ⟩
      (S • H) • ε                      ≈⟨ cright sym left-unit ⟩
      (S • H) • (ε • ε) ∎

  ----------------------------------------------------------------------
  -- (R • H) ^ 3 is trivial, and X and Z commute
  --
  -- R • H is (S • H) • X ^ ½, so cubing it and collecting the three
  -- X ^ ½ through the two conjugations above leaves (S • H) ^ 3 times a
  -- residue.  order-SH kills the first factor and M-power the whole
  -- thing, so the residue is trivial — and reading it as a factorisation
  -- of (Z ⁻¹ • X ⁻¹) ^ ½ makes the two half-powers commute.

  aux-RH : R • H ≈ (S • H) • X ^ half
  aux-RH = begin
    R • H               ≈⟨ assoc ⟩
    S • (Z ^ half • H)  ≈⟨ cright sym (conj-H-X^k half) ⟩
    S • (H • X ^ half)  ≈⟨ sym assoc ⟩
    (S • H) • X ^ half ∎

  lemma-order-RH : (R • H) ^ 3 ≈ ε
  lemma-order-RH = begin
    (R • H) ^ 3
      ≈⟨ by-passoc ((□ ^ 2) ^ 3) (□ • □ • □ • □ • □ • □) auto ⟩
    R • H • R • H • R • H
      ≈⟨ cright cright cleft aux-R ⟩
    R^ x • H • R^ x⁻¹ • H • R^ x • H
      ≈⟨ refl ⟩
    M x'
      ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    x' : ℤ* ₚ
    x' = (₁ , λ ())
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁)
    aux-R : R ≈ R^ x⁻¹
    aux-R = begin
      R       ≈⟨ refl ⟩
      R^ ₁    ≡⟨ Eq.cong R^ (Eq.sym aux₁⁻¹') ⟩
      R^ x⁻¹ ∎

  aux-collect : (R • H) ^ 3 ≈ Z ^ half • ((Z⁻¹ • X⁻¹) ^ half • X ^ half)
  aux-collect = begin
    (R • H) ^ 3
      ≈⟨ ^-cong (R • H) ((S • H) • X ^ half) 3 aux-RH ⟩
    ((S • H) • X ^ half) ^ 3
      ≈⟨ by-passoc ((□ ^ 2 • □) ^ 3)
                   (□ ^ 2 • ((□ • □ ^ 2) • ((□ • □ ^ 2) • □))) auto ⟩
    (S • H) • ((X ^ half • (S • H)) • ((X ^ half • (S • H)) • X ^ half))
      ≈⟨ cright cleft conj-SH-X^k half ⟩
    (S • H) • (((S • H) • (Z⁻¹ • X⁻¹) ^ half) • ((X ^ half • (S • H)) • X ^ half))
      ≈⟨ cright cright cleft conj-SH-X^k half ⟩
    (S • H) • (((S • H) • (Z⁻¹ • X⁻¹) ^ half) • (((S • H) • (Z⁻¹ • X⁻¹) ^ half) • X ^ half))
      ≈⟨ by-passoc (□ ^ 2 • ((□ ^ 2 • □) • ((□ ^ 2 • □) • □)))
                   (□ ^ 2 • (□ ^ 2 • ((□ • □ ^ 2) • (□ • □)))) auto ⟩
    (S • H) • ((S • H) • (((Z⁻¹ • X⁻¹) ^ half • (S • H)) • ((Z⁻¹ • X⁻¹) ^ half • X ^ half)))
      ≈⟨ cright cright cleft conj-SH-Y^k half ⟩
    (S • H) • ((S • H) • (((S • H) • Z ^ half) • ((Z⁻¹ • X⁻¹) ^ half • X ^ half)))
      ≈⟨ by-passoc (□ ^ 2 • (□ ^ 2 • ((□ ^ 2 • □) • (□ • □))))
                   ((□ ^ 2) ^ 3 • (□ • □ • □)) auto ⟩
    (S • H) ^ 3 • (Z ^ half • ((Z⁻¹ • X⁻¹) ^ half • X ^ half))
      ≈⟨ cleft axiom order-SH ⟩
    ε • (Z ^ half • ((Z⁻¹ • X⁻¹) ^ half • X ^ half))
      ≈⟨ left-unit ⟩
    Z ^ half • ((Z⁻¹ • X⁻¹) ^ half • X ^ half) ∎

  lemma-half-residue : Z ^ half • ((Z⁻¹ • X⁻¹) ^ half • X ^ half) ≈ ε
  lemma-half-residue = trans (sym aux-collect) lemma-order-RH

  aux-half-Y : Z⁻¹ ^ half • X⁻¹ ^ half ≈ (Z⁻¹ • X⁻¹) ^ half
  aux-half-Y = begin
    Z⁻¹ ^ half • X⁻¹ ^ half
      ≈⟨ cleft sym right-unit ⟩
    (Z⁻¹ ^ half • ε) • X⁻¹ ^ half
      ≈⟨ cleft cright sym lemma-half-residue ⟩
    (Z⁻¹ ^ half • (Z ^ half • ((Z⁻¹ • X⁻¹) ^ half • X ^ half))) • X⁻¹ ^ half
      ≈⟨ by-passoc ((□ • □ • □ • □) • □) (((□ • □) • □) • (□ • □)) auto ⟩
    ((Z⁻¹ ^ half • Z ^ half) • (Z⁻¹ • X⁻¹) ^ half) • (X ^ half • X⁻¹ ^ half)
      ≈⟨ cong (cleft aux-pow-inverseˡ Z lemma-order-Z half)
              (aux-pow-inverseʳ X lemma-order-X half) ⟩
    (ε • (Z⁻¹ • X⁻¹) ^ half) • ε
      ≈⟨ right-unit ⟩
    ε • (Z⁻¹ • X⁻¹) ^ half
      ≈⟨ left-unit ⟩
    (Z⁻¹ • X⁻¹) ^ half ∎

  comm-half-Z⁻¹-X⁻¹ : Z⁻¹ ^ half • X⁻¹ ^ half ≈ X⁻¹ ^ half • Z⁻¹ ^ half
  comm-half-Z⁻¹-X⁻¹ = bbc (Z⁻¹ ^ half) (X⁻¹ ^ half) claim
    where
    claim : Z⁻¹ ^ half • ((Z⁻¹ ^ half • X⁻¹ ^ half) • X⁻¹ ^ half)
          ≈ Z⁻¹ ^ half • ((X⁻¹ ^ half • Z⁻¹ ^ half) • X⁻¹ ^ half)
    claim = begin
      Z⁻¹ ^ half • ((Z⁻¹ ^ half • X⁻¹ ^ half) • X⁻¹ ^ half)
        ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) auto ⟩
      (Z⁻¹ ^ half • Z⁻¹ ^ half) • (X⁻¹ ^ half • X⁻¹ ^ half)
        ≈⟨ cong (aux-half-square Z⁻¹ aux-order-Z⁻¹) (aux-half-square X⁻¹ aux-order-X⁻¹) ⟩
      Z⁻¹ • X⁻¹
        ≈⟨ sym (aux-half-square (Z⁻¹ • X⁻¹) aux-order-Y) ⟩
      (Z⁻¹ • X⁻¹) ^ half • (Z⁻¹ • X⁻¹) ^ half
        ≈⟨ sym (cong aux-half-Y aux-half-Y) ⟩
      (Z⁻¹ ^ half • X⁻¹ ^ half) • (Z⁻¹ ^ half • X⁻¹ ^ half)
        ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
      Z⁻¹ ^ half • ((X⁻¹ ^ half • Z⁻¹ ^ half) • X⁻¹ ^ half) ∎

  comm-Z⁻¹-X⁻¹ : Z⁻¹ • X⁻¹ ≈ X⁻¹ • Z⁻¹
  comm-Z⁻¹-X⁻¹ = begin
    Z⁻¹ • X⁻¹
      ≈⟨ sym (cong (aux-half-square Z⁻¹ aux-order-Z⁻¹) (aux-half-square X⁻¹ aux-order-X⁻¹)) ⟩
    (Z⁻¹ ^ half • Z⁻¹ ^ half) • (X⁻¹ ^ half • X⁻¹ ^ half)
      ≈⟨ comm⇒pow-comm 2 2 comm-half-Z⁻¹-X⁻¹ ⟩
    (X⁻¹ ^ half • X⁻¹ ^ half) • (Z⁻¹ ^ half • Z⁻¹ ^ half)
      ≈⟨ cong (aux-half-square X⁻¹ aux-order-X⁻¹) (aux-half-square Z⁻¹ aux-order-Z⁻¹) ⟩
    X⁻¹ • Z⁻¹ ∎

  lemma-comm-X-Z : X • Z ≈ Z • X
  lemma-comm-X-Z = sym (begin
    Z • X                  ≈⟨ sym (cong aux-Z⁻¹⁻¹ aux-X⁻¹⁻¹) ⟩
    Z⁻¹ ^ p-1 • X⁻¹ ^ p-1  ≈⟨ comm⇒pow-comm p-1 p-1 comm-Z⁻¹-X⁻¹ ⟩
    X⁻¹ ^ p-1 • Z⁻¹ ^ p-1  ≈⟨ cong aux-X⁻¹⁻¹ aux-Z⁻¹⁻¹ ⟩
    X • Z ∎)

  comm-X-Z^k : ∀ k → X • Z ^ k ≈ Z ^ k • X
  comm-X-Z^k k = lemma-Induction lemma-comm-X-Z k
