{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Paper-V0's swap rules, inside Simplified-V1.
--
-- Paper-V0 axiomatises the two- and three-wire layer through the swap Ex
-- and the controlled-X; Simplified-V1 never writes Ex anywhere.  Its
-- rules are nevertheless theorems there, and this module derives them —
-- not by a new syntactic chain, but by transport along presentations
-- that already exist.  The route is
--
--   Symplectic  →  Symplectic.Simplified  →  SemiDirect  →  Simplified-V1
--
-- and every step is somebody else's theorem:
--
--   * the Ex calculus is proved in the symplectic tree (Lemmas/Ex-Sym*),
--     over the ORIGINAL symplectic rules;
--   * Symplectic.Simplified.Iso says the original and the simplified
--     symplectic rules present the same group, by the identity on words;
--   * the SemiDirect presentation of Pauli ⋊ Sp has the simplified
--     symplectic relation as the right half of an amalgamation, so a
--     symplectic theorem is a SemiDirect theorem about [_]ᵣ of it;
--   * Simplified-V1.Forward carries SemiDirect into Simplified-V1 along
--     f, which sends the symplectic S to R = S • Z ^ ½.
--
-- The last step is why this works at all: Simplified-V1's rules are the
-- symplectic ones written over R rather than S, which is exactly what f
-- does.  A rule with no S in it — and Ex, CX, CZ02 and the three-wire
-- relators are all words in H and CZ alone — is therefore carried to
-- itself, and the transport is the identity on the statement.
--
-- Rules that DO mention S are not covered here: f sends them to their
-- R-spelling, and the difference is a Pauli that has to be tracked
-- separately.  That is why blake-c12 and semi-Ex-S↑ are absent.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base using (Word ; _•_ ; ε ; _^_ ; [_]ʷ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base using ([_]ᵣ ; ConjRelʷ ; module LeftRightCongruence)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.ExRules
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics
  p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Forward
  p-3 p-prime g* g-gen as FWD

import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Lemmas
  p-3 p-prime g* g-gen as V1L
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.LemmasXZ
  p-3 p-prime g* g-gen as XZL
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.LemmasCZ
  p-3 p-prime g* g-gen as CZL

import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime as XZP
import Examples.Groups.Symplectic.Simplified.Iso p-2 p-prime g* g-gen as SimIso
import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime as ExSym0
import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime as ExSym2
import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n p-2 p-prime as ExSym4

private
  variable
    n : ℕ

module V1R = Clifford-Relations
private module FI = FWD.Iso 0

-- The Pauli words and R are Clifford-Relations', not the gate layer's.
open Clifford-Relations using (Z ; X ; Z⁻¹ ; X⁻¹ ; R)

------------------------------------------------------------------------
-- The three transport steps
--
-- Each is a congruence lifting of a well-definedness proof that already
-- exists: the identity morphism for the first, the right embedding of
-- the amalgamation for the second, and f for the third.

module Transport (m : ℕ) where

  open import Presentation.MorphismId
    (Sym._QRel,_===_ m) (Sim._QRel,_===_ m) using (module Star-Congruence)

  -- Symplectic ⟶ Symplectic.Simplified, by the identity on words.
  sym⇒sim : ∀ {w v} → let open PB (Sym._QRel,_===_ m) using (_≈_) in w ≈ v →
            let open PB (Sim._QRel,_===_ m) renaming (_≈_ to _≈'_) in w ≈' v
  sym⇒sim = Star-Congruence.lemma-id*-cong SimIso.f-well-defined

  -- Symplectic.Simplified ⟶ SemiDirect, along the right embedding.
  open LeftRightCongruence
    (XZP._QRel,_===_ m) (Sim._QRel,_===_ m) (ConjRelʷ (SemiDirect.conj {m}))
    using () renaming (rights to sim⇒sd) public

  -- SemiDirect ⟶ Simplified-V1, along f.
  open PP (SemiDirect._QRel,_===_ m) using (module StarCongruence)
  open StarCongruence (V1R._QRel,_===_ m) FI.f FI.f-well-defined
    using () renaming (fʷ-cong to sd⇒v1) public

------------------------------------------------------------------------
-- Ex is an involution
--
-- The symplectic proof is Ex-Sym2n.lemma-order-Ex-n; everything below is
-- the transport, plus the observation that f fixes Ex.

private
  -- f is the identity on any word with no S in it — for the words used
  -- here this is a computation, since both alphabets are the symplectic
  -- gate set and f sends each of the other two letters to itself.
  f-Ex : (FI.f ʷ) [ Ex {n} ]ᵣ ≡ Ex
  f-Ex = auto

lemma-order-Ex : let open PB (V1R._QRel,_===_ (₂₊ n)) using (_≈_) in
                 Ex ^ 2 ≈ ε
lemma-order-Ex {n} = begin
  Ex ^ 2
    ≡⟨ Eq.sym (Eq.trans (FI.lemma-f*-^ᵣ Ex 2) (Eq.cong (_^ 2) f-Ex)) ⟩
  (FI.f ʷ) [ Ex ^ 2 ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym2.lemma-order-Ex-n {n}))) ⟩
  (FI.f ʷ) ([_]ᵣ {A = XZP.Gen (₂₊ n)} ε)
    ≡⟨ auto ⟩
  ε ∎
  where
  module T = Transport (₂₊ n)
  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid

------------------------------------------------------------------------
-- The swap exchanges the wires
--
-- Ex-Sym2n.lemma-comm-Ex-H-n is the conjugation in the form
-- H ↑ • Ex ≈ Ex • H; Paper-V0 states the other side of it, which follows
-- because Ex is an involution.

lemma-comm-Ex-H : let open PB (V1R._QRel,_===_ (₂₊ n)) using (_≈_) in
                  H ↑ • Ex ≈ Ex • H
lemma-comm-Ex-H {n} = begin
  H ↑ • Ex
    ≡⟨ auto ⟩
  (FI.f ʷ) [ H ↑ • Ex ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym2.lemma-comm-Ex-H-n {n}))) ⟩
  (FI.f ʷ) [ Ex • H ]ᵣ
    ≡⟨ auto ⟩
  Ex • H ∎
  where
  module T = Transport (₂₊ n)
  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid

lemma-semi-Ex-H↑ : let open PB (V1R._QRel,_===_ (₂₊ n)) using (_≈_) in
                   Ex • H ↑ ≈ H • Ex
lemma-semi-Ex-H↑ {n} = begin
  Ex • H ↑
    ≈⟨ sym right-unit ⟩
  (Ex • H ↑) • ε
    ≈⟨ cright sym lemma-order-Ex ⟩
  (Ex • H ↑) • (Ex • Ex)
    ≈⟨ assoc ⟩
  Ex • (H ↑ • (Ex • Ex))
    ≈⟨ cright sym assoc ⟩
  Ex • ((H ↑ • Ex) • Ex)
    ≈⟨ cright cleft lemma-comm-Ex-H ⟩
  Ex • ((Ex • H) • Ex)
    ≈⟨ sym assoc ⟩
  (Ex • (Ex • H)) • Ex
    ≈⟨ cleft sym assoc ⟩
  ((Ex • Ex) • H) • Ex
    ≈⟨ cleft cleft lemma-order-Ex ⟩
  (ε • H) • Ex
    ≈⟨ cleft left-unit ⟩
  H • Ex ∎
  where
  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid

------------------------------------------------------------------------
-- The three-wire rules
--
-- Yang–Baxter and the CZ slide are Ex-Sym4n.lemma-yang-baxter and
-- Ex-Sym4n.lemma-Fig3-C17 verbatim: _↓ is the identity on circuits, so
-- Paper-V0's spelling with Ex ↓ is the same word.

lemma-yang-baxter : let open PB (V1R._QRel,_===_ (₃₊ n)) using (_≈_) in
                    Ex ↑ • Ex ↓ • Ex ↑ ≈ Ex ↓ • Ex ↑ • Ex ↓
lemma-yang-baxter {n} = begin
  Ex ↑ • Ex • Ex ↑
    ≡⟨ auto ⟩
  (FI.f ʷ) [ Ex ↑ • Ex • Ex ↑ ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym4.lemma-yang-baxter {n}))) ⟩
  (FI.f ʷ) [ Ex • Ex ↑ • Ex ]ᵣ
    ≡⟨ auto ⟩
  Ex • Ex ↑ • Ex ∎
  where
  module T = Transport (₃₊ n)
  open PB (V1R._QRel,_===_ (₃₊ n))
  open PP (V1R._QRel,_===_ (₃₊ n))
  open SR word-setoid

lemma-cz-slide : let open PB (V1R._QRel,_===_ (₃₊ n)) using (_≈_) in
                 Ex ↓ • Ex ↑ • CZ ≈ CZ ↑ • Ex ↓ • Ex ↑
lemma-cz-slide {n} = begin
  Ex • Ex ↑ • CZ
    ≡⟨ auto ⟩
  (FI.f ʷ) [ Ex • Ex ↑ • CZ ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym4.lemma-Fig3-C17 {n}))) ⟩
  (FI.f ʷ) [ CZ ↑ • Ex • Ex ↑ ]ᵣ
    ≡⟨ auto ⟩
  CZ ↑ • Ex • Ex ↑ ∎
  where
  module T = Transport (₃₊ n)
  open PB (V1R._QRel,_===_ (₃₊ n))
  open PP (V1R._QRel,_===_ (₃₊ n))
  open SR word-setoid

------------------------------------------------------------------------
-- C18: a CZ through a controlled-X on the pair above it
--
-- Ex-Sym4n.lemma-CX↑-CZ states this as CX ↑ • CZ ≈ CZ • CZ02 ⁻¹ • CX ↑;
-- Paper-V0 states the same relation the other way round, and the two
-- differ only by CZ and CZ02 commuting (Ex-Sym4n.lemma-comm-CZ-CZ02).
--
-- The image of CZ02 ⁻¹ is the only one of these computations that is not
-- a `refl`: it hides a CZ ^ p-1, whose exponent is symbolic, so f has to
-- be pushed through the power by hand.

private
  f-CZ02⁻¹ : (FI.f ʷ) [ CZ02⁻¹ {n} ]ᵣ ≡ CZ02⁻¹
  f-CZ02⁻¹ {n} =
    Eq.cong (λ w → Ex • (w • Ex))
      (Eq.trans (FI.lemma-f*-[w]ᵣ {w = CZ ^ p-1})
                (Eq.cong _↑ (FI.lemma-f*-^ᵣ CZ p-1)))

lemma-CX↑-CZ : let open PB (V1R._QRel,_===_ (₃₊ n)) using (_≈_) in
               CX ↑ • CZ ≈ CZ • CZ02⁻¹ • CX ↑
lemma-CX↑-CZ {n} = begin
  CX ↑ • CZ
    ≡⟨ auto ⟩
  (FI.f ʷ) [ CX ↑ • CZ ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym4.lemma-CX↑-CZ {n}))) ⟩
  (FI.f ʷ) [ CZ • CZ02⁻¹ • CX ↑ ]ᵣ
    ≡⟨ Eq.cong (λ w → CZ • (w • CX ↑)) f-CZ02⁻¹ ⟩
  CZ • CZ02⁻¹ • CX ↑ ∎
  where
  module T = Transport (₃₊ n)
  open PB (V1R._QRel,_===_ (₃₊ n))
  open PP (V1R._QRel,_===_ (₃₊ n))
  open SR word-setoid

lemma-CZ02-CZ02⁻¹ : let open PB (V1R._QRel,_===_ (₃₊ n)) using (_≈_) in
                    CZ02 • CZ02⁻¹ ≈ ε
lemma-CZ02-CZ02⁻¹ {n} = begin
  CZ02 • CZ02⁻¹
    ≡⟨ Eq.sym (Eq.cong (λ w → CZ02 • w) f-CZ02⁻¹) ⟩
  (FI.f ʷ) [ CZ02 • CZ02⁻¹ ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym4.aux-CZ02-CZ02⁻¹ {n}))) ⟩
  (FI.f ʷ) ([_]ᵣ {A = XZP.Gen (₃₊ n)} ε)
    ≡⟨ auto ⟩
  ε ∎
  where
  module T = Transport (₃₊ n)
  open PB (V1R._QRel,_===_ (₃₊ n))
  open PP (V1R._QRel,_===_ (₃₊ n))
  open SR word-setoid

lemma-comm-CZ-CZ02⁻¹ : let open PB (V1R._QRel,_===_ (₃₊ n)) using (_≈_) in
                       CZ • CZ02⁻¹ ≈ CZ02⁻¹ • CZ
lemma-comm-CZ-CZ02⁻¹ {n} = begin
  CZ • CZ02⁻¹
    ≡⟨ Eq.sym (Eq.cong (λ w → CZ • w) f-CZ02⁻¹) ⟩
  (FI.f ʷ) [ CZ • CZ02⁻¹ ]ᵣ
    ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym4.lemma-comm-CZ-CZ02⁻¹ {n}))) ⟩
  (FI.f ʷ) [ CZ02⁻¹ • CZ ]ᵣ
    ≡⟨ Eq.cong (λ w → w • CZ) f-CZ02⁻¹ ⟩
  CZ02⁻¹ • CZ ∎
  where
  module T = Transport (₃₊ n)
  open PB (V1R._QRel,_===_ (₃₊ n))
  open PP (V1R._QRel,_===_ (₃₊ n))
  open SR word-setoid

lemma-semi-CX↑-CZ↓ : let open PB (V1R._QRel,_===_ (₃₊ n)) using (_≈_) in
                     CZ ↓ • CX ↑ ≈ CZ02 • CX ↑ • CZ ↓
lemma-semi-CX↑-CZ↓ {n} = sym (begin
  CZ02 • (CX ↑ • CZ)
    ≈⟨ cright lemma-CX↑-CZ ⟩
  CZ02 • (CZ • (CZ02⁻¹ • CX ↑))
    ≈⟨ cright sym assoc ⟩
  CZ02 • ((CZ • CZ02⁻¹) • CX ↑)
    ≈⟨ cright cleft lemma-comm-CZ-CZ02⁻¹ ⟩
  CZ02 • ((CZ02⁻¹ • CZ) • CX ↑)
    ≈⟨ cright assoc ⟩
  CZ02 • (CZ02⁻¹ • (CZ • CX ↑))
    ≈⟨ sym assoc ⟩
  (CZ02 • CZ02⁻¹) • (CZ • CX ↑)
    ≈⟨ cleft lemma-CZ02-CZ02⁻¹ ⟩
  ε • (CZ • CX ↑)
    ≈⟨ left-unit ⟩
  CZ • CX ↑ ∎)
  where
  open PB (V1R._QRel,_===_ (₃₊ n))
  open PP (V1R._QRel,_===_ (₃₊ n))
  open SR word-setoid

------------------------------------------------------------------------
-- A Pauli through the swap
--
-- The transport stops at the two Paper-V0 rules that mention S, because
-- f sends the symplectic S to R = S • Z ^ ½.  Closing that gap means
-- moving a power of Z across the swap, which is pure Pauli content: the
-- symplectic tree has no Paulis and cannot supply it.
--
-- Ex is CZ • H ↓ • H ↑ three times over, so this is nine crossings, and
-- the Pauli carried along runs
--
--   Z ↑ ↦ Z ↑ ↦ Z ↑ ↦ X ↑ ↦ X ↑ • Z ⁻¹ ↦ X ↑ • X ⁻¹ ↦ Z ↑ ⁻¹ • X ⁻¹
--       ↦ X ⁻¹ ↦ Z ↦ Z
--
-- coming out as a Z on the lower wire.  Each crossing is one of three
-- things: a Pauli-versus-CZ axiom, a conjugation of a Pauli by H, or a
-- structural commutation between the two wires.  Everything is spelled
-- with p-1 powers rather than inverses, so no exponent is ever negative.

module Pauli-Ex (n : ℕ) where

  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid

  private
    module XZ₁ = XZL.Lemmas1b (₁₊ n)   -- the Pauli calculus on wire 0
    module XZ₀ = XZL.Lemmas1b n        -- … and one wire down, to lift

    open Lemmas-Clifford
      using (lemma-comm-H-w↑ ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑
            ; lemma-Inductionˡ ; lemma-↑^)

    -- The composition step: L is the letter of Ex being crossed, W the
    -- rest of it, and the Pauli goes in as P and comes out as R.
    slide : ∀ {P L Q W R} → P • L ≈ L • Q → Q • W ≈ W • R →
            P • (L • W) ≈ (L • W) • R
    slide {P} {L} {Q} {W} {R} e₁ e₂ = begin
      P • (L • W)  ≈⟨ sym assoc ⟩
      (P • L) • W  ≈⟨ cleft e₁ ⟩
      (L • Q) • W  ≈⟨ assoc ⟩
      L • (Q • W)  ≈⟨ cright e₂ ⟩
      L • (W • R)  ≈⟨ sym assoc ⟩
      (L • W) • R ∎

    Z↑⁻¹ : Word (Gen (₂₊ n))
    Z↑⁻¹ = (Z ↑) ^ p-1

    -- The two Paulis being carried sit on different wires, so they pass
    -- each other; both are powers, so the structural rule is iterated
    -- twice and the shift has to be moved across the exponent.
    X⁻¹Z↑⁻¹ : X⁻¹ • Z↑⁻¹ ≈ Z↑⁻¹ • X⁻¹
    X⁻¹Z↑⁻¹ = begin
      X⁻¹ • Z↑⁻¹         ≡⟨ Eq.cong (X⁻¹ •_) (Eq.sym (lemma-↑^ p-1 Z)) ⟩
      X⁻¹ • (Z ^ p-1) ↑  ≈⟨ lemma-Inductionˡ (lemma-comm-X-w↑ (Z ^ p-1)) p-1 ⟩
      (Z ^ p-1) ↑ • X⁻¹  ≡⟨ Eq.cong (_• X⁻¹) (lemma-↑^ p-1 Z) ⟩
      Z↑⁻¹ • X⁻¹ ∎

    Z↑ᵖ : Z↑⁻¹ • Z ↑ ≈ ε
    Z↑ᵖ = begin
      (Z ↑) ^ p-1 • Z ↑      ≈⟨ sym (^-+ (Z ↑) p-1 1) ⟩
      (Z ↑) ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong ((Z ↑) ^_) (NP.+-comm p-1 1) ⟩
      (Z ↑) ^ p              ≡⟨ Eq.sym (lemma-↑^ p Z) ⟩
      (Z ^ p) ↑              ≈⟨ Clifford-Relations.lemma-cong↑ _ _ (CZL.CL.lemma-order-Z n) ⟩
      ε ∎

    -- The nine crossings.

    c₁ : Z ↑ • CZ ≈ CZ • Z ↑
    c₁ = CZL.lemma-comm-Z↑-CZ

    c₂ : Z ↑ • H ≈ H • Z ↑
    c₂ = sym (lemma-comm-H-w↑ Z)

    c₃ : Z ↑ • H ↑ ≈ H ↑ • X ↑
    c₃ = Clifford-Relations.lemma-cong↑ _ _ (PB.sym XZ₀.conj-H-X)

    c₄ : X ↑ • CZ ≈ CZ • (X ↑ • Z⁻¹)
    c₄ = sym (begin
      CZ • (X ↑ • Z⁻¹)
        ≈⟨ sym assoc ⟩
      (CZ • X ↑) • Z⁻¹
        ≈⟨ cleft axiom V1R.rel-X↑-CZ ⟩
      (X ↑ • (Z • CZ)) • Z⁻¹
        ≈⟨ assoc ⟩
      X ↑ • ((Z • CZ) • Z⁻¹)
        ≈⟨ cright assoc ⟩
      X ↑ • (Z • (CZ • Z⁻¹))
        ≈⟨ cright cright sym (comm⇒pow-comm p-1 1 CZL.lemma-comm-Z-CZ) ⟩
      X ↑ • (Z • (Z⁻¹ • CZ))
        ≈⟨ cright sym assoc ⟩
      X ↑ • ((Z • Z⁻¹) • CZ)
        ≈⟨ cright cleft XZ₁.lemma-Z-Z⁻¹ ⟩
      X ↑ • (ε • CZ)
        ≈⟨ cright left-unit ⟩
      X ↑ • CZ ∎)

    c₅ : (X ↑ • Z⁻¹) • H ≈ H • (X ↑ • X⁻¹)
    c₅ = begin
      (X ↑ • Z⁻¹) • H  ≈⟨ assoc ⟩
      X ↑ • (Z⁻¹ • H)  ≈⟨ cright sym (XZ₁.conj-H-X^k p-1) ⟩
      X ↑ • (H • X⁻¹)  ≈⟨ sym assoc ⟩
      (X ↑ • H) • X⁻¹  ≈⟨ cleft sym (lemma-comm-H-w↑ X) ⟩
      (H • X ↑) • X⁻¹  ≈⟨ assoc ⟩
      H • (X ↑ • X⁻¹) ∎

    c₆ : (X ↑ • X⁻¹) • H ↑ ≈ H ↑ • (Z↑⁻¹ • X⁻¹)
    c₆ = begin
      (X ↑ • X⁻¹) • H ↑    ≈⟨ assoc ⟩
      X ↑ • (X⁻¹ • H ↑)    ≈⟨ cright lemma-Inductionˡ (lemma-comm-X-w↑ H) p-1 ⟩
      X ↑ • (H ↑ • X⁻¹)    ≈⟨ sym assoc ⟩
      (X ↑ • H ↑) • X⁻¹    ≈⟨ cleft x↑h↑ ⟩
      (H ↑ • Z↑⁻¹) • X⁻¹   ≈⟨ assoc ⟩
      H ↑ • (Z↑⁻¹ • X⁻¹) ∎
      where
      x↑h↑ : X ↑ • H ↑ ≈ H ↑ • Z↑⁻¹
      x↑h↑ = begin
        X ↑ • H ↑          ≈⟨ Clifford-Relations.lemma-cong↑ _ _ XZ₀.lemma-XH ⟩
        H ↑ • (Z ^ p-1) ↑  ≡⟨ Eq.cong (H ↑ •_) (lemma-↑^ p-1 Z) ⟩
        H ↑ • Z↑⁻¹ ∎

    -- The one crossing where something cancels: the Z ↑ the lower-wire
    -- X emits meets the Z ↑ ⁻¹ already being carried.
    c₇ : (Z↑⁻¹ • X⁻¹) • CZ ≈ CZ • X⁻¹
    c₇ = begin
      (Z↑⁻¹ • X⁻¹) • CZ
        ≈⟨ assoc ⟩
      Z↑⁻¹ • (X⁻¹ • CZ)
        ≈⟨ cright x⁻¹cz ⟩
      Z↑⁻¹ • (CZ • (X⁻¹ • Z ↑))
        ≈⟨ sym assoc ⟩
      (Z↑⁻¹ • CZ) • (X⁻¹ • Z ↑)
        ≈⟨ cleft comm⇒pow-comm p-1 1 CZL.lemma-comm-Z↑-CZ ⟩
      (CZ • Z↑⁻¹) • (X⁻¹ • Z ↑)
        ≈⟨ assoc ⟩
      CZ • (Z↑⁻¹ • (X⁻¹ • Z ↑))
        ≈⟨ cright sym assoc ⟩
      CZ • ((Z↑⁻¹ • X⁻¹) • Z ↑)
        ≈⟨ cright cleft sym X⁻¹Z↑⁻¹ ⟩
      CZ • ((X⁻¹ • Z↑⁻¹) • Z ↑)
        ≈⟨ cright assoc ⟩
      CZ • (X⁻¹ • (Z↑⁻¹ • Z ↑))
        ≈⟨ cright cright Z↑ᵖ ⟩
      CZ • (X⁻¹ • ε)
        ≈⟨ cright right-unit ⟩
      CZ • X⁻¹ ∎
      where
      -- rel-X↓-CZ iterated over the exponent: p-1 copies of the emitted
      -- Z ↑ make a Z ↑ ⁻¹, which is what cancels above.
      cz-x⁻¹ : CZ • X⁻¹ ≈ X⁻¹ • (Z↑⁻¹ • CZ)
      cz-x⁻¹ = aux p-1
        where
        aux : ∀ k → CZ • X ^ k ≈ X ^ k • ((Z ↑) ^ k • CZ)
        aux ₀ = begin
          CZ • ε        ≈⟨ right-unit ⟩
          CZ            ≈⟨ sym left-unit ⟩
          ε • CZ        ≈⟨ sym left-unit ⟩
          ε • (ε • CZ) ∎
        aux ₁ = axiom V1R.rel-X↓-CZ
        aux (₂₊ k) = begin
          CZ • (X • X ^ ₁₊ k)
            ≈⟨ sym assoc ⟩
          (CZ • X) • X ^ ₁₊ k
            ≈⟨ cleft axiom V1R.rel-X↓-CZ ⟩
          (X • (Z ↑ • CZ)) • X ^ ₁₊ k
            ≈⟨ assoc ⟩
          X • ((Z ↑ • CZ) • X ^ ₁₊ k)
            ≈⟨ cright assoc ⟩
          X • (Z ↑ • (CZ • X ^ ₁₊ k))
            ≈⟨ cright cright aux (₁₊ k) ⟩
          X • (Z ↑ • (X ^ ₁₊ k • ((Z ↑) ^ ₁₊ k • CZ)))
            ≈⟨ cright sym assoc ⟩
          X • ((Z ↑ • X ^ ₁₊ k) • ((Z ↑) ^ ₁₊ k • CZ))
            ≈⟨ cright cleft sym (lemma-Inductionˡ (lemma-comm-X-w↑ Z) (₁₊ k)) ⟩
          X • ((X ^ ₁₊ k • Z ↑) • ((Z ↑) ^ ₁₊ k • CZ))
            ≈⟨ cright assoc ⟩
          X • (X ^ ₁₊ k • (Z ↑ • ((Z ↑) ^ ₁₊ k • CZ)))
            ≈⟨ sym assoc ⟩
          (X • X ^ ₁₊ k) • (Z ↑ • ((Z ↑) ^ ₁₊ k • CZ))
            ≈⟨ cright sym assoc ⟩
          (X • X ^ ₁₊ k) • ((Z ↑ • (Z ↑) ^ ₁₊ k) • CZ) ∎

      x⁻¹cz : X⁻¹ • CZ ≈ CZ • (X⁻¹ • Z ↑)
      x⁻¹cz = sym (begin
        CZ • (X⁻¹ • Z ↑)
          ≈⟨ sym assoc ⟩
        (CZ • X⁻¹) • Z ↑
          ≈⟨ cleft cz-x⁻¹ ⟩
        (X⁻¹ • (Z↑⁻¹ • CZ)) • Z ↑
          ≈⟨ assoc ⟩
        X⁻¹ • ((Z↑⁻¹ • CZ) • Z ↑)
          ≈⟨ cright assoc ⟩
        X⁻¹ • (Z↑⁻¹ • (CZ • Z ↑))
          ≈⟨ cright cright sym CZL.lemma-comm-Z↑-CZ ⟩
        X⁻¹ • (Z↑⁻¹ • (Z ↑ • CZ))
          ≈⟨ cright sym assoc ⟩
        X⁻¹ • ((Z↑⁻¹ • Z ↑) • CZ)
          ≈⟨ cright cleft Z↑ᵖ ⟩
        X⁻¹ • (ε • CZ)
          ≈⟨ cright left-unit ⟩
        X⁻¹ • CZ ∎)

    c₈ : X⁻¹ • H ≈ H • Z
    c₈ = begin
      X⁻¹ • H        ≈⟨ XZ₁.conj-X^k-H p-1 ⟩
      H • Z⁻¹ ^ p-1  ≈⟨ cright XZ₁.aux-Z⁻¹⁻¹ ⟩
      H • Z ∎

    c₉ : Z • H ↑ ≈ H ↑ • Z
    c₉ = lemma-comm-Z-w↑ H

  -- Nine crossings, composed.  Ex is nine letters, so the chain is eight
  -- slides over a final crossing.
  lemma-Z↑-Ex : Z ↑ • Ex ≈ Ex • Z
  lemma-Z↑-Ex =
    slide c₁ (slide c₂ (slide c₃ (slide c₄ (slide c₅ (slide c₆ (slide c₇ (slide c₈ c₉)))))))

  lemma-Z↑ᵏ-Ex : ∀ k → (Z ↑) ^ k • Ex ≈ Ex • Z ^ k
  lemma-Z↑ᵏ-Ex k = lemma-Inductionˡ lemma-Z↑-Ex k

------------------------------------------------------------------------
-- The swap and the phase gate
--
-- The transport gives the R-spelling of this rule, since f sends the
-- symplectic S to R.  R is S • Z ^ ½ by definition, and lemma-Z↑ᵏ-Ex
-- puts that Z ^ ½ on the right of BOTH sides — where it cancels.  So the
-- S-spelling is the R-spelling with one right-cancellation.

module Ex-S (n : ℕ) where

  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid
  open Group-Lemmas (V1R._QRel,_===_ (₂₊ n)) (V1L.Clifford-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ)
  open Pauli-Ex n using (lemma-Z↑ᵏ-Ex)
  open Lemmas-Clifford using (lemma-↑^)

  private
    h½ : ℕ
    h½ = toℕ 1/2

    module T = Transport (₂₊ n)

    -- The symplectic rule, transported: f fixes Ex and sends S to R.
    lemma-R↑-Ex : R ↑ • Ex ≈ Ex • R
    lemma-R↑-Ex = begin
      R ↑ • Ex
        ≡⟨ auto ⟩
      (FI.f ʷ) [ S ↑ • Ex ]ᵣ
        ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSym0.Lemmas0a.lemma-comm-Ex-S {n}))) ⟩
      (FI.f ʷ) [ Ex • S ]ᵣ
        ≡⟨ auto ⟩
      Ex • R ∎

  lemma-S↑-Ex : S ↑ • Ex ≈ Ex • S
  lemma-S↑-Ex = •-cancelʳ {h = Z ^ h½} (begin
    (S ↑ • Ex) • Z ^ h½
      ≈⟨ assoc ⟩
    S ↑ • (Ex • Z ^ h½)
      ≈⟨ cright sym (lemma-Z↑ᵏ-Ex h½) ⟩
    S ↑ • ((Z ↑) ^ h½ • Ex)
      ≈⟨ sym assoc ⟩
    (S ↑ • (Z ↑) ^ h½) • Ex
      ≡⟨ Eq.cong (λ w → (S ↑ • w) • Ex) (Eq.sym (lemma-↑^ h½ Z)) ⟩
    (S ↑ • (Z ^ h½) ↑) • Ex
      ≈⟨ lemma-R↑-Ex ⟩
    Ex • R
      ≈⟨ sym assoc ⟩
    (Ex • S) • Z ^ h½ ∎)

  lemma-semi-Ex-S↑ : Ex • S ↑ ≈ S • Ex
  lemma-semi-Ex-S↑ = begin
    Ex • S ↑
      ≈⟨ sym right-unit ⟩
    (Ex • S ↑) • ε
      ≈⟨ cright sym lemma-order-Ex ⟩
    (Ex • S ↑) • (Ex • Ex)
      ≈⟨ assoc ⟩
    Ex • (S ↑ • (Ex • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((S ↑ • Ex) • Ex)
      ≈⟨ cright cleft lemma-S↑-Ex ⟩
    Ex • ((Ex • S) • Ex)
      ≈⟨ sym assoc ⟩
    (Ex • (Ex • S)) • Ex
      ≈⟨ cleft sym assoc ⟩
    ((Ex • Ex) • S) • Ex
      ≈⟨ cleft cleft lemma-order-Ex ⟩
    (ε • S) • Ex
      ≈⟨ cleft left-unit ⟩
    S • Ex ∎
