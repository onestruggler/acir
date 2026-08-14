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
-- Two of the seven rules — semi-Ex-S↑ and blake-c12 — DO mention S, so
-- the transport gives them in the R-spelling and the difference is a
-- Pauli.  Those are the two places where this module has to do its own
-- work, and it is the same work both times: move a Z ^ ½ across the
-- two-wire gate (Pauli-Ex for the swap, Pauli-CX for the controlled-X)
-- and watch the exponents add up to a multiple of p.  The symplectic
-- tree cannot help there — it has no Pauli generators at all.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Product using (_,_ ; ∃ ; proj₁)
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
import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n.Swap p-2 p-prime as ExSwap

private
  variable
    n : ℕ

module V1R = Clifford-Relations
private module FI = FWD.Iso 0

-- The Pauli words, R and the multiplier are Clifford-Relations', not the
-- gate layer's.
open Clifford-Relations using (Z ; X ; Z⁻¹ ; X⁻¹ ; R ; M₋₁)

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

------------------------------------------------------------------------
-- A Pauli through the controlled-X
--
-- The mirror of Paper-V0.Lemmas' lemma-conj-XC-Z↑, and the last thing
-- the transport cannot give.  CX = H ↓ ^ 3 • CZ • H ↓ has its TARGET on
-- wire 0, so it conjugates the wire-0 Z to Z • Z ↑.  As on the other
-- side, the crossings are taken in the directions that emit positive
-- powers, so no exponent is ever negative.

module Pauli-CX (n : ℕ) where

  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid
  open Group-Lemmas (V1R._QRel,_===_ (₂₊ n)) (V1L.Clifford-GroupLike.grouplike {₂₊ n})
    using (•-cancelˡ ; •-cancelʳ)
  open Lemmas-Clifford
    using (lemma-↑^ ; lemma-Inductionˡ ; lemma-comm-Hᵏ-w↑ ; lemma-comm-Z-w↑)

  private
    module XZ₁ = XZL.Lemmas1b (₁₊ n)
    module CL₁ = V1L.Lemmas1 (₁₊ n)
    module CL₀ = V1L.Lemmas1 n

    H³H : H ^ 3 • H ≈ ε
    H³H = begin
      H ^ 3 • H  ≈⟨ sym (^-+ H 3 1) ⟩
      H ^ 4      ≈⟨ CL₁.lemma-order-H ⟩
      ε ∎

    H⁶ : H ^ 3 • H ^ 3 ≈ M₋₁
    H⁶ = begin
      H ^ 3 • H ^ 3  ≈⟨ sym (^-+ H 3 3) ⟩
      H ^ 6          ≈⟨ ^-+ H 4 2 ⟩
      H ^ 4 • H ^ 2  ≈⟨ cleft CL₁.lemma-order-H ⟩
      ε • H ^ 2      ≈⟨ left-unit ⟩
      H ^ 2          ≈⟨ axiom V1R.order-H ⟩
      M₋₁ ∎

    M₋₁H : M₋₁ • H ≈ H ^ 3
    M₋₁H = begin
      M₋₁ • H    ≈⟨ cleft sym (axiom V1R.order-H) ⟩
      H ^ 2 • H  ≈⟨ sym (^-+ H 2 1) ⟩
      H ^ 3 ∎

    M₋₁-CZ' : M₋₁ • CZ ≈ CZ ^ p-1 • M₋₁
    M₋₁-CZ' = begin
      M₋₁ • CZ                       ≈⟨ CZL.lemma-M₋₁-CZ ⟩
      CZ ^ toℕ ((-'₁) .proj₁) • M₋₁  ≡⟨ Eq.cong (λ m → CZ ^ m • M₋₁) lemma-toℕ-1ₚ ⟩
      CZ ^ p-1 • M₋₁ ∎

    Z-conj : Z ≈ H • (X • H ^ 3)
    Z-conj = •-cancelʳ {h = H} (begin
      Z • H                  ≈⟨ sym XZ₁.conj-H-X ⟩
      H • X                  ≈⟨ cright sym right-unit ⟩
      H • (X • ε)            ≈⟨ cright cright sym CL₁.lemma-order-H ⟩
      H • (X • H ^ 4)        ≈⟨ cright cright ^-+ H 3 1 ⟩
      H • (X • (H ^ 3 • H))  ≈⟨ cright sym assoc ⟩
      H • ((X • H ^ 3) • H)  ≈⟨ sym assoc ⟩
      (H • (X • H ^ 3)) • H ∎)

    Z↑ᵖ : (Z ↑) ^ p-1 • Z ↑ ≈ ε
    Z↑ᵖ = begin
      (Z ↑) ^ p-1 • Z ↑      ≈⟨ sym (^-+ (Z ↑) p-1 1) ⟩
      (Z ↑) ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong ((Z ↑) ^_) (NP.+-comm p-1 1) ⟩
      (Z ↑) ^ p              ≡⟨ Eq.sym (lemma-↑^ p Z) ⟩
      (Z ^ p) ↑              ≈⟨ V1R.lemma-cong↑ _ _ CL₀.lemma-order-Z ⟩
      ε ∎

    -- rel-X↓-CZ iterated in the CZ exponent.  The emitted Z ↑'s gather,
    -- because they pass the CZ's still to come.
    czᵏ-x : ∀ j → CZ ^ j • X ≈ X • ((Z ↑) ^ j • CZ ^ j)
    czᵏ-x ₀ = begin
      ε • X        ≈⟨ left-unit ⟩
      X            ≈⟨ sym right-unit ⟩
      X • ε        ≈⟨ cright sym left-unit ⟩
      X • (ε • ε) ∎
    czᵏ-x ₁ = axiom V1R.rel-X↓-CZ
    czᵏ-x (₂₊ j) = begin
      (CZ • CZ ^ ₁₊ j) • X
        ≈⟨ assoc ⟩
      CZ • (CZ ^ ₁₊ j • X)
        ≈⟨ cright czᵏ-x (₁₊ j) ⟩
      CZ • (X • ((Z ↑) ^ ₁₊ j • CZ ^ ₁₊ j))
        ≈⟨ sym assoc ⟩
      (CZ • X) • ((Z ↑) ^ ₁₊ j • CZ ^ ₁₊ j)
        ≈⟨ cleft axiom V1R.rel-X↓-CZ ⟩
      (X • (Z ↑ • CZ)) • ((Z ↑) ^ ₁₊ j • CZ ^ ₁₊ j)
        ≈⟨ assoc ⟩
      X • ((Z ↑ • CZ) • ((Z ↑) ^ ₁₊ j • CZ ^ ₁₊ j))
        ≈⟨ cright assoc ⟩
      X • (Z ↑ • (CZ • ((Z ↑) ^ ₁₊ j • CZ ^ ₁₊ j)))
        ≈⟨ cright cright sym assoc ⟩
      X • (Z ↑ • ((CZ • (Z ↑) ^ ₁₊ j) • CZ ^ ₁₊ j))
        ≈⟨ cright cright cleft sym (comm⇒pow-comm (₁₊ j) 1 CZL.lemma-comm-Z↑-CZ) ⟩
      X • (Z ↑ • (((Z ↑) ^ ₁₊ j • CZ) • CZ ^ ₁₊ j))
        ≈⟨ cright cright assoc ⟩
      X • (Z ↑ • ((Z ↑) ^ ₁₊ j • (CZ • CZ ^ ₁₊ j)))
        ≈⟨ cright sym assoc ⟩
      X • ((Z ↑ • (Z ↑) ^ ₁₊ j) • (CZ • CZ ^ ₁₊ j)) ∎

    x-czᵉ : X • CZ ^ p-1 ≈ CZ ^ p-1 • (X • Z ↑)
    x-czᵉ = sym (begin
      CZ ^ p-1 • (X • Z ↑)
        ≈⟨ sym assoc ⟩
      (CZ ^ p-1 • X) • Z ↑
        ≈⟨ cleft czᵏ-x p-1 ⟩
      (X • ((Z ↑) ^ p-1 • CZ ^ p-1)) • Z ↑
        ≈⟨ assoc ⟩
      X • (((Z ↑) ^ p-1 • CZ ^ p-1) • Z ↑)
        ≈⟨ cright assoc ⟩
      X • ((Z ↑) ^ p-1 • (CZ ^ p-1 • Z ↑))
        ≈⟨ cright cright sym (comm⇒pow-comm 1 p-1 CZL.lemma-comm-Z↑-CZ) ⟩
      X • ((Z ↑) ^ p-1 • (Z ↑ • CZ ^ p-1))
        ≈⟨ cright sym assoc ⟩
      X • (((Z ↑) ^ p-1 • Z ↑) • CZ ^ p-1)
        ≈⟨ cright cleft Z↑ᵖ ⟩
      X • (ε • CZ ^ p-1)
        ≈⟨ cright left-unit ⟩
      X • CZ ^ p-1 ∎)

    -- CX read from the other side: the H ^ 2 the two spellings differ by
    -- is the multiplier by −1, which inverts the CZ it passes.
    CX-flip : H • (CZ ^ p-1 • H ^ 3) ≈ CX
    CX-flip = •-cancelˡ {g = H ^ 3} (begin
      H ^ 3 • (H • (CZ ^ p-1 • H ^ 3))
        ≈⟨ sym assoc ⟩
      (H ^ 3 • H) • (CZ ^ p-1 • H ^ 3)
        ≈⟨ cleft H³H ⟩
      ε • (CZ ^ p-1 • H ^ 3)
        ≈⟨ left-unit ⟩
      CZ ^ p-1 • H ^ 3
        ≈⟨ cright sym M₋₁H ⟩
      CZ ^ p-1 • (M₋₁ • H)
        ≈⟨ sym assoc ⟩
      (CZ ^ p-1 • M₋₁) • H
        ≈⟨ cleft sym M₋₁-CZ' ⟩
      (M₋₁ • CZ) • H
        ≈⟨ cleft cleft sym H⁶ ⟩
      ((H ^ 3 • H ^ 3) • CZ) • H
        ≈⟨ cleft assoc ⟩
      (H ^ 3 • (H ^ 3 • CZ)) • H
        ≈⟨ assoc ⟩
      H ^ 3 • ((H ^ 3 • CZ) • H)
        ≈⟨ cright assoc ⟩
      H ^ 3 • (H ^ 3 • (CZ • H)) ∎)

  lemma-Z-CX : Z • CX ≈ CX • (Z • Z ↑)
  lemma-Z-CX = begin
    Z • CX
      ≈⟨ cleft Z-conj ⟩
    (H • (X • H ^ 3)) • (H ^ 3 • (CZ • H))
      ≈⟨ assoc ⟩
    H • ((X • H ^ 3) • (H ^ 3 • (CZ • H)))
      ≈⟨ cright assoc ⟩
    H • (X • (H ^ 3 • (H ^ 3 • (CZ • H))))
      ≈⟨ cright cright sym assoc ⟩
    H • (X • ((H ^ 3 • H ^ 3) • (CZ • H)))
      ≈⟨ cright cright cleft H⁶ ⟩
    H • (X • (M₋₁ • (CZ • H)))
      ≈⟨ cright cright sym assoc ⟩
    H • (X • ((M₋₁ • CZ) • H))
      ≈⟨ cright cright cleft M₋₁-CZ' ⟩
    H • (X • ((CZ ^ p-1 • M₋₁) • H))
      ≈⟨ cright cright assoc ⟩
    H • (X • (CZ ^ p-1 • (M₋₁ • H)))
      ≈⟨ cright cright cright M₋₁H ⟩
    H • (X • (CZ ^ p-1 • H ^ 3))
      ≈⟨ cright sym assoc ⟩
    H • ((X • CZ ^ p-1) • H ^ 3)
      ≈⟨ cright cleft x-czᵉ ⟩
    H • ((CZ ^ p-1 • (X • Z ↑)) • H ^ 3)
      ≈⟨ cright assoc ⟩
    H • (CZ ^ p-1 • ((X • Z ↑) • H ^ 3))
      ≈⟨ cright cright assoc ⟩
    H • (CZ ^ p-1 • (X • (Z ↑ • H ^ 3)))
      ≈⟨ cright cright cright sym (lemma-comm-Hᵏ-w↑ 3 Z) ⟩
    H • (CZ ^ p-1 • (X • (H ^ 3 • Z ↑)))
      ≈⟨ cright cright sym assoc ⟩
    H • (CZ ^ p-1 • ((X • H ^ 3) • Z ↑))
      ≈⟨ cright cright cleft XZ₁.aux-X-H³ ⟩
    H • (CZ ^ p-1 • ((H ^ 3 • Z) • Z ↑))
      ≈⟨ cright cright assoc ⟩
    H • (CZ ^ p-1 • (H ^ 3 • (Z • Z ↑)))
      ≈⟨ cright sym assoc ⟩
    H • ((CZ ^ p-1 • H ^ 3) • (Z • Z ↑))
      ≈⟨ sym assoc ⟩
    (H • (CZ ^ p-1 • H ^ 3)) • (Z • Z ↑)
      ≈⟨ cleft CX-flip ⟩
    CX • (Z • Z ↑) ∎

  lemma-Zᵏ-CX : ∀ k → Z ^ k • CX ≈ CX • (Z ^ k • (Z ↑) ^ k)
  lemma-Zᵏ-CX k = begin
    Z ^ k • CX
      ≈⟨ lemma-Inductionˡ lemma-Z-CX k ⟩
    CX • (Z • Z ↑) ^ k
      ≈⟨ cright ^-• Z (Z ↑) k (lemma-comm-Z-w↑ Z) ⟩
    CX • (Z ^ k • (Z ↑) ^ k) ∎

------------------------------------------------------------------------
-- blake-c12
--
-- Paper-V0's path-sum decomposition of CZ.  The symplectic tree proves
-- it as Ex-Sym3n.Swap.lemma-semi-CXCZ^-alt; at k = 1 that reads
--
--     CX • CZ ≈ S • CX • S ⁻¹ • S ⁻¹ ↑
--
-- and Paper-V0's spelling is the same relation with the CX moved to the
-- other side.  The transport gives it over R, and the conversion to S is
-- where the Pauli rule above is spent: R = S • Z ^ ½, so the RHS carries
-- four Z ^ ½ factors, and exactly one of them stands to the LEFT of the
-- single CX.  Crossing it doubles that one onto the other wire, and the
-- exponents then add to h • p on each wire, which is zero.

module Blake (n : ℕ) where

  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid
  open Group-Lemmas (V1R._QRel,_===_ (₂₊ n)) (V1L.Clifford-GroupLike.grouplike {₂₊ n})
    using (•-cancelˡ)
  open Lemmas-Clifford
    using (lemma-↑^ ; lemma-Inductionˡ ; lemma-comm-S-w↑ ; lemma-comm-Z-w↑)
  open Pauli-CX n using (lemma-Zᵏ-CX)

  private
    module T = Transport (₂₊ n)
    module CL₁ = V1L.Lemmas1 (₁₊ n)
    module CL₀ = V1L.Lemmas1 n
    module PP₁ = PP (V1R._QRel,_===_ (₁₊ n))

    h : ℕ
    h = toℕ 1/2

    ------------------------------------------------------------------
    -- CX has order p, being a CZ conjugated by H.

    cxᵏ : ∀ k → CX ^ k ≈ H ^ 3 • (CZ ^ k • H)
    cxᵏ ₀ = begin
      ε                  ≈⟨ sym h³h ⟩
      H ^ 3 • H          ≈⟨ cright sym left-unit ⟩
      H ^ 3 • (ε • H) ∎
      where
      h³h : H ^ 3 • H ≈ ε
      h³h = trans (sym (^-+ H 3 1)) CL₁.lemma-order-H
    cxᵏ ₁ = refl
    cxᵏ (₂₊ k) = begin
      CX • CX ^ ₁₊ k
        ≈⟨ cright cxᵏ (₁₊ k) ⟩
      (H ^ 3 • (CZ • H)) • (H ^ 3 • (CZ ^ ₁₊ k • H))
        ≈⟨ assoc ⟩
      H ^ 3 • ((CZ • H) • (H ^ 3 • (CZ ^ ₁₊ k • H)))
        ≈⟨ cright assoc ⟩
      H ^ 3 • (CZ • (H • (H ^ 3 • (CZ ^ ₁₊ k • H))))
        ≈⟨ cright cright sym assoc ⟩
      H ^ 3 • (CZ • ((H • H ^ 3) • (CZ ^ ₁₊ k • H)))
        ≈⟨ cright cright cleft CL₁.lemma-order-H ⟩
      H ^ 3 • (CZ • (ε • (CZ ^ ₁₊ k • H)))
        ≈⟨ cright cright left-unit ⟩
      H ^ 3 • (CZ • (CZ ^ ₁₊ k • H))
        ≈⟨ cright sym assoc ⟩
      H ^ 3 • ((CZ • CZ ^ ₁₊ k) • H) ∎

    CXᵉ-CX : CX ^ p-1 • CX ≈ ε
    CXᵉ-CX = begin
      CX ^ p-1 • CX
        ≈⟨ sym (^-+ CX p-1 1) ⟩
      CX ^ (p-1 Nat.+ 1)
        ≡⟨ Eq.cong (CX ^_) (NP.+-comm p-1 1) ⟩
      CX ^ p
        ≈⟨ cxᵏ p ⟩
      H ^ 3 • (CZ ^ p • H)
        ≈⟨ cright cleft axiom V1R.order-CZ ⟩
      H ^ 3 • (ε • H)
        ≈⟨ cright left-unit ⟩
      H ^ 3 • H
        ≈⟨ sym (^-+ H 3 1) ⟩
      H ^ 4
        ≈⟨ CL₁.lemma-order-H ⟩
      ε ∎

    ------------------------------------------------------------------
    -- The transported symplectic rule, at k = 1.

    T-R : CX • CZ ≈ R • (CX • (R ^ p-1 • (R ↑) ^ p-1))
    T-R = begin
      CX • CZ
        ≡⟨ auto ⟩
      (FI.f ʷ) [ CX • CZ^ 1ₚ ]ᵣ
        ≈⟨ T.sd⇒v1 (T.sim⇒sd (T.sym⇒sim (ExSwap.lemma-semi-CXCZ^-alt {n} 1ₚ))) ⟩
      (FI.f ʷ) [ S^ 1ₚ • CX • S^ (- 1ₚ) • S^ (- 1ₚ) ↑ ]ᵣ
        ≡⟨ Eq.cong₂ (λ a b → R • (CX • (a • b)))
                    (FI.lemma-f*-^ᵣ S (toℕ (- 1ₚ)))
                    (Eq.trans (FI.lemma-f*-[w]ᵣ {w = S ^ toℕ (- 1ₚ)})
                      (Eq.trans (Eq.cong _↑ (FI.lemma-f*-^ᵣ S (toℕ (- 1ₚ))))
                                (lemma-↑^ (toℕ (- 1ₚ)) R))) ⟩
      R • (CX • (R ^ toℕ (- 1ₚ) • (R ↑) ^ toℕ (- 1ₚ)))
        ≡⟨ Eq.cong₂ (λ a b → R • (CX • (R ^ a • (R ↑) ^ b)))
                    lemma-toℕ-1ₚ lemma-toℕ-1ₚ ⟩
      R • (CX • (R ^ p-1 • (R ↑) ^ p-1)) ∎

    ------------------------------------------------------------------
    -- R = S • Z ^ ½ split out of the three places it occurs.

    comm-S-Zʰ : S • Z ^ h ≈ Z ^ h • S
    comm-S-Zʰ = sym (comm⇒pow-comm h 1 CL₁.lemma-comm-Z-S)

    comm-S↑-Z↑ʰ : S ↑ • (Z ↑) ^ h ≈ (Z ↑) ^ h • S ↑
    comm-S↑-Z↑ʰ = begin
      S ↑ • (Z ↑) ^ h    ≡⟨ Eq.cong (S ↑ •_) (Eq.sym (lemma-↑^ h Z)) ⟩
      S ↑ • (Z ^ h) ↑    ≈⟨ V1R.lemma-cong↑ _ _ (PB.sym (PP₁.comm⇒pow-comm h 1 CL₀.lemma-comm-Z-S)) ⟩
      (Z ^ h) ↑ • S ↑    ≡⟨ Eq.cong (_• S ↑) (lemma-↑^ h Z) ⟩
      (Z ↑) ^ h • S ↑ ∎

    R-split : R ^ p-1 ≈ S ^ p-1 • Z ^ (h Nat.* p-1)
    R-split = begin
      (S • Z ^ h) ^ p-1        ≈⟨ ^-• S (Z ^ h) p-1 comm-S-Zʰ ⟩
      S ^ p-1 • (Z ^ h) ^ p-1  ≈⟨ cright ^^ Z h p-1 ⟩
      S ^ p-1 • Z ^ (h Nat.* p-1) ∎

    R↑-split : (R ↑) ^ p-1 ≈ (S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1)
    R↑-split = begin
      (R ↑) ^ p-1
        ≡⟨ Eq.cong (λ w → (S ↑ • w) ^ p-1) (lemma-↑^ h Z) ⟩
      (S ↑ • (Z ↑) ^ h) ^ p-1
        ≈⟨ ^-• (S ↑) ((Z ↑) ^ h) p-1 comm-S↑-Z↑ʰ ⟩
      (S ↑) ^ p-1 • ((Z ↑) ^ h) ^ p-1
        ≈⟨ cright ^^ (Z ↑) h p-1 ⟩
      (S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1) ∎

    -- h + h(p-1) = h·p, so each wire's Pauli exponent is a multiple of p.
    arith : h Nat.+ h Nat.* p-1 ≡ p Nat.* h
    arith = Eq.trans (Eq.cong (Nat._+ (h Nat.* p-1)) (Eq.sym (NP.*-identityʳ h)))
                     (Eq.trans (Eq.sym (NP.*-distribˡ-+ h 1 p-1)) (NP.*-comm h p))

    pauli-cancel : ∀ (w : Word (Gen (₂₊ n))) → w ^ p ≈ ε →
                   w ^ h • w ^ (h Nat.* p-1) ≈ ε
    pauli-cancel w wp = begin
      w ^ h • w ^ (h Nat.* p-1)  ≈⟨ sym (^-+ w h (h Nat.* p-1)) ⟩
      w ^ (h Nat.+ h Nat.* p-1)  ≡⟨ Eq.cong (w ^_) arith ⟩
      w ^ (p Nat.* h)            ≈⟨ sym (^^ w p h) ⟩
      (w ^ p) ^ h                ≈⟨ ^-cong (w ^ p) ε h wp ⟩
      ε ^ h                      ≈⟨ ε^k=ε h ⟩
      ε ∎

    Zᵖ : Z ^ p ≈ ε
    Zᵖ = CL₁.lemma-order-Z

    Z↑ᵖ : (Z ↑) ^ p ≈ ε
    Z↑ᵖ = begin
      (Z ↑) ^ p  ≡⟨ Eq.sym (lemma-↑^ p Z) ⟩
      (Z ^ p) ↑  ≈⟨ V1R.lemma-cong↑ _ _ CL₀.lemma-order-Z ⟩
      ε ∎

    S↑ᵉ-S↑ : (S ↑) ^ p-1 • S ↑ ≈ ε
    S↑ᵉ-S↑ = begin
      (S ↑) ^ p-1 • S ↑      ≈⟨ sym (^-+ (S ↑) p-1 1) ⟩
      (S ↑) ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong ((S ↑) ^_) (NP.+-comm p-1 1) ⟩
      (S ↑) ^ p              ≡⟨ Eq.sym (lemma-↑^ p S) ⟩
      (S ^ p) ↑              ≈⟨ V1R.lemma-cong↑ _ _ (PB.axiom V1R.order-S) ⟩
      ε ∎

    Sᵉ-S : S ^ p-1 • S ≈ ε
    Sᵉ-S = begin
      S ^ p-1 • S      ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p            ≈⟨ axiom V1R.order-S ⟩
      ε ∎

    comm-Sᵉ-S↑ : S ^ p-1 • S ↑ ≈ S ↑ • S ^ p-1
    comm-Sᵉ-S↑ = lemma-Inductionˡ (lemma-comm-S-w↑ S) p-1

    ------------------------------------------------------------------
    -- The R-spelling becomes the S-spelling.
    --
    -- Only the Z ^ ½ of the leading R stands to the left of the CX, so
    -- only that one crosses; it comes out doubled onto the upper wire,
    -- and each wire's total exponent is then h + h(p-1) = h·p.

    T-S : CX • CZ ≈ S • (CX • (S ^ p-1 • (S ↑) ^ p-1))
    T-S = begin
      CX • CZ
        ≈⟨ T-R ⟩
      (S • Z ^ h) • (CX • (R ^ p-1 • (R ↑) ^ p-1))
        ≈⟨ cright cright cong R-split R↑-split ⟩
      (S • Z ^ h) • (CX • ((S ^ p-1 • Z ^ (h Nat.* p-1))
                            • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))))
        ≈⟨ assoc ⟩
      S • (Z ^ h • (CX • tail))
        ≈⟨ cright sym assoc ⟩
      S • ((Z ^ h • CX) • tail)
        ≈⟨ cright cleft lemma-Zᵏ-CX h ⟩
      S • ((CX • (Z ^ h • (Z ↑) ^ h)) • tail)
        ≈⟨ cright assoc ⟩
      S • (CX • ((Z ^ h • (Z ↑) ^ h) • tail))
        ≈⟨ cright cright core ⟩
      S • (CX • (S ^ p-1 • (S ↑) ^ p-1)) ∎
      where
      tail : Word (Gen (₂₊ n))
      tail = (S ^ p-1 • Z ^ (h Nat.* p-1)) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))

      -- Z ^ h and (Z ↑) ^ h walk right past the phase gates to meet the
      -- powers left over from R ^ (p-1), and annihilate them.
      core : (Z ^ h • (Z ↑) ^ h) • tail ≈ S ^ p-1 • (S ↑) ^ p-1
      core = begin
        (Z ^ h • (Z ↑) ^ h)
          • ((S ^ p-1 • Z ^ (h Nat.* p-1)) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1)))
          ≈⟨ cright assoc ⟩
        (Z ^ h • (Z ↑) ^ h)
          • (S ^ p-1 • (Z ^ (h Nat.* p-1) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ assoc ⟩
        Z ^ h • ((Z ↑) ^ h
          • (S ^ p-1 • (Z ^ (h Nat.* p-1) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1)))))
          ≈⟨ cright sym assoc ⟩
        Z ^ h • (((Z ↑) ^ h • S ^ p-1)
          • (Z ^ (h Nat.* p-1) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ cright cleft sym (comm⇒pow-comm p-1 h (lemma-comm-S-w↑ Z)) ⟩
        Z ^ h • ((S ^ p-1 • (Z ↑) ^ h)
          • (Z ^ (h Nat.* p-1) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ cright assoc ⟩
        Z ^ h • (S ^ p-1 • ((Z ↑) ^ h
          • (Z ^ (h Nat.* p-1) • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1)))))
          ≈⟨ cright cright sym assoc ⟩
        Z ^ h • (S ^ p-1 • (((Z ↑) ^ h • Z ^ (h Nat.* p-1))
          • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ cright cright cleft sym (comm⇒pow-comm (h Nat.* p-1) h (lemma-comm-Z-w↑ Z)) ⟩
        Z ^ h • (S ^ p-1 • ((Z ^ (h Nat.* p-1) • (Z ↑) ^ h)
          • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ cright cright assoc ⟩
        Z ^ h • (S ^ p-1 • (Z ^ (h Nat.* p-1)
          • ((Z ↑) ^ h • ((S ↑) ^ p-1 • (Z ↑) ^ (h Nat.* p-1)))))
          ≈⟨ cright cright cright sym assoc ⟩
        Z ^ h • (S ^ p-1 • (Z ^ (h Nat.* p-1)
          • (((Z ↑) ^ h • (S ↑) ^ p-1) • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ cright cright cright cleft comm-Z↑ʰ-S↑ᵉ ⟩
        Z ^ h • (S ^ p-1 • (Z ^ (h Nat.* p-1)
          • (((S ↑) ^ p-1 • (Z ↑) ^ h) • (Z ↑) ^ (h Nat.* p-1))))
          ≈⟨ cright cright cright assoc ⟩
        Z ^ h • (S ^ p-1 • (Z ^ (h Nat.* p-1)
          • ((S ↑) ^ p-1 • ((Z ↑) ^ h • (Z ↑) ^ (h Nat.* p-1)))))
          ≈⟨ cright cright cright cright pauli-cancel (Z ↑) Z↑ᵖ ⟩
        Z ^ h • (S ^ p-1 • (Z ^ (h Nat.* p-1) • ((S ↑) ^ p-1 • ε)))
          ≈⟨ cright cright cright right-unit ⟩
        Z ^ h • (S ^ p-1 • (Z ^ (h Nat.* p-1) • (S ↑) ^ p-1))
          ≈⟨ cright cright comm⇒pow-comm (h Nat.* p-1) p-1 (lemma-comm-Z-w↑ S) ⟩
        Z ^ h • (S ^ p-1 • ((S ↑) ^ p-1 • Z ^ (h Nat.* p-1)))
          ≈⟨ cright sym assoc ⟩
        Z ^ h • ((S ^ p-1 • (S ↑) ^ p-1) • Z ^ (h Nat.* p-1))
          ≈⟨ sym assoc ⟩
        (Z ^ h • (S ^ p-1 • (S ↑) ^ p-1)) • Z ^ (h Nat.* p-1)
          ≈⟨ cleft comm-Zʰ-SS↑ ⟩
        ((S ^ p-1 • (S ↑) ^ p-1) • Z ^ h) • Z ^ (h Nat.* p-1)
          ≈⟨ assoc ⟩
        (S ^ p-1 • (S ↑) ^ p-1) • (Z ^ h • Z ^ (h Nat.* p-1))
          ≈⟨ cright pauli-cancel Z Zᵖ ⟩
        (S ^ p-1 • (S ↑) ^ p-1) • ε
          ≈⟨ right-unit ⟩
        S ^ p-1 • (S ↑) ^ p-1 ∎
        where
        -- Same wire, so this is lemma-comm-Z-S lifted and iterated.
        comm-Z↑ʰ-S↑ᵉ : (Z ↑) ^ h • (S ↑) ^ p-1 ≈ (S ↑) ^ p-1 • (Z ↑) ^ h
        comm-Z↑ʰ-S↑ᵉ = begin
          (Z ↑) ^ h • (S ↑) ^ p-1
            ≡⟨ Eq.cong₂ (λ a b → a • b) (Eq.sym (lemma-↑^ h Z)) (Eq.sym (lemma-↑^ p-1 S)) ⟩
          (Z ^ h) ↑ • (S ^ p-1) ↑
            ≈⟨ V1R.lemma-cong↑ _ _ (PP₁.comm⇒pow-comm h p-1 CL₀.lemma-comm-Z-S) ⟩
          (S ^ p-1) ↑ • (Z ^ h) ↑
            ≡⟨ Eq.cong₂ (λ a b → a • b) (lemma-↑^ p-1 S) (lemma-↑^ h Z) ⟩
          (S ↑) ^ p-1 • (Z ↑) ^ h ∎

        -- Z ^ h passes S ^ (p-1) on its own wire and (S ↑) ^ (p-1) on the
        -- other one.
        comm-Zʰ-SS↑ : Z ^ h • (S ^ p-1 • (S ↑) ^ p-1)
                    ≈ (S ^ p-1 • (S ↑) ^ p-1) • Z ^ h
        comm-Zʰ-SS↑ = begin
          Z ^ h • (S ^ p-1 • (S ↑) ^ p-1)
            ≈⟨ sym assoc ⟩
          (Z ^ h • S ^ p-1) • (S ↑) ^ p-1
            ≈⟨ cleft comm⇒pow-comm h p-1 CL₁.lemma-comm-Z-S ⟩
          (S ^ p-1 • Z ^ h) • (S ↑) ^ p-1
            ≈⟨ assoc ⟩
          S ^ p-1 • (Z ^ h • (S ↑) ^ p-1)
            ≈⟨ cright comm⇒pow-comm h p-1 (lemma-comm-Z-w↑ S) ⟩
          S ^ p-1 • ((S ↑) ^ p-1 • Z ^ h)
            ≈⟨ sym assoc ⟩
          (S ^ p-1 • (S ↑) ^ p-1) • Z ^ h ∎

    ------------------------------------------------------------------
    -- …and blake-c12 is that, with the CX moved to the other side.

    A' : Word (Gen (₂₊ n))
    A' = CX ^ p-1 • (S • CX)

    CZ-split : CZ ≈ A' • (S ^ p-1 • (S ↑) ^ p-1)
    CZ-split = begin
      CZ
        ≈⟨ sym left-unit ⟩
      ε • CZ
        ≈⟨ cleft sym CXᵉ-CX ⟩
      (CX ^ p-1 • CX) • CZ
        ≈⟨ assoc ⟩
      CX ^ p-1 • (CX • CZ)
        ≈⟨ cright T-S ⟩
      CX ^ p-1 • (S • (CX • (S ^ p-1 • (S ↑) ^ p-1)))
        ≈⟨ cright sym assoc ⟩
      CX ^ p-1 • ((S • CX) • (S ^ p-1 • (S ↑) ^ p-1))
        ≈⟨ sym assoc ⟩
      (CX ^ p-1 • (S • CX)) • (S ^ p-1 • (S ↑) ^ p-1) ∎

    A'-conj : A' ≈ CZ • (S ↑ • S)
    A'-conj = begin
      A'
        ≈⟨ sym right-unit ⟩
      A' • ε
        ≈⟨ cright sym cancel ⟩
      A' • ((S ^ p-1 • (S ↑) ^ p-1) • (S ↑ • S))
        ≈⟨ sym assoc ⟩
      (A' • (S ^ p-1 • (S ↑) ^ p-1)) • (S ↑ • S)
        ≈⟨ cleft sym CZ-split ⟩
      CZ • (S ↑ • S) ∎
      where
      cancel : (S ^ p-1 • (S ↑) ^ p-1) • (S ↑ • S) ≈ ε
      cancel = begin
        (S ^ p-1 • (S ↑) ^ p-1) • (S ↑ • S)
          ≈⟨ assoc ⟩
        S ^ p-1 • ((S ↑) ^ p-1 • (S ↑ • S))
          ≈⟨ cright sym assoc ⟩
        S ^ p-1 • (((S ↑) ^ p-1 • S ↑) • S)
          ≈⟨ cright cleft S↑ᵉ-S↑ ⟩
        S ^ p-1 • (ε • S)
          ≈⟨ cright left-unit ⟩
        S ^ p-1 • S
          ≈⟨ Sᵉ-S ⟩
        ε ∎

  lemma-blake-c12 : (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ≈ CZ
  lemma-blake-c12 = begin
    (S ^ p-1) ↑ • (S ^ p-1 • A')
      ≡⟨ Eq.cong (λ w → w • (S ^ p-1 • A')) (lemma-↑^ p-1 S) ⟩
    (S ↑) ^ p-1 • (S ^ p-1 • A')
      ≈⟨ cright cright A'-conj ⟩
    (S ↑) ^ p-1 • (S ^ p-1 • (CZ • (S ↑ • S)))
      ≈⟨ cright sym assoc ⟩
    (S ↑) ^ p-1 • ((S ^ p-1 • CZ) • (S ↑ • S))
      ≈⟨ cright cleft sym (comm⇒pow-comm 1 p-1 (axiom V1R.comm-CZ-S↓)) ⟩
    (S ↑) ^ p-1 • ((CZ • S ^ p-1) • (S ↑ • S))
      ≈⟨ sym assoc ⟩
    ((S ↑) ^ p-1 • (CZ • S ^ p-1)) • (S ↑ • S)
      ≈⟨ cleft sym assoc ⟩
    (((S ↑) ^ p-1 • CZ) • S ^ p-1) • (S ↑ • S)
      ≈⟨ cleft cleft sym (comm⇒pow-comm 1 p-1 (axiom V1R.comm-CZ-S↑)) ⟩
    ((CZ • (S ↑) ^ p-1) • S ^ p-1) • (S ↑ • S)
      ≈⟨ cleft assoc ⟩
    (CZ • ((S ↑) ^ p-1 • S ^ p-1)) • (S ↑ • S)
      ≈⟨ assoc ⟩
    CZ • (((S ↑) ^ p-1 • S ^ p-1) • (S ↑ • S))
      ≈⟨ cright assoc ⟩
    CZ • ((S ↑) ^ p-1 • (S ^ p-1 • (S ↑ • S)))
      ≈⟨ cright cright sym assoc ⟩
    CZ • ((S ↑) ^ p-1 • ((S ^ p-1 • S ↑) • S))
      ≈⟨ cright cright cleft comm-Sᵉ-S↑ ⟩
    CZ • ((S ↑) ^ p-1 • ((S ↑ • S ^ p-1) • S))
      ≈⟨ cright cright assoc ⟩
    CZ • ((S ↑) ^ p-1 • (S ↑ • (S ^ p-1 • S)))
      ≈⟨ cright sym assoc ⟩
    CZ • (((S ↑) ^ p-1 • S ↑) • (S ^ p-1 • S))
      ≈⟨ cright cleft S↑ᵉ-S↑ ⟩
    CZ • (ε • (S ^ p-1 • S))
      ≈⟨ cright left-unit ⟩
    CZ • (S ^ p-1 • S)
      ≈⟨ cright Sᵉ-S ⟩
    CZ • ε
      ≈⟨ right-unit ⟩
    CZ ∎

------------------------------------------------------------------------
-- The three multiplier rules in their XM form
--
-- Paper-V0 states M-power, semi-MR and semi-M↑CZ over XMg = XM g′, which
-- is M at the INVERSE unit.  Here they are as Simplified-V1 theorems, so
-- that the identity on words is still a morphism the other way.
--
-- Everything rests on one fact: M (g′ ⁻¹) is Mg's inverse, because
-- M g′ • M (g′ ⁻¹) is M ₁ is ε (lemma-M-mul and lemma-M1, both already in
-- V1's Lemmas1).  Conjugating an axiom by an inverse flips it, which is
-- what turns each Mg rule into its XMg counterpart.

module XM-Rules (n : ℕ) where

  open PB (V1R._QRel,_===_ (₁₊ n))
  open PP (V1R._QRel,_===_ (₁₊ n))
  open SR word-setoid
  open Primitive-Root-Modp' g* g-gen

  private module L1 = V1L.Lemmas1 n

  -- M at the inverse unit — the word Paper-V0 calls XMg.
  Mh : Word (Gen (₁₊ n))
  Mh = V1R.M (g′ ⁻¹)

  MgMh : V1R.Mg • Mh ≈ ε
  MgMh = begin
    V1R.M g′ • V1R.M (g′ ⁻¹)
      ≈⟨ L1.lemma-M-mul g′ (g′ ⁻¹) ⟩
    V1R.M (g′ *' (g′ ⁻¹))
      ≡⟨ L1.aux-M≡M (g′ *' (g′ ⁻¹)) (₁ , λ ())
                    (lemma-⁻¹ʳ g {{nztoℕ {y = g} {neq0 = g≠0} }}) ⟩
    V1R.M (₁ , λ ())
      ≈⟨ L1.lemma-M1 ⟩
    ε ∎

  MhMg : Mh • V1R.Mg ≈ ε
  MhMg = begin
    V1R.M (g′ ⁻¹) • V1R.M g′
      ≈⟨ L1.lemma-M-mul (g′ ⁻¹) g′ ⟩
    V1R.M ((g′ ⁻¹) *' g′)
      ≡⟨ L1.aux-M≡M ((g′ ⁻¹) *' g′) (₁ , λ ())
                    (lemma-⁻¹ˡ g {{nztoℕ {y = g} {neq0 = g≠0} }}) ⟩
    V1R.M (₁ , λ ())
      ≈⟨ L1.lemma-M1 ⟩
    ε ∎

  comm-Mh-Mg : Mh • V1R.Mg ≈ V1R.Mg • Mh
  comm-Mh-Mg = trans MhMg (sym MgMh)

  ----------------------------------------------------------------------
  -- semi-MR, flipped

  lemma-semi-MR : Mh • V1R.R^ (g * g) ≈ R • Mh
  lemma-semi-MR = sym (begin
    R • Mh
      ≈⟨ cleft sym left-unit ⟩
    (ε • R) • Mh
      ≈⟨ cleft cleft sym MhMg ⟩
    ((Mh • V1R.Mg) • R) • Mh
      ≈⟨ cleft assoc ⟩
    (Mh • (V1R.Mg • R)) • Mh
      ≈⟨ cleft cright axiom V1R.semi-MR ⟩
    (Mh • (V1R.R^ (g * g) • V1R.Mg)) • Mh
      ≈⟨ cleft sym assoc ⟩
    ((Mh • V1R.R^ (g * g)) • V1R.Mg) • Mh
      ≈⟨ assoc ⟩
    (Mh • V1R.R^ (g * g)) • (V1R.Mg • Mh)
      ≈⟨ cright MgMh ⟩
    (Mh • V1R.R^ (g * g)) • ε
      ≈⟨ right-unit ⟩
    Mh • V1R.R^ (g * g) ∎)

  ----------------------------------------------------------------------
  -- M-power, flipped
  --
  -- Mh ^ m is what kills Mg ^ m, and so is M ((g ^ m) ⁻¹); inverses are
  -- unique, so the two agree.

  lemma-Mgⁿ : ∀ (m : ℕ) -> V1R.Mg ^ m ≈ V1R.M (g^′ m)
  lemma-Mgⁿ ₀ = begin
    ε                       ≈⟨ sym L1.lemma-M1 ⟩
    V1R.M (₁ , λ ())        ≡⟨ L1.aux-M≡M (₁ , λ ()) (g^′ 0) auto ⟩
    V1R.M (g^′ 0) ∎
  lemma-Mgⁿ ₁ = refl' (L1.aux-M≡M g′ (g^′ 1) (Eq.sym (*-identityʳ g)))
  lemma-Mgⁿ (₂₊ m) = begin
    V1R.Mg • V1R.Mg ^ ₁₊ m           ≈⟨ cright lemma-Mgⁿ (₁₊ m) ⟩
    V1R.M g′ • V1R.M (g^′ ₁₊ m)      ≈⟨ L1.lemma-M-mul g′ (g^′ ₁₊ m) ⟩
    V1R.M (g′ *' g^′ ₁₊ m)
      ≡⟨ L1.aux-M≡M (g′ *' g^′ ₁₊ m) (g^′ ₂₊ m) auto ⟩
    V1R.M (g^′ ₂₊ m) ∎

  lemma-MhMg-pow : ∀ (m : ℕ) -> Mh ^ m • V1R.Mg ^ m ≈ ε
  lemma-MhMg-pow ₀ = left-unit
  lemma-MhMg-pow ₁ = MhMg
  lemma-MhMg-pow (₂₊ m) = begin
    (Mh • Mh ^ ₁₊ m) • (V1R.Mg • V1R.Mg ^ ₁₊ m)
      ≈⟨ assoc ⟩
    Mh • (Mh ^ ₁₊ m • (V1R.Mg • V1R.Mg ^ ₁₊ m))
      ≈⟨ cright sym assoc ⟩
    Mh • ((Mh ^ ₁₊ m • V1R.Mg) • V1R.Mg ^ ₁₊ m)
      ≈⟨ cright cleft comm⇒pow-comm (₁₊ m) 1 comm-Mh-Mg ⟩
    Mh • ((V1R.Mg • Mh ^ ₁₊ m) • V1R.Mg ^ ₁₊ m)
      ≈⟨ cright assoc ⟩
    Mh • (V1R.Mg • (Mh ^ ₁₊ m • V1R.Mg ^ ₁₊ m))
      ≈⟨ cright cright lemma-MhMg-pow (₁₊ m) ⟩
    Mh • (V1R.Mg • ε)
      ≈⟨ cright right-unit ⟩
    Mh • V1R.Mg
      ≈⟨ MhMg ⟩
    ε ∎

  lemma-M-power : ∀ (k : ℤ ₚ) -> Mh ^ toℕ k ≈ V1R.M ((g^ k) ⁻¹)
  lemma-M-power k = begin
    Mh ^ toℕ k
      ≈⟨ sym right-unit ⟩
    Mh ^ toℕ k • ε
      ≈⟨ cright sym killer ⟩
    Mh ^ toℕ k • (V1R.Mg ^ toℕ k • V1R.M ((g^ k) ⁻¹))
      ≈⟨ sym assoc ⟩
    (Mh ^ toℕ k • V1R.Mg ^ toℕ k) • V1R.M ((g^ k) ⁻¹)
      ≈⟨ cleft lemma-MhMg-pow (toℕ k) ⟩
    ε • V1R.M ((g^ k) ⁻¹)
      ≈⟨ left-unit ⟩
    V1R.M ((g^ k) ⁻¹) ∎
    where
    killer : V1R.Mg ^ toℕ k • V1R.M ((g^ k) ⁻¹) ≈ ε
    killer = begin
      V1R.Mg ^ toℕ k • V1R.M ((g^ k) ⁻¹)
        ≈⟨ cleft lemma-Mgⁿ (toℕ k) ⟩
      V1R.M (g^′ toℕ k) • V1R.M ((g^ k) ⁻¹)
        ≡⟨ Eq.cong (_• V1R.M ((g^ k) ⁻¹))
                   (L1.aux-M≡M (g^′ toℕ k) (g^ k) auto) ⟩
      V1R.M (g^ k) • V1R.M ((g^ k) ⁻¹)
        ≈⟨ L1.lemma-M-mul (g^ k) ((g^ k) ⁻¹) ⟩
      V1R.M ((g^ k) *' ((g^ k) ⁻¹))
        ≡⟨ L1.aux-M≡M ((g^ k) *' ((g^ k) ⁻¹)) (₁ , λ ())
                      (lemma-⁻¹ʳ ((g^ k) .proj₁)
                        {{nztoℕ {y = (g^ k) .proj₁}
                                {neq0 = lemma-g^′k≠0 (toℕ k)} }}) ⟩
      V1R.M (₁ , λ ())
        ≈⟨ L1.lemma-M1 ⟩
      ε ∎

------------------------------------------------------------------------
-- semi-M↑CZ, flipped
--
-- The same cancellation one wire up; the two inverse facts are the
-- one-wire ones lifted.

module XM-Rules↑ (n : ℕ) where

  open PB (V1R._QRel,_===_ (₂₊ n))
  open PP (V1R._QRel,_===_ (₂₊ n))
  open SR word-setoid
  open Primitive-Root-Modp' g* g-gen

  private module X1 = XM-Rules n

  Mg↑Mh↑ : V1R.Mg ↑ • X1.Mh ↑ ≈ ε
  Mg↑Mh↑ = V1R.lemma-cong↑ _ _ X1.MgMh

  Mh↑Mg↑ : X1.Mh ↑ • V1R.Mg ↑ ≈ ε
  Mh↑Mg↑ = V1R.lemma-cong↑ _ _ X1.MhMg

  lemma-semi-M↑CZ : X1.Mh ↑ • CZ^ g ≈ CZ • X1.Mh ↑
  lemma-semi-M↑CZ = sym (begin
    CZ • X1.Mh ↑
      ≈⟨ cleft sym left-unit ⟩
    (ε • CZ) • X1.Mh ↑
      ≈⟨ cleft cleft sym Mh↑Mg↑ ⟩
    ((X1.Mh ↑ • V1R.Mg ↑) • CZ) • X1.Mh ↑
      ≈⟨ cleft assoc ⟩
    (X1.Mh ↑ • (V1R.Mg ↑ • CZ)) • X1.Mh ↑
      ≈⟨ cleft cright axiom V1R.semi-M↑CZ ⟩
    (X1.Mh ↑ • (CZ^ g • V1R.Mg ↑)) • X1.Mh ↑
      ≈⟨ cleft sym assoc ⟩
    ((X1.Mh ↑ • CZ^ g) • V1R.Mg ↑) • X1.Mh ↑
      ≈⟨ assoc ⟩
    (X1.Mh ↑ • CZ^ g) • (V1R.Mg ↑ • X1.Mh ↑)
      ≈⟨ cright Mg↑Mh↑ ⟩
    (X1.Mh ↑ • CZ^ g) • ε
      ≈⟨ right-unit ⟩
    X1.Mh ↑ • CZ^ g ∎)
