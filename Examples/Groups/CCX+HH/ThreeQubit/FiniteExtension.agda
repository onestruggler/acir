------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément translation through a finite collection of subgroup cosets.
--
-- The ambient presentation can have infinitely many cosets outside the
-- circuit image.  Here only a finite orbit inside that image is used.
-- A complete presentation of the stabilizer, a factorization table,
-- and distinct cosets give a complete circuit presentation.
--
-- All table equations are words in the original auxiliary presentation.
-- The target axioms are finitely indexed table equations and decoded
-- stabilizer axioms, never unrestricted semantic equalities.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect)
  renaming ([_] to [_]ᵢ)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.Base as PB

module Examples.Groups.CCX+HH.ThreeQubit.FiniteExtension
  {X B Y C : Set}
  (Δ : WRel Y) (gl : Grouplike Δ)
  (Γ : WRel B)
  (e : X → Word Y) (b : B → Word Y) (d : B → Word X)
  (d-correct : ∀ g → PB._≈_ Δ ((e ʷ) (d g)) (b g))
  (base-sound : ∀ {u v} → Γ u v → PB._≈_ Δ ((b ʷ) u) ((b ʷ) v))
  (base-complete : ∀ {u v} → PB._≈_ Δ ((b ʷ) u) ((b ʷ) v) → PB._≈_ Γ u v)
  (I : C) (rep : C → Word X) (rep-I : rep I ≡ ε)
  (h : C → X → Word B × C)
  (factor : ∀ c g → PB._≈_ Δ
    ((e ʷ) (rep c) • e g)
    ((b ʷ) (proj₁ (h c g)) • (e ʷ) (rep (proj₂ (h c g)))))
  (separate : ∀ c c′ u v → PB._≈_ Δ
    ((b ʷ) u • (e ʷ) (rep c)) ((b ʷ) v • (e ʷ) (rep c′)) → c ≡ c′)
  where

import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

private
  module A = PB Δ
  module AP = PP Δ
  module AG = Group-Lemmas Δ gl
  module Base = PB Γ

encode : Word X → Word Y
encode = e ʷ

base : Word B → Word Y
base = b ʷ

decode : Word B → Word X
decode = d ʷ

output : C → Word X → Word B
output c w = proj₁ ((h ᵗ) c w)

state : C → Word X → C
state c w = proj₂ ((h ᵗ) c w)

decode-correct : ∀ w → encode (decode w) A.≈ base w
decode-correct [ g ]ʷ = d-correct g
decode-correct ε = A.refl
decode-correct (u • v) = A.cong (decode-correct u) (decode-correct v)

infix 4 _===_
data _===_ : WRel X where
  table : ∀ c g → rep c • [ g ]ʷ ===
    decode (proj₁ (h c g)) • rep (proj₂ (h c g))
  stabilizer : ∀ {u v} → Γ u v → decode u === decode v

open PB _===_ public using (_≈_)
private
  module P = PB _===_
  module TP = PP _===_

module _ where
  open SR AP.word-setoid

  encode-axiom : ∀ {u v} → u === v → encode u A.≈ encode v
  encode-axiom (table c g) = begin
    encode (rep c) • e g
      ≈⟨ factor c g ⟩
    base (proj₁ (h c g)) • encode (rep (proj₂ (h c g)))
      ≈⟨ A.cong (A.sym (decode-correct (proj₁ (h c g)))) A.refl ⟩
    encode (decode (proj₁ (h c g))) • encode (rep (proj₂ (h c g))) ∎
  encode-axiom (stabilizer {u} {v} ax) = begin
    encode (decode u) ≈⟨ decode-correct u ⟩
    base u           ≈⟨ base-sound ax ⟩
    base v           ≈⟨ A.sym (decode-correct v) ⟩
    encode (decode v) ∎

  source-factor : ∀ c w → encode (rep c) • encode w A.≈
    base (output c w) • encode (rep (state c w))
  source-factor c [ g ]ʷ = factor c g
  source-factor c ε = A.trans A.right-unit (A.sym A.left-unit)
  source-factor c (u • v) with (h ᵗ) c u | inspect ((h ᵗ) c) u
  ... | (u′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v | inspect ((h ᵗ) c′) v
  ... | (v′ , c″) | [ Eq.refl ]ᵢ = begin
    encode (rep c) • (encode u • encode v) ≈⟨ A.sym A.assoc ⟩
    (encode (rep c) • encode u) • encode v
      ≈⟨ A.cong (source-factor c u) A.refl ⟩
    (base u′ • encode (rep c′)) • encode v ≈⟨ A.assoc ⟩
    base u′ • (encode (rep c′) • encode v)
      ≈⟨ A.cong A.refl (source-factor c′ v) ⟩
    base u′ • (base v′ • encode (rep c″)) ≈⟨ A.sym A.assoc ⟩
    base (u′ • v′) • encode (rep c″) ∎

  source-normalization : ∀ w → encode w A.≈
    base (output I w) • encode (rep (state I w))
  source-normalization w = begin
    encode w                         ≈⟨ A.sym A.left-unit ⟩
    ε • encode w
      ≈⟨ A.cong (A.refl' (Eq.cong encode (Eq.sym rep-I))) A.refl ⟩
    encode (rep I) • encode w         ≈⟨ source-factor I w ⟩
    base (output I w) • encode (rep (state I w)) ∎

encode-cong : ∀ {u v} → u ≈ v → encode u A.≈ encode v
encode-cong = PP.StarCongruence.fʷ-cong _===_ Δ e encode-axiom

base-lift : ∀ {u v} → u Base.≈ v → decode u ≈ decode v
base-lift = PP.StarCongruence.fʷ-cong Γ _===_ d (λ ax → P.axiom (stabilizer ax))

module _ where
  open SR TP.word-setoid

  normalization-at : ∀ c w → rep c • w ≈ decode (output c w) • rep (state c w)
  normalization-at c [ g ]ʷ = P.axiom (table c g)
  normalization-at c ε = P.trans P.right-unit (P.sym P.left-unit)
  normalization-at c (u • v) with (h ᵗ) c u | inspect ((h ᵗ) c) u
  ... | (u′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v | inspect ((h ᵗ) c′) v
  ... | (v′ , c″) | [ Eq.refl ]ᵢ = begin
    rep c • (u • v)              ≈⟨ P.sym P.assoc ⟩
    (rep c • u) • v              ≈⟨ P.cong (normalization-at c u) P.refl ⟩
    (decode u′ • rep c′) • v     ≈⟨ P.assoc ⟩
    decode u′ • (rep c′ • v)     ≈⟨ P.cong P.refl (normalization-at c′ v) ⟩
    decode u′ • (decode v′ • rep c″) ≈⟨ P.sym P.assoc ⟩
    decode (u′ • v′) • rep c″    ∎

  normalization : ∀ w → w ≈ decode (output I w) • rep (state I w)
  normalization w = begin
    w                       ≈⟨ P.sym P.left-unit ⟩
    ε • w                   ≈⟨ P.cong (P.refl' (Eq.sym rep-I)) P.refl ⟩
    rep I • w               ≈⟨ normalization-at I w ⟩
    decode (output I w) • rep (state I w) ∎

encode-injective : ∀ {u v} → encode u A.≈ encode v → u ≈ v
encode-injective {u} {v} eq =
  P.trans (normalization u)
    (P.trans (P.cong
      (base-lift {output I u} {output I v} (base-complete base-eq))
      (P.refl' (Eq.cong rep states-eq)))
             (P.sym (normalization v)))
  where
  normal-eq : base (output I u) • encode (rep (state I u)) A.≈
              base (output I v) • encode (rep (state I v))
  normal-eq = A.trans (A.sym (source-normalization u)) (A.trans eq (source-normalization v))

  states-eq : state I u ≡ state I v
  states-eq = separate (state I u) (state I v) (output I u) (output I v) normal-eq

  base-eq : base (output I u) A.≈ base (output I v)
  base-eq = AG.•-cancelʳ
    (A.trans normal-eq
      (A.cong A.refl (A.refl' (Eq.cong (λ c → encode (rep c)) (Eq.sym states-eq)))))
