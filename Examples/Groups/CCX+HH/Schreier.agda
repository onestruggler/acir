------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's back-and-forth method with a coset state.  A direct decoder
-- for every ambient generator need not exist: the circuit subgroup can
-- be proper.  The stateful version rewrites each auxiliary relation at
-- every coset, and adds the generator encode/decode equations.
--
-- The remaining premises are explicit: the coset states must agree
-- across each auxiliary axiom and return to I for encoded circuit
-- generators.  Soundness and agreement with independently defined
-- circuit matrices are separate obligations.  No decoder is postulated.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ) renaming (_^_ to _^ℕ_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ᵗ)
open import Examples.Groups.CCX+HH.Syntactics using (Gen ; Circuit)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T

module Examples.Groups.CCX+HH.Schreier
  (n : ℕ) (C : Set) (I : C)
  (h : C → T.Gen (2 ^ℕ n) → Circuit n × C)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect)
  renaming ([_] to [_]ᵢ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Normalization.Reidemeister-Schreier using (module Star-Injective-Full)
open import Examples.Groups.CCX+HH.Encoding using (e ; encode)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as M
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red

decode : C → Word (T.Gen (2 ^ℕ n)) → Circuit n
decode c w = proj₁ ((h ᵗ) c w)

state : C → Word (T.Gen (2 ^ℕ n)) → C
state c w = proj₂ ((h ᵗ) c w)

infix 4 _===_
data _===_ : WRel (Gen n) where
  roundtrip : (g : Gen n) → [ g ]ʷ === decode I (e g)
  translated : ∀ c {u v} → u T.=== v → decode c u === decode c v

open PB _===_ public using (_≈_)
private
  module P = PB _===_
  module R = Star-Injective-Full _===_ (T._===_ {2 ^ℕ n}) C I

module Complete
  (state-roundtrip : ∀ g → I ≡ state I (e g))
  (state-relations : ∀ c {u v} → u T.=== v → state c u ≡ state c v)
  where

  private
    roundtrip-ok : ∀ g → R._~_ ([ g ]ʷ , I) ((h ᵗ) I (e g))
    roundtrip-ok g = P.axiom (roundtrip g) , state-roundtrip g

    translated-ok : ∀ c {u v} → u T.=== v →
                    R._~_ ((h ᵗ) c u) ((h ᵗ) c v)
    translated-ok c ax = P.axiom (translated c ax) , state-relations c ax

    module Injective = R.Reidemeister-Schreier-Full e h roundtrip-ok translated-ok

  -- Equality of the encoded matrices is enough for a circuit derivation.
  -- Semantic preservation of encode identifies this with ordinary
  -- equality of circuit matrices once that theorem has been supplied.
  encoded-completeness : ∀ {u v : Circuit n} →
    S.⟦ encode u ⟧ᵐ ≡ S.⟦ encode v ⟧ᵐ → u ≈ v
  encoded-completeness eq = Injective.fʷ-inj (M.completeness eq)

  -- Soundness requires actual representative words and their 1-letter
  -- factorization equations.  The exact two-qubit computation checks
  -- these 33 equations; supplying their Agda proofs closes this premise.
  module Sound
    (rep : C → Word (T.Gen (2 ^ℕ n)))
    (rep-I : PB._≈_ (T._===_ {2 ^ℕ n}) (rep I) ε)
    (factor : ∀ c y → PB._≈_ (T._===_ {2 ^ℕ n})
       (rep c • [ y ]ʷ)
       (encode (proj₁ (h c y)) • rep (proj₂ (h c y))))
    where

    private
      module A = PB (T._===_ {2 ^ℕ n})
      module AP = PP (T._===_ {2 ^ℕ n})
      open SR AP.word-setoid

    factor-word : ∀ c w →
      rep c • w A.≈ encode (decode c w) • rep (state c w)
    factor-word c [ y ]ʷ = factor c y
    factor-word c ε = A.trans A.right-unit (A.sym A.left-unit)
    factor-word c (w • v) with (h ᵗ) c w | inspect ((h ᵗ) c) w
    ... | (w′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v | inspect ((h ᵗ) c′) v
    ... | (v′ , c″) | [ Eq.refl ]ᵢ = begin
      rep c • (w • v)                       ≈⟨ A.sym A.assoc ⟩
      (rep c • w) • v                       ≈⟨ A.cong (factor-word c w) A.refl ⟩
      (encode w′ • rep c′) • v              ≈⟨ A.assoc ⟩
      encode w′ • (rep c′ • v)              ≈⟨ A.cong A.refl (factor-word c′ v) ⟩
      encode w′ • (encode v′ • rep c″)     ≈⟨ A.sym A.assoc ⟩
      encode (w′ • v′) • rep c″            ∎

    encode-axiom : ∀ {u v} → u === v → encode u A.≈ encode v
    encode-axiom (roundtrip g) = begin
      e g                                    ≈⟨ A.sym A.left-unit ⟩
      ε • e g                                ≈⟨ A.cong (A.sym rep-I) A.refl ⟩
      rep I • e g                            ≈⟨ factor-word I (e g) ⟩
      encode (decode I (e g)) • rep (state I (e g))
        ≈⟨ A.cong A.refl (A.refl' (Eq.cong rep (Eq.sym (state-roundtrip g)))) ⟩
      encode (decode I (e g)) • rep I        ≈⟨ A.cong A.refl rep-I ⟩
      encode (decode I (e g)) • ε            ≈⟨ A.right-unit ⟩
      encode (decode I (e g))                ∎
    encode-axiom (translated c {u} {v} ax) = D.•-cancelʳ (begin
      encode (decode c u) • rep (state c u)  ≈⟨ A.sym (factor-word c u) ⟩
      rep c • u                             ≈⟨ A.cong A.refl (A.axiom ax) ⟩
      rep c • v                             ≈⟨ factor-word c v ⟩
      encode (decode c v) • rep (state c v)
        ≈⟨ A.cong A.refl (A.refl' (Eq.cong rep (Eq.sym (state-relations c ax)))) ⟩
      encode (decode c v) • rep (state c u)  ∎)

    encode-cong : ∀ {u v} → u ≈ v → encode u A.≈ encode v
    encode-cong = PP.StarCongruence.fʷ-cong _===_ (T._===_ {2 ^ℕ n}) e encode-axiom

    encoded-soundness : ∀ {u v} → u ≈ v → S.⟦ encode u ⟧ᵐ ≡ S.⟦ encode v ⟧ᵐ
    encoded-soundness eq = Red.sound-act (encode-cong eq) S.𝕀
