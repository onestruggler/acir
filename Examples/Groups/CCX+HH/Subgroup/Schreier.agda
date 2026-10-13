------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's stateful translation on the formal Schreier alphabet.
--
-- An edge (c,y) represents rep(c) y rep(c.y)^(-1).  The relation consists
-- of translated source axioms and the edge encode/decode equations.
-- Everything here is syntactic: no semantic equality is an axiom.
--
-- The action and a section of its orbit are the only additional data.
-- Theorems below prove soundness, injectivity, and that the image is
-- exactly the stabilizer of the distinguished coset.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.Base as PB
import Examples.Groups.CCX+HH.Subgroup.State as State
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect)
  renaming ([_] to [_]ᵢ)

module Examples.Groups.CCX+HH.Subgroup.Schreier
  {Y C : Set} (Δ : WRel Y) (gl : Grouplike Δ)
  (I : C) (step : C → Y → C)
  (relations : ∀ c {u v} → Δ u v → State.state step c u ≡ State.state step c v)
  (rep : C → Word Y)
  (rep-I : PB._≈_ Δ (rep I) ε)
  (rep-state : ∀ c → State.state step I (rep c) ≡ c)
  where

import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Normalization.Reidemeister-Schreier using (module Star-Injective-Full)

open State step public using (state)
open State.Congruence step Δ relations public using (state-cong)
private
  module A = PB Δ
  module AP = PP Δ
  module G = Group-Lemmas Δ gl
  open SR AP.word-setoid

Edge : Set
Edge = C × Y

e : Edge → Word Y
e (c , y) = (rep c • [ y ]ʷ) • G._⁻¹ (rep (step c y))

encode : Word Edge → Word Y
encode = e ʷ

h : C → Y → Word Edge × C
h c y = [ c , y ]ʷ , step c y

decode : C → Word Y → Word Edge
decode c w = proj₁ ((h ᵗ) c w)

walk-state : ∀ c w → proj₂ ((h ᵗ) c w) ≡ state c w
walk-state c [ y ]ʷ = Eq.refl
walk-state c ε = Eq.refl
walk-state c (u • v) with (h ᵗ) c u | inspect ((h ᵗ) c) u
... | (u′ , c′) | [ Eq.refl ]ᵢ =
  Eq.trans (walk-state c′ v) (Eq.cong (λ d → state d v) (walk-state c u))

-- Every edge word has trivial coset, because representatives form a
-- section and words in the source presentation have inverses.
edge-closed : ∀ g → state I (e g) ≡ I
edge-closed (c , y) = Eq.trans first (Eq.trans (Eq.sym second) third)
  where
  next = step c y
  first : state I (e (c , y)) ≡ state next (G._⁻¹ (rep next))
  first = Eq.cong (λ d → state (step d y) (G._⁻¹ (rep next))) (rep-state c)
  second : state I (rep next • G._⁻¹ (rep next)) ≡ state next (G._⁻¹ (rep next))
  second = Eq.cong (λ d → state d (G._⁻¹ (rep next))) (rep-state next)
  third : state I (rep next • G._⁻¹ (rep next)) ≡ I
  third = state-cong I (G.inverseʳ {rep next})

encode-closed : ∀ w → state I (encode w) ≡ I
encode-closed [ g ]ʷ = edge-closed g
encode-closed ε = Eq.refl
encode-closed (u • v) =
  Eq.trans (Eq.cong (λ c → state c (encode v)) (encode-closed u)) (encode-closed v)

infix 4 _===_
data _===_ : WRel Edge where
  roundtrip : ∀ g → [ g ]ʷ === decode I (e g)
  translated : ∀ c {u v} → Δ u v → decode c u === decode c v

open PB _===_ public using (_≈_)
private
  module P = PB _===_
  module R = Star-Injective-Full _===_ Δ C I

  roundtrip-ok : ∀ g → R._~_ ([ g ]ʷ , I) ((h ᵗ) I (e g))
  roundtrip-ok g = P.axiom (roundtrip g) ,
    Eq.sym (Eq.trans (walk-state I (e g)) (edge-closed g))

  translated-ok : ∀ c {u v} → Δ u v → R._~_ ((h ᵗ) c u) ((h ᵗ) c v)
  translated-ok c {u} {v} ax = P.axiom (translated c ax) ,
    Eq.trans (walk-state c u) (Eq.trans (relations c ax) (Eq.sym (walk-state c v)))

  module Injective = R.Reidemeister-Schreier-Full e h roundtrip-ok translated-ok

encode-injective : ∀ {u v} → encode u A.≈ encode v → u ≈ v
encode-injective = Injective.fʷ-inj

factor : ∀ c y → rep c • [ y ]ʷ A.≈ encode [ c , y ]ʷ • rep (step c y)
factor c y = begin
  rep c • [ y ]ʷ                       ≈⟨ A.sym A.right-unit ⟩
  (rep c • [ y ]ʷ) • ε                 ≈⟨ A.cong A.refl (A.sym G.inverseˡ) ⟩
  (rep c • [ y ]ʷ) • (G._⁻¹ (rep (step c y)) • rep (step c y))
    ≈⟨ A.sym A.assoc ⟩
  encode [ c , y ]ʷ • rep (step c y)    ∎

factor-word : ∀ c w → rep c • w A.≈ encode (decode c w) • rep (state c w)
factor-word c [ y ]ʷ = factor c y
factor-word c ε = A.trans A.right-unit (A.sym A.left-unit)
factor-word c (u • v) with (h ᵗ) c u | inspect ((h ᵗ) c) u
... | (u′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v | inspect ((h ᵗ) c′) v
... | (v′ , c″) | [ Eq.refl ]ᵢ = begin
  rep c • (u • v)                      ≈⟨ A.sym A.assoc ⟩
  (rep c • u) • v                      ≈⟨ A.cong (factor-word c u) A.refl ⟩
  (encode u′ • rep (state c u)) • v
    ≈⟨ A.cong (A.cong A.refl (A.refl' (Eq.cong rep (Eq.sym (walk-state c u))))) A.refl ⟩
  (encode u′ • rep c′) • v             ≈⟨ A.assoc ⟩
  encode u′ • (rep c′ • v)             ≈⟨ A.cong A.refl (factor-word c′ v) ⟩
  encode u′ • (encode v′ • rep (state c′ v))
    ≈⟨ A.sym A.assoc ⟩
  encode (u′ • v′) • rep (state c′ v)
    ≈⟨ A.cong A.refl (A.refl' (Eq.cong (λ d → rep (state d v)) (walk-state c u))) ⟩
  encode (u′ • v′) • rep (state c (u • v)) ∎

decode-loop : ∀ {w} → state I w ≡ I → encode (decode I w) A.≈ w
decode-loop {w} closed = A.sym (begin
  w                                    ≈⟨ A.sym A.left-unit ⟩
  ε • w                                ≈⟨ A.cong (A.sym rep-I) A.refl ⟩
  rep I • w                            ≈⟨ factor-word I w ⟩
  encode (decode I w) • rep (state I w) ≈⟨ A.cong A.refl (A.refl' (Eq.cong rep closed)) ⟩
  encode (decode I w) • rep I          ≈⟨ A.cong A.refl rep-I ⟩
  encode (decode I w) • ε              ≈⟨ A.right-unit ⟩
  encode (decode I w)                  ∎)

encode-axiom : ∀ {u v} → u === v → encode u A.≈ encode v
encode-axiom (roundtrip g) = A.sym (decode-loop (edge-closed g))
encode-axiom (translated c {u} {v} ax) = G.•-cancelʳ (begin
  encode (decode c u) • rep (state c u) ≈⟨ A.sym (factor-word c u) ⟩
  rep c • u                            ≈⟨ A.cong A.refl (A.axiom ax) ⟩
  rep c • v                            ≈⟨ factor-word c v ⟩
  encode (decode c v) • rep (state c v)
    ≈⟨ A.cong A.refl (A.refl' (Eq.cong rep (Eq.sym (relations c ax)))) ⟩
  encode (decode c v) • rep (state c u) ∎)

encode-cong : ∀ {u v} → u ≈ v → encode u A.≈ encode v
encode-cong = PP.StarCongruence.fʷ-cong _===_ Δ e encode-axiom

inverse-closed : ∀ {w} → state I w ≡ I → state I (G._⁻¹ w) ≡ I
inverse-closed {w} closed =
  Eq.trans (Eq.sym (Eq.cong (λ c → state c (G._⁻¹ w)) closed))
           (state-cong I (G.inverseʳ {w}))

grouplike : Grouplike _===_
grouplike g = decode I (G._⁻¹ (e g)) , encode-injective (begin
  encode (decode I (G._⁻¹ (e g))) • e g
    ≈⟨ A.cong (decode-loop (inverse-closed {e g} (edge-closed g))) A.refl ⟩
  G._⁻¹ (e g) • e g                    ≈⟨ G.inverseˡ ⟩
  ε                                    ∎)
