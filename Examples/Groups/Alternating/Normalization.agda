------------------------------------------------------------------------
-- Presentations of groups
--
-- Lafont's Lemmas 7 and 8: every circuit reduces to its canonical form
-- by the rules of Fig. 10.
--
-- The canonical forms of Lemma 6 are the coset normal forms of the
-- tower 𝔄₀ ⊆ 𝔄₁ ⊆ …: one on ₁₊ n wires is one on n wires, shifted up,
-- followed by a stairs (NF, inv-nf).  The coset action ract pushes a
-- generator through a stairs: [ c ]ᶜ • [ g ]ʷ is a circuit one wire up
-- followed by a stairs (ract-sound).  Its clauses are the rules of
-- Fig. 10, one for each shape of stairs that a cycle on the bottom
-- wires can meet, and Lemma 7, which carries a circuit two wires up
-- through the first cycle of a stairs: ω • w ↑ ↑ is conj* w ↑ • ω
-- (conj-pass, from rule₁).  nf runs the action from the trivial coset
-- and recurses on the residual, one wire up, and inv-nf∘nf≈id is
-- Lemma 8: a circuit is congruent to its canonical form, in any theory
-- where the seven rules hold.
--
-- That is all the syntax the presentation needs.  That nf respects the
-- congruence is not proved here, by checking the action against every
-- relation as Symmetric's coset table is: it follows, as in the paper,
-- from soundness and Lemma 6 (UniqueNormalForm), in Completeness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Normalization where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Alternating.Cosets
open import Examples.Groups.Alternating.Rules using (Fig10 ; module Fig10)
open import Examples.Groups.Alternating.Syntactics
  using ( Gen ; Circuit ; ω ; ω-gen ; ω-gate ; _↥ ; _↑ ; ₅₊
        ; no-gen₀ ; no-gen₂ ; Theory ; _∣_⊢_≈_ ; module Lift-Relation )

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Conjugation by ω, one wire down

-- conj g is the image of g under conjugation by ω, read one wire down:
-- ω • [ g ]ʷ ↑ ↑ ≈ conj g ↑ • ω.  For a cycle on the bottom wires this
-- is rule₁; anything higher commutes with ω.
conj : Gen (₁₊ n) → Circuit (₂₊ n)
conj ω-gen = ω ↑ • ω ↑ • ω • ω ↑
conj (g ↥) = [ g ↥ ↥ ]ʷ

conj* : Circuit (₁₊ n) → Circuit (₂₊ n)
conj* = conj ʷ

------------------------------------------------------------------------
-- The coset action

-- ract c g is a residual b and a coset c′ with [ c ]ᶜ • [ g ]ʷ ≈
-- b ↑ • [ c′ ]ᶜ.  A shifted generator passes a stairs one cycle at a
-- time and comes out conjugated (Lemma 7); a cycle on the bottom wires
-- meets the first cycles of the stairs, and the rule of Fig. 10 that
-- applies depends on how many there are before the stairs ends.
ract : C n → Gen (₁₊ n) → Circuit n × C n
ract ε             ω-gen = ε , ω• ε
ract ε             (g ↥) = [ g ]ʷ , ε
ract ωω            ω-gen = ε , ε                            -- rule₇
ract ωω            (g ↥) = ⊥-elim (no-gen₂ g)
ract (ω• c)        (g ↥) = conj* (proj₁ (ract c g)) , ω• proj₂ (ract c g)
ract {2}    (ω• ε) ω-gen = ε , ωω
ract {₃₊ _} (ω• ε) ω-gen = ω , ω• ω• ε                      -- rule₄
ract (ω• ωω)       ω-gen = ω • ω , ω• ωω                    -- rule₆
ract (ω• ω• ε)     ω-gen = ω • ω , ε                        -- rule₃
ract (ω• ω• ωω)    ω-gen = ω , ω• ω• ωω                     -- rule₅
ract (ω• ω• ω• c)  ω-gen = ω ↑ , ω• ω• ω• c                 -- rule₂

-- The action on circuits.
racts : C n → Circuit (₁₊ n) → Circuit n × C n
racts {n} = ract {n} ᵗ

------------------------------------------------------------------------
-- Canonical forms

NF : ℕ → Set
NF ₀      = ⊤
NF (₁₊ n) = NF n × C n

-- A canonical form on the top n wires, then a stairs.
inv-nf : NF n → Circuit n
inv-nf {₀}    tt      = ε
inv-nf {₁₊ n} (x , c) = inv-nf x ↑ • [ c ]ᶜ

-- Push the circuit through the trivial coset, then normalise the
-- residual on the top wires.
nf : Circuit n → NF n
nf {₀}    _ = tt
nf {₁₊ n} w = nf (proj₁ (racts ε w)) , proj₂ (racts ε w)

------------------------------------------------------------------------
-- Lemmas 7 and 8, in a theory with the rules of Fig. 10

module _ {T : Theory} (rules : Fig10 T) where

  open Fig10 rules
  open Lift-Relation T
    using (_VRel,_===_ ; comm₃ ; lemma-cong↑ ; comm-gate₃-w↑↑↑)

  -- Lemma 7, one cycle at a time: ω passes a circuit two wires up,
  -- which comes out conjugated.
  conj-pass : (w : Circuit (₁₊ n)) → T ∣ ₃₊ n ⊢ ω • w ↑ ↑ ≈ conj* w ↑ • ω
  conj-pass {n} ε = trans right-unit (sym left-unit)
    where open PB ((₃₊ n) VRel,_===_)
  conj-pass {₂₊ k} [ ω-gen ]ʷ = trans rule₁ (by-assoc Eq.refl)
    where
    open PB ((₅₊ k) VRel,_===_)
    open PP ((₅₊ k) VRel,_===_)
  conj-pass {n} [ g ↥ ]ʷ = sym (axiom (comm₃ ω-gate g))
    where open PB ((₃₊ n) VRel,_===_)
  conj-pass {n} (w • v) = begin
    ω • w ↑ ↑ • v ↑ ↑             ≈⟨ sym assoc ⟩
    (ω • w ↑ ↑) • v ↑ ↑           ≈⟨ cleft conj-pass w ⟩
    (conj* w ↑ • ω) • v ↑ ↑       ≈⟨ assoc ⟩
    conj* w ↑ • ω • v ↑ ↑         ≈⟨ cright conj-pass v ⟩
    conj* w ↑ • conj* v ↑ • ω     ≈⟨ sym assoc ⟩
    (conj* w ↑ • conj* v ↑) • ω   ∎
    where
    open PB ((₃₊ n) VRel,_===_)
    open SR (PP.word-setoid ((₃₊ n) VRel,_===_))

  -- The coset action is sound: each clause is one rule of Fig. 10,
  -- Lemma 7 or the unit laws.
  ract-sound : (c : C n) (g : Gen (₁₊ n)) →
               let (b , c′) = ract c g in
               T ∣ ₁₊ n ⊢ [ c ]ᶜ • [ g ]ʷ ≈ b ↑ • [ c′ ]ᶜ
  ract-sound {n} ε ω-gen = cright (sym right-unit)
    where open PB ((₁₊ n) VRel,_===_)
  ract-sound {n} ε (g ↥) = trans left-unit (sym right-unit)
    where open PB ((₁₊ n) VRel,_===_)
  ract-sound ωω ω-gen = trans assoc (trans rule₇ (sym left-unit))
    where open PB (3 VRel,_===_)
  ract-sound ωω (g ↥) = ⊥-elim (no-gen₂ g)
  ract-sound {₂₊ m} (ω• c) (g ↥) = begin
    (ω • [ c ]ᶜ ↑) • [ g ↥ ]ʷ     ≈⟨ assoc ⟩
    ω • ([ c ]ᶜ • [ g ]ʷ) ↑       ≈⟨ cright lemma-cong↑ _ _ (ract-sound c g) ⟩
    ω • (b ↑ • [ c′ ]ᶜ) ↑         ≈⟨ sym assoc ⟩
    (ω • b ↑ ↑) • [ c′ ]ᶜ ↑       ≈⟨ cleft conj-pass b ⟩
    (conj* b ↑ • ω) • [ c′ ]ᶜ ↑   ≈⟨ assoc ⟩
    conj* b ↑ • ω • [ c′ ]ᶜ ↑     ∎
    where
    b  = proj₁ (ract c g)
    c′ = proj₂ (ract c g)
    open PB ((₃₊ m) VRel,_===_)
    open SR (PP.word-setoid ((₃₊ m) VRel,_===_))
  ract-sound {2} (ω• ε) ω-gen = by-assoc Eq.refl
    where open PP (3 VRel,_===_)
  ract-sound {₃₊ n} (ω• ε) ω-gen = by-assoc-and rule₄ Eq.refl Eq.refl
    where open PP ((₄₊ n) VRel,_===_)
  ract-sound (ω• ωω) ω-gen = by-assoc-and rule₆ Eq.refl Eq.refl
    where open PP (4 VRel,_===_)
  ract-sound {₃₊ n} (ω• ω• ε) ω-gen = by-assoc-and rule₃ Eq.refl Eq.refl
    where open PP ((₄₊ n) VRel,_===_)
  ract-sound (ω• ω• ωω) ω-gen = by-assoc-and rule₅ Eq.refl Eq.refl
    where open PP (5 VRel,_===_)
  ract-sound {₄₊ n} (ω• ω• ω• c) ω-gen = begin
    (ω • ω ↑ • ω ↑ ↑ • X) • ω       ≈⟨ by-assoc Eq.refl ⟩
    ω • ω ↑ • ω ↑ ↑ • X • ω         ≈⟨ cright cright cright
                                         comm-gate₃-w↑↑↑ ω-gate [ c ]ᶜ ⟩
    ω • ω ↑ • ω ↑ ↑ • ω • X         ≈⟨ by-assoc Eq.refl ⟩
    (ω • ω ↑ • ω ↑ ↑ • ω) • X       ≈⟨ cleft rule₂ ⟩
    (ω ↑ ↑ • ω • ω ↑ • ω ↑ ↑) • X   ≈⟨ by-assoc Eq.refl ⟩
    ω ↑ ↑ • ω • ω ↑ • ω ↑ ↑ • X     ∎
    where
    X = [ c ]ᶜ ↑ ↑ ↑
    open PB ((₅₊ n) VRel,_===_)
    open PP ((₅₊ n) VRel,_===_)
    open SR word-setoid

  -- The action on circuits is sound.
  racts-sound : (c : C n) (w : Circuit (₁₊ n)) →
                let (w′ , c′) = racts c w in
                T ∣ ₁₊ n ⊢ [ c ]ᶜ • w ≈ w′ ↑ • [ c′ ]ᶜ
  racts-sound c [ g ]ʷ = ract-sound c g
  racts-sound {n} c ε = trans right-unit (sym left-unit)
    where open PB ((₁₊ n) VRel,_===_)
  racts-sound {n} c (w • v) with racts c w | racts-sound c w
  ... | (w′ , c′) | ih₁ with racts c′ v | racts-sound c′ v
  ... | (v′ , c″) | ih₂ = begin
    [ c ]ᶜ • w • v           ≈⟨ sym assoc ⟩
    ([ c ]ᶜ • w) • v         ≈⟨ cleft ih₁ ⟩
    (w′ ↑ • [ c′ ]ᶜ) • v     ≈⟨ assoc ⟩
    w′ ↑ • [ c′ ]ᶜ • v       ≈⟨ cright ih₂ ⟩
    w′ ↑ • v′ ↑ • [ c″ ]ᶜ    ≈⟨ sym assoc ⟩
    (w′ • v′) ↑ • [ c″ ]ᶜ    ∎
    where
    open PB ((₁₊ n) VRel,_===_)
    open SR (PP.word-setoid ((₁₊ n) VRel,_===_))

  -- On no wires every circuit is empty.
  width₀ : (w : Circuit ₀) → T ∣ ₀ ⊢ w ≈ ε
  width₀ [ g ]ʷ  = ⊥-elim (no-gen₀ g)
  width₀ ε       = PB.refl
  width₀ (w • v) = PB.trans (PB.cong (width₀ w) (width₀ v)) PB.left-unit

  -- Lemma 8: every circuit is congruent to its canonical form.
  inv-nf∘nf≈id : (w : Circuit n) → T ∣ n ⊢ inv-nf (nf w) ≈ w
  inv-nf∘nf≈id {₀}    w = PB.sym (width₀ w)
  inv-nf∘nf≈id {₁₊ n} w = begin
    inv-nf (nf b) ↑ • [ c ]ᶜ   ≈⟨ cleft lemma-cong↑ _ _ (inv-nf∘nf≈id b) ⟩
    b ↑ • [ c ]ᶜ               ≈⟨ sym (racts-sound ε w) ⟩
    ε • w                      ≈⟨ left-unit ⟩
    w                          ∎
    where
    b = proj₁ (racts ε w)
    c = proj₂ (racts ε w)
    open PB ((₁₊ n) VRel,_===_)
    open SR (PP.word-setoid ((₁₊ n) VRel,_===_))
