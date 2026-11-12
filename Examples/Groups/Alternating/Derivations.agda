------------------------------------------------------------------------
-- Presentations of groups
--
-- Lafont's Fig. 11: the rules of Fig. 10 from Theorem 4's relations.
--
-- The derivations are generic in the theory: any theory in which the
-- three relations of Theorem 4 hold has the seven rules, at every width
-- (FromRelations).  Theorem 4's own relations are one such theory
-- (fig10); Alternative is another.  rule₃ and rule₇ are relations of
-- Theorem 4 themselves; the others are a few steps each, every step
-- replacing one factor of a word by an equal one.  Each derivation was
-- found by a breadth-first search over the relations and their
-- shifts, and checked on permutations, before it was written here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Derivations where

open import Notations using (₃₊ ; ₄₊)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Alternating.Rules using (Fig10)
open import Examples.Groups.Alternating.Syntactics
  hiding (_VRel,_===_ ; lemma-cong↑ ; comm-gate₃-w↑↑↑)


------------------------------------------------------------------------
-- One rewriting step

-- Rewrite the factor l of pre • l • post to r.  The words before and
-- after are related to pre • l • post and pre • r • post by
-- associativity, which is checked by flattening both: every word here
-- is concrete.
step : ∀ {T : Theory} {m} {w v : Circuit m} (pre : Circuit m)
       {l r : Circuit m} (post : Circuit m) →
       let open PP (Lift-Relation._VRel,_===_ T m) in
       T ∣ m ⊢ l ≈ r →
       to-list w ≡ to-list (pre • l • post) →
       to-list (pre • r • post) ≡ to-list v →
       T ∣ m ⊢ w ≈ v
step {T} {m} pre {l} {r} post e =
  by-assoc-and {a = pre • l • post} {b = pre • r • post}
    (PB.cong PB.refl (PB.cong e PB.refl))
  where open PP (Lift-Relation._VRel,_===_ T m)

------------------------------------------------------------------------
-- The rules from the relations

module FromRelations
  (T : Theory)
  (r₁ : ∀ {n} → T ∣ ₃₊ n ⊢ ω • ω • ω ≈ ε)
  (r₂ : ∀ {n} → T ∣ ₄₊ n ⊢ ω • ω ↑ • ω ≈ ω ↑ • ω ↑)
  (r₃ : ∀ {n} → T ∣ ₅₊ n ⊢ ω • ω ↑ ↑ • ω ≈ ω ↑ ↑ • ω • ω ↑)
  where

  open Lift-Relation T using (_VRel,_===_ ; lemma-cong↑)

  private
    -- The relations one and two wires up.
    r₁↑ : ∀ {n} → T ∣ ₄₊ n ⊢ ω ↑ • ω ↑ • ω ↑ ≈ ε
    r₁↑ = lemma-cong↑ _ _ r₁

    r₁↑↑ : ∀ {n} → T ∣ ₅₊ n ⊢ ω ↑ ↑ • ω ↑ ↑ • ω ↑ ↑ ≈ ε
    r₁↑↑ = lemma-cong↑ _ _ r₁↑

    r₂↑ : ∀ {n} → T ∣ ₅₊ n ⊢ ω ↑ • ω ↑ ↑ • ω ↑ ≈ ω ↑ ↑ • ω ↑ ↑
    r₂↑ = lemma-cong↑ _ _ r₂

  rule₄ : ∀ {n} → T ∣ ₄₊ n ⊢ ω • ω ≈ ω ↑ • ω • ω ↑
  rule₄ {n} = begin
    ω • ω                        ≈⟨ step ε (ω • ω) (PB.sym r₁↑)
                                         Eq.refl Eq.refl ⟩
    ω ↑ • ω ↑ • ω ↑ • ω • ω      ≈⟨ step (ω ↑) (ω • ω) (PB.sym r₂)
                                         Eq.refl Eq.refl ⟩
    ω ↑ • ω • ω ↑ • ω • ω • ω    ≈⟨ step (ω ↑ • ω • ω ↑) ε r₁
                                         Eq.refl Eq.refl ⟩
    ω ↑ • ω • ω ↑                ∎
    where open SR (PP.word-setoid ((₄₊ n) VRel,_===_))

  rule₆ : ∀ {n} →
          T ∣ ₄₊ n ⊢ ω • ω ↑ • ω ↑ • ω ≈ ω ↑ • ω ↑ • ω • ω ↑ • ω ↑
  rule₆ {n} = begin
    ω • ω ↑ • ω ↑ • ω               ≈⟨ step (ω • ω ↑) (ω ↑ • ω)
                                            (PB.sym r₁) Eq.refl Eq.refl ⟩
    ω • ω ↑ • ω • ω • ω • ω ↑ • ω   ≈⟨ step ε (ω • ω • ω ↑ • ω) r₂
                                            Eq.refl Eq.refl ⟩
    ω ↑ • ω ↑ • ω • ω • ω ↑ • ω     ≈⟨ step (ω ↑ • ω ↑ • ω) ε r₂
                                            Eq.refl Eq.refl ⟩
    ω ↑ • ω ↑ • ω • ω ↑ • ω ↑       ∎
    where open SR (PP.word-setoid ((₄₊ n) VRel,_===_))

  rule₁ : ∀ {n} →
          T ∣ ₅₊ n ⊢ ω • ω ↑ ↑ ≈ ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω
  rule₁ {n} = begin
    ω • ω ↑ ↑                        ≈⟨ step (ω • ω ↑ ↑) ε (PB.sym r₁)
                                             Eq.refl Eq.refl ⟩
    ω • ω ↑ ↑ • ω • ω • ω            ≈⟨ step ε (ω • ω) r₃
                                             Eq.refl Eq.refl ⟩
    ω ↑ ↑ • ω • ω ↑ • ω • ω          ≈⟨ step (ω ↑ ↑) ω r₂
                                             Eq.refl Eq.refl ⟩
    ω ↑ ↑ • ω ↑ • ω ↑ • ω            ≈⟨ step (ω ↑ ↑) ω
                                             (lemma-cong↑ _ _ rule₄)
                                             Eq.refl Eq.refl ⟩
    ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω  ∎
    where open SR (PP.word-setoid ((₅₊ n) VRel,_===_))

  rule₂ : ∀ {n} →
          T ∣ ₅₊ n ⊢ ω • ω ↑ • ω ↑ ↑ • ω ≈ ω ↑ ↑ • ω • ω ↑ • ω ↑ ↑
  rule₂ {n} = begin
    ω • ω ↑ • ω ↑ ↑ • ω
      ≈⟨ step ω (ω ↑ • ω ↑ ↑ • ω) (PB.sym r₁↑↑) Eq.refl Eq.refl ⟩
    ω • ω ↑ ↑ • ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω
      ≈⟨ step (ω • ω ↑ ↑) ε (PB.sym rule₁) Eq.refl Eq.refl ⟩
    ω • ω ↑ ↑ • ω • ω ↑ ↑
      ≈⟨ step ε (ω ↑ ↑) r₃ Eq.refl Eq.refl ⟩
    ω ↑ ↑ • ω • ω ↑ • ω ↑ ↑
      ∎
    where open SR (PP.word-setoid ((₅₊ n) VRel,_===_))

  rule₅ : ∀ {n} →
          T ∣ ₅₊ n ⊢ ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑ • ω ≈
                     ω ↑ • ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑
  rule₅ {n} = begin
    ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑ • ω
      ≈⟨ step (ω • ω ↑ • ω ↑ ↑) (ω ↑ ↑ • ω) (PB.sym r₁↑)
              Eq.refl Eq.refl ⟩
    ω • ω ↑ • ω ↑ ↑ • ω ↑ • ω ↑ • ω ↑ • ω ↑ ↑ • ω
      ≈⟨ step ω (ω ↑ • ω ↑ • ω ↑ ↑ • ω) r₂↑ Eq.refl Eq.refl ⟩
    ω • ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ • ω ↑ ↑ • ω
      ≈⟨ step (ω • ω ↑ ↑ • ω ↑ ↑ • ω ↑) (ω ↑ • ω ↑ ↑ • ω) (PB.sym r₁↑↑)
              Eq.refl Eq.refl ⟩
    ω • ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω
      ≈⟨ step (ω • ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑) ε (PB.sym rule₁)
              Eq.refl Eq.refl ⟩
    ω • ω ↑ ↑ • ω ↑ ↑ • ω ↑ • ω ↑ ↑ • ω • ω ↑ ↑
      ≈⟨ step ω (ω ↑ ↑) (PB.sym rule₁) Eq.refl Eq.refl ⟩
    ω • ω • ω ↑ ↑ • ω ↑ ↑
      ≈⟨ step ε (ω ↑ ↑ • ω ↑ ↑) rule₄ Eq.refl Eq.refl ⟩
    ω ↑ • ω • ω ↑ • ω ↑ ↑ • ω ↑ ↑
      ∎
    where open SR (PP.word-setoid ((₅₊ n) VRel,_===_))

  fig10 : Fig10 T
  fig10 = record
    { rule₁ = rule₁
    ; rule₂ = rule₂
    ; rule₃ = r₂
    ; rule₄ = rule₄
    ; rule₅ = rule₅
    ; rule₆ = rule₆
    ; rule₇ = r₁
    }


------------------------------------------------------------------------
-- Theorem 4's relations derive the rules

fig10 : Fig10 _SRel,_===_
fig10 = FromRelations.fig10 _SRel,_===_
  (PB.axiom (srel order)) (PB.axiom (srel near)) (PB.axiom (srel far))
