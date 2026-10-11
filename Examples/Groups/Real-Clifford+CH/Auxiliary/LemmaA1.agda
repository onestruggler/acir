------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.1 and Proposition 4.8: Figure 7 derives Figure 6, so it is
-- complete wherever Figure 6 is (Clément, Appendix A.2)
--
-- Every rule of Figure 6 is a theorem of Figure 7, in the generality
-- the paper proves it in (distinct indices in any order): (a1), (b1),
-- (b4), (b6) in LemmaA1.Moves, (d3), (d4) in LemmaA1.General, (d1) in
-- LemmaA1.More, the rest in LemmaA1.Base, and (a2), (a3), (c1), (c5),
-- (d2) are rules of Figure 7.  Hence Figure 6's congruence is contained
-- in Figure 7's (`lemma-A1*`), and the completeness half of Proposition
-- 4.8 follows: if two proper words with the same semantics are equal
-- modulo Figure 6 — the paper's Theorem 4.4 — they are equal modulo
-- Figure 7 (`proposition-4-8`).  The other half, that Figure 7 is
-- sound, is Auxiliary.Soundness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1 where

open import Data.Fin using (Fin ; _<_)
open import Data.Fin.Properties using (<⇒≢ ; <-trans)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Word.Base using (Word)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics using (Gen ; _G,_===_ ; Proper)
open _G,_===_
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure6 using (_F,_===_)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure6 as F
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Moves using (_⊢ᴳ_≈_ ; a1 ; b1 ; b4 ; b6)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.General using (d3 ; d4)
import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Base as Base
import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.More as More

private
  variable
    N : ℕ
    u v : Word (Gen N)

  ne : ∀ {a b : Fin N} → a < b → a ≢ b
  ne = <⇒≢

  sy : ∀ {a b : Fin N} → a ≢ b → b ≢ a
  sy p e = p (Eq.sym e)

  tr : ∀ {a b c : Fin N} → a < b → b < c → a < c
  tr = <-trans

------------------------------------------------------------------------
-- Lemma A.1

lemma-A1 : N F, u === v → N ⊢ᴳ u ≈ v
lemma-A1 (F.a1 {a = a})            = a1 a
lemma-A1 (F.a2 ab)                 = PB.axiom (a2 (ne ab))
lemma-A1 (F.b1 ab)                 = b1 ab
lemma-A1 (F.b2 ab ac bc)           = Base.b2 _ (ne bc) (sy ab) (sy ac)
lemma-A1 (F.b3 ab cd ac ad bc bd)  = Base.b3 _ (ne cd) (sy ac) (sy bc) (sy ad) (sy bd) (ne ab)
lemma-A1 (F.c1 ab)                 = PB.axiom (c1 (ne ab))
lemma-A1 (F.c2 ab bc)              = PB.sym (Base.c2 _ (ne ab) (ne (tr ab bc)) (ne bc))
lemma-A1 (F.c3 ab bc)              = PB.sym (Base.c3′ _ (ne ab) (ne (tr ab bc)) (ne bc))
lemma-A1 (F.a3 ab)                 = PB.axiom (a3 (ne ab))
lemma-A1 (F.b4 ab ac bc)           = b4 ab ac (ne bc)
lemma-A1 (F.b5 ab cd ac ad bc bd)  = PB.sym (Base.b5 _ (ne ab) ac ad bc bd (ne cd))
lemma-A1 (F.b6 ab cd ac ad bc bd)  = b6 (ne ab) ac ad bc bd (ne cd)
lemma-A1 (F.c4 ab bc)              = PB.sym (Base.c4 _ (ne ab) (ne (tr ab bc)) (ne bc))
lemma-A1 (F.c5 ab bc)              = PB.axiom (c5 (ne ab) (ne (tr ab bc)) (ne bc))
lemma-A1 (F.d1 ab)                 = More.d1 _ (ne ab)
lemma-A1 (F.d2 ab)                 = PB.axiom (d2 (ne ab))
lemma-A1 (F.d3 ab cd ac bd bc)     =
  d3 (ne ab) (ne ac) (ne (tr ac cd)) bc (ne bd) (ne cd)
lemma-A1 (F.d4 ab ac bd ce df ef bc be cd de) =
  d4 (ne ab) (ne ac) (ne (tr ab bd)) (ne (tr ac ce)) (ne (tr (tr ac ce) ef))
     bc (ne bd) be (ne (tr bd df))
     cd (ne ce) (ne (tr ce ef)) de (ne df) (ne ef)
lemma-A1 (F.e1 bc)                 = Base.e1 _ (sy (ne bc))
lemma-A1 (F.e2 bc)                 = Base.e2 _ (ne bc)

-- The congruence of Figure 6 is contained in that of Figure 7.
lemma-A1* : PB._≈_ (N F,_===_) u v → N ⊢ᴳ u ≈ v
lemma-A1* PB.refl          = PB.refl
lemma-A1* (PB.sym e)       = PB.sym (lemma-A1* e)
lemma-A1* (PB.trans e f)   = PB.trans (lemma-A1* e) (lemma-A1* f)
lemma-A1* (PB.cong e f)    = PB.cong (lemma-A1* e) (lemma-A1* f)
lemma-A1* PB.assoc         = PB.assoc
lemma-A1* PB.left-unit     = PB.left-unit
lemma-A1* PB.right-unit    = PB.right-unit
lemma-A1* (PB.axiom a)     = lemma-A1 a

------------------------------------------------------------------------
-- Proposition 4.8, completeness: Figure 7 is complete where Figure 6 is

module _ {N : ℕ} {S : Set} (⟦_⟧ : Word (Gen N) → S) (_≋_ : S → S → Set) where

  -- Completeness of each theory for the proper words (words over G_N).
  Complete⁶ Complete⁷ : Set
  Complete⁶ = ∀ {u t : Word (Gen N)} → Proper u → Proper t → ⟦ u ⟧ ≋ ⟦ t ⟧ →
              PB._≈_ (N F,_===_) u t
  Complete⁷ = ∀ {u t : Word (Gen N)} → Proper u → Proper t → ⟦ u ⟧ ≋ ⟦ t ⟧ →
              N ⊢ᴳ u ≈ t

  proposition-4-8 : Complete⁶ → Complete⁷
  proposition-4-8 complete pu pt e = lemma-A1* (complete pu pt e)
