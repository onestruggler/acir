------------------------------------------------------------------------
-- Presentations of groups
--
-- Five.Facts4's gadgets commute with every CX off wire 0, on four wires
--
-- Stable.GadgetAll's four-wire input (`Gadget.Indep₀ 0`): every CX of
-- Affine.Circuits whose control is off wire 0 is, on four wires, a word
-- in the letters Five.Facts4 says the gadgets commute with — CX from
-- wire j + 1 onto j (j = 0, 1, 2) and the exchanges of the wires 1 2
-- and 2 3 — each by one four-wire evaluation (`cx-word`); so the
-- gadgets commute with it (`ind₄`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.Gadget4 (c4 : Complete 4) (F : Facts4) where

open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin using (toℕ)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (_<_ ; s≤s)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below ; Same)
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₂)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_ ; embed)
import Examples.Groups.Clifford+CS.Affine.Theory 3 as A₀
import Examples.Groups.Clifford+CS.Affine.Circuits 0 c4 as C₀

open Facts4 F using (G ; cx₀ ; cx₁ ; cx₂ ; sw₁ ; sw₂)

private
  module S₄ = Below 4 c4
  open Tools (4 VRel,_===_)

------------------------------------------------------------------------
-- The letters the gadgets commute with

data Let : Set where
  l₀ l₁ l₂ s₁ s₂ : Let

⟦_⟧L : Let → Circuit 4
⟦ l₀ ⟧L = CX₁₀
⟦ l₁ ⟧L = CX₁₀ ↑
⟦ l₂ ⟧L = CX₁₀ ↑ ↑
⟦ s₁ ⟧L = Swap ↑
⟦ s₂ ⟧L = Swap ↑ ↑

⟦_⟧W : List Let → Circuit 4
⟦ [] ⟧W    = ε
⟦ a ∷ w ⟧W = ⟦ a ⟧L • ⟦ w ⟧W

private
  pass-L : ∀ V a → 4 ⊢ ⟦ a ⟧L • G V ≈ G V • ⟦ a ⟧L
  pass-L V l₀ = cx₀ V
  pass-L V l₁ = cx₁ V
  pass-L V l₂ = cx₂ V
  pass-L V s₁ = sw₁ V
  pass-L V s₂ = sw₂ V

  pass-W : ∀ V w → 4 ⊢ ⟦ w ⟧W • G V ≈ G V • ⟦ w ⟧W
  pass-W V []      = trans left-unit (sym right-unit)
  pass-W V (a ∷ w) = begin
    (⟦ a ⟧L • ⟦ w ⟧W) • G V     ≈⟨ assoc ⟩
    ⟦ a ⟧L • (⟦ w ⟧W • G V)     ≈⟨ back _ (pass-W V w) ⟩
    ⟦ a ⟧L • (G V • ⟦ w ⟧W)     ≈⟨ sym assoc ⟩
    (⟦ a ⟧L • G V) • ⟦ w ⟧W     ≈⟨ front _ (pass-L V a) ⟩
    (G V • ⟦ a ⟧L) • ⟦ w ⟧W     ≈⟨ assoc ⟩
    G V • ⟦ a ⟧L • ⟦ w ⟧W       ∎

------------------------------------------------------------------------
-- Every CX off wire 0 as such a word

private
  cx : ∀ (u : Fin 3) (v : Fin 4) .(p : sF u ≢ v) → Circuit 4
  cx u v p = C₀.⟪ A₀.tL (sF u) v p ⟫

  -- The word for CX from u + 1 onto v.
  wd : Fin 3 → Fin 4 → List Let
  wd 0F                0F                = l₀ ∷ []
  wd 0F                (sF (sF 0F))      = s₁ ∷ l₁ ∷ s₁ ∷ []
  wd 0F                (sF (sF (sF 0F))) = s₂ ∷ s₁ ∷ l₁ ∷ s₁ ∷ s₂ ∷ []
  wd (sF 0F)           0F                = s₁ ∷ l₀ ∷ s₁ ∷ []
  wd (sF 0F)           (sF 0F)           = l₁ ∷ []
  wd (sF 0F)           (sF (sF (sF 0F))) = s₂ ∷ l₂ ∷ s₂ ∷ []
  wd (sF (sF 0F))      0F                = s₂ ∷ s₁ ∷ l₀ ∷ s₁ ∷ s₂ ∷ []
  wd (sF (sF 0F))      (sF 0F)           = s₂ ∷ l₁ ∷ s₂ ∷ []
  wd (sF (sF 0F))      (sF (sF 0F))      = l₂ ∷ []
  wd _                 _                 = []

  back-to : ∀ (σ : Word (S.Gen 4)) {a i} → perm σ ⟨$⟩ʳ a ≡ i → perm (revS σ) ⟨$⟩ʳ i ≡ a
  back-to σ {a} e = Eq.subst (λ x → perm (revS σ) ⟨$⟩ʳ x ≡ a) e (perm-inv σ a)

  -- The CX placed by any network bringing its target to 0 and its
  -- control to 1.
  fr : ∀ (u : Fin 3) (v : Fin 4) .(p : sF u ≢ v) (ν : Word (S.Gen 4)) →
       perm ν ⟨$⟩ʳ v ≡ 0F → perm ν ⟨$⟩ʳ sF u ≡ sF 0F → 4 ⊢ cx u v p ≈ pl ν CX₁₀
  fr u v p ν e0 e1 = place-eq {k = 2} CX₁₀ b ν agree
    where
    B = bring₂ v (sF u) (C₀.ne p)
    b = proj₁ B
    agree : ∀ (j : Fin 4) → toℕ j < 2 → perm ν ⟨$⟩ʳ (perm (revS b) ⟨$⟩ʳ j) ≡ j
    agree 0F _          = Eq.trans (Eq.cong (perm ν ⟨$⟩ʳ_) (back-to b (proj₁ (proj₂ B)))) e0
    agree (sF 0F) _     = Eq.trans (Eq.cong (perm ν ⟨$⟩ʳ_) (back-to b (proj₂ (proj₂ B)))) e1
    agree (sF (sF j)) (s≤s (s≤s ()))

  σ₀ σ₁ σ₂ : Word (S.Gen 4)
  σ₀ = S.σ
  σ₁ = S.σ S.↑
  σ₂ = S.σ S.↑ S.↑

  by : ∀ (u : Fin 3) (v : Fin 4) .(p : sF u ≢ v) (ν : Word (S.Gen 4)) →
       perm ν ⟨$⟩ʳ v ≡ 0F → perm ν ⟨$⟩ʳ sF u ≡ sF 0F → Same (pl ν CX₁₀) ⟦ wd u v ⟧W →
       4 ⊢ cx u v p ≈ ⟦ wd u v ⟧W
  by u v p ν e0 e1 s = trans (fr u v p ν e0 e1) (S₄.by-sem₀ (pl ν CX₁₀) ⟦ wd u v ⟧W s)

  cx-word : ∀ (u : Fin 3) (v : Fin 4) .(p : sF u ≢ v) → 4 ⊢ cx u v p ≈ ⟦ wd u v ⟧W
  cx-word 0F           0F                p = by 0F 0F p ε Eq.refl Eq.refl Eq.refl
  cx-word 0F           (sF 0F)           p = Irr.⊥-elim (p Eq.refl)
  cx-word 0F           (sF (sF 0F))      p = by 0F (sF (sF 0F)) p (σ₀ • σ₁ • σ₀) Eq.refl Eq.refl Eq.refl
  cx-word 0F           (sF (sF (sF 0F))) p = by 0F (sF (sF (sF 0F))) p (σ₀ • σ₁ • σ₂ • σ₁ • σ₀) Eq.refl Eq.refl Eq.refl
  cx-word (sF 0F)      0F                p = by (sF 0F) 0F p σ₁ Eq.refl Eq.refl Eq.refl
  cx-word (sF 0F)      (sF 0F)           p = by (sF 0F) (sF 0F) p (σ₀ • σ₁) Eq.refl Eq.refl Eq.refl
  cx-word (sF 0F)      (sF (sF 0F))      p = Irr.⊥-elim (p Eq.refl)
  cx-word (sF 0F)      (sF (sF (sF 0F))) p = by (sF 0F) (sF (sF (sF 0F))) p (σ₂ • σ₁ • σ₀ • σ₂ • σ₁) Eq.refl Eq.refl Eq.refl
  cx-word (sF (sF 0F)) 0F                p = by (sF (sF 0F)) 0F p (σ₂ • σ₁) Eq.refl Eq.refl Eq.refl
  cx-word (sF (sF 0F)) (sF 0F)           p = by (sF (sF 0F)) (sF 0F) p (σ₀ • σ₂ • σ₁) Eq.refl Eq.refl Eq.refl
  cx-word (sF (sF 0F)) (sF (sF 0F))      p = by (sF (sF 0F)) (sF (sF 0F)) p (σ₁ • σ₀ • σ₂ • σ₁) Eq.refl Eq.refl Eq.refl
  cx-word (sF (sF 0F)) (sF (sF (sF 0F))) p = Irr.⊥-elim (p Eq.refl)

-- Stable.Gadget's Indep₀ on four wires.
ind₄ : ∀ V (u : Fin 3) (v : A₀.Wire) .(p : sF u ≢ v) →
       4 ⊢ᵧ C₀.⟪ A₀.tL (sF u) v p ⟫ • G V ≈ G V • C₀.⟪ A₀.tL (sF u) v p ⟫
ind₄ V u v p = embed (begin
  cx u v p • G V              ≈⟨ front _ (cx-word u v p) ⟩
  ⟦ wd u v ⟧W • G V           ≈⟨ pass-W V (wd u v) ⟩
  G V • ⟦ wd u v ⟧W           ≈⟨ back _ (sym (cx-word u v p)) ⟩
  G V • cx u v p              ∎)
