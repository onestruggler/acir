------------------------------------------------------------------------
-- Presentations of groups
--
-- Two wires: the rules are complete, and the circuits present S₄
--
-- The instance of BySymmetric at two wires and four states, numbered
-- along the Gray code 00, 01, 11, 10 (wire 1 first).  The transposition
-- of two consecutive states is a controlled NOT: Θ 0 is CX with a
-- white control, Θ 1 is CX upside down, Θ 2 is CX.  NOT on wire 0
-- exchanges the states 0 1 and 2 3, CX the states 2 3, and the swap the
-- states 1 3; NOT on wire 1 is NOT on wire 0 between swaps.  The
-- Coxeter relations between the Θ d and the three gates' words are
-- derived from the rules (1)–(3) in Width2.Derivations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Width2 where

open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; #_)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; suc ; _+_ ; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

import Examples.Groups.Symmetric.Interpretation as SI
open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Alt16-RevCir.BySymmetric
  using (gᵈ ; no-gen₁ ; module Step)
open import Examples.Groups.Alt16-RevCir.Semantics
  using (Bits ; ⟦_⟧ᵍ ; ⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using (Gen ; Circuit ; X-gen ; CX-gen ; Ex-gen ; gate₀ ; _↥)
open import Examples.Groups.Alt16-RevCir.Theory using (module T ; X↑≈)
import Examples.Groups.Alt16-RevCir.Width2.Derivations as D

open D using (Θ ; eqn→)

------------------------------------------------------------------------
-- The gates as words in the transpositions of four points

τ₀ τ₁ τ₂ : S.Circuit 4
τ₀ = S.σ {2}
τ₁ = S.σ {1} S.↑ᵏ 1
τ₂ = S.σ {0} S.↑ᵏ 2

fX fCX fEx fX₁ : S.Circuit 4
fX  = τ₀ • τ₂
fCX = τ₂
fEx = τ₁ • τ₂ • τ₁
fX₁ = fEx • fX • fEx

f : Gen 2 → S.Circuit 4
f X-gen     = fX
f CX-gen    = fCX
f Ex-gen    = fEx
f (X-gen ↥) = fX₁
f (gate₀ ())
f (gate₀ () ↥)
f (gate₀ () ↥ ↥)

------------------------------------------------------------------------
-- The four states

fin4 : ∀ {ℓ} (P : Fin 4 → Set ℓ) →
       P (# 0) → P (# 1) → P (# 2) → P (# 3) → ∀ i → P i
fin4 P a b c d zero                   = a
fin4 P a b c d (suc zero)             = b
fin4 P a b c d (suc (suc zero))       = c
fin4 P a b c d (suc (suc (suc zero))) = d

enc : Fin 4 → Bits 2
enc = fin4 _ (false ∷ false ∷ []) (true ∷ false ∷ [])
             (true ∷ true ∷ [])   (false ∷ true ∷ [])

dec : Bits 2 → Fin 4
dec (false ∷ false ∷ []) = # 0
dec (true  ∷ false ∷ []) = # 1
dec (true  ∷ true  ∷ []) = # 2
dec (false ∷ true  ∷ []) = # 3

dec-enc : ∀ i → dec (enc i) ≡ i
dec-enc = fin4 _ refl refl refl refl

enc-dec : ∀ x → enc (dec x) ≡ x
enc-dec (false ∷ false ∷ []) = refl
enc-dec (true  ∷ false ∷ []) = refl
enc-dec (true  ∷ true  ∷ []) = refl
enc-dec (false ∷ true  ∷ []) = refl

------------------------------------------------------------------------
-- The hypotheses of the step

private
  g : S.Gen 4 → Circuit 2
  g = gᵈ Θ 0

  order : ∀ d → 2 + d ≤ 4 → 2 T.⊢ Θ d • Θ d ≈ ε
  order d p = D.order d (≤⇒≤ᵇ p)

  braid : ∀ d → 3 + d ≤ 4 →
          2 T.⊢ Θ d • Θ (suc d) • Θ d ≈ Θ (suc d) • Θ d • Θ (suc d)
  braid d p = D.braid d (≤⇒≤ᵇ p)

  far : ∀ d e → 2 + d ≤ e → 2 + e ≤ 4 → 2 T.⊢ Θ e • Θ d ≈ Θ d • Θ e
  far d e p q = D.far d e (≤⇒≤ᵇ p) (≤⇒≤ᵇ q)

  -- The gates on their own wires, from the derivations.
  gX : 2 T.⊢ [ X-gen ]ʷ ≈ (g ʷ) fX
  gX = eqn→ D.gate-X0 refl refl

  gCX : 2 T.⊢ [ CX-gen ]ʷ ≈ (g ʷ) fCX
  gCX = eqn→ D.gate-CX0 refl refl

  gEx : 2 T.⊢ [ Ex-gen ]ʷ ≈ (g ʷ) fEx
  gEx = eqn→ D.gate-Ex0 refl refl

  gate : (x : Gen 2) → 2 T.⊢ [ x ]ʷ ≈ (g ʷ) (f x)
  gate X-gen     = gX
  gate CX-gen    = gCX
  gate Ex-gen    = gEx
  gate (X-gen ↥) = PB.trans X↑≈ (PB.cong gEx (PB.cong gX gEx))
  gate (gate₀ ())
  gate (gate₀ () ↥)
  gate (gate₀ () ↥ ↥)

  f-sem-gen : (x : Gen 2) (i : Fin 4) →
              SI.⟦ f x ⟧ ⟨$⟩ʳ i ≡ dec (⟦ x ⟧ᵍ (enc i))
  f-sem-gen X-gen     = fin4 _ refl refl refl refl
  f-sem-gen CX-gen    = fin4 _ refl refl refl refl
  f-sem-gen Ex-gen    = fin4 _ refl refl refl refl
  f-sem-gen (X-gen ↥) = fin4 _ refl refl refl refl
  f-sem-gen (gate₀ ())
  f-sem-gen (gate₀ () ↥)
  f-sem-gen (gate₀ () ↥ ↥)

  g-sem-gen : (y : S.Gen 4) (i : Fin 4) →
              dec (⟦ g y ⟧ (enc i)) ≡ SI.⟦ [ y ]ʷ ⟧ ⟨$⟩ʳ i
  g-sem-gen S.σ-gen             = fin4 _ refl refl refl refl
  g-sem-gen (S.σ-gen S.↥)       = fin4 _ refl refl refl refl
  g-sem-gen (S.σ-gen S.↥ S.↥)   = fin4 _ refl refl refl refl
  g-sem-gen (y S.↥ S.↥ S.↥) i   = ⊥-elim (no-gen₁ y)

------------------------------------------------------------------------
-- The step

module Step₂ = Step Θ f enc dec dec-enc enc-dec
                    order braid far gate f-sem-gen g-sem-gen

-- Two two-wire circuits with the same function are equal by the rules.
complete₂ : {w v : Circuit 2} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 2 T.⊢ w ≈ v
complete₂ = Step₂.complete

presentation₂ : (T._VRel,_===_ 2) IsPresentationOf (Permutation′-group 4)
presentation₂ = Step₂.presentation
