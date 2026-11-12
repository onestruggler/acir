------------------------------------------------------------------------
-- Presentations of groups
--
-- Three wires: the rules are complete, and the circuits present S₈
--
-- The instance of BySymmetric at three wires and eight states,
-- numbered along the Gray code 000, 001, 011, 010, 110, 111, 101, 100
-- (wire 2 first).  The transposition of two consecutive states is an
-- edge Toffoli Θ d: NOT on the wire that changes, controlled by the
-- other two, between NOT gates on the controls that are 0 and the
-- swaps that bring the wires into place (Width3.Derivations has the
-- seven).  The gates on their own wires are words in them — NOT on
-- wire 0 exchanges the states 0 1, 2 3, 4 5 and 6 7, CX the states 2 3
-- and 4 5, CCX the states 4 5, the swap of the wires 0 1 the states
-- 1 3 and 4 6, and that of the wires 1 2 the states 2 6 and 3 7 — and
-- NOT and CX further up are those between swaps.  The Coxeter
-- relations between the Θ d and the five gates' words are derived from
-- the rules (1)–(6) in Width3.Derivations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Width3 where

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
  using (Gen ; Circuit ; X-gen ; CX-gen ; Ex-gen ; CCX-gen ; gate₀ ; _↥)
open import Examples.Groups.Alt16-RevCir.Theory
  using (module T ; X↑≈ ; CX↑≈)
import Examples.Groups.Alt16-RevCir.Width3.Derivations as D

open D using (Θ ; eqn→)

------------------------------------------------------------------------
-- The gates as words in the transpositions of eight points

τ₀ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : S.Circuit 8
τ₀ = S.σ {6}
τ₁ = S.σ {5} S.↑ᵏ 1
τ₂ = S.σ {4} S.↑ᵏ 2
τ₃ = S.σ {3} S.↑ᵏ 3
τ₄ = S.σ {2} S.↑ᵏ 4
τ₅ = S.σ {1} S.↑ᵏ 5
τ₆ = S.σ {0} S.↑ᵏ 6

-- The gates on their own wires.
fX fCX fCCX fEx₀ fEx₁ : S.Circuit 8
fX   = τ₀ • τ₂ • τ₄ • τ₆
fCX  = τ₂ • τ₄
fCCX = τ₄
fEx₀ = τ₁ • τ₂ • τ₁ • τ₄ • τ₅ • τ₄
fEx₁ = τ₂ • τ₃ • τ₄ • τ₅ • τ₄ • τ₃ • τ₂ •
       τ₃ • τ₄ • τ₅ • τ₆ • τ₅ • τ₄ • τ₃

-- NOT and CX further up, between the swaps.
fX₁ fX₂ fCX₁ : S.Circuit 8
fX₁  = fEx₀ • fX • fEx₀
fX₂  = fEx₁ • fX₁ • fEx₁
fCX₁ = (fEx₀ • fEx₁) • fCX • (fEx₁ • fEx₀)

f : Gen 3 → S.Circuit 8
f X-gen         = fX
f CX-gen        = fCX
f Ex-gen        = fEx₀
f CCX-gen       = fCCX
f (X-gen ↥)     = fX₁
f (CX-gen ↥)    = fCX₁
f (Ex-gen ↥)    = fEx₁
f (X-gen ↥ ↥)   = fX₂
f (gate₀ ())
f (gate₀ () ↥)
f (gate₀ () ↥ ↥)
f (gate₀ () ↥ ↥ ↥)

------------------------------------------------------------------------
-- The eight states

fin8 : ∀ {ℓ} (P : Fin 8 → Set ℓ) →
       P (# 0) → P (# 1) → P (# 2) → P (# 3) →
       P (# 4) → P (# 5) → P (# 6) → P (# 7) → ∀ i → P i
fin8 P a b c d e f′ g′ h zero = a
fin8 P a b c d e f′ g′ h (suc zero) = b
fin8 P a b c d e f′ g′ h (suc (suc zero)) = c
fin8 P a b c d e f′ g′ h (suc (suc (suc zero))) = d
fin8 P a b c d e f′ g′ h (suc (suc (suc (suc zero)))) = e
fin8 P a b c d e f′ g′ h (suc (suc (suc (suc (suc zero))))) = f′
fin8 P a b c d e f′ g′ h (suc (suc (suc (suc (suc (suc zero)))))) = g′
fin8 P a b c d e f′ g′ h
     (suc (suc (suc (suc (suc (suc (suc zero))))))) = h

enc : Fin 8 → Bits 3
enc = fin8 _
  (false ∷ false ∷ false ∷ []) (true  ∷ false ∷ false ∷ [])
  (true  ∷ true  ∷ false ∷ []) (false ∷ true  ∷ false ∷ [])
  (false ∷ true  ∷ true  ∷ []) (true  ∷ true  ∷ true  ∷ [])
  (true  ∷ false ∷ true  ∷ []) (false ∷ false ∷ true  ∷ [])

dec : Bits 3 → Fin 8
dec (false ∷ false ∷ false ∷ []) = # 0
dec (true  ∷ false ∷ false ∷ []) = # 1
dec (true  ∷ true  ∷ false ∷ []) = # 2
dec (false ∷ true  ∷ false ∷ []) = # 3
dec (false ∷ true  ∷ true  ∷ []) = # 4
dec (true  ∷ true  ∷ true  ∷ []) = # 5
dec (true  ∷ false ∷ true  ∷ []) = # 6
dec (false ∷ false ∷ true  ∷ []) = # 7

dec-enc : ∀ i → dec (enc i) ≡ i
dec-enc = fin8 _ refl refl refl refl refl refl refl refl

enc-dec : ∀ x → enc (dec x) ≡ x
enc-dec (false ∷ false ∷ false ∷ []) = refl
enc-dec (true  ∷ false ∷ false ∷ []) = refl
enc-dec (true  ∷ true  ∷ false ∷ []) = refl
enc-dec (false ∷ true  ∷ false ∷ []) = refl
enc-dec (false ∷ true  ∷ true  ∷ []) = refl
enc-dec (true  ∷ true  ∷ true  ∷ []) = refl
enc-dec (true  ∷ false ∷ true  ∷ []) = refl
enc-dec (false ∷ false ∷ true  ∷ []) = refl

------------------------------------------------------------------------
-- The hypotheses of the step

private
  g : S.Gen 8 → Circuit 3
  g = gᵈ Θ 0

  order : ∀ d → 2 + d ≤ 8 → 3 T.⊢ Θ d • Θ d ≈ ε
  order d p = D.order d (≤⇒≤ᵇ p)

  braid : ∀ d → 3 + d ≤ 8 →
          3 T.⊢ Θ d • Θ (suc d) • Θ d ≈ Θ (suc d) • Θ d • Θ (suc d)
  braid d p = D.braid d (≤⇒≤ᵇ p)

  far : ∀ d e → 2 + d ≤ e → 2 + e ≤ 8 → 3 T.⊢ Θ e • Θ d ≈ Θ d • Θ e
  far d e p q = D.far d e (≤⇒≤ᵇ p) (≤⇒≤ᵇ q)

  -- The gates on their own wires, from the derivations.
  gX : 3 T.⊢ [ X-gen ]ʷ ≈ (g ʷ) fX
  gX = eqn→ D.gate-X0 refl refl

  gCX : 3 T.⊢ [ CX-gen ]ʷ ≈ (g ʷ) fCX
  gCX = eqn→ D.gate-CX0 refl refl

  gCCX : 3 T.⊢ [ CCX-gen ]ʷ ≈ (g ʷ) fCCX
  gCCX = eqn→ D.gate-CCX0 refl refl

  gEx₀ : 3 T.⊢ [ Ex-gen ]ʷ ≈ (g ʷ) fEx₀
  gEx₀ = eqn→ D.gate-Ex0 refl refl

  gEx₁ : 3 T.⊢ [ Ex-gen ↥ ]ʷ ≈ (g ʷ) fEx₁
  gEx₁ = eqn→ D.gate-Ex1 refl refl

  -- NOT and CX further up, by the naturality of the swap.
  gX₁ : 3 T.⊢ [ X-gen ↥ ]ʷ ≈ (g ʷ) fX₁
  gX₁ = PB.trans X↑≈ (PB.cong gEx₀ (PB.cong gX gEx₀))

  gX₂ : 3 T.⊢ [ X-gen ↥ ↥ ]ʷ ≈ (g ʷ) fX₂
  gX₂ = PB.trans (T.lemma-cong↑ _ _ (X↑≈ {0}))
                 (PB.cong gEx₁ (PB.cong gX₁ gEx₁))

  gCX₁ : 3 T.⊢ [ CX-gen ↥ ]ʷ ≈ (g ʷ) fCX₁
  gCX₁ = PB.trans CX↑≈
    (PB.cong (PB.cong gEx₀ gEx₁) (PB.cong gCX (PB.cong gEx₁ gEx₀)))

  gate : (x : Gen 3) → 3 T.⊢ [ x ]ʷ ≈ (g ʷ) (f x)
  gate X-gen       = gX
  gate CX-gen      = gCX
  gate Ex-gen      = gEx₀
  gate CCX-gen     = gCCX
  gate (X-gen ↥)   = gX₁
  gate (CX-gen ↥)  = gCX₁
  gate (Ex-gen ↥)  = gEx₁
  gate (X-gen ↥ ↥) = gX₂
  gate (gate₀ ())
  gate (gate₀ () ↥)
  gate (gate₀ () ↥ ↥)
  gate (gate₀ () ↥ ↥ ↥)

  f-sem-gen : (x : Gen 3) (i : Fin 8) →
              SI.⟦ f x ⟧ ⟨$⟩ʳ i ≡ dec (⟦ x ⟧ᵍ (enc i))
  f-sem-gen X-gen       = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen CX-gen      = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen Ex-gen      = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen CCX-gen     = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen (X-gen ↥)   = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen (CX-gen ↥)  = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen (Ex-gen ↥)  = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen (X-gen ↥ ↥) = fin8 _ refl refl refl refl refl refl refl refl
  f-sem-gen (gate₀ ())
  f-sem-gen (gate₀ () ↥)
  f-sem-gen (gate₀ () ↥ ↥)
  f-sem-gen (gate₀ () ↥ ↥ ↥)

  pattern 3↥ y = y S.↥ S.↥ S.↥

  g-sem-gen : (y : S.Gen 8) (i : Fin 8) →
              dec (⟦ g y ⟧ (enc i)) ≡ SI.⟦ [ y ]ʷ ⟧ ⟨$⟩ʳ i
  g-sem-gen S.σ-gen =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (S.σ-gen S.↥) =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (S.σ-gen S.↥ S.↥) =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (3↥ S.σ-gen) =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (3↥ (S.σ-gen S.↥)) =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (3↥ (S.σ-gen S.↥ S.↥)) =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (3↥ (3↥ S.σ-gen)) =
    fin8 _ refl refl refl refl refl refl refl refl
  g-sem-gen (3↥ (3↥ (y S.↥))) i = ⊥-elim (no-gen₁ y)

------------------------------------------------------------------------
-- The step

module Step₃ = Step Θ f enc dec dec-enc enc-dec
                    order braid far gate f-sem-gen g-sem-gen

-- Two three-wire circuits with the same function are equal by the
-- rules.
complete₃ : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 3 T.⊢ w ≈ v
complete₃ = Step₃.complete

presentation₃ : (T._VRel,_===_ 3) IsPresentationOf (Permutation′-group 8)
presentation₃ = Step₃.presentation
