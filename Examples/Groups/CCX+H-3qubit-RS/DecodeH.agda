------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators ℱ₈ of Li, Ross and Selinger's §5 decoded as circuits
-- over Σ₂: a generator of 𝒢₈ as in Decode, and I ⊗ H as H₂.  The
-- decoding respects Tables 1 and 2: Table 1 by Decode one level up,
-- and each relation H g H = t of Table 2 by passing H₂ through the
-- decoding of g (Push) and comparing matrices, R₁⁺ being complete.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.DecodeH where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Presentation.Base as PB
import Relation.Binary.Reasoning.Setoid as SR
import Presentation.Properties as PP

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as L using (Gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as LS
  using (Genᴸ ; ⌊_⌋ ; IH ; ⌊_⌋ʷ ; _===ᴸ_ ; table1 ; r7a ; r7b ; r7c ; r7d₀ ; r7d₁)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.Lift using (lift₁₂)
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Decode coxeter₁ using (dec ; decʷ ; dec-cong)
open import Examples.Groups.CCX+HH-3qubit-opus.PresentationO8 using (complete₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Push using (conj ; pushʷ)
open import Examples.Groups.CCX+HH-3qubit-opus.TableMatrices

open PB _===₂⁺_ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open SR (PP.word-setoid _===₂⁺_)

------------------------------------------------------------------------
-- The decoding

decᴸ : Genᴸ 8 → Word G₂
decᴸ ⌊ g ⌋ = ↑ʷ (dec g)
decᴸ IH    = H2

decᴸʷ : Word (Genᴸ 8) → Word G₂
decᴸʷ = decᴸ ʷ

decᴸ-⌊⌋ : (w : Word (Gen 8)) → decᴸʷ ⌊ w ⌋ʷ ≡ ↑ʷ (decʷ w)
decᴸ-⌊⌋ [ g ]ʷ   = Eq.refl
decᴸ-⌊⌋ ε       = Eq.refl
decᴸ-⌊⌋ (u • v) = Eq.cong₂ _•_ (decᴸ-⌊⌋ u) (decᴸ-⌊⌋ v)

------------------------------------------------------------------------
-- Table 2

-- H₂ around a circuit over Σ₁ that it turns into t.
conj-H : (w t : Word G₁) → ⟦ (conj ʷ) w ⟧ ≡ ⟦ t ⟧ → H2 • ↑ʷ w • H2 ≈ ↑ʷ t
conj-H w t m = begin
  H2 • (↑ʷ w • H2)                  ≈⟨ sym assoc ⟩
  (H2 • ↑ʷ w) • H2                  ≈⟨ cong (pushʷ w) refl ⟩
  (↑ʷ ((conj ʷ) w) • H2) • H2       ≈⟨ assoc ⟩
  ↑ʷ ((conj ʷ) w) • (H2 • H2)       ≈⟨ cong refl (axiom (fig8 r108)) ⟩
  ↑ʷ ((conj ʷ) w) • ε               ≈⟨ right-unit ⟩
  ↑ʷ ((conj ʷ) w)                   ≈⟨ lift₁₂ (complete₁ m) ⟩
  ↑ʷ t                              ∎

private
  not8 : (b : Fin 8) → toℕ b ≡ 8 → ∀ {A : Set} → A
  not8 b h = ⊥-elim (ℕP.<-irrefl Eq.refl (Eq.subst (ℕ._< 8) h (FinP.toℕ<n b)))

  inj : {i j : Fin 8} → toℕ i ≡ toℕ j → i ≡ j
  inj = FinP.toℕ-injective

decᴸ-ax : {u v : Word (Genᴸ 8)} → u ===ᴸ v → decᴸʷ u ≈ decᴸʷ v
decᴸ-ax (table1 {w} {v} a) =
  Eq.subst₂ _≈_ (Eq.sym (decᴸ-⌊⌋ w)) (Eq.sym (decᴸ-⌊⌋ v)) (lift₁₂ (dec-cong (PB.axiom a)))
decᴸ-ax r7a = axiom (fig8 r108)
decᴸ-ax (r7b {a = a} {b = b} {c = c} {d = d} p q r a0 b1 c2 d3)
  with inj {a} {# 0} a0 | inj {b} {# 1} b1 | inj {c} {# 2} c2 | inj {d} {# 3} d3
... | Eq.refl | Eq.refl | Eq.refl | Eq.refl = conj-H K0123 K0123 t7b
decᴸ-ax (r7c {a = a} {b = b} p a0 b1) with inj {a} {# 0} a0 | inj {b} {# 1} b1
... | Eq.refl | Eq.refl = conj-H M0 (M0 • X01 • M0) t7c
decᴸ-ax (r7d₀ {x = zero} {y = y} p e _) with inj {y} {# 1} e
... | Eq.refl = conj-H X01 M1 t7d0
decᴸ-ax (r7d₀ {x = suc zero} p e ())
decᴸ-ax (r7d₀ {x = suc (suc zero)} {y = y} p e _) with inj {y} {# 3} e
... | Eq.refl = conj-H X23 M3 t7d2
decᴸ-ax (r7d₀ {x = suc (suc (suc zero))} p e ())
decᴸ-ax (r7d₀ {x = suc (suc (suc (suc zero)))} {y = y} p e _) with inj {y} {# 5} e
... | Eq.refl = conj-H X45 M5 t7d4
decᴸ-ax (r7d₀ {x = suc (suc (suc (suc (suc zero))))} p e ())
decᴸ-ax (r7d₀ {x = suc (suc (suc (suc (suc (suc zero)))))} {y = y} p e _) with inj {y} {# 7} e
... | Eq.refl = conj-H X67 M7 t7d6
decᴸ-ax (r7d₀ {x = suc (suc (suc (suc (suc (suc (suc zero))))))} p e ())
decᴸ-ax (r7d₁ {x = zero} p q r ex ey ez ())
decᴸ-ax (r7d₁ {w = w} {x = suc zero} {y = y} {z = z} p q r ex ey ez _)
  with inj {w} {# 0} (ℕP.suc-injective (Eq.sym ex)) | inj {y} {# 2} ey | inj {z} {# 3} (Eq.trans ez (Eq.cong ℕ.suc (Eq.trans (Eq.cong toℕ (inj {y} {# 2} ey)) Eq.refl)))
... | Eq.refl | Eq.refl | Eq.refl = conj-H X12 (X12 • K0123) t7d1
decᴸ-ax (r7d₁ {x = suc (suc zero)} p q r ex ey ez ())
decᴸ-ax (r7d₁ {w = w} {x = suc (suc (suc zero))} {y = y} {z = z} p q r ex ey ez _)
  with inj {w} {# 2} (ℕP.suc-injective (Eq.sym ex)) | inj {y} {# 4} ey | inj {z} {# 5} (Eq.trans ez (Eq.cong ℕ.suc (Eq.cong toℕ (inj {y} {# 4} ey))))
... | Eq.refl | Eq.refl | Eq.refl = conj-H X34 (X34 • K2345) t7d3
decᴸ-ax (r7d₁ {x = suc (suc (suc (suc zero)))} p q r ex ey ez ())
decᴸ-ax (r7d₁ {w = w} {x = suc (suc (suc (suc (suc zero))))} {y = y} {z = z} p q r ex ey ez _)
  with inj {w} {# 4} (ℕP.suc-injective (Eq.sym ex)) | inj {y} {# 6} ey | inj {z} {# 7} (Eq.trans ez (Eq.cong ℕ.suc (Eq.cong toℕ (inj {y} {# 6} ey))))
... | Eq.refl | Eq.refl | Eq.refl = conj-H X56 (X56 • K4567) t7d5
decᴸ-ax (r7d₁ {x = suc (suc (suc (suc (suc (suc zero)))))} p q r ex ey ez ())
decᴸ-ax (r7d₁ {x = suc (suc (suc (suc (suc (suc (suc zero))))))} {y = y} p q r ex ey ez _) = not8 y ey

decᴸ-cong : {u v : Word (Genᴸ 8)} → PB._≈_ (_===ᴸ_ {8}) u v → decᴸʷ u ≈ decᴸʷ v
decᴸ-cong PB.refl        = refl
decᴸ-cong (PB.sym h)     = sym (decᴸ-cong h)
decᴸ-cong (PB.trans h g) = trans (decᴸ-cong h) (decᴸ-cong g)
decᴸ-cong (PB.cong h g)  = cong (decᴸ-cong h) (decᴸ-cong g)
decᴸ-cong PB.assoc       = assoc
decᴸ-cong PB.left-unit   = left-unit
decᴸ-cong PB.right-unit  = right-unit
decᴸ-cong (PB.axiom a)   = decᴸ-ax a
