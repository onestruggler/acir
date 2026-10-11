------------------------------------------------------------------------
-- Presentations of groups
--
-- The box wire is a dirty ancilla (Clément, Lemma D.9, Equation (308))
--
-- A box passes any circuit on its box wire and the wires below it: on
-- its box wire the box's payload is a scalar, and below it the box is
-- idle.  By induction on the circuit, as in the paper: a gate below the
-- box wire is disjoint from the box; Z and H on the box wire are (19)
-- (Box.box-Z₀) and (285) (Keystone); the CZ from the box wire onto the
-- wire below is (272), and the CH, which is the swap of the two wires
-- around HC, is (274) and (280) (ZXPass).
--
-- The box here has at least two controls; with one it is Z on its
-- control and its box wire is idle.  `boxAt K j` is the box with K
-- controls whose box wire is wire j; the paper's controls above the box
-- wire are the wires j + 1 … j + K.  Only completeness below the width
-- is used (`Below`), for (285) and (274)/(280) one width down.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_)
open import Data.Nat.Properties using (n<1+n ; m<n⇒m<1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq155)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (box-Z₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃
  using (Complete ; box272 ; box274 ; eq280)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃ using (eq285ₙ)

------------------------------------------------------------------------
-- Completeness below a width

Comp : ℕ → Set
Comp n = ∀ {u v : Circuit n} → ⟦ u ⟧ ~ ⟦ v ⟧ → n ⊢ u ≈ v

Below : ℕ → Set
Below n = ∀ {i} → i < n → Comp i

below-suc : ∀ {n} → Below (suc n) → Below n
below-suc b i< = b (m<n⇒m<1+n i<)

------------------------------------------------------------------------
-- The box, its box wire on wire j

boxAt : ∀ K j → Circuit (₁₊ j + K)
boxAt K zero    = Λ□ K
boxAt K (suc j) = boxAt K j ↑

------------------------------------------------------------------------
-- Word algebra

module _ {W : ℕ} where
  open Tools (W VRel,_===_)

  -- Two words passing B pass their product.
  pass-• : ∀ {B x y : Circuit W} → x • B ≈ B • x → y • B ≈ B • y → (x • y) • B ≈ B • (x • y)
  pass-• {B} {x} {y} ex ey = begin
    (x • y) • B   ≈⟨ assoc ⟩
    x • (y • B)   ≈⟨ back _ ey ⟩
    x • (B • y)   ≈⟨ sym assoc ⟩
    (x • B) • y   ≈⟨ front _ ex ⟩
    (B • x) • y   ≈⟨ assoc ⟩
    B • (x • y) ∎

  pass-ε : ∀ {B : Circuit W} → ε • B ≈ B • ε
  pass-ε = trans left-unit (sym right-unit)

  -- A word passing B passes an equal word.
  pass-≈ : ∀ {B x y : Circuit W} → x ≈ y → x • B ≈ B • x → y • B ≈ B • y
  pass-≈ e p = trans (front _ (sym e)) (trans p (back _ e))

------------------------------------------------------------------------
-- The generators

private
  -- On the box wire: Z by (19), H by (285) one width down.
  one : ∀ k → Below (₃₊ k) → ∀ h →
        (₃₊ k) ⊢ [ gate₁ h ]ʷ • Λ□ (₂₊ k) ≈ Λ□ (₂₊ k) • [ gate₁ h ]ʷ
  one k             b Z-gate = box-Z₀ k
  one zero          b H-gate = PB.sym (comm-gate₁-w↑ H-gate (CZ {0}))
  one (suc zero)    b H-gate = eq155 {0}
  one (suc (suc k)) b H-gate = eq285ₙ (₁₊ k) (b (n<1+n (₄₊ k)))

  -- The CH from the box wire onto the wire below: the swap of the two
  -- wires around HC, each passing the box.
  CH-pass : ∀ k → Complete k → (₄₊ k) ⊢ CH • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • CH
  CH-pass k c = pass-≈ CH-HC (pass-• ex (pass-• (eq280 k c) ex))
    where
    open Tools ((₄₊ k) VRel,_===_)
    ex : Ex • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • Ex
    ex = sym (conj-comm Ex² (box274 k c))
    CH-HC : Ex • HC • Ex ≈ CH
    CH-HC = begin
      Ex • (Ex • CH • Ex) • Ex     ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (Ex • Ex) • CH • (Ex • Ex)   ≈⟨ cong Ex² (back _ Ex²) ⟩
      ε • CH • ε                   ≈⟨ trans left-unit right-unit ⟩
      CH ∎

  -- From the box wire onto the wire below: CZ by (272), CH as above.
  two : ∀ k → Complete k → ∀ h →
        (₄₊ k) ⊢ [ gate₂ h ]ʷ • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • [ gate₂ h ]ʷ
  two k c CZ-gate = box272 k
  two k c CH-gate = CH-pass k c

  -- Every generator on the box wire or below it.
  gen : ∀ k j → Below (₁₊ j + ₂₊ k) → (g : Gen (₁₊ j)) →
        (₁₊ j + ₂₊ k) ⊢ ([ g ]ʷ ↓ᵏ ₂₊ k) • boxAt (₂₊ k) j ≈ boxAt (₂₊ k) j • ([ g ]ʷ ↓ᵏ ₂₊ k)
  gen k j             b (gate₀ ())
  gen k zero          b (gate₁ h)    = one k b h
  gen k zero          b (gate₀ () ↥)
  gen k (suc j)       b (gate₁ h)    = PB.sym (comm-gate₁-w↑ h (boxAt (₂₊ k) j))
  gen k (suc zero)    b (gate₂ h)    = two k (b (n<1+n (₃₊ k))) h
  gen k (suc (suc j)) b (gate₂ h)    = PB.sym (comm-gate₂-w↑↑ h (boxAt (₂₊ k) j))
  gen k (suc j)       b (g ↥)        =
    lemma-cong↑ (([ g ]ʷ ↓ᵏ ₂₊ k) • boxAt (₂₊ k) j) (boxAt (₂₊ k) j • ([ g ]ʷ ↓ᵏ ₂₊ k))
                (gen k j (below-suc b) g)

------------------------------------------------------------------------
-- (308)

eq308 : ∀ k j → Below (₁₊ j + ₂₊ k) → (C : Circuit (₁₊ j)) →
        (₁₊ j + ₂₊ k) ⊢ (C ↓ᵏ ₂₊ k) • boxAt (₂₊ k) j ≈ boxAt (₂₊ k) j • (C ↓ᵏ ₂₊ k)
eq308 k j b [ g ]ʷ  = gen k j b g
eq308 k j b ε       = pass-ε
eq308 k j b (u • v) = pass-• (eq308 k j b u) (eq308 k j b v)
