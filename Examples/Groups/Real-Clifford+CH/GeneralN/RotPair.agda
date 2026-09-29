------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation passes a placed box on another target, inverted
-- (Clément, Appendix E.5; the pair step of rule (31))
--
-- A rotation on the wire t and a box on the wire t′ ≠ t, coloured alike
-- off those two wires, are conjugated by a network bringing t, t′ to
-- the wires 0, 1 (Placed.bring₂).  The rotation becomes the canonical
-- one and the box B, the box on wire 1, in a colouring relative to the
-- rotation's that is black off the wires 0 1 — which is Canon31's pair
-- step K1: the rotation passes the box and comes out inverted.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotPair
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; combine ; _⇔_ ; col-col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pl ; pl-• ; pl-cong ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (Rigid ; frame₁ ; place ; place-pl ; unpl ; swW-lookup ; combine-lookup ; ⇔-same ;
         revS² ; perm-back ; bring₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon31 complete₂ complete₃ using (K1)

------------------------------------------------------------------------
-- Generalities

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  -- An equation carried back through a placement.
  reflect′ : ∀ (w : Word (S.Gen n)) {a b c d : Circuit n} →
             pl (revS w) a • pl (revS w) b ≈ pl (revS w) c • pl (revS w) d → a • b ≈ c • d
  reflect′ w {a} {b} {c} {d} e = begin
    a • b                                          ≈⟨ sym (cong (unpl′ a) (unpl′ b)) ⟩
    pl w (pl (revS w) a) • pl w (pl (revS w) b)    ≈⟨ sym (pl-• w _ _) ⟩
    pl w (pl (revS w) a • pl (revS w) b)           ≈⟨ pl-cong w e ⟩
    pl w (pl (revS w) c • pl (revS w) d)           ≈⟨ pl-• w _ _ ⟩
    pl w (pl (revS w) c) • pl w (pl (revS w) d)    ≈⟨ cong (unpl′ c) (unpl′ d) ⟩
    c • d ∎
    where
    unpl′ : ∀ z → pl w (pl (revS w) z) ≈ z
    unpl′ z = Eq.subst (λ v → pl v (pl (revS w) z) ≈ z) (revS² w) (unpl (revS w) z)

  -- Two colourings: only the relative colouring counts.
  col-rel′ : ∀ (x y : Bits n) {w w′ v : Circuit n} →
             w • col (combine x y) v ≈ col (combine x y) v • w′ → col x w • col y v ≈ col y v • col x w′
  col-rel′ x y {w} {w′} {v} h = Cx.⟪⟫-≈ h (Cx.⟪⟫-•₂ refl e) (Cx.⟪⟫-•₂ e refl)
    where
    module Cx = Conj {n} (negsB x) (negs² x)
    cancel : ∀ a b → (a ⇔ (a ⇔ b)) ≡ b
    cancel true  b     = Eq.refl
    cancel false true  = Eq.refl
    cancel false false = Eq.refl
    ccancel : ∀ {j} (p q : Bits j) → combine p (combine p q) ≡ q
    ccancel []      []      = Eq.refl
    ccancel (a ∷ p) (b ∷ q) = Eq.cong₂ _∷_ (cancel a b) (ccancel p q)
    e : Cx.⟪ col (combine x y) v ⟫ ≈ col y v
    e = trans (col-col x (combine x y) v)
              (Eq.subst (λ u → col (combine x (combine x y)) v ≈ col u v) (ccancel x y) refl)

-- A bit string all true from the wire 2 on.
private
  lookup-ones : ∀ {j} i → i < j → lookupℕ i (replicate j true) ≡ true
  lookup-ones {suc j} zero    _       = Eq.refl
  lookup-ones {suc j} (suc i) (s≤s p) = lookup-ones i p

  ext : ∀ {j} (p q : Bits j) → (∀ i → i < j → lookupℕ i p ≡ lookupℕ i q) → p ≡ q
  ext []      []      _ = Eq.refl
  ext (a ∷ p) (b ∷ q) h = Eq.cong₂ _∷_ (h 0 (s≤s z≤n)) (ext p q (λ i i< → h (suc i) (s≤s i<)))

  split₂ : ∀ {j} (z : Bits (₂₊ j)) → (∀ i → i < j → lookupℕ (₂₊ i) z ≡ true) →
           z ≡ lookupℕ 0 z ∷ lookupℕ 1 z ∷ replicate j true
  split₂ (a ∷ b ∷ r) h = Eq.cong (λ q → a ∷ b ∷ q) (ext r _ (λ i i< → Eq.trans (h i i<) (Eq.sym (lookup-ones i i<))))

------------------------------------------------------------------------
-- The pair step, placed

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

    Λ B : Circuit N
    Λ = Λ□ (₄₊ k)
    B = Ex ↓ • Λ • Ex ↓

  open Tools (N VRel,_===_)

  private
    rig-rot : ∀ β → Rigid 1 (rot {₂₊ k} β)
    rig-rot β v = rot-rigid k below β v

    rig-Λ : Rigid 1 Λ
    rig-Λ v = Canon.swaps canon v

    -- In the frame of σ: σ sends the target to wire 0, resp. 1.
    frame-0 : ∀ {g} → Rigid 1 g → (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
              (s : Bits N) → pl (revS σ) (place u s g) ≈ col (swW (revS σ) s) g
    frame-0 {g} rg σ u t pu σt s =
      trans (place-pl (revS σ) u s g) (mid _ _ (trans (frame₁ rg (revS σ • u) ε cond) (trans left-unit right-unit)))
      where
      cond : perm ε ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                      (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)

    frame-1 : ∀ {g} → Rigid 1 g → (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF 0F →
              (s : Bits N) → pl (revS σ) (place u s g) ≈ col (swW (revS σ) s) (Ex • g • Ex)
    frame-1 {g} rg σ u t pu σt s =
      trans (place-pl (revS σ) u s g) (mid _ _ (frame₁ rg (revS σ • u) S.σ cond))
      where
      cond : perm S.σ ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm S.σ ⟨$⟩ʳ_)
                        (Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                                  (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)))
                      perm-σ₁

    bit : ∀ (σ : Word (S.Gen N)) (s : Bits N) (t i : Fin N) → perm σ ⟨$⟩ʳ t ≡ i →
          lookupℕ (toℕ i) (swW (revS σ) s) ≡ lookupℕ (toℕ t) s
    bit σ s t i e = Eq.trans (swW-lookup (revS σ) s i) (Eq.cong (λ x → lookupℕ (toℕ x) s) (perm-back σ e))

  pair-step : ∀ β (u u′ : Word (S.Gen N)) (t t′ : Fin N) → t′ ≢ t →
              perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F → (s s′ : Bits N) →
              (∀ (j : Fin N) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≡ lookupℕ (toℕ j) s′) →
              place u s (rot β) • place u′ s′ Λ ≈ place u′ s′ Λ • place u s (rot (not β))
  pair-step β u u′ t t′ t′t pu pu′ s s′ agree with bring₂ t t′ t′t
  ... | σ , σt , σt′ = reflect′ σ (begin
    pl (revS σ) (place u s (rot β)) • pl (revS σ) (place u′ s′ Λ)
      ≈⟨ cong (frame-0 (rig-rot β) σ u t pu σt s) (frame-1 rig-Λ σ u′ t′ pu′ σt′ s′) ⟩
    col x (rot β) • col y B
      ≈⟨ col-rel′ x y (Eq.subst (λ w → rot β • col w B ≈ col w B • rot (not β)) (Eq.sym zs)
                                (K1 k below β (lookupℕ 0 z) (lookupℕ 1 z))) ⟩
    col y B • col x (rot (not β))
      ≈⟨ sym (cong (frame-1 rig-Λ σ u′ t′ pu′ σt′ s′) (frame-0 (rig-rot (not β)) σ u t pu σt s)) ⟩
    pl (revS σ) (place u′ s′ Λ) • pl (revS σ) (place u s (rot (not β))) ∎)
    where
    x y z : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) s′
    z = combine x y
    -- Off the wires 0 1 the two colourings agree in the frame.
    high : ∀ i → i < ₃₊ k → lookupℕ (₂₊ i) z ≡ true
    high i i< = Eq.trans (combine-lookup (₂₊ i) x y (s≤s (s≤s i<)))
                  (Eq.trans (Eq.cong₂ _⇔_ (Eq.trans (Eq.cong (λ q → lookupℕ q x) (Eq.sym ti)) (swW-lookup (revS σ) s iF))
                                         (Eq.trans (Eq.cong (λ q → lookupℕ q y) (Eq.sym ti)) (swW-lookup (revS σ) s′ iF)))
                    (Eq.trans (Eq.cong (λ b → lookupℕ (toℕ j) s ⇔ b) (Eq.sym (agree j jt jt′))) (⇔-same (lookupℕ (toℕ j) s))))
      where
      i<N : ₂₊ i < N
      i<N = s≤s (s≤s i<)
      iF : Fin N
      iF = fromℕ< i<N
      ti : toℕ iF ≡ ₂₊ i
      ti = toℕ-fromℕ< i<N
      j : Fin N
      j = perm (revS σ) ⟨$⟩ʳ iF
      -- σ sends j back to iF, which is neither wire 0 nor wire 1.
      σj : perm σ ⟨$⟩ʳ j ≡ iF
      σj = Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ j) (Eq.sym (revS² σ))) (perm-back (revS σ) Eq.refl)
      jt : j ≢ t
      jt e with Eq.trans (Eq.sym ti) (Eq.cong toℕ (Eq.trans (Eq.sym σj) (Eq.trans (Eq.cong (perm σ ⟨$⟩ʳ_) e) σt)))
      ... | ()
      jt′ : j ≢ t′
      jt′ e with Eq.trans (Eq.sym ti) (Eq.cong toℕ (Eq.trans (Eq.sym σj) (Eq.trans (Eq.cong (perm σ ⟨$⟩ʳ_) e) σt′)))
      ... | ()
    zs : z ≡ lookupℕ 0 z ∷ lookupℕ 1 z ∷ replicate (₃₊ k) true
    zs = split₂ z high
