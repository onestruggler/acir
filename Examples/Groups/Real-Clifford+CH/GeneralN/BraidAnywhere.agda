------------------------------------------------------------------------
-- Presentations of groups
--
-- Two crossed rotations braid, in every colour and placed anywhere
-- (Clément, Appendix E.5, (358) as rule (24) uses it)
--
-- Two placed rotations P, Q with targets t ≠ t′, whose colourings agree
-- off the two targets, where P's type is decided by Q's colour on P's
-- target and Q's by P's colour on Q's target (as for two consecutive
-- Gray-code steps), satisfy P • Q • P ≈ Q • P • Q (`braid`).  A network
-- bringing t, t′ to the wires 0, 1 (Placed.bring₂) makes them the
-- canonical rotations on wires 0 and 1, and the colourings, relative to
-- each other, differ only on those two wires (a three-factor `col-rel`).
-- What is left is `C24 γ δ`, the canonical braid in the four colourings
-- of the wires 0 1.  A white control on B's target is X there, which
-- turns B over ((356)); white on A's target is X on wire 0 around (358),
-- which turns A over.  So all four are (358).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BraidAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; X² ; Ex² ; S-X↓)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; revS)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; _⇔_ ; combine ; col-col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-• ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (Rigid ; frame₁ ; place ; place-pl ; swW-lookup ; combine-lookup ; ⇔-same ; revS² ; perm-back ; bring₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (Braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotPair complete₂ complete₃ using (reflect′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX356 complete₂ complete₃ using (eq356)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon358 complete₂ complete₃ using (eq358)

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

  ⇔-true : ∀ b → (b ⇔ true) ≡ b
  ⇔-true true  = Eq.refl
  ⇔-true false = Eq.refl

  not-not : ∀ b → not (not b) ≡ b
  not-not true  = Eq.refl
  not-not false = Eq.refl

  cancel : ∀ a b → (a ⇔ (a ⇔ b)) ≡ b
  cancel true  b     = Eq.refl
  cancel false true  = Eq.refl
  cancel false false = Eq.refl

  ccancel : ∀ {j} (p q : Bits j) → combine p (combine p q) ≡ q
  ccancel []      []      = Eq.refl
  ccancel (a ∷ p) (b ∷ q) = Eq.cong₂ _∷_ (cancel a b) (ccancel p q)

-- Only the relative colouring counts, for three factors.
module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  col-rel₃ : ∀ (x y : Bits n) {w v : Circuit n} →
             w • (col (combine x y) v • w) ≈ col (combine x y) v • (w • col (combine x y) v) →
             col x w • (col y v • col x w) ≈ col y v • (col x w • col y v)
  col-rel₃ x y {w} {v} h = Cx.⟪⟫-≈ h (Cx.⟪⟫-•₃ refl e refl) (Cx.⟪⟫-•₃ e refl e)
    where
    module Cx = Conj {n} (negsB x) (negs² x)
    e : Cx.⟪ col (combine x y) v ⟫ ≈ col y v
    e = trans (col-col x (combine x y) v)
              (Eq.subst (λ u → col (combine x (combine x y)) v ≈ col u v) (ccancel x y) refl)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

  open Tools (N VRel,_===_)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    ones₃ : Bits (₃₊ k)
    ones₃ = replicate (₃₊ k) true

    module NX = Conj {N} X X²
    module S₀₁ = Conj {N} (Ex ↓) Ex²

    -- The rotation on wire 1, and its colourings of the wires 0 1.
    B : Bool → Circuit N
    B δ = Ex ↓ • rot δ • Ex ↓

    cl : Bool → Bool → Circuit N
    cl γ δ = col (γ ∷ δ ∷ ones₃) (B δ)

    col-11 : ∀ (w : Circuit N) → col (true ∷ true ∷ ones₃) w ≈ w
    col-11 w = trans (≡→≈ (Eq.cong (λ z → z • w • z) (allT N))) (trans left-unit right-unit)

    col-01 : ∀ (w : Circuit N) → col (false ∷ true ∷ ones₃) w ≈ X • w • X
    col-01 w = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) • w • (X • z ↑)) (allT (₄₊ k))))
                     (cong right-unit (back _ right-unit))

    col-10 : ∀ (w : Circuit N) → col (true ∷ false ∷ ones₃) w ≈ X ↑ • w • X ↑
    col-10 w = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) ↑ • w • (X • z ↑) ↑) (allT (₃₊ k))))
                     (cong right-unit (back _ right-unit))

    col-00 : ∀ (w : Circuit N) → col (false ∷ false ∷ ones₃) w ≈ X • (X ↑ • w • X ↑) • X
    col-00 w = begin
      (X • (X • z ↑) ↑) • w • (X • (X • z ↑) ↑)
        ≈⟨ ≡→≈ (Eq.cong (λ u → (X • (X • u ↑) ↑) • w • (X • (X • u ↑) ↑)) (allT (₃₊ k))) ⟩
      (X • (X ↑ • ε)) • w • (X • (X ↑ • ε))
        ≈⟨ cong (back _ right-unit) (back _ (back _ right-unit)) ⟩
      (X • X ↑) • w • (X • X ↑)
        ≈⟨ back _ (back _ (X-↑ X)) ⟩
      (X • X ↑) • w • (X ↑ • X)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      X • (X ↑ • w • X ↑) • X ∎
      where
      z : Circuit (₃₊ k)
      z = negsB ones₃

    -- X on B's target turns it over ((356) under the swap).
    X-B : X ↑ • B false • X ↑ ≈ B true
    X-B = trans (sym (S₀₁.⟪⟫-•₃ S-X↓ refl S-X↓)) (S₀₁.⟪⟫-cong (eq356 k below))

    cl-0 : ∀ γ → cl γ false ≈ cl γ true
    cl-0 true  = trans (col-10 (B false)) (trans X-B (sym (col-11 (B true))))
    cl-0 false = trans (col-00 (B false)) (trans (back _ (front _ X-B)) (sym (col-01 (B true))))

  ----------------------------------------------------------------------
  -- The canonical braid in the four colourings of the wires 0 1

  private
    C24-tt : rot false • (cl true true • rot false) ≈ cl true true • (rot false • cl true true)
    C24-tt = trans (back _ (front _ (col-11 (B true))))
               (trans (eq358 k below) (sym (cong (col-11 (B true)) (back _ (col-11 (B true))))))

    C24-ft : rot true • (cl false true • rot true) ≈ cl false true • (rot true • cl false true)
    C24-ft = trans (back _ (front _ (col-01 (B true))))
               (trans (NX.⟪⟫-≈ (eq358 k below) (NX.⟪⟫-•₃ (eq356 k below) refl (eq356 k below))
                                               (NX.⟪⟫-•₃ refl (eq356 k below) refl))
                      (sym (cong (col-01 (B true)) (back _ (col-01 (B true))))))

    -- A white control on B's target changes nothing.
    via-0 : ∀ γ → rot (not γ) • (cl γ true • rot (not γ)) ≈ cl γ true • (rot (not γ) • cl γ true) →
            rot (not γ) • (cl γ false • rot (not γ)) ≈ cl γ false • (rot (not γ) • cl γ false)
    via-0 γ e = trans (back _ (front _ (cl-0 γ))) (trans e (sym (cong (cl-0 γ) (back _ (cl-0 γ)))))

  C24 : ∀ γ δ → rot (not γ) • (cl γ δ • rot (not γ)) ≈ cl γ δ • (rot (not γ) • cl γ δ)
  C24 true  true  = C24-tt
  C24 false true  = C24-ft
  C24 true  false = via-0 true C24-tt
  C24 false false = via-0 false C24-ft

  private
    C24′ : ∀ α β → rot α • (col (not α ∷ β ∷ ones₃) (B β) • rot α) ≈
                   col (not α ∷ β ∷ ones₃) (B β) • (rot α • col (not α ∷ β ∷ ones₃) (B β))
    C24′ true  β = C24 false β
    C24′ false β = C24 true β

    rig-rot : ∀ β → Rigid 1 (rot {₂₊ k} β)
    rig-rot β v = rot-rigid k below β v

    frame-0 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (rot β)
    frame-0 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β))
            (mid _ _ (trans (frame₁ (rig-rot β) (revS σ • u) ε cond) (trans left-unit right-unit)))
      where
      cond : perm ε ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                      (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)

    frame-1 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF 0F →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (Ex • rot β • Ex)
    frame-1 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β)) (mid _ _ (frame₁ (rig-rot β) (revS σ • u) S.σ cond))
      where
      cond : perm S.σ ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm S.σ ⟨$⟩ʳ_)
                        (Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                                  (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)))
                      perm-σ₁

    bit : ∀ (σ : Word (S.Gen N)) (s : Bits N) (t i : Fin N) → perm σ ⟨$⟩ʳ t ≡ i →
          lookupℕ (toℕ i) (swW (revS σ) s) ≡ lookupℕ (toℕ t) s
    bit σ s t i e = Eq.trans (swW-lookup (revS σ) s i) (Eq.cong (λ x → lookupℕ (toℕ x) s) (perm-back σ e))

  ----------------------------------------------------------------------
  -- The braid, placed

  braid : Braid (₂₊ k)
  braid α β u u′ t t′ t′t pu pu′ s s′ st st′ agree αe βe with bring₂ t t′ t′t
  ... | σ , σt , σt′ = reflect′ σ (begin
    pl (revS σ) P • pl (revS σ) (Q • P)
      ≈⟨ back _ (pl-• (revS σ) Q P) ⟩
    pl (revS σ) P • (pl (revS σ) Q • pl (revS σ) P)
      ≈⟨ cong fP (cong fQ fP) ⟩
    col x (rot α) • (col y (B β) • col x (rot α))
      ≈⟨ col-rel₃ x y (Eq.subst (λ w → rot α • (col w (B β) • rot α) ≈ col w (B β) • (rot α • col w (B β)))
                                (Eq.sym zs) (C24′ α β)) ⟩
    col y (B β) • (col x (rot α) • col y (B β))
      ≈⟨ sym (cong fQ (cong fP fQ)) ⟩
    pl (revS σ) Q • (pl (revS σ) P • pl (revS σ) Q)
      ≈⟨ sym (back _ (pl-• (revS σ) P Q)) ⟩
    pl (revS σ) Q • pl (revS σ) (P • Q) ∎)
    where
    P Q : Circuit N
    P = place u s (rot α)
    Q = place u′ s′ (rot β)
    x y z : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) s′
    z = combine x y
    fP : pl (revS σ) P ≈ col x (rot α)
    fP = frame-0 α σ u t pu σt s
    fQ : pl (revS σ) Q ≈ col y (B β)
    fQ = frame-1 β σ u′ t′ pu′ σt′ s′
    -- Off the wires 0 1 the two colourings agree in the frame.
    high : ∀ i → i < ₃₊ k → lookupℕ (₂₊ i) z ≡ true
    high i i< = Eq.trans (combine-lookup (₂₊ i) x y (s≤s (s≤s i<)))
                  (Eq.trans (Eq.cong₂ _⇔_ (Eq.trans (Eq.cong (λ q → lookupℕ q x) (Eq.sym ti)) (swW-lookup (revS σ) s iF))
                                         (Eq.trans (Eq.cong (λ q → lookupℕ q y) (Eq.sym ti)) (swW-lookup (revS σ) s′ iF)))
                    (Eq.trans (Eq.cong (λ b → lookupℕ (toℕ j) s ⇔ b) (Eq.sym (agree j jt jt′)))
                              (⇔-same (lookupℕ (toℕ j) s))))
      where
      i<N : ₂₊ i < N
      i<N = s≤s (s≤s i<)
      iF : Fin N
      iF = fromℕ< i<N
      ti : toℕ iF ≡ ₂₊ i
      ti = toℕ-fromℕ< i<N
      j : Fin N
      j = perm (revS σ) ⟨$⟩ʳ iF
      σj : perm σ ⟨$⟩ʳ j ≡ iF
      σj = Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ j) (Eq.sym (revS² σ))) (perm-back (revS σ) Eq.refl)
      jt : j ≢ t
      jt e with Eq.trans (Eq.sym ti) (Eq.cong toℕ (Eq.trans (Eq.sym σj) (Eq.trans (Eq.cong (perm σ ⟨$⟩ʳ_) e) σt)))
      ... | ()
      jt′ : j ≢ t′
      jt′ e with Eq.trans (Eq.sym ti) (Eq.cong toℕ (Eq.trans (Eq.sym σj) (Eq.trans (Eq.cong (perm σ ⟨$⟩ʳ_) e) σt′)))
      ... | ()
    -- On the wires 0 1: P's colour on Q's target, Q's colour on P's target.
    z0 : lookupℕ 0 z ≡ not α
    z0 = Eq.trans (combine-lookup 0 x y (s≤s z≤n))
           (Eq.trans (Eq.cong (λ b → b ⇔ lookupℕ 0 y) (Eq.trans (bit σ s t 0F σt) st))
                     (Eq.trans (bit σ s′ t 0F σt) (Eq.sym αe)))
    z1 : lookupℕ 1 z ≡ β
    z1 = Eq.trans (combine-lookup 1 x y (s≤s (s≤s z≤n)))
           (Eq.trans (Eq.cong₂ _⇔_ (bit σ s t′ (sF 0F) σt′) (Eq.trans (bit σ s′ t′ (sF 0F) σt′) st′))
                     (Eq.trans (⇔-true (lookupℕ (toℕ t′) s)) (Eq.sym βe)))
    zs : z ≡ not α ∷ β ∷ ones₃
    zs = Eq.trans (split₂ z high) (Eq.cong₂ (λ a b → a ∷ b ∷ ones₃) z0 z1)
