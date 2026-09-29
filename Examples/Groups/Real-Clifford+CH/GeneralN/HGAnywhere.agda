------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget, in every position (Clément,
-- Appendix E.5, rule (38))
--
-- `hgrot` proves HGRotCol.HGRot at width 5 + k.  The gadget is the H
-- gate HG in the colouring black on the wires 0 1 and white above
-- (Box338Eq's S-ΛH).  A network σ on the wires 2 … passes HG
-- (Canon38.HG-rigid), so conjugating by it keeps the gadget in place and
-- brings the separating wire j to wire 2 and, when the rotation's target
-- t is above wire 1, t to wire 3 (Placed.bring₁ / bring₂ one wire up
-- twice).  In that frame the rotation is the canonical one on wire 0,
-- 1 or 3 (the last placed by the transposition of the wires 0 3), and
-- only the relative colouring counts (RotPair.col-rel′): black on its
-- target, white on wire 2 and, for a target on wire 3, white there.
-- That is Canon38's C38₀, C38₁ or C38₂.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.HGAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; net-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; revS-↑ ; net-inv)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; combine ; _⇔_)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-• ; pl-cong ; perm-↑0 ; perm-↑s ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (Rigid ; frame₁ ; place ; place-pl ; pl-col ; swW-lookup ; combine-lookup ; revS² ; perm-back ;
         bring₁ ; bring₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol using (HGRot ; gcol ; gadgetG)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotPair complete₂ complete₃ using (reflect′ ; col-rel′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon38 complete₂ complete₃
  using (t03 ; perm-t03 ; HG ; HG-rigid ; C38₀ ; C38₁ ; C38₂)

private
  lk-falses : ∀ {n} (j : Fin n) → lookupℕ (toℕ j) (replicate n false) ≡ false
  lk-falses 0F     = Eq.refl
  lk-falses (sF j) = lk-falses j

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

  open Tools (N VRel,_===_)
  open XY k below using (S-ΛH)

  private
    rig-rot : ∀ β → Rigid 1 (rot {₂₊ k} β)
    rig-rot β v = rot-rigid k below β v

    Hk : Circuit N
    Hk = HG k below

    -- In the frame of σ: σ sends the target to wire 0, 1 or 3.
    frame-0 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (rot β)
    frame-0 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β)) (mid _ _ (trans (frame₁ (rig-rot β) (revS σ • u) ε cond) (trans left-unit right-unit)))
      where
      cond : perm ε ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                      (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)

    back-t : ∀ (σ u : Word (S.Gen N)) (t : Fin N) (i : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ i →
             perm (revS (revS σ • u)) ⟨$⟩ʳ 0F ≡ i
    back-t σ u t i pu σt = Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                                    (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)

    frame-1 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF 0F →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (Ex • rot β • Ex)
    frame-1 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β))
            (mid _ _ (frame₁ (rig-rot β) (revS σ • u) S.σ
                               (Eq.trans (Eq.cong (perm S.σ ⟨$⟩ʳ_) (back-t σ u t (sF 0F) pu σt)) perm-σ₁)))

    frame-3 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF (sF (sF 0F)) →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (pl t03 (rot β))
    frame-3 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β))
            (mid _ _ (frame₁ (rig-rot β) (revS σ • u) t03
                               (Eq.trans (Eq.cong (perm t03 ⟨$⟩ʳ_) (back-t σ u t (sF (sF (sF 0F))) pu σt)) perm-t03)))

    bit : ∀ (σ : Word (S.Gen N)) (s : Bits N) (t i : Fin N) → perm σ ⟨$⟩ʳ t ≡ i →
          lookupℕ (toℕ i) (swW (revS σ) s) ≡ lookupℕ (toℕ t) s
    bit σ s t i e = Eq.trans (swW-lookup (revS σ) s i) (Eq.cong (λ x → lookupℕ (toℕ x) s) (perm-back σ e))

    -- A network on the wires 2 … fixes the gadget.
    up2 : Word (S.Gen (₃₊ k)) → Word (S.Gen N)
    up2 w = (w S.↑) S.↑

    net-up2 : ∀ w → net (up2 w) ≡ net w ↑ ↑
    net-up2 w = Eq.trans (net-↑ (w S.↑)) (Eq.cong _↑ (net-↑ w))

    revS-up2 : ∀ w → revS (up2 w) ≡ up2 (revS w)
    revS-up2 w = Eq.trans (revS-↑ (w S.↑)) (Eq.cong S._↑ (revS-↑ w))

    HG-pl : ∀ w → pl (up2 w) Hk ≈ Hk
    HG-pl w = trans (sym assoc) (trans (front _ nH) (trans assoc (trans (back _ (net-inv (up2 w))) right-unit)))
      where
      nH : net (up2 w) • Hk ≈ Hk • net (up2 w)
      nH = Eq.subst (λ x → x • Hk ≈ Hk • x) (Eq.sym (net-up2 w)) (HG-rigid k below w)

    gadget-pl : ∀ w → pl (revS (up2 w)) (gadgetG (₂₊ k)) ≈ col (swW (revS (up2 w)) (gcol (₂₊ k))) Hk
    gadget-pl w = begin
      pl (revS (up2 w)) (gadgetG (₂₊ k))
        ≈⟨ pl-cong (revS (up2 w)) (mid _ _ S-ΛH) ⟩
      pl (revS (up2 w)) (col (gcol (₂₊ k)) Hk)
        ≈⟨ pl-col (revS (up2 w)) (gcol (₂₊ k)) Hk ⟩
      col (swW (revS (up2 w)) (gcol (₂₊ k))) (pl (revS (up2 w)) Hk)
        ≈⟨ mid _ _ (Eq.subst (λ v → pl v Hk ≈ Hk) (Eq.sym (revS-up2 w)) (HG-pl (revS w))) ⟩
      col (swW (revS (up2 w)) (gcol (₂₊ k))) Hk ∎

    -- Where up2 w sends the wires 0, 1 and those above.
    up2-0 : ∀ w → perm (up2 w) ⟨$⟩ʳ 0F ≡ 0F
    up2-0 w = perm-↑0 (w S.↑)

    up2-1 : ∀ w → perm (up2 w) ⟨$⟩ʳ sF 0F ≡ sF 0F
    up2-1 w = Eq.trans (perm-↑s (w S.↑) 0F) (Eq.cong sF (perm-↑0 w))

    up2-s : ∀ w x y → perm w ⟨$⟩ʳ x ≡ y → perm (up2 w) ⟨$⟩ʳ sF (sF x) ≡ sF (sF y)
    up2-s w x y e = Eq.trans (perm-↑s (w S.↑) (sF x)) (Eq.cong sF (Eq.trans (perm-↑s w x) (Eq.cong sF e)))

  ----------------------------------------------------------------------
  -- The rotation placed anywhere against the gadget

  hgrot : HGRot (₂₊ k)
  hgrot β u t pu s st 0F () _ _
  hgrot β u t pu s st (sF 0F) (s≤s ()) _ _
  hgrot β u 0F pu s st (sF (sF j′)) _ jt sj with bring₁ j′
  ... | σ′ , σj′ = reflect′ σ (begin
    pl (revS σ) P • pl (revS σ) G
      ≈⟨ cong (frame-0 β σ u 0F pu (up2-0 σ′) s) (gadget-pl σ′) ⟩
    col x (rot β) • col y Hk
      ≈⟨ col-rel′ x y (C38₀ k below β (combine x y) z0 z2) ⟩
    col y Hk • col x (rot β)
      ≈⟨ sym (cong (gadget-pl σ′) (frame-0 β σ u 0F pu (up2-0 σ′) s)) ⟩
    pl (revS σ) G • pl (revS σ) P ∎)
    where
    σ : Word (S.Gen N)
    σ = up2 σ′
    P G : Circuit N
    P = place u s (rot β)
    G = gadgetG (₂₊ k)
    x y : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) (gcol (₂₊ k))
    σj : perm σ ⟨$⟩ʳ sF (sF j′) ≡ sF (sF 0F)
    σj = up2-s σ′ j′ 0F σj′
    z0 : lookupℕ 0 (combine x y) ≡ true
    z0 = Eq.trans (combine-lookup 0 x y (s≤s z≤n))
                  (Eq.cong₂ _⇔_ (Eq.trans (bit σ s 0F 0F (up2-0 σ′)) st) (bit σ (gcol (₂₊ k)) 0F 0F (up2-0 σ′)))
    z2 : lookupℕ 2 (combine x y) ≡ false
    z2 = Eq.trans (combine-lookup 2 x y (s≤s (s≤s (s≤s z≤n))))
                  (Eq.cong₂ _⇔_ (Eq.trans (bit σ s _ _ σj) sj)
                                (Eq.trans (bit σ (gcol (₂₊ k)) _ _ σj) (lk-falses j′)))
  hgrot β u (sF 0F) pu s st (sF (sF j′)) _ jt sj with bring₁ j′
  ... | σ′ , σj′ = reflect′ σ (begin
    pl (revS σ) P • pl (revS σ) G
      ≈⟨ cong (frame-1 β σ u (sF 0F) pu (up2-1 σ′) s) (gadget-pl σ′) ⟩
    col x R₁ • col y Hk
      ≈⟨ sym (col-rel′ y x (C38₁ k below β (combine y x) z1 z2)) ⟩
    col y Hk • col x R₁
      ≈⟨ sym (cong (gadget-pl σ′) (frame-1 β σ u (sF 0F) pu (up2-1 σ′) s)) ⟩
    pl (revS σ) G • pl (revS σ) P ∎)
    where
    σ : Word (S.Gen N)
    σ = up2 σ′
    P G R₁ : Circuit N
    P  = place u s (rot β)
    G  = gadgetG (₂₊ k)
    R₁ = Ex • rot β • Ex
    x y : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) (gcol (₂₊ k))
    σj : perm σ ⟨$⟩ʳ sF (sF j′) ≡ sF (sF 0F)
    σj = up2-s σ′ j′ 0F σj′
    z1 : lookupℕ 1 (combine y x) ≡ true
    z1 = Eq.trans (combine-lookup 1 y x (s≤s (s≤s z≤n)))
                  (Eq.cong₂ _⇔_ (bit σ (gcol (₂₊ k)) (sF 0F) (sF 0F) (up2-1 σ′))
                                (Eq.trans (bit σ s (sF 0F) (sF 0F) (up2-1 σ′)) st))
    z2 : lookupℕ 2 (combine y x) ≡ false
    z2 = Eq.trans (combine-lookup 2 y x (s≤s (s≤s (s≤s z≤n))))
                  (Eq.cong₂ _⇔_ (Eq.trans (bit σ (gcol (₂₊ k)) _ _ σj) (lk-falses j′))
                                (Eq.trans (bit σ s _ _ σj) sj))
  hgrot β u (sF (sF t′)) pu s st (sF (sF j′)) _ jt sj with bring₂ j′ t′ (λ e → jt (Eq.cong sF (Eq.cong sF (Eq.sym e))))
  ... | σ′ , σj′ , σt′ = reflect′ σ (begin
    pl (revS σ) P • pl (revS σ) G
      ≈⟨ cong (frame-3 β σ u (sF (sF t′)) pu σt s) (gadget-pl σ′) ⟩
    col x R₃ • col y Hk
      ≈⟨ col-rel′ x y (C38₂ k below β (combine x y) z2 z3) ⟩
    col y Hk • col x R₃
      ≈⟨ sym (cong (gadget-pl σ′) (frame-3 β σ u (sF (sF t′)) pu σt s)) ⟩
    pl (revS σ) G • pl (revS σ) P ∎)
    where
    σ : Word (S.Gen N)
    σ = up2 σ′
    P G R₃ : Circuit N
    P  = place u s (rot β)
    G  = gadgetG (₂₊ k)
    R₃ = pl t03 (rot β)
    x y : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) (gcol (₂₊ k))
    σj : perm σ ⟨$⟩ʳ sF (sF j′) ≡ sF (sF 0F)
    σj = up2-s σ′ j′ 0F σj′
    σt : perm σ ⟨$⟩ʳ sF (sF t′) ≡ sF (sF (sF 0F))
    σt = up2-s σ′ t′ (sF 0F) σt′
    z2 : lookupℕ 2 (combine x y) ≡ false
    z2 = Eq.trans (combine-lookup 2 x y (s≤s (s≤s (s≤s z≤n))))
                  (Eq.cong₂ _⇔_ (Eq.trans (bit σ s _ _ σj) sj)
                                (Eq.trans (bit σ (gcol (₂₊ k)) _ _ σj) (lk-falses j′)))
    z3 : lookupℕ 3 (combine x y) ≡ false
    z3 = Eq.trans (combine-lookup 3 x y (s≤s (s≤s (s≤s (s≤s z≤n)))))
                  (Eq.cong₂ _⇔_ (Eq.trans (bit σ s _ _ σt) st)
                                (Eq.trans (bit σ (gcol (₂₊ k)) _ _ σt) (lk-falses t′)))
