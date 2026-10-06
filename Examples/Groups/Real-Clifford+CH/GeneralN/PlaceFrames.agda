------------------------------------------------------------------------
-- Presentations of groups
--
-- Placed gates in the frame of a network (Clément, Appendix E.5)
--
-- What the placement arguments of RotAnywhereGen, BraidFrom and
-- PairFrom share, at any width.  An equation between gates conjugated
-- by a network comes back through it (`reflect′`); a gate rigid on
-- wire 0, placed by u and coloured by s, is in the frame of a network σ
-- sending its target to wire 0 the gate itself coloured by s read
-- through σ (`frame-0`), and with the target sent to wire 1 the gate
-- under the swap of the wires 0 1 (`frame-1`).  Only the relative
-- colouring of two coloured gates counts (`col-rel′`, `col-rel₃`), and
-- when σ brings two targets to the wires 0 1, two colourings that agree
-- off them agree in the frame off the wires 0 1 (`frame-agree`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames where

open import Data.Bool using (true ; false)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; combine ; _⇔_ ; col-col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-• ; pl-cong ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (Rigid ; frame₁ ; place ; place-pl ; unpl ; swW-lookup ; combine-lookup ; ⇔-same ; revS² ; perm-back)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

------------------------------------------------------------------------
-- Relative colourings, and equations carried back

private
  cancel : ∀ a b → (a ⇔ (a ⇔ b)) ≡ b
  cancel true  b     = Eq.refl
  cancel false true  = Eq.refl
  cancel false false = Eq.refl

ccancel : ∀ {j} (p q : Bits j) → combine p (combine p q) ≡ q
ccancel []      []      = Eq.refl
ccancel (a ∷ p) (b ∷ q) = Eq.cong₂ _∷_ (cancel a b) (ccancel p q)

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  private
    module Rel (x y : Bits n) (v : Circuit n) where
      module Cx = Conj {n} (negsB x) (negs² x)
      e : Cx.⟪ col (combine x y) v ⟫ ≈ col y v
      e = trans (col-col x (combine x y) v)
                (Eq.subst (λ u → col (combine x (combine x y)) v ≈ col u v) (ccancel x y) refl)

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
  col-rel′ x y {w} {w′} {v} h = R.Cx.⟪⟫-≈ h (R.Cx.⟪⟫-•₂ refl R.e) (R.Cx.⟪⟫-•₂ R.e refl)
    where
    module R = Rel x y v

  -- The same for three factors.
  col-rel₃ : ∀ (x y : Bits n) {w v : Circuit n} →
             w • (col (combine x y) v • w) ≈ col (combine x y) v • (w • col (combine x y) v) →
             col x w • (col y v • col x w) ≈ col y v • (col x w • col y v)
  col-rel₃ x y {w} {v} h = R.Cx.⟪⟫-≈ h (R.Cx.⟪⟫-•₃ refl R.e refl) (R.Cx.⟪⟫-•₃ R.e refl R.e)
    where
    module R = Rel x y v

------------------------------------------------------------------------
-- Conjugations by involutions

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  -- Conjugating by commuting involutions in either order.
  conj-swap : ∀ {c d : Circuit n} → c • d ≈ d • c → (w : Circuit n) →
              c • (d • w • d) • c ≈ d • (c • w • c) • d
  conj-swap {c} {d} cd w = begin
    c • (d • w • d) • c        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (c • d) • w • (d • c)      ≈⟨ cong cd (back _ (sym cd)) ⟩
    (d • c) • w • (c • d)      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    d • (c • w • c) • d ∎

  -- Conjugating by c • r where c commutes with r.
  conj-split : ∀ {c r : Circuit n} → c • r ≈ r • c → (w : Circuit n) →
               (c • r) • w • (c • r) ≈ c • (r • w • r) • c
  conj-split {c} {r} cr w = begin
    (c • r) • w • (c • r)      ≈⟨ back _ (back _ cr) ⟩
    (c • r) • w • (r • c)      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    c • (r • w • r) • c ∎

------------------------------------------------------------------------
-- A rigid gate in the frame of a network

module _ {r : ℕ} where

  private
    N : ℕ
    N = ₂₊ r

  open Tools (N VRel,_===_)

  -- σ sends the target to wire 0 …
  frame-0 : ∀ {g} → Rigid 1 g → (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
            (s : Bits N) → pl (revS σ) (place u s g) ≈ col (swW (revS σ) s) g
  frame-0 {g} rg σ u t pu σt s =
    trans (place-pl (revS σ) u s g) (mid _ _ (trans (frame₁ rg (revS σ • u) ε cond) (trans left-unit right-unit)))
    where
    cond : perm ε ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
    cond = Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                    (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)

  -- … or to wire 1.
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

  -- The bit of a colouring in the frame of σ, at a wire σ sends there.
  bit : ∀ (σ : Word (S.Gen N)) (s : Bits N) (t i : Fin N) → perm σ ⟨$⟩ʳ t ≡ i →
        lookupℕ (toℕ i) (swW (revS σ) s) ≡ lookupℕ (toℕ t) s
  bit σ s t i e = Eq.trans (swW-lookup (revS σ) s i) (Eq.cong (λ x → lookupℕ (toℕ x) s) (perm-back σ e))

  private
    lookup-ones : ∀ {j} i → i < j → lookupℕ i (replicate j true) ≡ true
    lookup-ones {suc j} zero    _       = Eq.refl
    lookup-ones {suc j} (suc i) (s≤s p) = lookup-ones i p

    ext : ∀ {j} (p q : Bits j) → (∀ i → i < j → lookupℕ i p ≡ lookupℕ i q) → p ≡ q
    ext []      []      _ = Eq.refl
    ext (a ∷ p) (b ∷ q) h = Eq.cong₂ _∷_ (h 0 (s≤s z≤n)) (ext p q (λ i i< → h (suc i) (s≤s i<)))

    split₂ : ∀ {j} (z : Bits (₂₊ j)) → (∀ i → i < j → lookupℕ (₂₊ i) z ≡ true) →
             z ≡ lookupℕ 0 z ∷ lookupℕ 1 z ∷ replicate j true
    split₂ (a ∷ b ∷ q) h = Eq.cong (λ p → a ∷ b ∷ p) (ext q _ (λ i i< → Eq.trans (h i i<) (Eq.sym (lookup-ones i i<))))

  -- Two colourings agreeing off the two targets σ brings to the wires
  -- 0 1 agree in the frame off those wires.
  frame-agree : ∀ (σ : Word (S.Gen N)) (t t′ : Fin N) → perm σ ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t′ ≡ sF 0F →
                (s s′ : Bits N) → (∀ (j : Fin N) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≡ lookupℕ (toℕ j) s′) →
                let z = combine (swW (revS σ) s) (swW (revS σ) s′) in z ≡ lookupℕ 0 z ∷ lookupℕ 1 z ∷ replicate r true
  frame-agree σ t t′ σt σt′ s s′ agree = split₂ z high
    where
    x y z : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) s′
    z = combine x y
    high : ∀ i → i < r → lookupℕ (₂₊ i) z ≡ true
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
