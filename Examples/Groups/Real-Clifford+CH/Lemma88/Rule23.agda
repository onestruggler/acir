------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (23) of Figure 8 (Clément, Appendix E.5)
--
-- (23) is (−1)_[a] (−1)_[a+1] = ((−1)_[a] X_[a,a+1])², at every a.
-- Decoded, both sides are gates placed by the one layout of a, a + 1:
-- the box, and the multi-controlled ZX or XZ twice (by the bit of the
-- code of a on the target wire, `βof`).  A placement is a conjugation
-- (`conj₁-•`), so the rule is (355) at the canonical position in both
-- signs, the module's parameters `core` and `core′`, which
-- GeneralN.ZX355 gives at every width from five on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule23
  {m : ℕ}
  (core  : (₃₊ m) ⊢ Λ□ (₂₊ m) ≈ ΛXZ (₂₊ m) • ΛXZ (₂₊ m))
  (core′ : (₃₊ m) ⊢ Λ□ (₂₊ m) ≈ ΛZX (₂₊ m) • ΛZX (₂₊ m))
  where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (zero ; suc ; _^_ ; _<_ ; _<ᵇ_ ; _∸_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; <⇒≢)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Layout ; negs ; tgtWire ; conj₁ ; shiftDown ; shiftUp ; mc±XZ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZZ ; dZZ-chain ; dZZ₁ ; dZX ; dZXlo₁ ; βof ; layout□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (su-sd)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-zx ; dZX-lo₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m} using (negs²)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  lt-true : ∀ a b → a < b → (a <ᵇ b) ≡ true
  lt-true a       zero    ()
  lt-true zero    (suc b) _       = Eq.refl
  lt-true (suc a) (suc b) (s≤s p) = lt-true a b p

  sx∸x : ∀ x → suc x ∸ x ≡ 1
  sx∸x zero    = Eq.refl
  sx∸x (suc x) = sx∸x x

  -- The sign pair on a, a + 1 decodes to one box.
  dZZ-s : ∀ x → dZZ {m} x (suc x) ≡ dZZ₁ x • ε
  dZZ-s x = Eq.trans (Eq.cong (λ β → if β then dZZ-chain {m} x (suc x ∸ x) else dZZ-chain (suc x) (x ∸ suc x))
                              (lt-true x (suc x) (n<1+n x)))
                     (Eq.cong (dZZ-chain x) (sx∸x x))

  -- Gates placed by one layout multiply as the gates do.
  conj₁-• : ∀ (L : Layout N) (g g′ : Circuit N) → conj₁ L g • conj₁ L g′ ≈ conj₁ L (g • g′)
  conj₁-• L g g′ = begin
    (n • s • g • u • n) • (n • s • g′ • u • n)
      ≈⟨ by-passoc ((□ • □ • □ • □ • □) • (□ • □ • □ • □ • □)) (□ • □ • □ • ((□ • (□ • □) • □) • □ • □ • □)) Eq.refl ⟩
    n • s • g • ((u • (n • n) • s) • g′ • u • n)
      ≈⟨ back _ (back _ (back _ (front _ (trans (back _ (trans (front _ (negs² L)) left-unit)) (su-sd (tgtWire L)))))) ⟩
    n • s • g • (ε • g′ • u • n)
      ≈⟨ back _ (back _ (trans (back _ left-unit) (sym assoc))) ⟩
    n • s • (g • g′) • u • n ∎
    where
    n s u : Circuit N
    n = negs L
    s = shiftDown (tgtWire L)
    u = shiftUp (tgtWire L)

  conj₁-cong : ∀ (L : Layout N) {g g′ : Circuit N} → g ≈ g′ → conj₁ L g ≈ conj₁ L g′
  conj₁-cong L e = back _ (back _ (front _ e))

  -- The unreversed rule, in either sign.
  unrev : ∀ β (L : Layout N) → conj₁ L (Λ□ (₂₊ m)) • ε ≈ mc±XZ β L • mc±XZ β L
  unrev false L = trans right-unit (trans (conj₁-cong L core) (sym (conj₁-• L _ _)))
  unrev true  L = trans right-unit (trans (conj₁-cong L core′) (sym (conj₁-• L _ _)))

------------------------------------------------------------------------
-- (23)

e23 : ∀ (a a′ : I) → Succ a a′ → (d ʷ) (zz {N} a a′) ≈ (d ʷ) (zx a a a′ • zx a a a′)
e23 a a′ s = begin
  (d ʷ) (zz a a′)
    ≈⟨ ≡→≈ (Eq.trans (Eq.cong (λ t → rev (dZZ {m} x t)) s) (Eq.cong rev (dZZ-s x))) ⟩
  rev (dZZ₁ x • ε)
    ≈⟨ rev-cong (unrev (βof x) (layout□ x)) ⟩
  rev (dZXlo₁ x • dZXlo₁ x)
    ≈⟨ ≡→≈ (Eq.sym (Eq.trans (Eq.cong₂ _•_ (d-zx a a a′ aa′) (d-zx a a a′ aa′))
                             (Eq.trans (Eq.cong (λ t → rev (dZX {m} x x t) • rev (dZX x x t)) s)
                                       (Eq.cong (λ u → rev u • rev u) (dZX-lo₁ x))))) ⟩
  (d ʷ) (zx a a a′ • zx a a a′) ∎
  where
  x : ℕ
  x = toℕ a
  aa′ : a ≢ a′
  aa′ e = <⇒≢ (n<1+n x) (Eq.trans (Eq.cong toℕ e) s)

------------------------------------------------------------------------
-- For the rule (31): the box of a Gray-code step is the square of its
-- rotation

box-rot : ∀ x → dZZ₁ {m} x ≈ dZXlo₁ x • dZXlo₁ x
box-rot x = trans (sym right-unit) (unrev (βof x) (layout□ x))
