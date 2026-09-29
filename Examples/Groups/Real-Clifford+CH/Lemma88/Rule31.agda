------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (31) of Figure 8 (Clément, Appendix E.5)
--
-- (31) is (−1)_[a′] (−1)_[c] · (−1)_[a] X_[a,a′] = (−1)_[a] X_[a,a′] ·
-- (−1)_[a] (−1)_[c], for a′ = a + 1 and c ≠ a, a′.  Decoded, the sign
-- pairs are chains of the boxes B_k of consecutive Gray-code steps and
-- the signed exchange is the rotation R_a; unreversed, the rule is
--
--   R_a • dZZ (a + 1) c ≈ dZZ a c • R_a.
--
-- Far from a the boxes pass R_a: B_k = R_k R_k by (23) and R_a, R_k
-- commute by (32).  Next to a the rotation passes the box inverted — the
-- pair step R_a B_{a±1} ≈ B_{a±1} R_a⁻¹ (the module's parameter
-- `pairstep`, which GeneralN.RotPair gives at every width from five on)
-- — and with B_a = R_a R_a and R_a⁻¹ R_a = ε ((29)) that is the two
-- bases, R_a B_{a+1} ≈ B_a B_{a+1} R_a for c above and
-- R_{a+1} B_a B_{a+1} ≈ B_a R_{a+1} for c below.  The decodings are
-- reversed, which reversal of the equation absorbs.  Checked
-- numerically at five and six wires first (scratchpad r5x/r31.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Bool using (not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)
open import Notations using (₂₊ ; ₃₊)
import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; RotComm)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule31
  {m : ℕ} (C : Canon m)
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (core  : (₃₊ m) ⊢ Λ□ (₂₊ m) ≈ ΛXZ (₂₊ m) • ΛXZ (₂₊ m))
  (core′ : (₃₊ m) ⊢ Λ□ (₂₊ m) ≈ ΛZX (₂₊ m) • ΛZX (₂₊ m))
  (rotcomm : RotComm m)
  (pairstep : ∀ β (u u′ : Word (S.Gen (₃₊ m))) (t t′ : Fin (₃₊ m)) → t′ ≢ t →
              perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F → (s s′ : Bits (₃₊ m)) →
              (∀ (j : Fin (₃₊ m)) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≡ lookupℕ (toℕ j) s′) →
              (₃₊ m) ⊢ place u s (rot β) • place u′ s′ (Λ□ (₂₊ m)) ≈ place u′ s′ (Λ□ (₂₊ m)) • place u s (rot (not β)))
  where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Vec using ([] ; _∷_)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n ; toℕ-fromℕ<)
open import Data.Nat using (zero ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<ᵇ_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (n<1+n ; <⇒≢ ; <⇒≤ ; ≤-refl ; ≤-trans ; <-trans ; ≤-<-trans ; <-≤-trans ; +-suc ; +-identityʳ ; m+n∸m≡n ;
         m≤m+n ; n≤1+n ; <-cmp ; suc-injective ; m≤n⇒m<n∨m≡n)
open import Data.Product using (Σ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
import Relation.Binary.Definitions
open import Word.Base using (ε ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Layout ; conj₁ ; mc±ZX)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dZZ ; dZZ-chain ; dZZ₁ ; dZX ; dZXlo₁ ; dZXhi₁ ; βof ; layout□ ; gcode)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (sdS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (setT)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-zx ; dZX-lo₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Invol C complete₂ using (rot-inv)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule23 {m} core core′ using (box-rot)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 {m} rotcomm using (letterG′ ; letter′ ; tw ; comm)
open import Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness {m}
  using (tgt ; tgt< ; gstep ; tgt-apart ; lookup-flip-other)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  R Ri Bx : ℕ → Circuit N
  R  = dZXlo₁ {m}
  Ri = dZXhi₁ {m}
  Bx = dZZ₁ {m}

  mc±ZX-rot : ∀ β (L : Layout N) → mc±ZX β L ≡ conj₁ L (rot (not β))
  mc±ZX-rot true  L = Eq.refl
  mc±ZX-rot false L = Eq.refl

  lookup-setT-other : ∀ {n} i j (s : Bits n) → j ≢ i → lookupℕ j (setT i s) ≡ lookupℕ j s
  lookup-setT-other i       j       []      _  = Eq.refl
  lookup-setT-other zero    zero    (b ∷ s) ne = ⊥-elim (ne Eq.refl)
  lookup-setT-other zero    (suc j) (b ∷ s) _  = Eq.refl
  lookup-setT-other (suc i) zero    (b ∷ s) _  = Eq.refl
  lookup-setT-other (suc i) (suc j) (b ∷ s) ne = lookup-setT-other i j s (λ e → ne (Eq.cong suc e))

  ------------------------------------------------------------------------
  -- The letters

  -- (29) and (23).
  K3 : ∀ x → Ri x • R x ≈ ε
  K3 x = rot-inv (βof x) (layout□ x)

  K2 : ∀ x → Bx x ≈ R x • R x
  K2 = box-rot

  -- The pair step, for two steps x, y whose codes agree off their
  -- targets.
  step : ∀ x y → suc x < 2 ^ N → suc y < 2 ^ N → tgt y ≢ tgt x →
         (∀ j → j ≢ tgt x → j ≢ tgt y → lookupℕ j (gcode {m} x) ≡ lookupℕ j (gcode y)) →
         R x • Bx y ≈ Bx y • Ri x
  step x y xb yb d agree = begin
    R x • Bx y
      ≈⟨ cong (letter′ x xb) (letterG′ y yb (Λ□ (₂₊ m))) ⟩
    place ux sx (rot β) • place uy sy (Λ□ (₂₊ m))
      ≈⟨ pairstep β ux uy tx ty yx (sd-target tx) (sd-target ty) sx sy ag ⟩
    place uy sy (Λ□ (₂₊ m)) • place ux sx (rot (not β))
      ≈⟨ sym (cong (letterG′ y yb (Λ□ (₂₊ m))) (trans (≡→≈ (mc±ZX-rot β (layout□ x))) (letterG′ x xb (rot (not β))))) ⟩
    Bx y • Ri x ∎
    where
    β : Bool
    β = βof x
    tx ty : Fin N
    tx = tw x xb
    ty = tw y yb
    tx-≡ : toℕ tx ≡ tgt x
    tx-≡ = toℕ-fromℕ< (tgt< x xb)
    ty-≡ : toℕ ty ≡ tgt y
    ty-≡ = toℕ-fromℕ< (tgt< y yb)
    ux uy : Word (S.Gen N)
    ux = sdS (toℕ tx)
    uy = sdS (toℕ ty)
    sx sy : Bits N
    sx = setT (toℕ tx) (gcode x)
    sy = setT (toℕ ty) (gcode y)
    yx : ty ≢ tx
    yx e = d (Eq.trans (Eq.sym ty-≡) (Eq.trans (Eq.cong toℕ e) tx-≡))
    ag : ∀ (j : Fin N) → j ≢ tx → j ≢ ty → lookupℕ (toℕ j) sx ≡ lookupℕ (toℕ j) sy
    ag j jx jy = Eq.trans (lookup-setT-other (toℕ tx) (toℕ j) (gcode x) (λ e → jx (toℕ-injective e)))
                   (Eq.trans (agree (toℕ j) (λ e → jx (toℕ-injective (Eq.trans e (Eq.sym tx-≡))))
                                            (λ e → jy (toℕ-injective (Eq.trans e (Eq.sym ty-≡)))))
                             (Eq.sym (lookup-setT-other (toℕ ty) (toℕ j) (gcode y) (λ e → jy (toℕ-injective e)))))

  step+ : ∀ x → suc (suc x) < 2 ^ N → R x • Bx (suc x) ≈ Bx (suc x) • Ri x
  step+ x bnd = step x (suc x) (<-trans (n<1+n (suc x)) bnd) bnd (λ e → tgt-apart x (Eq.sym e)) agree
    where
    agree : ∀ j → j ≢ tgt x → j ≢ tgt (suc x) → lookupℕ j (gcode {m} x) ≡ lookupℕ j (gcode (suc x))
    agree j jx _ = Eq.sym (Eq.trans (Eq.cong (lookupℕ j) (gstep x (<-trans (n<1+n (suc x)) bnd)))
                                    (lookup-flip-other (tgt x) j (gcode x) jx))

  step- : ∀ y → suc (suc y) < 2 ^ N → R (suc y) • Bx y ≈ Bx y • Ri (suc y)
  step- y bnd = step (suc y) y bnd (<-trans (n<1+n (suc y)) bnd) (tgt-apart y) agree
    where
    agree : ∀ j → j ≢ tgt (suc y) → j ≢ tgt y → lookupℕ j (gcode {m} (suc y)) ≡ lookupℕ j (gcode y)
    agree j _ jy = Eq.trans (Eq.cong (lookupℕ j) (gstep y (<-trans (n<1+n (suc y)) bnd)))
                            (lookup-flip-other (tgt y) j (gcode y) jy)

  -- The two bases.
  base+ : ∀ x → suc (suc x) < 2 ^ N → R x • Bx (suc x) ≈ Bx x • Bx (suc x) • R x
  base+ x bnd = sym (begin
    Bx x • Bx (suc x) • R x                   ≈⟨ front _ (K2 x) ⟩
    (R x • R x) • Bx (suc x) • R x            ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    R x • (R x • Bx (suc x)) • R x            ≈⟨ back _ (front _ (step+ x bnd)) ⟩
    R x • (Bx (suc x) • Ri x) • R x           ≈⟨ back _ (trans assoc (back _ (K3 x))) ⟩
    R x • Bx (suc x) • ε                      ≈⟨ back _ right-unit ⟩
    R x • Bx (suc x) ∎)

  base- : ∀ y → suc (suc y) < 2 ^ N → R (suc y) • Bx y • Bx (suc y) ≈ Bx y • R (suc y)
  base- y bnd = begin
    R (suc y) • Bx y • Bx (suc y)                   ≈⟨ trans (sym assoc) (front _ (step- y bnd)) ⟩
    (Bx y • Ri (suc y)) • Bx (suc y)                ≈⟨ back _ (K2 (suc y)) ⟩
    (Bx y • Ri (suc y)) • R (suc y) • R (suc y)     ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    Bx y • (Ri (suc y) • R (suc y)) • R (suc y)     ≈⟨ back _ (trans (front _ (K3 (suc y))) left-unit) ⟩
    Bx y • R (suc y) ∎

  -- A box far from x passes R x.
  far : ∀ x k → suc x < 2 ^ N → suc k < 2 ^ N → (suc x < k) ⊎ (suc k < x) → R x • Bx k ≈ Bx k • R x
  far x k xb kb h = trans (back _ (K2 k)) (trans (pass₂ c c) (front _ (sym (K2 k))))
    where
    c : R x • R k ≈ R k • R x
    c = [ (λ xk → sym (comm x k xk kb)) , (λ kx → comm k x kx xb) ]′ h

  -- A chain of far boxes passes R x.
  chain-pass : ∀ x a e → (∀ i → a ≤ i → i < a + e → R x • Bx i ≈ Bx i • R x) →
               R x • dZZ-chain {m} a e ≈ dZZ-chain a e • R x
  chain-pass x a zero    h = trans right-unit (sym left-unit)
  chain-pass x a (suc e) h =
    pass₂ (h a ≤-refl (Eq.subst (a <_) (Eq.sym (+-suc a e)) (s≤s (m≤m+n a e))))
          (chain-pass x (suc a) e (λ i ai i< → h i (<⇒≤ ai) (Eq.subst (i <_) (Eq.sym (+-suc a e)) i<)))

  -- The last box of a chain.
  snoc : ∀ a e → dZZ-chain {m} a (suc e) ≈ dZZ-chain a e • Bx (a + e)
  snoc a zero    = trans right-unit (trans (≡→≈ (Eq.cong Bx (Eq.sym (+-identityʳ a)))) (sym left-unit))
  snoc a (suc e) = begin
    Bx a • dZZ-chain (suc a) (suc e)                    ≈⟨ back _ (snoc (suc a) e) ⟩
    Bx a • (dZZ-chain (suc a) e • Bx (suc a + e))       ≈⟨ sym assoc ⟩
    (Bx a • dZZ-chain (suc a) e) • Bx (suc a + e)       ≈⟨ back _ (≡→≈ (Eq.cong Bx (Eq.sym (+-suc a e)))) ⟩
    dZZ-chain a (suc e) • Bx (a + suc e) ∎

  ------------------------------------------------------------------------
  -- The unreversed rule

  lt-true : ∀ a b → a < b → (a <ᵇ b) ≡ true
  lt-true a       zero    ()
  lt-true zero    (suc b) _       = Eq.refl
  lt-true (suc a) (suc b) (s≤s p) = lt-true a b p

  ge-false : ∀ a b → b ≤ a → (a <ᵇ b) ≡ false
  ge-false a       zero    _       = Eq.refl
  ge-false zero    (suc b) ()
  ge-false (suc a) (suc b) (s≤s p) = ge-false a b p

  dZZ-lt : ∀ {x y} → x < y → dZZ {m} x y ≡ dZZ-chain x (y ∸ x)
  dZZ-lt {x} {y} p = Eq.cong (λ β → if β then dZZ-chain {m} x (y ∸ x) else dZZ-chain y (x ∸ y)) (lt-true x y p)

  dZZ-ge : ∀ {x y} → y ≤ x → dZZ {m} x y ≡ dZZ-chain y (x ∸ y)
  dZZ-ge {x} {y} p = Eq.cong (λ β → if β then dZZ-chain {m} x (y ∸ x) else dZZ-chain y (x ∸ y)) (ge-false x y p)

  -- c above a + 1: c = a + 2 + e.
  up : ∀ x e → suc (suc (x + e)) < 2 ^ N →
       R x • dZZ (suc x) (suc (suc (x + e))) ≈ dZZ x (suc (suc (x + e))) • R x
  up x e bnd = begin
    R x • dZZ (suc x) z
      ≈⟨ back _ (≡→≈ (Eq.trans (dZZ-lt (s≤s (s≤s (m≤m+n x e)))) (Eq.cong (dZZ-chain (suc x)) d₁))) ⟩
    R x • (Bx (suc x) • Cp)
      ≈⟨ trans (sym assoc) (front _ (base+ x (≤-<-trans (s≤s (s≤s (m≤m+n x e))) bnd))) ⟩
    (Bx x • Bx (suc x) • R x) • Cp
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    Bx x • Bx (suc x) • (R x • Cp)
      ≈⟨ back _ (back _ (chain-pass x (suc (suc x)) e farC)) ⟩
    Bx x • Bx (suc x) • (Cp • R x)
      ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (Bx x • Bx (suc x) • Cp) • R x
      ≈⟨ front _ (≡→≈ (Eq.sym (Eq.trans (dZZ-lt (<-trans (n<1+n x) (s≤s (s≤s (m≤m+n x e)))))
                                         (Eq.cong (dZZ-chain x) d₂)))) ⟩
    dZZ x z • R x ∎
    where
    z : ℕ
    z = suc (suc (x + e))
    Cp : Circuit N
    Cp = dZZ-chain (suc (suc x)) e
    d₁ : z ∸ suc x ≡ suc e
    d₁ = Eq.trans (Eq.cong (_∸ x) (Eq.sym (+-suc x e))) (m+n∸m≡n x (suc e))
    d₂ : z ∸ x ≡ suc (suc e)
    d₂ = Eq.trans (Eq.cong (_∸ x) (Eq.sym (Eq.trans (+-suc x (suc e)) (Eq.cong suc (+-suc x e))))) (m+n∸m≡n x (suc (suc e)))
    xb : suc x < 2 ^ N
    xb = <-trans (s≤s (s≤s (m≤m+n x e))) bnd
    farC : ∀ i → suc (suc x) ≤ i → i < suc (suc x) + e → R x • Bx i ≈ Bx i • R x
    farC i xi i< = far x i xb (≤-<-trans i< bnd) (inj₁ xi)

  -- c below a: a = c + 1 + e.
  down : ∀ z e → suc (suc (z + e)) < 2 ^ N →
         R (suc (z + e)) • dZZ (suc (suc (z + e))) z ≈ dZZ (suc (z + e)) z • R (suc (z + e))
  down z e bnd = begin
    R x • dZZ (suc x) z
      ≈⟨ back _ (≡→≈ (Eq.trans (dZZ-ge (≤-trans (m≤m+n z e) (≤-trans (n≤1+n _) (n≤1+n _))))
                                (Eq.cong (dZZ-chain z) d₁))) ⟩
    R x • dZZ-chain z (suc (suc e))
      ≈⟨ back _ (trans (snoc z (suc e)) (≡→≈ (Eq.cong (λ i → dZZ-chain z (suc e) • Bx i) (+-suc z e)))) ⟩
    R x • (dZZ-chain z (suc e) • Bx x)
      ≈⟨ back _ (front _ (snoc z e)) ⟩
    R x • ((Cm • Bx y) • Bx x)
      ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
    (R x • Cm) • (Bx y • Bx x)
      ≈⟨ front _ (chain-pass x z e farC) ⟩
    (Cm • R x) • (Bx y • Bx x)
      ≈⟨ trans assoc (back _ (base- y bnd′)) ⟩
    Cm • (Bx y • R x)
      ≈⟨ trans (sym assoc) (front _ (sym (snoc z e))) ⟩
    dZZ-chain z (suc e) • R x
      ≈⟨ front _ (≡→≈ (Eq.sym (Eq.trans (dZZ-ge (≤-trans (m≤m+n z e) (n≤1+n _))) (Eq.cong (dZZ-chain z) d₂)))) ⟩
    dZZ x z • R x ∎
    where
    y x : ℕ
    y = z + e
    x = suc y
    Cm : Circuit N
    Cm = dZZ-chain z e
    bnd′ : suc (suc y) < 2 ^ N
    bnd′ = bnd
    d₁ : suc x ∸ z ≡ suc (suc e)
    d₁ = Eq.trans (Eq.cong (_∸ z) (Eq.sym (Eq.trans (+-suc z (suc e)) (Eq.cong suc (+-suc z e))))) (m+n∸m≡n z (suc (suc e)))
    d₂ : x ∸ z ≡ suc e
    d₂ = Eq.trans (Eq.cong (_∸ z) (Eq.sym (+-suc z e))) (m+n∸m≡n z (suc e))
    xb : suc x < 2 ^ N
    xb = bnd
    farC : ∀ i → z ≤ i → i < z + e → R x • Bx i ≈ Bx i • R x
    farC i _ i< = far x i xb (≤-<-trans (s≤s (<⇒≤ (<-trans i< (n<1+n y)))) bnd′) (inj₂ (s≤s i<))

  plus₁ : ∀ z x → z < x → Σ ℕ λ e → x ≡ suc (z + e)
  plus₁ zero    (suc x) _       = x , Eq.refl
  plus₁ (suc z) (suc x) (s≤s p) with plus₁ z x p
  ... | e , q = e , Eq.cong suc q

  unrev : ∀ x z → suc x < 2 ^ N → z < 2 ^ N → z ≢ x → z ≢ suc x →
          R x • dZZ (suc x) z ≈ dZZ x z • R x
  unrev x z xb zb zx zx′ = go (<-cmp z x)
    where
    below : (Σ ℕ λ e → x ≡ suc (z + e)) → R x • dZZ (suc x) z ≈ dZZ x z • R x
    below (e , q) = Eq.subst (λ w → R w • dZZ (suc w) z ≈ dZZ w z • R w) (Eq.sym q)
                             (down z e (Eq.subst (λ w → suc w < 2 ^ N) q xb))
    above : (suc x < z) ⊎ (suc x ≡ z) → R x • dZZ (suc x) z ≈ dZZ x z • R x
    above (inj₂ q) = ⊥-elim (zx′ (Eq.sym q))
    above (inj₁ p) with plus₁ (suc x) z p
    ... | e , q = Eq.subst (λ w → R x • dZZ (suc x) w ≈ dZZ x w • R x) (Eq.sym q)
                           (up x e (Eq.subst (_< 2 ^ N) q zb))
    go : Relation.Binary.Definitions.Tri (z < x) (z ≡ x) (x < z) → R x • dZZ (suc x) z ≈ dZZ x z • R x
    go (tri≈ _ e _)  = ⊥-elim (zx e)
    go (tri< zx< _ _) = below (plus₁ z x zx<)
    go (tri> _ _ xz) = above (m≤n⇒m<n∨m≡n xz)

------------------------------------------------------------------------
-- (31)

e31 : ∀ (a a′ c : I) → Succ a a′ → c ≢ a → c ≢ a′ →
      (d ʷ) (zz {N} a′ c • zx a a a′) ≈ (d ʷ) (zx {N} a a a′ • zz a c)
e31 a a′ c s ca ca′ = begin
  (d ʷ) (zz a′ c • zx a a a′)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ (Eq.cong (λ i → rev (dZZ {m} i z)) s) (dec a a′ s)) ⟩
  rev (R x • dZZ (suc x) z)
    ≈⟨ rev-cong (unrev x z xb (toℕ<n c) (λ e → ca (toℕ-injective e)) (λ e → ca′ (toℕ-injective (Eq.trans e (Eq.sym s))))) ⟩
  rev (dZZ x z • R x)
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong (λ u → u • rev (dZZ {m} x z)) (dec a a′ s))) ⟩
  (d ʷ) (zx a a a′ • zz a c) ∎
  where
  x z : ℕ
  x = toℕ a
  z = toℕ c
  xb : suc x < 2 ^ N
  xb = Eq.subst (_< 2 ^ N) s (toℕ<n a′)
  dec : ∀ (c c′ : I) → Succ c c′ → (d ʷ) (zx {N} c c c′) ≡ rev (dZXlo₁ {m} (toℕ c))
  dec c c′ s′ = Eq.trans (d-zx c c c′ cc′)
                  (Eq.trans (Eq.cong (λ i → rev (dZX {m} (toℕ c) (toℕ c) i)) s′) (Eq.cong rev (dZX-lo₁ (toℕ c))))
    where
    cc′ : c ≢ c′
    cc′ e = <⇒≢ (n<1+n (toℕ c)) (Eq.trans (Eq.cong toℕ e) s′)
