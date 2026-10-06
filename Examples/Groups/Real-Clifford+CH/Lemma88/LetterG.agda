------------------------------------------------------------------------
-- Presentations of groups
--
-- A decoded Gray-code letter as a placed gate (Clément, Appendix E.5)
--
-- A gate conjugated by the layout of the Gray-code step x — the
-- network bringing the step's target t_x to wire 0 and the negations
-- of the code of x off that target — is that gate placed by `sdS t_x`
-- and coloured by the code with the bit t_x set (`letterG`).  So the
-- letter (−1)_[x] X_[x,x+1] decodes to the canonical rotation placed
-- that way (`letter′`).  Nothing here depends on the width beyond the
-- Gray code, so the rules that decode such letters — (24), (31), (32),
-- (38), and Lemma 8.5 — share it at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Lemma88.LetterG {m : ℕ} where

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (zero ; suc ; _<_ ; _^_ ; s≤s)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (_•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (conj₁ ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.Decoding using (dZXlo₁ ; βof ; layout□ ; gcode ; slot)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (sdS ; revS ; net-sdS ; net-suS ; revS-sdS ; negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt ; setT ; zip-flip ; tgtWire-at ; negs-at)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; mc±XZ-rot)
open import Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness {m} using (tgt ; tgt< ; gstep)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- Setting a bit

lookup-setT-same : ∀ {n} i (s : Bits n) → i < n → lookupℕ i (setT i s) ≡ true
lookup-setT-same zero    (b ∷ s) _       = Eq.refl
lookup-setT-same (suc i) (b ∷ s) (s≤s p) = lookup-setT-same i s p

lookup-setT-other : ∀ {n} i j (s : Bits n) → j ≢ i → lookupℕ j (setT i s) ≡ lookupℕ j s
lookup-setT-other i       j       []      _  = Eq.refl
lookup-setT-other zero    zero    (b ∷ s) ne = ⊥-elim (ne Eq.refl)
lookup-setT-other zero    (suc j) (b ∷ s) _  = Eq.refl
lookup-setT-other (suc i) zero    (b ∷ s) _  = Eq.refl
lookup-setT-other (suc i) (suc j) (b ∷ s) ne = lookup-setT-other i j s (λ e → ne (Eq.cong suc e))

------------------------------------------------------------------------
-- A gate placed by the layout of a, as a placed gate

letterG : ∀ x → suc x < 2 ^ N → ∀ (g : Circuit N) →
          conj₁ (layout□ {m} x) g ≈ place (sdS (tgt x)) (setT (tgt x) (gcode x)) g
letterG x bnd g = trans (≡→≈ e₁) (by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl)
  where
  t : ℕ
  t = tgt x
  G : Bits N
  G = gcode x
  s′ : Bits N
  s′ = setT t G
  lay : layout□ {m} x ≡ layoutAt t G
  lay = Eq.trans (Eq.cong (zipWith slot G) (gstep x bnd)) (zip-flip t G (tgt< x bnd))
  e₁ : conj₁ (layout□ {m} x) g ≡ negsB s′ • net (sdS t) • g • net (revS (sdS {N} t)) • negsB s′
  e₁ = Eq.trans (Eq.cong (λ L → conj₁ L g) lay)
         (Eq.trans (Eq.cong₂ (λ w j → w • shiftDown j • g • shiftUp j • w) (negs-at t G) (tgtWire-at t G (tgt< x bnd)))
                   (Eq.cong₂ (λ a b → negsB s′ • a • g • b • negsB s′)
                             (Eq.sym (net-sdS t)) (Eq.sym (Eq.trans (Eq.cong net (revS-sdS t)) (net-suS t)))))

-- The target as a wire.
tw : ∀ x → suc x < 2 ^ N → Fin N
tw x bnd = fromℕ< (tgt< x bnd)

letterG′ : ∀ x (bnd : suc x < 2 ^ N) (g : Circuit N) →
           conj₁ (layout□ {m} x) g ≈ place (sdS (toℕ (tw x bnd))) (setT (toℕ (tw x bnd)) (gcode x)) g
letterG′ x bnd g = Eq.subst (λ j → conj₁ (layout□ {m} x) g ≈ place (sdS j) (setT j (gcode x)) g)
                            (Eq.sym (toℕ-fromℕ< (tgt< x bnd))) (letterG x bnd g)

-- The letter (−1)_[a] X_[a,a+1] as a placed rotation.
letter′ : ∀ x (bnd : suc x < 2 ^ N) →
          dZXlo₁ {m} x ≈ place (sdS (toℕ (tw x bnd))) (setT (toℕ (tw x bnd)) (gcode x)) (rot (βof x))
letter′ x bnd = trans (≡→≈ (mc±XZ-rot (βof x) (layout□ x))) (letterG′ x bnd (rot (βof x)))
