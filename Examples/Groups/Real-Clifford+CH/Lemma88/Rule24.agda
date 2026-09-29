------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (24) of Figure 8 (Clément, Appendix E.5)
--
-- (24) is the braid relation of two consecutive signed exchanges,
-- (−1)_[a] X_[a,a′] · (−1)_[a′] X_[a′,a″] · (−1)_[a] X_[a,a′] = the same
-- with a and a′ exchanged, for a′ = a + 1 and a″ = a + 2.  Decoded, each
-- letter is a rotation R_x placed by the layout of the Gray-code step x
-- (Rule32.letter′), so the rule is R_a R_{a+1} R_a ≈ R_{a+1} R_a R_{a+1}.
-- The two steps have different targets (`tgt-apart`), their codes agree
-- off the first target (`gstep`), and the type of each rotation is its
-- code's bit at its own target — the negation of the other code's bit
-- there, resp. equal to it.  That is exactly the placed braid, the
-- module's parameter `braid`, which GeneralN.BraidAnywhere gives at
-- every width from five on.  The decodings are reversed, and reversal
-- is a congruence (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (RotComm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (Braid)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule24 {m : ℕ} (rotcomm : RotComm m) (braid : Braid m) where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ< ; toℕ-injective)
open import Data.Nat using (zero ; suc ; _<_ ; _^_ ; s≤s)
open import Data.Nat.Properties using (n<1+n ; <⇒≢ ; <-trans)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; _ʷ)

open import Notations using (₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zx)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (tgtWire)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZX ; dZXlo₁ ; βof ; layout□ ; gcode ; slot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (sdS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt ; setT ; zip-flip ; tgtWire-at)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-zx ; dZX-lo₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 {m} rotcomm using (letter′ ; tw)
open import Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness {m}
  using (tgt ; tgt< ; gstep ; tgt-apart ; lookup-flip-same ; lookup-flip-other)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  R : ℕ → Circuit N
  R = dZXlo₁ {m}

  lookup-setT-same : ∀ {n} i (s : Bits n) → i < n → lookupℕ i (setT i s) ≡ true
  lookup-setT-same zero    (b ∷ s) _       = Eq.refl
  lookup-setT-same (suc i) (b ∷ s) (s≤s p) = lookup-setT-same i s p

  lookup-setT-other : ∀ {n} i j (s : Bits n) → j ≢ i → lookupℕ j (setT i s) ≡ lookupℕ j s
  lookup-setT-other i       j       []      _  = Eq.refl
  lookup-setT-other zero    zero    (b ∷ s) ne = ⊥-elim (ne Eq.refl)
  lookup-setT-other zero    (suc j) (b ∷ s) _  = Eq.refl
  lookup-setT-other (suc i) zero    (b ∷ s) _  = Eq.refl
  lookup-setT-other (suc i) (suc j) (b ∷ s) ne = lookup-setT-other i j s (λ e → ne (Eq.cong suc e))

  -- The type of a step is its code's bit at its target.
  βof-tgt : ∀ x → suc x < 2 ^ N → βof {m} x ≡ lookupℕ (tgt x) (gcode x)
  βof-tgt x bnd = Eq.cong (λ i → lookupℕ i (gcode x)) (Eq.trans (Eq.cong tgtWire lay) (tgtWire-at (tgt x) (gcode x) (tgt< x bnd)))
    where
    lay : layout□ {m} x ≡ layoutAt (tgt x) (gcode x)
    lay = Eq.trans (Eq.cong (zipWith slot (gcode x)) (gstep x bnd)) (zip-flip (tgt x) (gcode x) (tgt< x bnd))

  ------------------------------------------------------------------------
  -- The unreversed rule

  unrev : ∀ x → suc (suc x) < 2 ^ N → R x • R (suc x) • R x ≈ R (suc x) • R x • R (suc x)
  unrev x bnd = begin
    R x • R (suc x) • R x
      ≈⟨ cong lx (cong ly lx) ⟩
    place ux sx (rot βx) • place uy sy (rot βy) • place ux sx (rot βx)
      ≈⟨ braid βx βy ux uy tx ty yx (sd-target tx) (sd-target ty) sx sy stx sty ag αe βe ⟩
    place uy sy (rot βy) • place ux sx (rot βx) • place uy sy (rot βy)
      ≈⟨ sym (cong ly (cong lx ly)) ⟩
    R (suc x) • R x • R (suc x) ∎
    where
    xb : suc x < 2 ^ N
    xb = <-trans (n<1+n (suc x)) bnd
    βx βy : Bool
    βx = βof x
    βy = βof (suc x)
    tx ty : Fin N
    tx = tw x xb
    ty = tw (suc x) bnd
    tx-≡ : toℕ tx ≡ tgt x
    tx-≡ = toℕ-fromℕ< (tgt< x xb)
    ty-≡ : toℕ ty ≡ tgt (suc x)
    ty-≡ = toℕ-fromℕ< (tgt< (suc x) bnd)
    ux uy : Word (S.Gen N)
    ux = sdS (toℕ tx)
    uy = sdS (toℕ ty)
    sx sy : Bits N
    sx = setT (toℕ tx) (gcode x)
    sy = setT (toℕ ty) (gcode (suc x))
    lx : R x ≈ place ux sx (rot βx)
    lx = letter′ x xb
    ly : R (suc x) ≈ place uy sy (rot βy)
    ly = letter′ (suc x) bnd
    yx : ty ≢ tx
    yx e = tgt-apart x (Eq.trans (Eq.sym tx-≡) (Eq.trans (Eq.cong toℕ (Eq.sym e)) ty-≡))
    txy : toℕ tx ≢ toℕ ty
    txy e = yx (toℕ-injective (Eq.sym e))
    stx : lookupℕ (toℕ tx) sx ≡ true
    stx = lookup-setT-same (toℕ tx) (gcode x) (toℕ<n tx)
    sty : lookupℕ (toℕ ty) sy ≡ true
    sty = lookup-setT-same (toℕ ty) (gcode (suc x)) (toℕ<n ty)
    flip : gcode {m} (suc x) ≡ flipAt (tgt x) (gcode x)
    flip = gstep x xb
    -- Off both targets the codes agree.
    ag : ∀ (j : Fin N) → j ≢ tx → j ≢ ty → lookupℕ (toℕ j) sx ≡ lookupℕ (toℕ j) sy
    ag j jx jy = Eq.trans (lookup-setT-other (toℕ tx) (toℕ j) (gcode x) (λ e → jx (toℕ-injective e)))
                   (Eq.trans (Eq.sym (Eq.trans (Eq.cong (lookupℕ (toℕ j)) flip)
                                              (lookup-flip-other (tgt x) (toℕ j) (gcode x)
                                                                 (λ e → jx (toℕ-injective (Eq.trans e (Eq.sym tx-≡)))))))
                             (Eq.sym (lookup-setT-other (toℕ ty) (toℕ j) (gcode (suc x)) (λ e → jy (toℕ-injective e)))))
    -- The first rotation's type is the negation of the second code's bit
    -- on the first target, the second's the first code's bit on the
    -- second target.
    αe : not βx ≡ lookupℕ (toℕ tx) sy
    αe = Eq.sym (Eq.trans (lookup-setT-other (toℕ ty) (toℕ tx) (gcode (suc x)) txy)
                  (Eq.trans (Eq.cong (λ i → lookupℕ i (gcode (suc x))) tx-≡)
                    (Eq.trans (Eq.cong (lookupℕ (tgt x)) flip)
                      (Eq.trans (lookup-flip-same (tgt x) (gcode x) (tgt< x xb))
                                (Eq.cong not (Eq.sym (βof-tgt x xb)))))))
    βe : βy ≡ lookupℕ (toℕ ty) sx
    βe = Eq.trans (βof-tgt (suc x) bnd)
           (Eq.trans (Eq.cong (λ i → lookupℕ i (gcode (suc x))) (Eq.sym ty-≡))
             (Eq.trans (Eq.cong (lookupℕ (toℕ ty)) flip)
               (Eq.trans (lookup-flip-other (tgt x) (toℕ ty) (gcode x) (λ e → txy (Eq.trans tx-≡ (Eq.sym e))))
                         (Eq.sym (lookup-setT-other (toℕ tx) (toℕ ty) (gcode x) (λ e → txy (Eq.sym e)))))))

------------------------------------------------------------------------
-- (24)

e24 : ∀ (a a′ a″ : I) → Succ a a′ → Succ a′ a″ →
      (d ʷ) (zx {N} a a a′ • zx a′ a′ a″ • zx a a a′) ≈ (d ʷ) (zx {N} a′ a′ a″ • zx a a a′ • zx a′ a′ a″)
e24 a a′ a″ s s′ = begin
  (d ʷ) (zx a a a′ • zx a′ a′ a″ • zx a a a′)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ (dec a a′ s) (Eq.cong₂ _•_ dec′ (dec a a′ s))) ⟩
  rev (R x) • rev (R (suc x)) • rev (R x)
    ≈⟨ by-passoc (□ • □ • □) ((□ • □) • □) Eq.refl ⟩
  rev (R x • R (suc x) • R x)
    ≈⟨ rev-cong (unrev x bnd) ⟩
  rev (R (suc x) • R x • R (suc x))
    ≈⟨ by-passoc ((□ • □) • □) (□ • □ • □) Eq.refl ⟩
  rev (R (suc x)) • rev (R x) • rev (R (suc x))
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ dec′ (Eq.cong₂ _•_ (dec a a′ s) dec′))) ⟩
  (d ʷ) (zx a′ a′ a″ • zx a a a′ • zx a′ a′ a″) ∎
  where
  x : ℕ
  x = toℕ a
  bnd : suc (suc x) < 2 ^ N
  bnd = Eq.subst (_< 2 ^ N) (Eq.trans s′ (Eq.cong suc s)) (toℕ<n a″)
  dec : ∀ (c c′ : I) → Succ c c′ → (d ʷ) (zx {N} c c c′) ≡ rev (dZXlo₁ {m} (toℕ c))
  dec c c′ s″ = Eq.trans (d-zx c c c′ cc′)
                  (Eq.trans (Eq.cong (λ i → rev (dZX {m} (toℕ c) (toℕ c) i)) s″) (Eq.cong rev (dZX-lo₁ (toℕ c))))
    where
    cc′ : c ≢ c′
    cc′ e = <⇒≢ (n<1+n (toℕ c)) (Eq.trans (Eq.cong toℕ e) s″)
  dec′ : (d ʷ) (zx {N} a′ a′ a″) ≡ rev (R (suc x))
  dec′ = Eq.trans (dec a′ a″ s′) (Eq.cong (λ i → rev (R i)) s)
