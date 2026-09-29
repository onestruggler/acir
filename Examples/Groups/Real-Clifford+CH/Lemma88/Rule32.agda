------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (32) of Figure 8 (Clément, Appendix E.5)
--
-- (32) is (−1)_[a] X_[a,a′] · (−1)_[b] X_[b,b′] = the same letters in
-- the other order, for a′ = a + 1 < b and b′ = b + 1.  Each decodes to a
-- rotation — the multi-controlled ZX or XZ on the wire t_a where the
-- Gray codes of a and a + 1 differ, controlled by the other bits of the
-- code of a — which is the canonical rotation placed by the network
-- bringing t_a to wire 0 and coloured by the code (`letter`, as
-- Lemma84's mc□-boxF for the box).  Their colourings differ on a wire
-- off both targets (GrayWitness), so they commute: the module's
-- parameter, `RotComm`, which GeneralN.RotAnywhere gives at every width
-- from five on.  The decodings are reversed, which reversal of the
-- commutation absorbs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (RotComm)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 {m : ℕ} (rotcomm : RotComm m) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ<)
open import Data.Nat using (zero ; suc ; _<_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; <⇒≢ ; <-trans ; ≤-<-trans)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_ ; _ʷ)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zx)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (conj₁ ; negs ; tgtWire ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZX ; dZXlo₁ ; βof ; layout□ ; gcode ; slot)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (sdS ; revS ; net-sdS ; net-suS ; revS-sdS ; sd-target ; negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt ; setT ; zip-flip ; tgtWire-at ; negs-at)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; mc±XZ-rot)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-zx ; dZX-lo₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness {m} using (tgt ; tgt< ; gstep ; witness)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

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
         (Eq.trans (Eq.cong₂ (λ w j → w • shiftDown j • g • shiftUp j • w) (negs-at t G) (tgt-at t G (tgt< x bnd)))
                   (Eq.cong₂ (λ a b → negsB s′ • a • g • b • negsB s′)
                             (Eq.sym (net-sdS t)) (Eq.sym (Eq.trans (Eq.cong net (revS-sdS t)) (net-suS t)))))
    where
    tgt-at = tgtWire-at

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

------------------------------------------------------------------------
-- Two letters commute

comm : ∀ x y → suc x < y → suc y < 2 ^ N → dZXlo₁ {m} y • dZXlo₁ {m} x ≈ dZXlo₁ x • dZXlo₁ y
comm x y xy yb with witness x y xy yb
... | j , j< , jx , jy , ne = begin
  dZXlo₁ y • dZXlo₁ x
    ≈⟨ cong (letter′ y yb) (letter′ x xb) ⟩
  place (sdS (toℕ ty)) sy (rot (βof y)) • place (sdS (toℕ tx)) sx (rot (βof x))
    ≈⟨ rotcomm (βof y) (βof x) (sdS (toℕ ty)) (sdS (toℕ tx)) ty tx (sd-target ty) (sd-target tx) sy sx
               (lookup-setT-same (toℕ ty) (gcode y) (toℕ<n ty)) (lookup-setT-same (toℕ tx) (gcode x) (toℕ<n tx))
               jF (λ e → jy (wire e ty-≡)) (λ e → jx (wire e tx-≡)) diff ⟩
  place (sdS (toℕ tx)) sx (rot (βof x)) • place (sdS (toℕ ty)) sy (rot (βof y))
    ≈⟨ sym (cong (letter′ x xb) (letter′ y yb)) ⟩
  dZXlo₁ x • dZXlo₁ y ∎
  where
  xb : suc x < 2 ^ N
  xb = <-trans xy (<-trans (n<1+n y) yb)
  tx ty : Fin N
  tx = tw x xb
  ty = tw y yb
  tx-≡ : toℕ tx ≡ tgt x
  tx-≡ = toℕ-fromℕ< (tgt< x xb)
  ty-≡ : toℕ ty ≡ tgt y
  ty-≡ = toℕ-fromℕ< (tgt< y yb)
  sx sy : Bits N
  sx = setT (toℕ tx) (gcode x)
  sy = setT (toℕ ty) (gcode y)
  jF : Fin N
  jF = fromℕ< j<
  jF-≡ : toℕ jF ≡ j
  jF-≡ = toℕ-fromℕ< j<
  wire : ∀ {t : Fin N} {z} → jF ≡ t → toℕ t ≡ z → j ≡ z
  wire Eq.refl e = Eq.trans (Eq.sym jF-≡) e
  -- Off both targets the colourings are the codes.
  diff : lookupℕ (toℕ jF) sy ≢ lookupℕ (toℕ jF) sx
  diff e = ne (Eq.trans (Eq.sym (at x tx tx-≡ jx))
                (Eq.trans (Eq.sym (Eq.cong (λ i → lookupℕ i sx) jF-≡))
                  (Eq.trans (Eq.sym e) (Eq.trans (Eq.cong (λ i → lookupℕ i sy) jF-≡) (at y ty ty-≡ jy)))))
    where
    at : ∀ z (tz : Fin N) → toℕ tz ≡ tgt z → j ≢ tgt z → lookupℕ j (setT (toℕ tz) (gcode z)) ≡ lookupℕ j (gcode {m} z)
    at z tz e jz = lookup-setT-other (toℕ tz) j (gcode z) (λ q → jz (Eq.trans q e))

------------------------------------------------------------------------
-- (32)

e32 : ∀ (a a′ b b′ : I) → Succ a a′ → Succ b b′ → toℕ a′ < toℕ b →
      (d ʷ) (zx {N} a a a′ • zx b b b′) ≈ (d ʷ) (zx {N} b b b′ • zx a a a′)
e32 a a′ b b′ sa sb ab = begin
  (d ʷ) (zx a a a′ • zx b b b′)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ (dec a a′ sa) (dec b b′ sb)) ⟩
  rev (dZXlo₁ x) • rev (dZXlo₁ y)
    ≈⟨ rev-cong (comm x y xy yb) ⟩
  rev (dZXlo₁ y) • rev (dZXlo₁ x)
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ (dec b b′ sb) (dec a a′ sa))) ⟩
  (d ʷ) (zx b b b′ • zx a a a′) ∎
  where
  x y : ℕ
  x = toℕ a
  y = toℕ b
  xy : suc x < y
  xy = Eq.subst (_< y) sa ab
  yb : suc y < 2 ^ N
  yb = Eq.subst (_< 2 ^ N) sb (toℕ<n b′)
  -- (−1)_[c] X_[c,c′] decodes to the rotation of c.
  dec : ∀ (c c′ : I) → Succ c c′ → (d ʷ) (zx {N} c c c′) ≡ rev (dZXlo₁ {m} (toℕ c))
  dec c c′ s = Eq.trans (d-zx c c c′ cc′)
                 (Eq.trans (Eq.cong (λ i → rev (dZX {m} (toℕ c) (toℕ c) i)) s) (Eq.cong rev (dZX-lo₁ (toℕ c))))
    where
    cc′ : c ≢ c′
    cc′ e = <⇒≢ (n<1+n (toℕ c)) (Eq.trans (Eq.cong toℕ e) s)
