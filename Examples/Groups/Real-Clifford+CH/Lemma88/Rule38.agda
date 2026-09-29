------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (38) of Figure 8 (Clément, Appendix E.5)
--
-- (38) is (−1)_[a] X_[a,a′] · H_[0,1] H_[3,2] = H_[0,1] H_[3,2] · (−1)_[a] X_[a,a′]
-- for a′ = a + 1 and a ≥ 4.  Decoded, the letter is a rotation placed by
-- the layout of the Gray-code step a (Rule32.letter′), and the pair is
-- the gadget, the H gate on the wires 0 1 with every other control
-- white (Layout.gadget-form, its negations read off as the colouring
-- HGRotCol.gcol).  Since a ≥ 4 the code of a is black on some wire
-- j ≥ 2 other than the step's target (`sep38`: otherwise the code of a,
-- or of a + 1, would vanish above wire 1 and be the code of one of
-- 0 … 3), and there the gadget is white.  That is the module's
-- parameter `hgrot`, which GeneralN.HGAnywhere gives at every width from
-- five on.  The decodings are reversed, and reversal is a congruence
-- (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (RotComm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol using (HGRot)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule38 {m : ℕ} (rotcomm : RotComm m) (hgrot : HGRot m) where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ< ; toℕ-injective ; any?)
open import Data.Nat using (zero ; suc ; _<_ ; _≤_ ; _^_ ; s≤s ; z≤n ; _≟_ ; _≤?_)
open import Data.Nat.Properties using (n<1+n ; <⇒≢ ; ≤-trans ; <-trans ; <⇒≱)
open import Data.Product using (Σ ; _,_ ; _×_)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (_×?_ ; ¬?)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (_•_ ; _ʷ)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (toBits ; 8≤2^)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (Succ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zx ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (negs)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZX ; dZXlo₁ ; βof ; gcode ; gadget)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; sdS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (setT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters using (negs-layoutH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol using (gcol ; gadgetG)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-zx ; dZX-lo₁ ; d-hh0132)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 {m} rotcomm using (letter′ ; tw)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m}
  using (t ; g0 ; g1 ; g2 ; g3 ; layH ; T ; S ; gadget-form)
open import Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness {m}
  using (tgt ; tgt< ; gstep ; gcode-inj ; lookup-flip-same ; lookup-flip-other ; bits-ext)

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
  -- The gadget as a colouring of the H gate

  toBits0 : ∀ n → toBits n 0 ≡ replicate n false
  toBits0 zero    = Eq.refl
  toBits0 (suc n) = Eq.cong (false ∷_) (toBits0 n)

  T-≡ : T ≡ negsB (gcol m)
  T-≡ = Eq.trans (Eq.cong negs (Eq.sym layH))
          (Eq.trans (negs-layoutH 0 1 (gcode {m} 0))
                    (Eq.cong (λ g → negsB (setT 0 (setT 1 g)))
                             (Eq.trans g0 (Eq.cong (λ v → false ∷ false ∷ false ∷ v) (toBits0 m)))))

  gadget-G : gadget {m} ≈ gadgetG m
  gadget-G = trans gadget-form (≡→≈ (Eq.cong (λ z → z • S • z) T-≡))

  ------------------------------------------------------------------------
  -- A code vanishing above wire 1 is the code of one of 0 … 3

  lk-rep : ∀ {n} i → lookupℕ i (replicate n false) ≡ false
  lk-rep {zero}  i       = Eq.refl
  lk-rep {suc n} zero    = Eq.refl
  lk-rep {suc n} (suc i) = lk-rep {n} i

  lk-t : ∀ i → lookupℕ i (false ∷ t) ≡ false
  lk-t i = Eq.subst (λ v → lookupℕ i (false ∷ v) ≡ false) (Eq.sym (toBits0 m)) (lk-rep {suc m} i)

  <2^N : ∀ y → y < 4 → y < 2 ^ N
  <2^N y y<4 = ≤-trans y<4 (≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) (8≤2^ m))

  low4 : ∀ x → x < 2 ^ N → (∀ i → 2 ≤ i → i < N → lookupℕ i (gcode {m} x) ≡ false) → x < 4
  low4 x x< hi = go (lookupℕ 0 (gcode {m} x)) (lookupℕ 1 (gcode {m} x)) Eq.refl Eq.refl
    where
    shape : gcode {m} x ≡ lookupℕ 0 (gcode {m} x) ∷ lookupℕ 1 (gcode {m} x) ∷ false ∷ t
    shape = bits-ext _ _ f
      where
      f : ∀ j → j < N → lookupℕ j (gcode {m} x) ≡ lookupℕ j (lookupℕ 0 (gcode {m} x) ∷ lookupℕ 1 (gcode {m} x) ∷ false ∷ t)
      f zero          _ = Eq.refl
      f (suc zero)    _ = Eq.refl
      f (suc (suc i)) p = Eq.trans (hi (suc (suc i)) (s≤s (s≤s z≤n)) p) (Eq.sym (lk-t i))
    at : ∀ y → y < 4 → gcode {m} x ≡ gcode {m} y → x < 4
    at y y<4 e = Eq.subst (_< 4) (Eq.sym (gcode-inj x< (<2^N y y<4) e)) y<4
    to : ∀ {b0 b1} → lookupℕ 0 (gcode {m} x) ≡ b0 → lookupℕ 1 (gcode {m} x) ≡ b1 →
         gcode {m} x ≡ b0 ∷ b1 ∷ false ∷ t
    to e0 e1 = Eq.trans shape (Eq.cong₂ (λ a b → a ∷ b ∷ false ∷ t) e0 e1)
    go : ∀ b0 b1 → lookupℕ 0 (gcode {m} x) ≡ b0 → lookupℕ 1 (gcode {m} x) ≡ b1 → x < 4
    go false false e0 e1 = at 0 (s≤s z≤n) (Eq.trans (to e0 e1) (Eq.sym g0))
    go true  false e0 e1 = at 1 (s≤s (s≤s z≤n)) (Eq.trans (to e0 e1) (Eq.sym g1))
    go true  true  e0 e1 = at 2 (s≤s (s≤s (s≤s z≤n))) (Eq.trans (to e0 e1) (Eq.sym g2))
    go false true  e0 e1 = at 3 (s≤s (s≤s (s≤s (s≤s z≤n)))) (Eq.trans (to e0 e1) (Eq.sym g3))

  ------------------------------------------------------------------------
  -- The separating wire

  not-true : ∀ {b : Bool} → (b ≡ true → ⊥) → b ≡ false
  not-true {false} _ = Eq.refl
  not-true {true}  f = ⊥-elim (f Eq.refl)

  sep38 : ∀ a → 4 ≤ a → suc a < 2 ^ N →
          Σ (Fin N) λ j → (2 ≤ toℕ j) × (toℕ j ≢ tgt a) × (lookupℕ (toℕ j) (gcode {m} a) ≡ true)
  sep38 a 4≤a bnd
    with any? (λ (j : Fin N) → (2 ≤? toℕ j) ×? ((¬? (toℕ j ≟ tgt a)) ×? (lookupℕ (toℕ j) (gcode {m} a) ≟ᵇ true)))
  ... | yes (j , p , q , r) = j , p , q , r
  ... | no ¬e = ⊥-elim (decide (lookupℕ (tgt a) (gcode {m} a)) Eq.refl)
    where
    hi : ∀ i → 2 ≤ i → i < N → i ≢ tgt a → lookupℕ i (gcode {m} a) ≡ false
    hi i 2≤i i<N ne = not-true (λ e → ¬e (fromℕ< i<N , Eq.subst (2 ≤_) (Eq.sym ti) 2≤i ,
                                          (λ e′ → ne (Eq.trans (Eq.sym ti) e′)) ,
                                          Eq.trans (Eq.cong (λ x → lookupℕ x (gcode {m} a)) ti) e))
      where
      ti : toℕ (fromℕ< i<N) ≡ i
      ti = toℕ-fromℕ< i<N
    a< : a < 2 ^ N
    a< = <-trans (n<1+n a) bnd
    decide : ∀ b → lookupℕ (tgt a) (gcode {m} a) ≡ b → ⊥
    decide false e = <⇒≱ (low4 a a< hiA) 4≤a
      where
      hiA : ∀ i → 2 ≤ i → i < N → lookupℕ i (gcode {m} a) ≡ false
      hiA i 2≤i i<N with i ≟ tgt a
      ... | yes i≡ = Eq.trans (Eq.cong (λ x → lookupℕ x (gcode {m} a)) i≡) e
      ... | no  i≢ = hi i 2≤i i<N i≢
    decide true e = <⇒≱ (<-trans (n<1+n a) (low4 (suc a) bnd hiB)) 4≤a
      where
      hiB : ∀ i → 2 ≤ i → i < N → lookupℕ i (gcode {m} (suc a)) ≡ false
      hiB i 2≤i i<N with i ≟ tgt a
      ... | yes i≡ = Eq.trans (Eq.cong (lookupℕ i) (gstep a bnd))
                       (Eq.trans (Eq.cong (λ x → lookupℕ x (flipAt (tgt a) (gcode {m} a))) i≡)
                         (Eq.trans (lookup-flip-same (tgt a) (gcode {m} a) (tgt< a bnd)) (Eq.cong not e)))
      ... | no  i≢ = Eq.trans (Eq.cong (lookupℕ i) (gstep a bnd))
                       (Eq.trans (lookup-flip-other (tgt a) i (gcode {m} a) i≢) (hi i 2≤i i<N i≢))

  ------------------------------------------------------------------------
  -- The letter commutes with the gadget

  lookup-setT-same : ∀ {n} i (s : Bits n) → i < n → lookupℕ i (setT i s) ≡ true
  lookup-setT-same zero    (b ∷ s) _       = Eq.refl
  lookup-setT-same (suc i) (b ∷ s) (s≤s p) = lookup-setT-same i s p

  lookup-setT-other : ∀ {n} i j (s : Bits n) → j ≢ i → lookupℕ j (setT i s) ≡ lookupℕ j s
  lookup-setT-other i       j       []      _  = Eq.refl
  lookup-setT-other zero    zero    (b ∷ s) ne = ⊥-elim (ne Eq.refl)
  lookup-setT-other zero    (suc j) (b ∷ s) _  = Eq.refl
  lookup-setT-other (suc i) zero    (b ∷ s) _  = Eq.refl
  lookup-setT-other (suc i) (suc j) (b ∷ s) ne = lookup-setT-other i j s (λ e → ne (Eq.cong suc e))

  unrev : ∀ x → 4 ≤ x → (bnd : suc x < 2 ^ N) → gadget {m} • dZXlo₁ {m} x ≈ dZXlo₁ {m} x • gadget {m}
  unrev x 4≤x bnd with sep38 x 4≤x bnd
  ... | j , 2≤j , jt , gj = begin
    gadget • dZXlo₁ x
      ≈⟨ cong gadget-G lx ⟩
    gadgetG m • place (sdS (toℕ tF)) sx (rot (βof x))
      ≈⟨ sym (hgrot (βof x) (sdS (toℕ tF)) tF (sd-target tF) sx st j 2≤j jtF sj) ⟩
    place (sdS (toℕ tF)) sx (rot (βof x)) • gadgetG m
      ≈⟨ sym (cong lx gadget-G) ⟩
    dZXlo₁ x • gadget ∎
    where
    tF : Fin N
    tF = tw x bnd
    tF-≡ : toℕ tF ≡ tgt x
    tF-≡ = toℕ-fromℕ< (tgt< x bnd)
    sx : Bits N
    sx = setT (toℕ tF) (gcode {m} x)
    lx : dZXlo₁ {m} x ≈ place (sdS (toℕ tF)) sx (rot (βof x))
    lx = letter′ x bnd
    st : lookupℕ (toℕ tF) sx ≡ true
    st = lookup-setT-same (toℕ tF) (gcode {m} x) (toℕ<n tF)
    jtF : j ≢ tF
    jtF e = jt (Eq.trans (Eq.cong toℕ e) tF-≡)
    sj : lookupℕ (toℕ j) sx ≡ true
    sj = Eq.trans (lookup-setT-other (toℕ tF) (toℕ j) (gcode {m} x) (λ e → jtF (toℕ-injective e))) gj

------------------------------------------------------------------------
-- (38)

e38 : ∀ (a a′ : I) → Succ a a′ → 4 ≤ toℕ a →
      (d ʷ) (zx {N} a a a′ • hhℕ 0 1 3 2) ≈ (d ʷ) (hhℕ {N} 0 1 3 2 • zx a a a′)
e38 a a′ s 4≤a = begin
  (d ʷ) (zx a a a′ • hhℕ 0 1 3 2)          ≈⟨ ≡→≈ (Eq.cong₂ _•_ dec d-hh0132) ⟩
  rev (dZXlo₁ x) • rev gadget              ≈⟨ rev-cong (unrev x 4≤a bnd) ⟩
  rev gadget • rev (dZXlo₁ x)              ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d-hh0132 dec)) ⟩
  (d ʷ) (hhℕ 0 1 3 2 • zx a a a′) ∎
  where
  x : ℕ
  x = toℕ a
  bnd : suc x < 2 ^ N
  bnd = Eq.subst (_< 2 ^ N) s (toℕ<n a′)
  aa′ : a ≢ a′
  aa′ e = <⇒≢ (n<1+n (toℕ a)) (Eq.trans (Eq.cong toℕ e) s)
  dec : (d ʷ) (zx {N} a a a′) ≡ rev (dZXlo₁ {m} x)
  dec = Eq.trans (d-zx a a a′ aa′)
          (Eq.trans (Eq.cong (λ i → rev (dZX {m} x x i)) s) (Eq.cong rev (dZX-lo₁ x)))
