------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoded X gate and swap decoded (Clément, Lemmas 8.6 and 8.7 for
-- the gates of Appendix A.4.1)
--
-- At width 5 + k.  E-X 0 is E-Z 0 followed, over every context c of
-- the wires 1 …, by the letter (−1)_[1c] X_[0c,1c] on the two codes
-- that differ on wire 0.  Those two indices are consecutive — bit 0 of
-- a code flips bit 0 of its index, `idx-bit` — so the letter decodes to
-- one rotation (`dZXlo₁` or `dZXhi₁` of the lower index, whichever
-- carries the sign), and in both cases to the ZX on wire 0 coloured by
-- c; reversed by the decoding, the XZ (`dec-ℓ`).  Over every c they
-- merge into XZ on wire 0 (RotMerge's top merges, `mergeN`), E-Z 0
-- decodes to Z (Lemma87Z), and Z • XZ is X (`dEX0`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.DecX
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; _+_ ; _*_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-pred ; ≤-trans ; n≤1+n ; m≤n⇒m<n∨m≡n ; +-suc)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using (_∷_ ; _∷ʳ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Presentation.GroupLike using (module Group-Lemmas)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Z² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using () renaming (module Below to SBelow)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev≈⁻¹)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ ; insertℕ ; flipℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitAlg using (swapBits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (bit ; hd ; ungray ; fromBits ; index ; code-index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏ ; zx ; E-X ; E-Z ; E-CZ ; E-swap)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; Layout ; negs ; tgtWire ; mcZX ; mcXZ ; mc±ZX ; mc±XZ ; Xat ; swapAt)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dZX ; dZXlo₁ ; dZXhi₁ ; gcode ; layout□ ; slot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.OneWire using (on1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (∏-cong ; ∏-conj)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotMerge complete₂ complete₃
  using (F ; TopMerge ; top-merge ; rmerge-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (module MergeTop ; pairing ; pair-merge ; placeAt-∏)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87CZ as Lemma87CZ
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z as Lemma87Z
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
open import Examples.Groups.Real-Clifford+CH.Lemma88.Free complete₂ complete₃ using (dA5)
import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm as SignedPerm
import Examples.Groups.Real-Clifford+CH.Auxiliary.NetSP as NetSP
import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65H as Eq65H
import Examples.Groups.Real-Clifford+CH.Auxiliary.NF as NF

------------------------------------------------------------------------
-- Merges at the full width

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  -- The top merges below the full width are RotMerge's, the last one
  -- is (354) on the top wire.
  tmN : ∀ β K → K < ₄₊ k → TopMerge β K
  tmN β K K< with m≤n⇒m<n∨m≡n (≤-pred K<)
  tmN β     K K< | inj₁ K<′      = top-merge k below β K K<′
  tmN true  K K< | inj₂ Eq.refl  = rmerge-top k below true
  tmN false K K< | inj₂ Eq.refl  = rmerge-top k below false

  private
    ins-top : ∀ {j} (c : Bits j) b → insertℕ j b c ≡ c ∷ʳ b
    ins-top Data.Vec.[] b = Eq.refl
    ins-top (x ∷ c)     b = Eq.cong (x ∷_) (ins-top c b)

    top-↓ : ∀ β j → top (F β 1 ↓ᵏ j) ≡ F β 1 ↓ᵏ suc j
    top-↓ true  j = Eq.refl
    top-↓ false j = Eq.refl

    base : ∀ β → 2 ⊢ ∏ (allBits 0) (λ c → negsB (true ∷ true ∷ c) • F β 1 • negsB (true ∷ true ∷ c)) ≈ F β 1 ↓ᵏ 0
    base true  = trans right-unit (trans left-unit right-unit)
      where open Tools (2 VRel,_===_)
    base false = trans right-unit (trans left-unit right-unit)
      where open Tools (2 VRel,_===_)

  -- The rotation over every colouring of the wires 2 …, wire 1 kept a
  -- black control: the two-wire rotation.  merge-top₀ with two bottom
  -- wires.
  merge₁R : ∀ β j → j ≤ ₃₊ k →
            (₂₊ j) ⊢ ∏ (allBits j) (λ c → negsB (true ∷ true ∷ c) • F β (₁₊ j) • negsB (true ∷ true ∷ c))
                     ≈ F β 1 ↓ᵏ j
  merge₁R β zero    _ = base β
  merge₁R β (suc j) b = begin
    ∏ (allBits (suc j)) G
      ≈⟨ pairing j G ⟩
    ∏ (allBits j) (λ c → G (c ∷ʳ false) • G (c ∷ʳ true))
      ≈⟨ ∏-cong (allBits j) pair ⟩
    ∏ (allBits j) (λ c → placeAt (₂₊ j) (h c))
      ≈⟨ sym (placeAt-∏ (₂₊ j) (allBits j) h) ⟩
    placeAt (₂₊ j) (∏ (allBits j) h)
      ≈⟨ placeAt-cong (₂₊ j) (merge₁R β j (≤-trans (n≤1+n j) b)) ⟩
    placeAt (₂₊ j) (F β 1 ↓ᵏ j)
      ≈⟨ trans (placeAt-top (F β 1 ↓ᵏ j)) (≡→≈ (top-↓ β j)) ⟩
    F β 1 ↓ᵏ suc j ∎
    where
    open Tools ((₃₊ j) VRel,_===_)
    G : Bits (suc j) → Circuit (₃₊ j)
    G c = negsB (true ∷ true ∷ c) • F β (₂₊ j) • negsB (true ∷ true ∷ c)
    h : Bits j → Circuit (₂₊ j)
    h c = negsB (true ∷ true ∷ c) • F β (₁₊ j) • negsB (true ∷ true ∷ c)
    ≡→≈ : ∀ {x y : Circuit (₃₊ j)} → x ≡ y → x ≈ y
    ≡→≈ Eq.refl = refl
    pair : ∀ c → G (c ∷ʳ false) • G (c ∷ʳ true) ≈ placeAt (₂₊ j) (h c)
    pair c = trans (≡→≈ (Eq.cong₂ (λ x y → (negsB (true ∷ true ∷ x) • F β (₂₊ j) • negsB (true ∷ true ∷ x)) •
                                           (negsB (true ∷ true ∷ y) • F β (₂₊ j) • negsB (true ∷ true ∷ y)))
                                  (Eq.sym (ins-top c false)) (Eq.sym (ins-top c true))))
                   (pair-merge (F β (₂₊ j)) (F β (₁₊ j)) (₂₊ j) ≤-refl (true ∷ true ∷ c) (tmN β (₁₊ j) (s≤s b)))

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    m N : ℕ
    m = ₂₊ k
    N = ₃₊ m

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  open Tools (N VRel,_===_)
  open Group-Lemmas (N VRel,_===_) grouplike using (inverseʳ-unique)
  open Easy m using (d-zx ; dZX-lo₁ ; dZX-hi₁ ; e33)
  open Invol (canonN k completes) complete₂ using (rot-inv)
  open Lemma87Z (canonN k completes) (mergesₙ k completes) using (lemmaZ ; dʷ-∏)
  open Lemma87CZ (canonN k completes) (mergesₙ k completes) using (lemmaCZ)
  open SBelow 2 (s≤s (s≤s z≤n)) complete₂ using () renaming (by-sem to by-sem₂)
  open SignedPerm m using (sp ; _≐_ ; ≐-trans ; ≐-sym ; ≐-refl ; ⊙-cong)
  open NetSP m using (bm ; bm-⊙ ; bm-cong ; sp-EX ; sp-Eswap)
  open Eq65H m using (hf-EX ; hf-Eswap)
  open NF m using (cat)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    2*suc : ∀ x → 2 * suc x ≡ suc (suc (2 * x))
    2*suc x = Eq.cong suc (+-suc x (x + 0))

  ----------------------------------------------------------------------
  -- The rotation merged over every colouring of its controls, at the
  -- full width: the top merges below it are RotMerge's, the last one
  -- is (354) on the top wire.

  mergeN : ∀ β → ∏ (allBits (₄₊ k)) (λ c → negsB (true ∷ c) • F β (₄₊ k) • negsB (true ∷ c))
                 ≈ F β 0 ↓ᵏ (₄₊ k)
  mergeN true  = MergeTop.merge-top₀ (F true) (₄₊ k) (tmN k below true) Eq.refl (λ j → Eq.refl) (₄₊ k) ≤-refl
  mergeN false = MergeTop.merge-top₀ (F false) (₄₊ k) (tmN k below false) Eq.refl (λ j → Eq.refl) (₄₊ k) ≤-refl

  ----------------------------------------------------------------------
  -- The letters of E-X 0

  -- The index of a code: bit 0 of the code is bit 0 of the index,
  -- corrected by the rest.
  idx-bit : ∀ b (c : Bits (₄₊ k)) →
            toℕ (index N (b ∷ c)) ≡ bit (b xor hd (ungray c)) + 2 * fromBits (ungray c)
  idx-bit b c = toℕ-fromℕ< _

  -- The layout of the two codes: the target on wire 0, the rest
  -- controls.
  private
    negs-diag : ∀ {j} (c : Bits j) → negs (Data.Vec.zipWith slot c c) ≡ negsB c
    negs-diag Data.Vec.[]  = Eq.refl
    negs-diag (true ∷ c)   = Eq.cong _↑ (negs-diag c)
    negs-diag (false ∷ c)  = Eq.cong (λ z → X • z ↑) (negs-diag c)

    L₀ : Bits (₄₊ k) → Layout N
    L₀ c = tgt ∷ Data.Vec.zipWith slot c c

    -- mcXZ on that layout is the XZ coloured by c.
    mcXZ-col : ∀ c → mcXZ (L₀ c) ≈ col (true ∷ c) (ΛXZ (₄₊ k))
    mcXZ-col c = trans (≡→≈ (Eq.cong (λ z → z ↑ • ε • ΛXZ (₄₊ k) • ε • z ↑) (negs-diag c)))
                       (back _ (trans left-unit (back _ left-unit)))

    -- A decoded ZX, reversed, is the XZ.
    rev-ZX : ∀ L → rev (mcZX {₄₊ k} L) ≈ mcXZ L
    rev-ZX L = trans (rev≈⁻¹ (mcZX L)) (sym (inverseʳ-unique (rot-inv false L)))


  -- The letter of the context c.
  ℓ : Bits (₄₊ k) → Word (GenP N)
  ℓ c = zx {N} (index N (true ∷ c)) (index N (false ∷ c)) (index N (true ∷ c))

  dec-ℓ : ∀ c → (d ʷ) (ℓ c) ≈ col (true ∷ c) (ΛXZ (₄₊ k))
  dec-ℓ c = go (hd (ungray c)) Eq.refl
    where
    x1 x0 : Fin (2 ^ N)
    x1 = index N (true ∷ c)
    x0 = index N (false ∷ c)
    R : ℕ
    R = fromBits (ungray c)
    c1 : gcode {m} (toℕ x1) ≡ true ∷ c
    c1 = code-index N (true ∷ c)
    c0 : gcode {m} (toℕ x0) ≡ false ∷ c
    c0 = code-index N (false ∷ c)
    x0≢x1 : x0 ≢ x1
    x0≢x1 e = clash (Eq.trans (Eq.sym c0) (Eq.trans (Eq.cong (λ z → gcode {m} (toℕ z)) e) c1))
      where
      clash : false ∷ c ≢ true ∷ c
      clash ()
    go : ∀ h → hd (ungray c) ≡ h → (d ʷ) (ℓ c) ≈ col (true ∷ c) (ΛXZ (₄₊ k))
    -- h true: x1 = 2R is the lower index, the sign on it.
    go true e = begin
      (d ʷ) (zx x1 x0 x1)
        ≈⟨ e33 x1 x0 ⟩
      (d ʷ) (zx x1 x1 x0)
        ≈⟨ ≡→≈ (d-zx x1 x1 x0 (λ q → x0≢x1 (Eq.sym q))) ⟩
      rev (dZX (toℕ x1) (toℕ x1) (toℕ x0))
        ≈⟨ ≡→≈ (Eq.cong (λ v → rev (dZX (toℕ x1) (toℕ x1) v)) x0-suc) ⟩
      rev (dZX (toℕ x1) (toℕ x1) (suc (toℕ x1)))
        ≈⟨ ≡→≈ (Eq.cong rev (dZX-lo₁ (toℕ x1))) ⟩
      rev (dZXlo₁ (toℕ x1))
        ≈⟨ ≡→≈ (Eq.cong rev lo-≡) ⟩
      rev (mcZX (L₀ c))
        ≈⟨ rev-ZX (L₀ c) ⟩
      mcXZ (L₀ c)
        ≈⟨ mcXZ-col c ⟩
      col (true ∷ c) (ΛXZ (₄₊ k)) ∎
      where
      x1-eq : toℕ x1 ≡ 2 * R
      x1-eq = Eq.trans (idx-bit true c) (Eq.cong (λ h → bit (true xor h) + 2 * R) e)
      x0-suc : toℕ x0 ≡ suc (toℕ x1)
      x0-suc = Eq.trans (idx-bit false c) (Eq.trans (Eq.cong (λ h → bit (false xor h) + 2 * R) e) (Eq.cong suc (Eq.sym x1-eq)))
      lo-≡ : dZXlo₁ {m} (toℕ x1) ≡ mcZX (L₀ c)
      lo-≡ = Eq.cong₂ (λ g g′ → mc±XZ (lookupℕ (tgtWire (Data.Vec.zipWith slot g g′)) g) (Data.Vec.zipWith slot g g′))
                      c1 (Eq.trans (Eq.cong (gcode {m}) (Eq.sym x0-suc)) c0)
    -- h false: x0 = 2R is the lower index, the sign on the upper one.
    go false e = begin
      (d ʷ) (zx x1 x0 x1)
        ≈⟨ ≡→≈ (d-zx x1 x0 x1 x0≢x1) ⟩
      rev (dZX (toℕ x1) (toℕ x0) (toℕ x1))
        ≈⟨ ≡→≈ (Eq.cong (λ v → rev (dZX v (toℕ x0) v)) x1-suc) ⟩
      rev (dZX (suc (toℕ x0)) (toℕ x0) (suc (toℕ x0)))
        ≈⟨ ≡→≈ (Eq.cong rev (dZX-hi₁ (toℕ x0))) ⟩
      rev (dZXhi₁ (toℕ x0))
        ≈⟨ ≡→≈ (Eq.cong rev hi-≡) ⟩
      rev (mcZX (L₀ c))
        ≈⟨ rev-ZX (L₀ c) ⟩
      mcXZ (L₀ c)
        ≈⟨ mcXZ-col c ⟩
      col (true ∷ c) (ΛXZ (₄₊ k)) ∎
      where
      x0-eq : toℕ x0 ≡ 2 * R
      x0-eq = Eq.trans (idx-bit false c) (Eq.cong (λ h → bit (false xor h) + 2 * R) e)
      x1-suc : toℕ x1 ≡ suc (toℕ x0)
      x1-suc = Eq.trans (idx-bit true c) (Eq.trans (Eq.cong (λ h → bit (true xor h) + 2 * R) e) (Eq.cong suc (Eq.sym x0-eq)))
      hi-≡ : dZXhi₁ {m} (toℕ x0) ≡ mcZX (L₀ c)
      hi-≡ = Eq.cong₂ (λ g g′ → mc±ZX (lookupℕ (tgtWire (Data.Vec.zipWith slot g g′)) g) (Data.Vec.zipWith slot g g′))
                      c0 (Eq.trans (Eq.cong (gcode {m}) (Eq.sym x1-suc)) c1)

  ----------------------------------------------------------------------
  -- E-X 0

  dEX0 : (d ʷ) (E-X {m} 0) ≈ X
  dEX0 = begin
    (d ʷ) (E-Z 0) • (d ʷ) (∏ (allBits (₄₊ k)) ℓ)
      ≈⟨ cong (sym (lemmaZ 0 (s≤s z≤n))) (≡→≈ (dʷ-∏ (allBits (₄₊ k)) ℓ)) ⟩
    on1 Z 0 • ∏ (allBits (₄₊ k)) (λ c → (d ʷ) (ℓ c))
      ≈⟨ back _ (∏-cong (allBits (₄₊ k)) dec-ℓ) ⟩
    on1 Z 0 • ∏ (allBits (₄₊ k)) (λ c → col (true ∷ c) (ΛXZ (₄₊ k)))
      ≈⟨ back _ (mergeN false) ⟩
    Z • (Z • X)
      ≈⟨ trans (sym assoc) (trans (front _ Z²) left-unit) ⟩
    X ∎

  ----------------------------------------------------------------------
  -- The letters of the second product of E-swap 0: the rotation on
  -- wire 1, wire 0 a black control

  private
    L₁ : Bits (₃₊ k) → Layout N
    L₁ c = ctrl true ∷ tgt ∷ Data.Vec.zipWith slot c c

    mcZX-col₁ : ∀ c → mcZX (L₁ c) ≈ col (true ∷ true ∷ c) (Ex • ΛZX (₄₊ k) • Ex)
    mcZX-col₁ c = begin
      (negs Zl ↑ ↑) • (Ex • ε) • ΛZX (₄₊ k) • (ε • Ex) • (negs Zl ↑ ↑)
        ≈⟨ ≡→≈ (Eq.cong (λ z → (z ↑ ↑) • (Ex • ε) • ΛZX (₄₊ k) • (ε • Ex) • (z ↑ ↑)) (negs-diag c)) ⟩
      (negsB c ↑ ↑) • (Ex • ε) • ΛZX (₄₊ k) • (ε • Ex) • (negsB c ↑ ↑)
        ≈⟨ back _ (cong right-unit (back _ (front _ left-unit))) ⟩
      (negsB c ↑ ↑) • Ex • ΛZX (₄₊ k) • Ex • (negsB c ↑ ↑)
        ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
      col (true ∷ true ∷ c) (Ex • ΛZX (₄₊ k) • Ex) ∎
      where
      Zl : Layout (₃₊ k)
      Zl = Data.Vec.zipWith slot c c

    rev-XZ : ∀ L → rev (mcXZ {₄₊ k} L) ≈ mcZX L
    rev-XZ L = trans (rev≈⁻¹ (mcXZ L)) (sym (inverseʳ-unique (rot-inv true L)))

  ℓ₂ : Bits (₃₊ k) → Word (GenP N)
  ℓ₂ c = zx {N} (index N (true ∷ false ∷ c)) (index N (true ∷ false ∷ c)) (index N (true ∷ true ∷ c))

  dec-ℓ₂ : ∀ c → (d ʷ) (ℓ₂ c) ≈ col (true ∷ true ∷ c) (Ex • ΛZX (₄₊ k) • Ex)
  dec-ℓ₂ c = go (hd (ungray c)) Eq.refl
    where
    y0 y1 : Fin (2 ^ N)
    y0 = index N (true ∷ false ∷ c)
    y1 = index N (true ∷ true ∷ c)
    R : ℕ
    R = fromBits (ungray c)
    c0 : gcode {m} (toℕ y0) ≡ true ∷ false ∷ c
    c0 = code-index N (true ∷ false ∷ c)
    c1 : gcode {m} (toℕ y1) ≡ true ∷ true ∷ c
    c1 = code-index N (true ∷ true ∷ c)
    y0≢y1 : y0 ≢ y1
    y0≢y1 e = clash (Eq.trans (Eq.sym c0) (Eq.trans (Eq.cong (λ z → gcode {m} (toℕ z)) e) c1))
      where
      clash : true ∷ false ∷ c ≢ true ∷ true ∷ c
      clash ()
    idx₂ : ∀ b → toℕ (index N (true ∷ b ∷ c)) ≡ bit (true xor (b xor hd (ungray c))) + 2 * (bit (b xor hd (ungray c)) + 2 * R)
    idx₂ b = toℕ-fromℕ< _
    go : ∀ h → hd (ungray c) ≡ h → (d ʷ) (ℓ₂ c) ≈ col (true ∷ true ∷ c) (Ex • ΛZX (₄₊ k) • Ex)
    -- h false: y0 = 1 + 4R is the lower index, the sign on it.
    go false e = begin
      (d ʷ) (zx y0 y0 y1)
        ≈⟨ ≡→≈ (d-zx y0 y0 y1 y0≢y1) ⟩
      rev (dZX (toℕ y0) (toℕ y0) (toℕ y1))
        ≈⟨ ≡→≈ (Eq.cong (λ v → rev (dZX (toℕ y0) (toℕ y0) v)) y1-suc) ⟩
      rev (dZX (toℕ y0) (toℕ y0) (suc (toℕ y0)))
        ≈⟨ ≡→≈ (Eq.cong rev (dZX-lo₁ (toℕ y0))) ⟩
      rev (dZXlo₁ (toℕ y0))
        ≈⟨ ≡→≈ (Eq.cong rev lo-≡) ⟩
      rev (mcXZ (L₁ c))
        ≈⟨ rev-XZ (L₁ c) ⟩
      mcZX (L₁ c)
        ≈⟨ mcZX-col₁ c ⟩
      col (true ∷ true ∷ c) (Ex • ΛZX (₄₊ k) • Ex) ∎
      where
      y0-eq : toℕ y0 ≡ 1 + 2 * (2 * R)
      y0-eq = Eq.trans (idx₂ false) (Eq.cong (λ h → bit (true xor (false xor h)) + 2 * (bit (false xor h) + 2 * R)) e)
      y1-suc : toℕ y1 ≡ suc (toℕ y0)
      y1-suc = Eq.trans (idx₂ true) (Eq.trans (Eq.cong (λ h → bit (true xor (true xor h)) + 2 * (bit (true xor h) + 2 * R)) e)
                                              (Eq.trans (2*suc (2 * R)) (Eq.cong suc (Eq.sym y0-eq))))
      lo-≡ : dZXlo₁ {m} (toℕ y0) ≡ mcXZ (L₁ c)
      lo-≡ = Eq.cong₂ (λ g g′ → mc±XZ (lookupℕ (tgtWire (Data.Vec.zipWith slot g g′)) g) (Data.Vec.zipWith slot g g′))
                      c0 (Eq.trans (Eq.cong (gcode {m}) (Eq.sym y1-suc)) c1)
    -- h true: y1 = 1 + 4R is the lower index, the sign on the upper one.
    go true e = begin
      (d ʷ) (zx y0 y0 y1)
        ≈⟨ sym (e33 y0 y1) ⟩
      (d ʷ) (zx y0 y1 y0)
        ≈⟨ ≡→≈ (d-zx y0 y1 y0 (λ q → y0≢y1 (Eq.sym q))) ⟩
      rev (dZX (toℕ y0) (toℕ y1) (toℕ y0))
        ≈⟨ ≡→≈ (Eq.cong (λ v → rev (dZX v (toℕ y1) v)) y0-suc) ⟩
      rev (dZX (suc (toℕ y1)) (toℕ y1) (suc (toℕ y1)))
        ≈⟨ ≡→≈ (Eq.cong rev (dZX-hi₁ (toℕ y1))) ⟩
      rev (dZXhi₁ (toℕ y1))
        ≈⟨ ≡→≈ (Eq.cong rev hi-≡) ⟩
      rev (mcXZ (L₁ c))
        ≈⟨ rev-XZ (L₁ c) ⟩
      mcZX (L₁ c)
        ≈⟨ mcZX-col₁ c ⟩
      col (true ∷ true ∷ c) (Ex • ΛZX (₄₊ k) • Ex) ∎
      where
      y1-eq : toℕ y1 ≡ 1 + 2 * (2 * R)
      y1-eq = Eq.trans (idx₂ true) (Eq.cong (λ h → bit (true xor (true xor h)) + 2 * (bit (true xor h) + 2 * R)) e)
      y0-suc : toℕ y0 ≡ suc (toℕ y1)
      y0-suc = Eq.trans (idx₂ false) (Eq.trans (Eq.cong (λ h → bit (true xor (false xor h)) + 2 * (bit (false xor h) + 2 * R)) e)
                                               (Eq.trans (2*suc (2 * R)) (Eq.cong suc (Eq.sym y1-eq))))
      hi-≡ : dZXhi₁ {m} (toℕ y1) ≡ mcXZ (L₁ c)
      hi-≡ = Eq.cong₂ (λ g g′ → mc±ZX (lookupℕ (tgtWire (Data.Vec.zipWith slot g g′)) g) (Data.Vec.zipWith slot g g′))
                      c1 (Eq.trans (Eq.cong (gcode {m}) (Eq.sym y0-suc)) c0)

  ----------------------------------------------------------------------
  -- E-swap 0

  private
    col-Ex : ∀ c (g : Circuit N) → col (true ∷ true ∷ c) (Ex • g • Ex) ≈ Ex • col (true ∷ true ∷ c) g • Ex
    col-Ex c g = conj-swap (sym (low-comm Ex (negsB c))) g

  dP1 : (d ʷ) (∏ (allBits (₃₊ k)) (λ c → ℓ (true ∷ c))) ≈ ΛXZ 1 ↓ᵏ (₃₊ k)
  dP1 = begin
    (d ʷ) (∏ (allBits (₃₊ k)) (λ c → ℓ (true ∷ c)))
      ≈⟨ ≡→≈ (dʷ-∏ (allBits (₃₊ k)) (λ c → ℓ (true ∷ c))) ⟩
    ∏ (allBits (₃₊ k)) (λ c → (d ʷ) (ℓ (true ∷ c)))
      ≈⟨ ∏-cong (allBits (₃₊ k)) (λ c → dec-ℓ (true ∷ c)) ⟩
    ∏ (allBits (₃₊ k)) (λ c → col (true ∷ true ∷ c) (ΛXZ (₄₊ k)))
      ≈⟨ merge₁R k below false (₃₊ k) ≤-refl ⟩
    ΛXZ 1 ↓ᵏ (₃₊ k) ∎

  dP2 : (d ʷ) (∏ (allBits (₃₊ k)) ℓ₂) ≈ Ex • (ΛZX 1 ↓ᵏ (₃₊ k)) • Ex
  dP2 = begin
    (d ʷ) (∏ (allBits (₃₊ k)) ℓ₂)
      ≈⟨ ≡→≈ (dʷ-∏ (allBits (₃₊ k)) ℓ₂) ⟩
    ∏ (allBits (₃₊ k)) (λ c → (d ʷ) (ℓ₂ c))
      ≈⟨ ∏-cong (allBits (₃₊ k)) (λ c → trans (dec-ℓ₂ c) (col-Ex c (ΛZX (₄₊ k)))) ⟩
    ∏ (allBits (₃₊ k)) (λ c → Ex • col (true ∷ true ∷ c) (ΛZX (₄₊ k)) • Ex)
      ≈⟨ sym (∏-conj Ex Ex² (allBits (₃₊ k)) (λ c → col (true ∷ true ∷ c) (ΛZX (₄₊ k)))) ⟩
    Ex • ∏ (allBits (₃₊ k)) (λ c → col (true ∷ true ∷ c) (ΛZX (₄₊ k))) • Ex
      ≈⟨ mid _ _ (merge₁R k below true (₃₊ k) ≤-refl) ⟩
    Ex • (ΛZX 1 ↓ᵏ (₃₊ k)) • Ex ∎

  dEswap0 : (d ʷ) (E-swap {m} 0) ≈ Ex
  dEswap0 = begin
    (d ʷ) (E-CZ 0) • (d ʷ) (∏ (allBits (₃₊ k)) (λ c → ℓ (true ∷ c))) • (d ʷ) (∏ (allBits (₃₊ k)) ℓ₂) •
      (d ʷ) (∏ (allBits (₃₊ k)) (λ c → ℓ (true ∷ c)))
      ≈⟨ cong (sym (lemmaCZ 0 (s≤s (s≤s z≤n)))) (cong dP1 (cong dP2 dP1)) ⟩
    CZ • (ΛXZ 1 ↓ᵏ (₃₊ k)) • (Ex • (ΛZX 1 ↓ᵏ (₃₊ k)) • Ex) • (ΛXZ 1 ↓ᵏ (₃₊ k))
      ≈⟨ by-sem₂ (CZ • ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1) Ex Eq.refl {₃₊ k} ⟩
    Ex ∎

  ----------------------------------------------------------------------
  -- E-X one wire up: its signed permutation is that of E-X conjugated
  -- by the swap below it, so by Corollary A.5 its decoding is too

  private
    flip-swap : ∀ {n} w (x : Bits n) → suc w < n → swapBits w (flipℕ w (swapBits w x)) ≡ flipℕ (suc w) x
    flip-swap zero    Data.Vec.[] ()
    flip-swap zero    (a ∷ Data.Vec.[]) (s≤s ())
    flip-swap zero    (a ∷ b ∷ r) _       = Eq.refl
    flip-swap (suc w) Data.Vec.[] ()
    flip-swap (suc w) (a ∷ r)     (s≤s b) = Eq.cong (a ∷_) (flip-swap w r b)

    sp-rec : ∀ w → suc w < N → sp (E-X {m} (suc w)) ≐ sp (E-swap {m} w • E-X w • E-swap w)
    sp-rec w b = ≐-trans (sp-EX (suc w) b) (≐-sym (begin′))
      where
      w<N : w < N
      w<N = ≤-trans (n≤1+n (suc w)) b
      begin′ : sp (E-swap {m} w • E-X w • E-swap w) ≐ bm (flipℕ (suc w))
      begin′ = ≐-trans (⊙-cong (sp-Eswap w b) (⊙-cong (sp-EX w w<N) (sp-Eswap w b)))
               (≐-trans (⊙-cong (≐-refl {bm (swapBits w)}) (bm-⊙ (flipℕ w) (swapBits w)))
               (≐-trans (bm-⊙ (swapBits w) (λ x → swapBits w (flipℕ w x)))
                        (bm-cong _ (flipℕ (suc w)) (λ x → flip-swap w x b))))

  step-X : ∀ w → suc w < N → (d ʷ) (E-swap {m} w) ≈ swapAt w → (d ʷ) (E-X {m} w) ≈ Xat w →
           (d ʷ) (E-X {m} (suc w)) ≈ Xat (suc w)
  step-X w b ds dx = begin
    (d ʷ) (E-X (suc w))
      ≈⟨ dA5 k below (hf-EX (suc w)) (cat (hf-Eswap w) (cat (hf-EX w) (hf-Eswap w))) (sp-rec w b) ⟩
    (d ʷ) (E-swap w) • (d ʷ) (E-X w) • (d ʷ) (E-swap w)
      ≈⟨ cong ds (cong dx ds) ⟩
    swapAt w • Xat w • swapAt w
      ≈⟨ X-step w (≤-pred b) ⟩
    Xat (suc w) ∎
