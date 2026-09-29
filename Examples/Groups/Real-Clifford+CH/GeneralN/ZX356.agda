------------------------------------------------------------------------
-- Presentations of groups
--
-- Z, CZ and X on the target of a rotation turn it over (Clément, Lemma
-- D.15, Equations (356), (357))
--
-- At width 5 + k, with ZX = ΛZX (4 + k) and XZ = ΛXZ (4 + k) the
-- rotations on wire 0:
--
--   Z • ZX • Z ≈ XZ          (`zx-Z`)
--   CZ • ZX • CZ ≈ XZ        (`eq357`, CZ on the wires 0 1)
--   X • ZX • X ≈ XZ          (`eq356`)
--
-- The first two are one argument, the D-trick (`conj-trick`).  Z on wire
-- 0 is the box on wire 1 merged over every colouring of the wires 2 …
-- (MergeAll.merge-top₁ under the swap).  CZ on the wires 0 1 is the box
-- on wire 2 merged over the wires 3 … (merge-top₂ under two swaps).
-- Every factor but the black one is the square of a coloured rotation
-- separated from the rotation on wire 0 by a white wire (RotAnywhere).
-- The black one, B, turns ZX over: ZX = CH B CH B with B the box on
-- wire 1 (Definition 2.4), and ZX = HG K HG K with K the box on wire 2
-- ((333)).  The third: the rotation merged over every colouring of its
-- controls is X • Z on wire 0 (RotMerge), which commutes with ZX by the
-- D-trick again, so X • XZ • X = (X Z) ZX (Z X) = ZX.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.ZX356
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; m≤n⇒m<n∨m≡n)
open import Data.Product using (Σ ; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; X² ; Z² ; CZ² ; Ex² ; S-Z↑)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (CZ₂₀-Ex↑)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; sdS ; net-sdS ; revS-sdS ; net-suS ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT ; ∏-conj ; ∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX355 complete₂ complete₃ using (eq355)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (K ; HG ; eq333 ; eq334)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere complete₂ complete₃ using (rot-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotMerge complete₂ complete₃
  using (F ; TopMerge ; top-merge ; rmerge-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (pass-last′ ; module MergeTop)
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol

private
  -- A white bit of a colouring that is not all black.
  white : ∀ {n} (c : Bits n) → c ≢ replicate n true → Σ (Fin n) (λ j → lookupℕ (toℕ j) c ≡ false)
  white []          ne = ⊥-elim (ne Eq.refl)
  white (false ∷ c) ne = 0F , Eq.refl
  white (true ∷ c)  ne with white c (λ e → ne (Eq.cong (true ∷_) e))
  ... | j , e = sF j , e

  lk-ones : ∀ {n} (j : Fin n) → lookupℕ (toℕ j) (replicate n true) ≡ true
  lk-ones 0F     = Eq.refl
  lk-ones (sF j) = lk-ones j

  tf : true ≢ false
  tf ()

------------------------------------------------------------------------
-- The merge on the top wire at every width below 5 + k + 1

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  top⁺ : ∀ β K → K < ₄₊ k → TopMerge β K
  top⁺ β K (s≤s K≤) with m≤n⇒m<n∨m≡n K≤
  top⁺ β     K           (s≤s K≤) | inj₁ K< = top-merge k below β K K<
  top⁺ true  .(₃₊ k)     (s≤s K≤) | inj₂ Eq.refl = rmerge-top k below true
  top⁺ false .(₃₊ k)     (s≤s K≤) | inj₂ Eq.refl = rmerge-top k below false

  -- The rotation on 5 + k wires over every colouring of its controls.
  merge-rot⁺ : ∀ β → (₁₊ (₄₊ k)) ⊢ ∏ (allBits (₄₊ k)) (λ c → negsB (true ∷ c) • F β (₄₊ k) • negsB (true ∷ c))
                                   ≈ F β 0 ↓ᵏ (₄₊ k)
  merge-rot⁺ true  = MergeTop.merge-top₀ (F true) (₄₊ k) (top⁺ true) Eq.refl (λ j → Eq.refl) (₄₊ k) ≤-refl
  merge-rot⁺ false = MergeTop.merge-top₀ (F false) (₄₊ k) (top⁺ false) Eq.refl (λ j → Eq.refl) (₄₊ k) ≤-refl

------------------------------------------------------------------------
-- (356), (357)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

    module I = Invol canon complete₂

  open Tools (N VRel,_===_)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₁ ; merge-top₂)

  private
    ZXn XZn Λ E : Circuit N
    ZXn = ΛZX (₄₊ k)
    XZn = ΛXZ (₄₊ k)
    Λ  = Λ□ (₄₊ k)
    E  = Ex ↓ • Λ • Ex ↓

    ones₅ : Bits N
    ones₅ = replicate N true

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    pass₂ : ∀ {y a b : Circuit N} → y • a ≈ a • y → y • b ≈ b • y → y • (a • b) ≈ (a • b) • y
    pass₂ pa pb = trans (sym assoc) (trans (front _ pa) (trans assoc (trans (back _ pb) (sym assoc))))

    module S₀₁ = Conj {N} (Ex ↓) Ex²
    module S₁₂ = Conj {N} (Ex ↑) (lemma-cong↑ _ _ Ex²)

    Λ² : Λ • Λ ≈ ε
    Λ² = Canon.invol canon

    E² : E • E ≈ ε
    E² = S₀₁.⟪⟫-invol Λ²

    K² : K k below • K k below ≈ ε
    K² = S₁₂.⟪⟫-invol E²

    col-• : ∀ (s : Bits N) a b → col s (a • b) ≈ col s a • col s b
    col-• s a b = sym (begin
      (negsB s • a • negsB s) • (negsB s • b • negsB s)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      negsB s • a • ((negsB s • negsB s) • b • negsB s)
        ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      negsB s • a • (b • negsB s)
        ≈⟨ back _ (sym assoc) ⟩
      negsB s • (a • b) • negsB s ∎)

    col-sq : ∀ (s : Bits N) {B A : Circuit N} → B ≈ A • A → col s B ≈ col s A • col s A
    col-sq s e = trans (back _ (front _ e)) (col-• s _ _)

    -- The colourings all black.
    col-1 : ∀ (w : Circuit N) → col ones₅ w ≈ w
    col-1 w = trans (≡→≈ (Eq.cong (λ z → z • w • z) (allT N))) (trans left-unit right-unit)

    ----------------------------------------------------------------------
    -- Placed rotations

    pl-sd : ∀ t (g : Circuit N) → pl (sdS {N} t) g ≡ shiftDown t • g • shiftUp t
    pl-sd t g = Eq.cong₂ (λ a b → a • g • b) (net-sdS t) (Eq.trans (Eq.cong net (revS-sdS t)) (net-suS t))

    R-ones : ∀ β → rot β ≈ place ε ones₅ (rot β)
    R-ones β = sym (trans (≡→≈ (Eq.cong (λ z → z • (ε • rot β • ε) • z) (allT N)))
                          (trans left-unit (trans right-unit (trans left-unit right-unit))))

    place-ε : ∀ (s : Bits N) (g : Circuit N) → place ε s g ≈ col s g
    place-ε s g = back _ (front _ (trans left-unit right-unit))

    -- A rotation on wire t, coloured s, and the rotation on wire 0 are
    -- separated by a wire j where s is white ((351)/(352)).
    sep-rot : ∀ α β (t : Fin N) (s : Bits N) → lookupℕ (toℕ t) s ≡ true →
              (j : Fin N) → j ≢ 0F → j ≢ t → lookupℕ (toℕ j) s ≡ false →
              rot α • place (sdS (toℕ t)) s (rot β) ≈ place (sdS (toℕ t)) s (rot β) • rot α
    sep-rot α β t s st j j0 jt sj =
      trans (front _ (R-ones α))
        (trans (rot-comm k below α β ε (sdS (toℕ t)) 0F t Eq.refl (sd-target t) ones₅ s Eq.refl st j j0 jt
                         (λ e → tf (Eq.trans (Eq.sym (lk-ones j)) (Eq.trans e sj))))
               (back _ (sym (R-ones α))))

    -- The box on wire 1, and on wire 2, as the square of a rotation there.
    R₁ R₂ : Circuit N
    R₁ = pl (sdS {N} 1) XZn
    R₂ = pl (sdS {N} 2) XZn

    E-sq : E ≈ R₁ • R₁
    E-sq = trans (S₀₁.⟪⟫-cong (eq355 k below)) (trans (S₀₁.⟪⟫-• XZn XZn) (cong u₁ u₁))
      where
      u₁ : S₀₁.⟪ XZn ⟫ ≈ R₁
      u₁ = trans (cong (sym right-unit) (back _ (sym left-unit))) (≡→≈ (Eq.sym (pl-sd 1 XZn)))

    K-sq : K k below ≈ R₂ • R₂
    K-sq = trans (S₁₂.⟪⟫-cong E-sq′) (trans (S₁₂.⟪⟫-• _ _) (cong u₂ u₂))
      where
      E-sq′ : E ≈ S₀₁.⟪ XZn ⟫ • S₀₁.⟪ XZn ⟫
      E-sq′ = trans (S₀₁.⟪⟫-cong (eq355 k below)) (S₀₁.⟪⟫-• XZn XZn)
      u₂ : S₁₂.⟪ S₀₁.⟪ XZn ⟫ ⟫ ≈ R₂
      u₂ = trans (sym (trans (front _ (back _ right-unit)) (trans (back _ (back _ (front _ left-unit)))
                                (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl))))
                 (≡→≈ (Eq.sym (pl-sd 2 XZn)))

    ----------------------------------------------------------------------
    -- The D-trick: a merge C whose black factor B turns ZX over does too

    conj-trick : ∀ {j} (g : Bits j → Circuit N) (B C : Circuit N) →
                 C ≈ ∏ (allBits j) g → g (replicate j true) ≈ B → B • B ≈ ε → C • C ≈ ε →
                 (∀ c → c ≢ replicate j true → XZn • g c ≈ g c • XZn) →
                 B • ZXn • B ≈ XZn → C • ZXn • C ≈ XZn
    conj-trick {j} g B C C∏ g1 B² C² sep BZB = begin
      C • ZXn • C                   ≈⟨ cong CDB (back _ CBDi) ⟩
      (D • B) • ZXn • (B • Di)      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      D • (B • ZXn • B) • Di        ≈⟨ back _ (front _ BZB) ⟩
      D • XZn • Di                  ≈⟨ trans (sym assoc) (trans (front _ (sym XZ-D)) assoc) ⟩
      XZn • D • Di                  ≈⟨ trans (back _ DDi) right-unit ⟩
      XZn ∎
      where
      D Di : Circuit N
      D  = ∏ (allBits j) g • B
      Di = B • C
      XZ-D : XZn • D ≈ D • XZn
      XZ-D = pass-last′ j g sep (trans (front _ g1) B²)
      CDB : C ≈ D • B
      CDB = trans C∏ (sym (trans assoc (trans (back _ B²) right-unit)))
      CBDi : C ≈ B • Di
      CBDi = sym (trans (sym assoc) (trans (front _ B²) left-unit))
      DDi : D • Di ≈ ε
      DDi = trans (sym assoc) (trans (front _ (sym CDB)) C²)

    ----------------------------------------------------------------------
    -- Z on wire 0

    gZ : Bits (₃₊ k) → Circuit N
    gZ c = col (true ∷ true ∷ c) E

    Z-∏ : Z ≈ ∏ (allBits (₃₊ k)) gZ
    Z-∏ = begin
      Z
        ≈⟨ sym S-Z↑ ⟩
      Ex ↓ • (Λ□ 1 ↓ᵏ (₃₊ k)) • Ex ↓
        ≈⟨ mid _ _ (sym (merge-top₁ (₃₊ k) ≤-refl)) ⟩
      Ex ↓ • ∏ (allBits (₃₊ k)) (λ c → col (true ∷ true ∷ c) Λ) • Ex ↓
        ≈⟨ ∏-conj (Ex ↓) Ex² (allBits (₃₊ k)) (λ c → col (true ∷ true ∷ c) Λ) ⟩
      ∏ (allBits (₃₊ k)) (λ c → Ex ↓ • col (true ∷ true ∷ c) Λ • Ex ↓)
        ≈⟨ ∏-cong (allBits (₃₊ k)) (λ c → sym (conj-swap (sym (low-comm Ex (negsB c))) Λ)) ⟩
      ∏ (allBits (₃₊ k)) gZ ∎

    sepZ : ∀ c → c ≢ replicate (₃₊ k) true → XZn • gZ c ≈ gZ c • XZn
    sepZ c ne with white c ne
    ... | j , cj = trans (back _ sq) (trans (pass₂ p p) (front _ (sym sq)))
      where
      s : Bits N
      s = true ∷ true ∷ c
      sq : gZ c ≈ place (sdS 1) s (rot false) • place (sdS 1) s (rot false)
      sq = col-sq s E-sq
      p : XZn • place (sdS 1) s (rot false) ≈ place (sdS 1) s (rot false) • XZn
      p = sep-rot false false (sF 0F) s Eq.refl (sF (sF j)) (λ ()) (λ ()) cj

    EZE : E • ZXn • E ≈ XZn
    EZE = trans (by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl)
                (back _ (back _ (back _ (trans (back _ E²) right-unit))))

    ----------------------------------------------------------------------
    -- CZ on the wires 0 1

    gK : Bits (₂₊ k) → Circuit N
    gK c = col (true ∷ true ∷ true ∷ c) (K k below)

    CZ-∏ : CZ ↓ ≈ ∏ (allBits (₂₊ k)) gK
    CZ-∏ = begin
      CZ ↓
        ≈⟨ sym (trans (back _ CZ₂₀-Ex↑) (trans (sym assoc) (trans (front _ (lemma-cong↑ _ _ Ex²)) left-unit))) ⟩
      S₁₂.⟪ S₀₁.⟪ Λ□ 2 ↓ᵏ (₂₊ k) ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong (sym (merge-top₂ (₂₊ k) ≤-refl))) ⟩
      S₁₂.⟪ S₀₁.⟪ ∏ (allBits (₂₊ k)) (λ c → col (true ∷ true ∷ true ∷ c) Λ) ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (∏-conj (Ex ↓) Ex² (allBits (₂₊ k)) (λ c → col (true ∷ true ∷ true ∷ c) Λ)) ⟩
      S₁₂.⟪ ∏ (allBits (₂₊ k)) (λ c → S₀₁.⟪ col (true ∷ true ∷ true ∷ c) Λ ⟫) ⟫
        ≈⟨ ∏-conj (Ex ↑) (lemma-cong↑ _ _ Ex²) (allBits (₂₊ k)) (λ c → S₀₁.⟪ col (true ∷ true ∷ true ∷ c) Λ ⟫) ⟩
      ∏ (allBits (₂₊ k)) (λ c → S₁₂.⟪ S₀₁.⟪ col (true ∷ true ∷ true ∷ c) Λ ⟫ ⟫)
        ≈⟨ ∏-cong (allBits (₂₊ k)) fac ⟩
      ∏ (allBits (₂₊ k)) gK ∎
      where
      fac : ∀ c → S₁₂.⟪ S₀₁.⟪ col (true ∷ true ∷ true ∷ c) Λ ⟫ ⟫ ≈ gK c
      fac c = trans (S₁₂.⟪⟫-cong (sym (conj-swap (sym (low-comm Ex (negsB c ↑))) Λ)))
                    (sym (conj-swap (sym (lemma-cong↑ _ _ (low-comm Ex (negsB c)))) E))

    sepK : ∀ c → c ≢ replicate (₂₊ k) true → XZn • gK c ≈ gK c • XZn
    sepK c ne with white c ne
    ... | j , cj = trans (back _ sq) (trans (pass₂ p p) (front _ (sym sq)))
      where
      s : Bits N
      s = true ∷ true ∷ true ∷ c
      sq : gK c ≈ place (sdS 2) s (rot false) • place (sdS 2) s (rot false)
      sq = col-sq s K-sq
      p : XZn • place (sdS 2) s (rot false) ≈ place (sdS 2) s (rot false) • XZn
      p = sep-rot false false (sF (sF 0F)) s Eq.refl (sF (sF (sF j))) (λ ()) (λ ()) cj

    KZK : K k below • ZXn • K k below ≈ XZn
    KZK = begin
      Kk • ZXn • Kk                            ≈⟨ back _ (front _ (sym (eq333 k below))) ⟩
      Kk • (HG k below • Kk • HG k below • Kk) • Kk
        ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
      Kk • HG k below • Kk • HG k below • (Kk • Kk)
        ≈⟨ back _ (back _ (back _ (trans (back _ K²) right-unit))) ⟩
      Kk • HG k below • Kk • HG k below   ≈⟨ eq334 k below ⟩
      XZn ∎
      where
      Kk : Circuit N
      Kk = K k below

  ----------------------------------------------------------------------
  -- Z and CZ on the target

  zx-Z : Z • ZXn • Z ≈ XZn
  zx-Z = conj-trick gZ E Z Z-∏ (col-1 E) E² Z² sepZ EZE

  eq357 : CZ ↓ • ZXn • CZ ↓ ≈ XZn
  eq357 = conj-trick gK (K k below) (CZ ↓) CZ-∏ (col-1 (K k below)) K² CZ² sepK KZK

  -- And the other way round, conjugating by the involution.
  xz-Z : Z • XZn • Z ≈ ZXn
  xz-Z = conj-sym Z² zx-Z

  eq357′ : CZ ↓ • XZn • CZ ↓ ≈ ZXn
  eq357′ = conj-sym CZ² eq357

  private
    ----------------------------------------------------------------------
    -- The rotation over every colouring of its controls commutes with ZX

    gz : Bits (₄₊ k) → Circuit N
    gz c = negsB (true ∷ c) • ZXn • negsB (true ∷ c)

    sepG : ∀ c → c ≢ replicate (₄₊ k) true → ZXn • gz c ≈ gz c • ZXn
    sepG c ne with white c ne
    ... | j , cj = trans (cong (R-ones true) (sym (place-ε (true ∷ c) ZXn)))
                         (trans (rot-comm k below true true ε ε 0F 0F Eq.refl Eq.refl ones₅ (true ∷ c) Eq.refl Eq.refl
                                          (sF j) (λ ()) (λ ()) (λ e → tf (Eq.trans (Eq.sym (lk-ones j)) (Eq.trans e cj))))
                                (cong (place-ε (true ∷ c) ZXn) (sym (R-ones true))))

    G-comm : (X • Z) • ZXn ≈ ZXn • (X • Z)
    G-comm = begin
      (X • Z) • ZXn
        ≈⟨ front _ (sym (merge-rot⁺ k below true)) ⟩
      G • ZXn
        ≈⟨ front _ GD ⟩
      (D • ZXn) • ZXn
        ≈⟨ front _ (sym D-ZX) ⟩
      (ZXn • D) • ZXn
        ≈⟨ trans assoc (back _ (sym GD)) ⟩
      ZXn • G
        ≈⟨ back _ (merge-rot⁺ k below true) ⟩
      ZXn • (X • Z) ∎
      where
      G D : Circuit N
      G = ∏ (allBits (₄₊ k)) gz
      D = G • XZn
      D-ZX : ZXn • D ≈ D • ZXn
      D-ZX = pass-last′ (₄₊ k) gz sepG (trans (front _ (col-1 ZXn)) I.zx-xz)
      GD : G ≈ D • ZXn
      GD = sym (trans assoc (trans (back _ I.xz-zx) right-unit))

  ----------------------------------------------------------------------
  -- (356)

  eq356 : X • XZn • X ≈ ZXn
  eq356 = begin
    X • XZn • X
      ≈⟨ back _ (front _ (sym zx-Z)) ⟩
    X • (Z • ZXn • Z) • X
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (X • Z) • ZXn • (Z • X)
      ≈⟨ trans (sym assoc) (trans (front _ G-comm) assoc) ⟩
    ZXn • (X • Z) • (Z • X)
      ≈⟨ back _ (trans (by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl)
                       (trans (back _ (trans (front _ Z²) left-unit)) X²)) ⟩
    ZXn • ε
      ≈⟨ right-unit ⟩
    ZXn ∎

  eq356′ : X • ZXn • X ≈ XZn
  eq356′ = conj-sym X² eq356
