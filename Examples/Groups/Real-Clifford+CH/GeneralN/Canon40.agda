------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical form of rule (40) of Figure 8 (Clément, Lemma 8.8)
--
-- At width 5 + k, with Λ the box on wire 0, B = Ex-conj Λ the box on
-- wire 1 (Col.B₁), K = S₁₂⟪B⟫ the box on wire 2, Bt = K negated on wire
-- 0 and HG = Col.Hg the H gate on wire 0 with its box wire on wire 1:
--
--   HG • Bt ≈ ΛZX • Bt • HG                                     (`eq40c`)
--
-- which is what rule (40) decodes to once the negations common to its
-- three gates are conjugated away (Lemma88.Rule40).  The paper's proof
-- uses (333) with (353), (338) twice and (309); here:
--
--   * ΛZX ≈ CH₂ K CH₂ K by (353) (GeneralN.ZX353), CH₂ the CH from
--     wire 2 onto wire 0;
--   * K Bt ≈ B₂, the box on wire 2 with wire 0 idle ((309), Canon's
--     merge, and (274)), which CH₂ passes: the CH from a box wire onto an
--     idle wire, (280);
--   * HG ≈ CH₂ D with D = CH₂ HG, and D passes Bt: CH₂ is the product of HG
--     over every colouring of the wires 3 … (`merge-top₂`), and every
--     factor but the black one passes Bt by (339) — C339 transported by
--     the swap of the wires 2 3 and τ₀₂, then by adjacent swaps of the
--     wires 3 … to move its white control (`move′`); a product over
--     `allBits` times its black factor then passes (`pass-last`).
--
-- So ΛZX Bt HG = CH₂ K CH₂ K Bt CH₂ D = CH₂ K CH₂ B₂ CH₂ D = CH₂ K B₂ D
-- = CH₂ Bt D = CH₂ D Bt = HG Bt.  Every step was checked numerically at
-- four to six wires first (scratchpad r40/check40.py).
--
-- The same argument with the colour on wire 3 black says D passes K,
-- and (335) factor by factor says CH₂ passes HG ((340), `HG-CH₂`), so D
-- is an involution passing CH₂ and K and cancels from (353): the
-- rotations are words in HG and K, (333) and (334) (`eq333`, `eq334`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon40
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; ≤-refl)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Data.Vec.Properties using (∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt ; ΛH)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; CH² ; X²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt² ; swap-far ; swap-braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (eq280)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (P₁₃ ; Hg ; Hg₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base40 using (e-CH₂ ; e-X₃ ; e-τX ; e-trX ; e-trP)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box339 complete₂ complete₃ using (eq339)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃
  using (S-ZX ; S-XZ ; ∏-conj ; ∏-cong ; pass-∏ ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (move′ ; eq335)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Swaps of bits

swB-invol : ∀ i (t : Bits n) → swB i (swB i t) ≡ t
swB-invol i       []          = Eq.refl
swB-invol zero    (a ∷ [])    = Eq.refl
swB-invol zero    (a ∷ b ∷ t) = Eq.refl
swB-invol (suc i) (a ∷ t)     = Eq.cong (a ∷_) (swB-invol i t)

swB-T : ∀ i n → swB i (replicate n true) ≡ replicate n true
swB-T i       zero          = Eq.refl
swB-T zero    (suc zero)    = Eq.refl
swB-T zero    (suc (suc n)) = Eq.refl
swB-T (suc i) (suc n)       = Eq.cong (true ∷_) (swB-T i n)

swB-1 : ∀ i (t : Bits n) → swB i t ≡ replicate n true → t ≡ replicate n true
swB-1 {n} i t e = Eq.trans (Eq.sym (swB-invol i t)) (Eq.trans (Eq.cong (swB i) e) (swB-T i n))

------------------------------------------------------------------------
-- A product over every colouring, times its black factor

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  private
    ∏-++ : ∀ {A : Set} (xs ys : List A) (g : A → Circuit n) → ∏ (xs ++ ys) g ≈ ∏ xs g • ∏ ys g
    ∏-++ []       ys g = sym left-unit
    ∏-++ (x ∷ xs) ys g = trans (back _ (∏-++ xs ys g)) (sym assoc)

    ∏-map : ∀ {A C : Set} (h : C → A) (xs : List C) (g : A → Circuit n) →
            ∏ (map h xs) g ≡ ∏ xs (λ c → g (h c))
    ∏-map h []       g = Eq.refl
    ∏-map h (x ∷ xs) g = Eq.cong (g (h x) •_) (∏-map h xs g)

    ≡→≈ : ∀ {a b : Circuit n} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    via : ∀ {y u w : Circuit n} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    pass₂ : ∀ {a u v : Circuit n} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  -- y passes the product over every colouring times its all-black
  -- factor, when it passes every other factor and the all-black one is an
  -- involution: the black factor is in the second half of `allBits`.
  pass-last : ∀ j (g : Bits j → Circuit n) {y : Circuit n} →
              (∀ c → c ≢ replicate j true → y • g c ≈ g c • y) →
              g (replicate j true) • g (replicate j true) ≈ ε →
              y • (∏ (allBits j) g • g (replicate j true)) ≈ (∏ (allBits j) g • g (replicate j true)) • y
  pass-last zero    g p e = via (trans (front _ right-unit) e) (trans right-unit (sym left-unit))
  pass-last (suc j) g {y} p e =
    via split (pass₂ (pass-∏ (allBits j) (λ c → g (false ∷ c)) (λ c → p (false ∷ c) (λ ())))
                     (pass-last j (λ c → g (true ∷ c)) (λ c c≢ → p (true ∷ c) (λ q → c≢ (∷-injectiveʳ q))) e))
    where
    A : List (Bits j)
    A = allBits j
    split : ∏ (allBits (suc j)) g • g (replicate (suc j) true) ≈
            ∏ A (λ c → g (false ∷ c)) • (∏ A (λ c → g (true ∷ c)) • g (true ∷ replicate j true))
    split = begin
      ∏ (map (false ∷_) A ++ map (true ∷_) A) g • g (true ∷ replicate j true)
        ≈⟨ front _ (∏-++ (map (false ∷_) A) (map (true ∷_) A) g) ⟩
      (∏ (map (false ∷_) A) g • ∏ (map (true ∷_) A) g) • g (true ∷ replicate j true)
        ≈⟨ front _ (≡→≈ (Eq.cong₂ _•_ (∏-map (false ∷_) A g) (∏-map (true ∷_) A g))) ⟩
      (∏ A (λ c → g (false ∷ c)) • ∏ A (λ c → g (true ∷ c))) • g (true ∷ replicate j true)
        ≈⟨ assoc ⟩
      ∏ A (λ c → g (false ∷ c)) • (∏ A (λ c → g (true ∷ c)) • g (true ∷ replicate j true)) ∎

------------------------------------------------------------------------
-- The canonical form of rule (40)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m m′ : ℕ
    N  = ₁₊ (₄₊ k)
    m  = ₂₊ k
    m′ = ₁₊ k

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₂)

  Λ B K Bt CH₂ HG D B₂ : Circuit N
  Λ   = Λ□ (₄₊ k)
  B   = Ex ↓ • Λ • Ex ↓
  K   = S₁₂.⟪ B ⟫
  Bt  = X • K • X
  CH₂ = S₁₂.⟪ CH ⟫
  HG   = Hg (₂₊ k)
  D   = CH₂ • HG
  B₂  = S₁₂.⟪ Λ□ (₃₊ k) ↑ ⟫

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    via : ∀ {y u w : Circuit N} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p • q ≈ q • p → p′ • q′ ≈ q′ • p′
    both ep eq e = trans (sym (cong ep eq)) (trans e (cong eq ep))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    Ex↑↑² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
    Ex↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ Ex²)

    τ² : τ₀₂ • τ₀₂ ≈ ε
    τ² = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)

    module C₁₂ = Carry {N} (Ex ↑) Ex↑²
    module C₂₃ = Carry {N} (Ex ↑ ↑) Ex↑↑²
    module Cτ  = Carry {N} τ₀₂ τ²
    module Tτ  = Conj {N} τ₀₂ τ²
    module Pc  = Conj {N} (PP ↓) eq111

    --------------------------------------------------------------------
    -- Involutions

    Λ² : Λ • Λ ≈ ε
    Λ² = Canon.invol canon

    K² : K • K ≈ ε
    K² = S₁₂.⟪⟫-invol (S₀₁.⟪⟫-invol Λ²)

    CH₂² : CH₂ • CH₂ ≈ ε
    CH₂² = S₁₂.⟪⟫-invol CH²

    HG² : HG • HG ≈ ε
    HG² = Pc.⟪⟫-invol (S₀₁.⟪⟫-invol Λ²)

    -- The swaps of the wires 1 2 and 2 3 pass the box.
    S₁₂-Λ : S₁₂.⟪ Λ ⟫ ≈ Λ
    S₁₂-Λ = trans (sym assoc) (trans (front _ (symAt 0)) (trans assoc (trans (back _ Ex↑²) right-unit)))

    S₂₃-Λ : S₂₃.⟪ Λ ⟫ ≈ Λ
    S₂₃-Λ = trans (sym assoc) (trans (front _ (symAt 1)) (trans assoc (trans (back _ Ex↑↑²) right-unit)))

    --------------------------------------------------------------------
    -- (353), the merge on wire 0, and (280)

    ZX-K : ΛZX (₄₊ k) ≈ CH₂ • K • CH₂ • K
    ZX-K = trans (sym (S-ZX k below)) (S₁₂.⟪⟫-•₄ refl refl refl refl)

    -- X on wire 0 is X on wire 1 of Λ, through the two swaps.
    S01X : S₀₁.⟪ X ↑ ⟫ ≈ X
    S01X = conj-sym Ex² (X-step 0 (s≤s z≤n))

    S12X : S₁₂.⟪ X ⟫ ≈ X
    S12X = trans (sym assoc) (trans (front _ (sym (X-↑ Ex))) (trans assoc (trans (back _ Ex↑²) right-unit)))

    Xs : Bt ≈ S₁₂.⟪ S₀₁.⟪ X ↑ • Λ • X ↑ ⟫ ⟫
    Xs = trans (sym (S₁₂.⟪⟫-•₃ S12X refl S12X)) (S₁₂.⟪⟫-cong (sym (S₀₁.⟪⟫-•₃ S01X refl S01X)))

    merge₀ : K • Bt ≈ B₂
    merge₀ = begin
      K • Bt
        ≈⟨ back _ Xs ⟩
      S₁₂.⟪ S₀₁.⟪ Λ ⟫ ⟫ • S₁₂.⟪ S₀₁.⟪ X ↑ • Λ • X ↑ ⟫ ⟫
        ≈⟨ sym (trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-• Λ (X ↑ • Λ • X ↑))) (S₁₂.⟪⟫-• (S₀₁.⟪ Λ ⟫) (S₀₁.⟪ X ↑ • Λ • X ↑ ⟫))) ⟩
      S₁₂.⟪ S₀₁.⟪ Λ • (X ↑ • Λ • X ↑) ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong (Canon.merge canon)) ⟩
      S₁₂.⟪ S₀₁.⟪ Λ□ (₃₊ k) ↑ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (Canon.wire274 canon) ⟩
      B₂ ∎

    -- The CH from the box wire onto the idle wire below passes the box
    -- one wire up: (280), the swap of the two wires around it passing the
    -- box by (274).
    CH-Λ↑ : CH • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • CH
    CH-Λ↑ = trans (front _ (sym (unconj Ex²)))
                  (trans (lp ex (lp (eq280 (suc k) c) ex)) (back _ (unconj Ex²)))
      where
      L : Circuit N
      L = Λ□ (₃₊ k) ↑
      ex : Ex • L ≈ L • Ex
      ex = sym (conj-comm Ex² (Canon.wire274 canon))
      lp : ∀ {x y : Circuit N} → x • L ≈ L • x → y • L ≈ L • y → (x • y) • L ≈ L • (x • y)
      lp ex ey = trans assoc (trans (back _ ey) (trans (sym assoc) (trans (front _ ex) assoc)))

    B₂-CH₂ : B₂ • CH₂ ≈ CH₂ • B₂
    B₂-CH₂ = C₁₂.carry refl refl (sym CH-Λ↑)

    --------------------------------------------------------------------
    -- CH₂ as the product of HG over every colouring of the wires 3 …

    Hc : Bits m → Circuit N
    Hc y = col (true ∷ true ∷ true ∷ y) HG

    Lc : Bits m → Circuit N
    Lc y = col (true ∷ true ∷ true ∷ y) Λ

    Hc-form : ∀ y → Hc y ≈ PP ↓ • (Ex ↓ • Lc y • Ex ↓) • PP ↓
    Hc-form y = trans (conj-swap (sym (local-comm (PP {1}) (negsB y))) B)
                      (mid _ _ (conj-swap (sym (local-comm (Ex {1}) (negsB y))) Λ))

    CH₂-∏ : CH₂ ≈ ∏ (allBits m) Hc
    CH₂-∏ = begin
      CH₂
        ≈⟨ by-sem (Ex ↑ • CH • Ex ↑) (PP ↓ • (Ex ↓ • (Λ□ 2 ↓ᵏ 1) • Ex ↓) • PP ↓) (Evaluated.same e-CH₂) {m′} ⟩
      PP ↓ • (Ex ↓ • (Λ□ 2 ↓ᵏ m) • Ex ↓) • PP ↓
        ≈⟨ mid _ _ (mid _ _ (sym (merge-top₂ m ≤-refl))) ⟩
      PP ↓ • (Ex ↓ • ∏ (allBits m) Lc • Ex ↓) • PP ↓
        ≈⟨ mid _ _ (∏-conj (Ex ↓) Ex² (allBits m) Lc) ⟩
      PP ↓ • ∏ (allBits m) (λ y → Ex ↓ • Lc y • Ex ↓) • PP ↓
        ≈⟨ ∏-conj (PP ↓) eq111 (allBits m) (λ y → Ex ↓ • Lc y • Ex ↓) ⟩
      ∏ (allBits m) (λ y → PP ↓ • (Ex ↓ • Lc y • Ex ↓) • PP ↓)
        ≈⟨ ∏-cong (allBits m) (λ y → sym (Hc-form y)) ⟩
      ∏ (allBits m) Hc ∎

    Hc1 : Hc (replicate m true) ≈ HG
    Hc1 = trans (≡→≈ (Eq.cong (λ z → z ↑ ↑ ↑ • HG • z ↑ ↑ ↑) (allT m))) (trans left-unit right-unit)

    --------------------------------------------------------------------
    -- (339): C339 carried by the swap of the wires 2 3 and τ₀₂

    tr : Circuit N → Circuit N
    tr w = Tτ.⟪ S₂₃.⟪ w ⟫ ⟫

    tr-• : ∀ a b → tr (a • b) ≈ tr a • tr b
    tr-• a b = trans (Tτ.⟪⟫-cong (S₂₃.⟪⟫-• a b)) (Tτ.⟪⟫-• _ _)

    tr-cong : ∀ {a b} → a ≈ b → tr a ≈ tr b
    tr-cong e = Tτ.⟪⟫-cong (S₂₃.⟪⟫-cong e)

    trΛ : tr Λ ≈ K
    trΛ = begin
      τ₀₂ • S₂₃.⟪ Λ ⟫ • τ₀₂
        ≈⟨ mid _ _ S₂₃-Λ ⟩
      (Ex • Ex ↑ • Ex) • Λ • (Ex • Ex ↑ • Ex)
        ≈⟨ cong br (back _ br) ⟩
      (Ex ↑ • Ex • Ex ↑) • Λ • (Ex ↑ • Ex • Ex ↑)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
      Ex ↑ • (Ex • S₁₂.⟪ Λ ⟫ • Ex) • Ex ↑
        ≈⟨ mid _ _ (mid _ _ S₁₂-Λ) ⟩
      K ∎
      where
      br : Ex • Ex ↑ • Ex ≈ Ex ↑ • Ex • Ex ↑
      br = swap-braid 0 (s≤s (s≤s (s≤s z≤n)))

    trB : tr B ≈ B
    trB = begin
      τ₀₂ • S₂₃.⟪ S₀₁.⟪ Λ ⟫ ⟫ • τ₀₂
        ≈⟨ mid _ _ (trans (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
                   (trans (cong far (back _ (sym far)))
                   (trans (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)
                          (mid _ _ S₂₃-Λ)))) ⟩
      (Ex • Ex ↑ • Ex) • (Ex • Λ • Ex) • (Ex • Ex ↑ • Ex)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
      Ex • Ex ↑ • (Ex • Ex) • Λ • (Ex • Ex) • Ex ↑ • Ex
        ≈⟨ back _ (back _ (trans (front _ Ex²) (trans left-unit (back _ (trans (front _ Ex²) left-unit))))) ⟩
      Ex • Ex ↑ • Λ • Ex ↑ • Ex
        ≈⟨ back _ S₁₂-Λ′ ⟩
      Ex • Λ • Ex ∎
      where
      far : Ex ↑ ↑ • Ex ≈ Ex • Ex ↑ ↑
      far = sym (swap-far 0 2 (s≤s (s≤s z≤n)))
      S₁₂-Λ′ : Ex ↑ • Λ • Ex ↑ • Ex ≈ Λ • Ex
      S₁₂-Λ′ = trans (sym assoc) (trans (front _ (symAt 0)) (trans assoc (trans (back _ (trans (sym assoc) (trans (front _ Ex↑²) left-unit))) refl)))

    trX₃ : tr (X ↑ ↑ ↑) ≈ X
    trX₃ = trans (Tτ.⟪⟫-cong (by-sem (Ex ↑ ↑ • X ↑ ↑ ↑ • Ex ↑ ↑) (X ↑ ↑) (Evaluated.same e-X₃) {m′}))
                 (by-sem (τ₀₂ • X ↑ ↑ • τ₀₂) X (Evaluated.same e-τX) {m′})

    trX₂ : tr (X ↑ ↑) ≈ X ↑ ↑ ↑
    trX₂ = by-sem (τ₀₂ • (Ex ↑ ↑ • X ↑ ↑ • Ex ↑ ↑) • τ₀₂) (X ↑ ↑ ↑) (Evaluated.same e-trX) {m′}

    trP : tr P₁₃ ≈ PP ↓
    trP = by-sem (τ₀₂ • (Ex ↑ ↑ • P₁₃ • Ex ↑ ↑) • τ₀₂) (PP ↓) (Evaluated.same e-trP) {m′}

    trU : ∀ (y : Bits m′) → tr (negsB y ↑ ↑ ↑ ↑) ≈ negsB y ↑ ↑ ↑ ↑
    trU y = trans (Tτ.⟪⟫-cong (fix (local-comm (Ex {0} ↑ ↑) (negsB y)) Ex↑↑²))
                  (fix (local-comm (τ₀₂ {1}) (negsB y)) τ²)
      where
      fix : ∀ {s u : Circuit N} → s • u ≈ u • s → s • s ≈ ε → s • u • s ≈ u
      fix e s² = trans (sym assoc) (trans (front _ e) (trans assoc (trans (back _ s²) right-unit)))

    -- The box on wire 0, black but for the colour a on wire 3, and what
    -- the carrying makes of it: K, or K negated on wire 0.
    G1 : Bool → Circuit N
    G1 a = col (true ∷ true ∷ true ∷ a ∷ replicate m′ true) Λ

    Ka : Bool → Circuit N
    Ka true  = K
    Ka false = Bt

    G2 : Bits m′ → Circuit N
    G2 y = col (true ∷ true ∷ false ∷ true ∷ y) (Hg₃ m′)

    trG1 : ∀ a → tr (G1 a) ≈ Ka a
    trG1 true = trans (tr-cong (trans (≡→≈ (Eq.cong (λ z → z ↑ ↑ ↑ ↑ • Λ • z ↑ ↑ ↑ ↑) (allT m′)))
                                      (trans left-unit right-unit))) trΛ
    trG1 false = begin
      tr (G1 false)
        ≈⟨ tr-cong (trans (≡→≈ (Eq.cong (λ z → (X ↑ ↑ ↑ • z ↑ ↑ ↑ ↑) • Λ • (X ↑ ↑ ↑ • z ↑ ↑ ↑ ↑)) (allT m′)))
                          (cong right-unit (back _ right-unit))) ⟩
      tr (X ↑ ↑ ↑ • Λ • X ↑ ↑ ↑)
        ≈⟨ trans (tr-• _ _) (back _ (tr-• _ _)) ⟩
      tr (X ↑ ↑ ↑) • tr Λ • tr (X ↑ ↑ ↑)
        ≈⟨ cong trX₃ (cong trΛ trX₃) ⟩
      Bt ∎

    trG2 : ∀ y → tr (G2 y) ≈ Hc (false ∷ y)
    trG2 y = begin
      tr ((X ↑ ↑ • U) • (P₁₃ • B • P₁₃) • (X ↑ ↑ • U))
        ≈⟨ trans (tr-• _ _) (back _ (trans (tr-• _ _) (cong (trans (tr-• _ _) (back _ (tr-• _ _))) refl))) ⟩
      tr (X ↑ ↑ • U) • (tr P₁₃ • tr B • tr P₁₃) • tr (X ↑ ↑ • U)
        ≈⟨ cong XU (cong (cong trP (cong trB trP)) XU) ⟩
      (X ↑ ↑ ↑ • U) • (PP ↓ • B • PP ↓) • (X ↑ ↑ ↑ • U) ∎
      where
      U : Circuit N
      U = negsB y ↑ ↑ ↑ ↑
      XU : tr (X ↑ ↑ • U) ≈ X ↑ ↑ ↑ • U
      XU = trans (tr-• _ _) (cong trX₂ (trU y))

    base339 : ∀ a (y : Bits m′) → Ka a • Hc (false ∷ y) ≈ Hc (false ∷ y) • Ka a
    base339 a y = both (trG1 a) (trG2 y) (Cτ.carry refl refl (C₂₃.carry refl refl
                    (eq339 k below a (replicate m′ true) y)))

    -- The swap of two adjacent wires above wire 2.
    module Sw (i : ℕ) where
      S : Circuit N
      S = swapAt (suc (suc (suc i)))

      S² : S • S ≈ ε
      S² = swapAt² (suc (suc (suc i)))

      S-X : S • X ≈ X • S
      S-X = sym (X-↑ (swapAt (suc (suc i))))

      S-Ex : S • Ex ≈ Ex • S
      S-Ex = sym (swap-far 0 (suc (suc (suc i))) (s≤s (s≤s z≤n)))

      S-Ex↑ : S • Ex ↑ ≈ Ex ↑ • S
      S-Ex↑ = sym (swap-far 1 (suc (suc (suc i))) (s≤s (s≤s (s≤s z≤n))))

      S-Λ : S • Λ ≈ Λ • S
      S-Λ = symAt (suc (suc i))

      S-PP : S • PP ↓ ≈ PP ↓ • S
      S-PP = sym (low-comm PP (swapAt (suc i)))

      S-B : S • B ≈ B • S
      S-B = pass₂ S-Ex (pass₂ S-Λ S-Ex)

      S-K : S • K ≈ K • S
      S-K = pass₂ S-Ex↑ (pass₂ S-B S-Ex↑)

      S-Ka : ∀ a → S • Ka a ≈ Ka a • S
      S-Ka true  = S-K
      S-Ka false = pass₂ S-X (pass₂ S-K S-X)

      S-H : S • HG ≈ HG • S
      S-H = pass₂ S-PP (pass₂ S-B S-PP)

      module CS = Carry {N} S S²
      module TS = Conj {N} S S²

      S-Hc : ∀ t → TS.⟪ Hc (swB i t) ⟫ ≈ Hc t
      S-Hc t = trans (TS.⟪⟫-•₃ (swapAt-negsB (suc (suc (suc i))) (true ∷ true ∷ true ∷ swB i t))
                               (TS.⟪⟫-fix S-H)
                               (swapAt-negsB (suc (suc (suc i))) (true ∷ true ∷ true ∷ swB i t)))
                     (≡→≈ (Eq.cong (λ z → col (true ∷ true ∷ true ∷ z) HG) (swB-invol i t)))

    Q : Bool → Bits m → Set
    Q a t = t ≢ replicate m true → Ka a • Hc t ≈ Hc t • Ka a

    all339 : ∀ a t → Q a t
    all339 a = move′ (Q a) (λ r _ → base339 a r)
                     (λ i t q t≢ → Sw.CS.carry i (Sw.TS.⟪⟫-fix i (Sw.S-Ka i a)) (Sw.S-Hc i t)
                                     (q (λ e → t≢ (swB-1 i t e))))
                     (λ ne → ⊥-elim (ne Eq.refl))

    --------------------------------------------------------------------
    -- D passes K and Bt

    Ka-D : ∀ a → Ka a • D ≈ D • Ka a
    Ka-D a = via (cong CH₂-∏ (sym Hc1))
                 (pass-last m Hc (all339 a) (trans (cong Hc1 Hc1) HG²))

    Bt-D : Bt • D ≈ D • Bt
    Bt-D = Ka-D false

    H-CD : HG ≈ CH₂ • D
    H-CD = sym (trans (sym assoc) (trans (front _ CH₂²) left-unit))

    --------------------------------------------------------------------
    -- (340) at the canonical position: CH₂ passes HG, factor by factor,
    -- each factor being HG in a colouring of the wires 3 …, and two
    -- colourings of one box commuting by (335)

    module C₀₁ = Carry {N} Ex Ex²
    module CP  = Carry {N} (PP ↓) eq111

    HG-Hc : ∀ t → HG • Hc t ≈ Hc t • HG
    HG-Hc t = both refl (sym (Hc-form t))
                (CP.carry refl refl (C₀₁.carry refl refl (eq335 k below (true ∷ true ∷ true ∷ t))))

  HG-CH₂ : HG • CH₂ ≈ CH₂ • HG
  HG-CH₂ = trans (back _ CH₂-∏) (trans (pass-∏ (allBits m) Hc HG-Hc) (front _ (sym CH₂-∏)))

  -- (339) at the canonical position of this module: the H gate HG in a
  -- colouring of the wires 3 … that is not all black, against K,
  -- negated on wire 0 or not.
  Hcol : Bits m → Circuit N
  Hcol = Hc

  Kcol : Bool → Circuit N
  Kcol = Ka

  eq339c : ∀ a t → t ≢ replicate m true → Kcol a • Hcol t ≈ Hcol t • Kcol a
  eq339c = all339

  private
    D-CH₂ : D • CH₂ ≈ CH₂ • D
    D-CH₂ = trans assoc (back _ HG-CH₂)

    D² : D • D ≈ ε
    D² = begin
      (CH₂ • HG) • (CH₂ • HG)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      CH₂ • (HG • CH₂) • HG       ≈⟨ back _ (front _ HG-CH₂) ⟩
      CH₂ • (CH₂ • HG) • HG       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
      (CH₂ • CH₂) • (HG • HG)     ≈⟨ trans (cong CH₂² HG²) left-unit ⟩
      ε ∎

    XZ-K : ΛXZ (₄₊ k) ≈ K • CH₂ • K • CH₂
    XZ-K = trans (sym (S-XZ k below)) (S₁₂.⟪⟫-•₄ refl refl refl refl)

  --------------------------------------------------------------------
  -- (333) and (334) at the canonical position: the rotations as words
  -- in the H gate HG and the box K on wire 2.  HG = CH₂ D, D passes K
  -- and CH₂ and is an involution, so D cancels from ΛZX = CH₂ K CH₂ K.

  eq333 : HG • K • HG • K ≈ ΛZX (₄₊ k)
  eq333 = begin
    HG • K • HG • K
      ≈⟨ cong H-CD (back _ (front _ H-CD)) ⟩
    (CH₂ • D) • K • (CH₂ • D) • K
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    CH₂ • (D • K) • CH₂ • D • K
      ≈⟨ back _ (front _ (sym (Ka-D true))) ⟩
    CH₂ • (K • D) • CH₂ • D • K
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    CH₂ • K • (D • CH₂) • D • K
      ≈⟨ back _ (back _ (front _ D-CH₂)) ⟩
    CH₂ • K • (CH₂ • D) • D • K
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    CH₂ • K • CH₂ • (D • D) • K
      ≈⟨ back _ (back _ (back _ (trans (front _ D²) left-unit))) ⟩
    CH₂ • K • CH₂ • K
      ≈⟨ sym ZX-K ⟩
    ΛZX (₄₊ k) ∎

  eq334 : K • HG • K • HG ≈ ΛXZ (₄₊ k)
  eq334 = begin
    K • HG • K • HG
      ≈⟨ back _ (cong H-CD (back _ H-CD)) ⟩
    K • (CH₂ • D) • K • (CH₂ • D)
      ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    K • CH₂ • (D • K) • CH₂ • D
      ≈⟨ back _ (back _ (front _ (sym (Ka-D true)))) ⟩
    K • CH₂ • (K • D) • CH₂ • D
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    K • CH₂ • K • (D • CH₂) • D
      ≈⟨ back _ (back _ (back _ (front _ D-CH₂))) ⟩
    K • CH₂ • K • (CH₂ • D) • D
      ≈⟨ back _ (back _ (back _ (trans assoc (back _ D²)))) ⟩
    K • CH₂ • K • CH₂ • ε
      ≈⟨ back _ (back _ (back _ right-unit)) ⟩
    K • CH₂ • K • CH₂
      ≈⟨ sym XZ-K ⟩
    ΛXZ (₄₊ k) ∎

  --------------------------------------------------------------------
  -- Rule (40), canonical

  eq40c : HG • Bt ≈ ΛZX (₄₊ k) • Bt • HG
  eq40c = sym (begin
    ΛZX (₄₊ k) • Bt • HG
      ≈⟨ cong ZX-K (back _ H-CD) ⟩
    (CH₂ • K • CH₂ • K) • Bt • (CH₂ • D)
      ≈⟨ by-passoc ((□ • □ • □ • □) • □ • (□ • □)) (□ • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
    CH₂ • K • CH₂ • (K • Bt) • CH₂ • D
      ≈⟨ back _ (back _ (back _ (front _ merge₀))) ⟩
    CH₂ • K • CH₂ • B₂ • CH₂ • D
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (front _ B₂-CH₂)))) ⟩
    CH₂ • K • CH₂ • (CH₂ • B₂) • D
      ≈⟨ back _ (back _ (trans (sym assoc) (front _ (trans (sym assoc) (trans (front _ CH₂²) left-unit))))) ⟩
    CH₂ • K • B₂ • D
      ≈⟨ back _ (back _ (front _ (sym merge₀))) ⟩
    CH₂ • K • (K • Bt) • D
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (trans (sym assoc) (trans (front _ K²) left-unit))) refl)) ⟩
    CH₂ • Bt • D
      ≈⟨ back _ Bt-D ⟩
    CH₂ • D • Bt
      ≈⟨ trans (sym assoc) (front _ (sym H-CD)) ⟩
    HG • Bt ∎)

  --------------------------------------------------------------------
  -- In the spelling of the decoding

  -- X on the wires 0 and 2 around K: X on the box wire passes the box.
  Btd : Circuit N
  Btd = (X • X ↑ ↑) • K • (X • X ↑ ↑)

  Btd-Bt : Btd ≈ Bt
  Btd-Bt = begin
    (X • X ↑ ↑) • K • (X • X ↑ ↑)     ≈⟨ back _ (back _ (X-↑ (X ↑))) ⟩
    (X • X ↑ ↑) • K • (X ↑ ↑ • X)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X • (X ↑ ↑ • K • X ↑ ↑) • X       ≈⟨ mid _ _ X₂K ⟩
    Bt ∎
    where
    S01X0 : S₀₁.⟪ X ⟫ ≈ X ↑
    S01X0 = X-step 0 (s≤s z≤n)
    S12X1 : S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
    S12X1 = X-step 1 (s≤s (s≤s z≤n))
    XΛX : X • Λ • X ≈ Λ
    XΛX = trans (sym assoc) (trans (front _ (Canon.x-box canon)) (trans assoc (trans (back _ X²) right-unit)))
    X₂K : X ↑ ↑ • K • X ↑ ↑ ≈ K
    X₂K = trans (sym (S₁₂.⟪⟫-•₃ S12X1 refl S12X1))
                (S₁₂.⟪⟫-cong (trans (sym (S₀₁.⟪⟫-•₃ S01X0 refl S01X0)) (S₀₁.⟪⟫-cong XΛX)))

  -- The core of the decoded rule (40): the H gate as the decoding spells
  -- it (ΛH under the swap of the wires 0 1), and Btd.
  core40 : (Ex ↓ • ΛH (₃₊ k) • Ex ↓) • Btd ≈ ΛZX (₄₊ k) • Btd • (Ex ↓ • ΛH (₃₊ k) • Ex ↓)
  core40 = trans (cong S-ΛH Btd-Bt) (trans eq40c (sym (back _ (cong Btd-Bt S-ΛH))))
    where open XY k below using (S-ΛH)
