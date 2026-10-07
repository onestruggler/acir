------------------------------------------------------------------------
-- Presentations of groups
--
-- The two controlled circuits of level 3
--
-- A circuit of level 2 times x₀ (Phase.Control at κ x₀ = x₀): ω, Z, S
-- go to Z, CZ and SC on wire 0 and the wire of the gate (ctrl*); and a
-- circuit of level 1 times (x₀ choose 2) (κ = binom2): ω, Z go to S and
-- CS (ctrl₂*).  The images of the rules with phases are the rules of
-- CZ, CS and SC: their placements (Phase.Two), rules (30), (35), (37),
-- (42), CZ and CS past X (Phase.Cube.Trans), and CCZ for the image of CZ
-- (Phase.Cube.CCZ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Ctrl
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Empty using (⊥ ; ⊥-elim-irr)
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (s≤s)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; binom2 ; half ; Labels ; big⇒odd ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv using (module Pow)
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime lv
  using (DiagC ; DiagC-≡ ; DiagC-conj ; SWAP-at)
  renaming (Z-diag to Z-sem ; S-diag to S-sem)
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Derived p-2 p-prime lv
  using (module Quadratic ; module Cubic)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Two p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Control p-2 p-prime lv h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates p-2 p-prime lv h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Mono p-2 p-prime lv h gt3 using (Diag₃-order)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Trans p-2 p-prime lv h gt3
  using (CS-X₀ ; CS-X₁ ; SC-X₁ ; cx∥↑)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.CCZ p-2 p-prime lv h gt3
  using (W-M ; W-CX)

private
  variable
    n : ℕ

  h₂ : 2 ≤ lv
  h₂ = quad₃ h

  h₁ : 1 ≤ lv
  h₁ = lin₃ h

  odd : 1 ≤ p-2
  odd = big⇒odd gt3

  no3₂ : 3 ≤ 2 → ⊥
  no3₂ (s≤s (s≤s ()))

  no3₁ : 3 ≤ 1 → ⊥
  no3₁ (s≤s ())

  no2₁ : 2 ≤ 1 → ⊥
  no2₁ (s≤s ())

------------------------------------------------------------------------
-- CZ, CS and SC as two-wire codes

cCZ : Two
cCZ = t0 (o1 (S-gate h₂) ^¹ toℕ (- 1F)) ⊙² t1 (o1 (S-gate h₂) ^¹ toℕ (- 1F)) ⊙² (t2 CX-gate ^² toℕ (- 1F))
      ⊙² t0 (o1 (S-gate h₂)) ⊙² t2 CX-gate

cCS : Two
cCS = t2 CX-gate ⊙² t0 (o1 (T-gate h) ^¹ toℕ (- half)) ⊙² (t2 CX-gate ^² toℕ (- 1F)) ⊙² (t2 CX-gate ^² toℕ (- 1F))
      ⊙² t0 (o1 (T-gate h) ^¹ toℕ half) ⊙² t2 CX-gate ⊙² t1 (o1 (S-gate h₂) ^¹ toℕ (- 1F))
      ⊙² t1 (o1 (T-gate h) ^¹ toℕ (- 1F)) ⊙² t1 (o1 (Z-gate h₁) ^¹ toℕ (- half)) ⊙² (cCZ ^² toℕ half)

cSC : Two
cSC = t2 SWAP-gate ⊙² cCS ⊙² t2 SWAP-gate

------------------------------------------------------------------------
-- Swaps

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  -- A gate on wire 1 conjugated by SWAP is the gate on wire 0, and back.
  sw-down : (g : Gate 1) → (₂₊ n) ⊢ SWAP • [ gate₁ g ↥ ]ʷ • SWAP ≈ [ gate₁ g ]ʷ
  sw-down g = trans (back _ (sym (swap-gate₁ g))) (cancel-in ss _)

  sw-up : (g : Gate 1) → (₂₊ n) ⊢ SWAP • [ gate₁ g ]ʷ • SWAP ≈ [ gate₁ g ↥ ]ʷ
  sw-up g = trans (trans (sym assoc) (front _ (swap-gate₁ g))) (trans assoc (cancel-at ss _))

  -- SWAP conjugation distributes.
  sw-• : (a b : Circuit (₂₊ n)) → (₂₊ n) ⊢ SWAP • (a • b) • SWAP ≈ (SWAP • a • SWAP) • SWAP • b • SWAP
  sw-• a b = begin
    SWAP • (a • b) • SWAP              ≈⟨ back _ (trans assoc (back _ (sym (cancel-in ss _)))) ⟩
    SWAP • a • SWAP • SWAP • b • SWAP  ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
    (SWAP • a • SWAP) • SWAP • b • SWAP ∎

  sw-^ : (a : Circuit (₂₊ n)) (m : ℕ) → (₂₊ n) ⊢ SWAP • a ^ m • SWAP ≈ (SWAP • a • SWAP) ^ m
  sw-^ a m = sym (conj-pow ss ss m)

module _ {n : ℕ} where

  open Width (₃₊ n)

  -- A two-wire word passes SWAP ↑ into its placement by SWAP.
  place-sw : (c : Two) → (₃₊ n) ⊢ ⟦ c ⟧² • SWAP ↑ ≈ SWAP ↑ • SWAP • ⟦ c ⟧² ↑ • SWAP
  place-sw c = begin
    ⟦ c ⟧² • SWAP ↑                     ≈⟨ sym (cancel-in (lift (ax swap-order)) _) ⟩
    SWAP ↑ • SWAP ↑ • ⟦ c ⟧² • SWAP ↑   ≈⟨ back _ (two-place c) ⟩
    SWAP ↑ • SWAP • ⟦ c ⟧² ↑ • SWAP     ∎

------------------------------------------------------------------------
-- The phases

private
  sw01 : Labels (₂₊ n) → Labels (₂₊ n)
  sw01 (a ∷ b ∷ x) = b ∷ a ∷ x

  SWAP-at′ : (x : Labels (₂₊ n)) → ⟦ SWAP ⟧ x ≡ (sw01 x , 0F)
  SWAP-at′ (a ∷ b ∷ x) = SWAP-at a b x

  sw01-inv : (x : Labels (₂₊ n)) → sw01 (sw01 x) ≡ x
  sw01-inv (a ∷ b ∷ x) = Eq.refl

  CZ-sem : DiagC {₂₊ n} (CZ h₂) (λ y → head y * head (tail y))
  CZ-sem = Quadratic.CZ-diag odd h₂

  CS-sem : DiagC {₂₊ n} (CS h) (λ y → binom2 (head y) * head (tail y))
  CS-sem = DiagC-≡ (Cubic.CS-diag gt3 h) (λ y → FR.*-comm _ _)

  SC-sem : DiagC {₂₊ n} SC (λ y → head y * binom2 (head (tail y)))
  SC-sem = DiagC-≡ (DiagC-conj SWAP-at′ sw01-inv (Cubic.CS-diag gt3 h)) λ { (a ∷ b ∷ x) → Eq.refl }

------------------------------------------------------------------------
-- x₀ times a circuit of level 2

private
  module _ {n : ℕ} where

    open Width (₂₊ n)

    CZ-X₁ : (₂₊ n) ⊢ CZ h₂ • X ↑ ≈ Z h₁ • X ↑ • CZ h₂
    CZ-X₁ = begin
      CZ h₂ • X ↑
        ≈⟨ cong (sym CZ≈) (sym (sw-up X-gate)) ⟩
      (SWAP • CZ h₂ • SWAP) • SWAP • X • SWAP
        ≈⟨ sym (sw-• (CZ h₂) X) ⟩
      SWAP • (CZ h₂ • X) • SWAP
        ≈⟨ back _ (front _ CZ-X) ⟩
      SWAP • (X • CZ h₂ • Z h₁ ↑) • SWAP
        ≈⟨ trans (sw-• X _) (cong (sw-up X-gate) (trans (sw-• (CZ h₂) _) (cong CZ≈ (sw-down (Z-gate h₁))))) ⟩
      X ↑ • CZ h₂ • Z h₁
        ≈⟨ back _ (sym (Z∥CZ)) ⟩
      X ↑ • Z h₁ • CZ h₂
        ≈⟨ trans (sym assoc) (trans (front _ (comm-gate₁-w↑ (Z-gate h₁) X)) assoc) ⟩
      Z h₁ • X ↑ • CZ h₂ ∎
      where
      CZ≈ : (₂₊ n) ⊢ SWAP • CZ h₂ • SWAP ≈ CZ h₂
      CZ≈ = trans (trans (sym assoc) (front _ CZ-sym)) (trans assoc (cancel-at (ax swap-order) _))

    SC-M₁ : (x : F*) → (₂₊ n) ⊢ SC • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • CZ h₂ ^ toℕ (binom2 (proj₁ x)) • SC ^ toℕ (proj₁ x * proj₁ x)
    SC-M₁ x = begin
      (SWAP • CS h • SWAP) • M⟨ x ⟩ ↑
        ≈⟨ trans assoc (back _ (trans assoc (back _ (sym (ax (swap-M (proj₁ x) (proj₂ x))))))) ⟩
      SWAP • CS h • M⟨ x ⟩ • SWAP
        ≈⟨ back _ (trans (sym assoc) (front _ (sym (ax (ax35 h x))))) ⟩
      SWAP • (M⟨ x ⟩ • CZ h₂ ^ᶠ binom2 (proj₁ x) • CS h ^ᶠ (proj₁ x * proj₁ x)) • SWAP
        ≈⟨ trans (sw-• _ _) (cong (sw-up (M-gate (proj₁ x) (proj₂ x))) (sw-• _ _)) ⟩
      M⟨ x ⟩ ↑ • (SWAP • CZ h₂ ^ᶠ binom2 (proj₁ x) • SWAP) • SWAP • CS h ^ᶠ (proj₁ x * proj₁ x) • SWAP
        ≈⟨ back _ (cong (trans (sw-^ _ _) (Pow.pow-cong (₂₊ n) _ CZ≈)) (sw-^ _ _)) ⟩
      M⟨ x ⟩ ↑ • CZ h₂ ^ toℕ (binom2 (proj₁ x)) • SC ^ toℕ (proj₁ x * proj₁ x) ∎
      where
      CZ≈ : (₂₊ n) ⊢ SWAP • CZ h₂ • SWAP ≈ CZ h₂
      CZ≈ = trans (trans (sym assoc) (front _ CZ-sym)) (trans assoc (cancel-at (ax swap-order) _))

  module _ {n : ℕ} where

    open Width (₃₊ n)

    CZ-CX₁ : (₃₊ n) ⊢ CX ↑ • CZ h₂ • SWAP • CZ h₂ ↑ • SWAP ≈ CZ h₂ • CX ↑
    CZ-CX₁ = trans (back _ (back _ (sym (two-place cCZ)))) (sym (ax (ax30 h₂)))

    SC-CX₁ : (₃₊ n) ⊢ CX ↑ • SWAP • SC ↑ • SWAP ≈ (SWAP • SC ↑ • SWAP) • CX ↑
    SC-CX₁ = ∥-≈ˡ (sym (trans (sym assoc) (trans (front _ (two-σ (t2 CX-gate))) (trans assoc (cancel-at σσ⁻ _)))))
               (∥-≈ʳ (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl)
                 (conj∥ σ⁻σ (cx∥↑ Diag₃-CS)))

module C1 = Functor 2 no3₂ (λ a → a) (Z h₁) (CZ h₂) (λ _ → SC)
  (Diag₃-2 Diag-Z) (Diag₃-2 Diag-CZ) (λ _ → Diag₃-SC)
  (one∥ (o1 (Z-gate h₁))) (two∥ cCZ) (λ _ → two∥ cSC)
  (sw-down (Z-gate h₁)) (place-sw cCZ) (λ _ → place-sw cSC)
  Z-order CZ-order CZ-CX₁ CZ-M₁ CZ-X₁
  (λ _ → Diag₃-order Diag₃-SC) (λ _ → SC-X₁) (λ _ → SC-M₁) (λ _ → SC-CX₁)
  (λ _ → W-M) (λ _ → W-CX)
  (Z-sem h₁) CZ-sem (λ _ → SC-sem)

------------------------------------------------------------------------
-- (x₀ choose 2) times a circuit of level 1

private
  module _ {n : ℕ} where

    open Width (₃₊ n)

    CS-CX₁ : (₃₊ n) ⊢ CX ↑ • CS h • SWAP • CS h ↑ • SWAP ≈ CS h • CX ↑
    CS-CX₁ = trans (back _ (back _ (sym (two-place cCS)))) (ax (ax42 h))

module C2 = Functor 1 no3₁ binom2 (S h₂) (CS h) (λ _ → ε)
  (Diag₃-2 Diag-S) Diag₃-CS (λ h' → ⊥-elim-irr (no2₁ h'))
  (one∥ (o1 (S-gate h₂))) (two∥ cCS) (λ h' → ⊥-elim-irr (no2₁ h'))
  (sw-down (S-gate h₂)) (place-sw cCS) (λ h' → ⊥-elim-irr (no2₁ h'))
  S-order (Diag₃-order Diag₃-CS) CS-CX₁ (λ x → Width.sym (ax (ax37 h x))) CS-X₁
  (λ h' → ⊥-elim-irr (no2₁ h')) (λ h' → ⊥-elim-irr (no2₁ h')) (λ h' → ⊥-elim-irr (no2₁ h'))
  (λ h' → ⊥-elim-irr (no2₁ h')) (λ h' → ⊥-elim-irr (no2₁ h')) (λ h' → ⊥-elim-irr (no2₁ h'))
  (S-sem h₂) CS-sem (λ h' → ⊥-elim-irr (no2₁ h'))
