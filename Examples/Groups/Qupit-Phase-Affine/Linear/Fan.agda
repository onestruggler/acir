------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: identities of the fan-in R and the fan-out
-- col
--
-- * Labels add (R-add, col-add), and the zero vectors are empty
--   (R-zero, col-zero).
-- * A generator y on the upper wires passes either one, acting on its
--   vector (R-push, col-push): one wire up by induction, and at the
--   bottom of the upper wires by the three-wire calculus, after
--   writing the fan with its first two additions in front of the rest
--   (R-split, col-split).
-- * CX on wires 0, 1 past the fan-in one wire up leaves a fan-in on
--   wire 0 behind (R-up-CX): the Steinberg relation, by induction.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Fan
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; _⁻¹ᶠ ; _⁻¹* ; ⁻¹ᶠ-inverseˡ ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Two p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linear words as circuits

⌊↑ₗ⌋ : (L : Word (LGen n)) → ⌊ L ↑ₗ ⌋ ≡ ⌊ L ⌋ ↑
⌊↑ₗ⌋ [ y ]ʷ   = Eq.refl
⌊↑ₗ⌋ ε        = Eq.refl
⌊↑ₗ⌋ (w • v)  = Eq.cong₂ _•_ (⌊↑ₗ⌋ w) (⌊↑ₗ⌋ v)

⌊^⌋ : (L : Word (LGen n)) (k : ℕ) → ⌊ L ^ k ⌋ ≡ ⌊ L ⌋ ^ k
⌊^⌋ L zero          = Eq.refl
⌊^⌋ L (suc zero)    = Eq.refl
⌊^⌋ L (suc (suc k)) = Eq.cong (⌊ L ⌋ •_) (⌊^⌋ L (suc k))

⌊Rʷ⌋ : (w : Vec F n) → ⌊ Rʷ w ⌋ ≡ R w
⌊Rʷ⌋ []      = Eq.refl
⌊Rʷ⌋ (c ∷ w) =
  Eq.cong₂ (λ a b → (SWAP • a • SWAP) • b)
    (Eq.trans (⌊↑ₗ⌋ (Rʷ w)) (Eq.cong _↑ (⌊Rʷ⌋ w))) (⌊^⌋ [ cx ]ʷ (toℕ c))

-- The zero vector.
0ᵛ : Vec F n
0ᵛ {zero}  = []
0ᵛ {suc n} = 0F ∷ 0ᵛ

------------------------------------------------------------------------
-- Generic helpers

module _ {m : ℕ} where

  open Width m

  -- A word passing a product from the right, in two slides.
  pass : {h g a b c : Circuit m} → h • b ≈ c • h → g • a ≈ b • g → (h • g) • a ≈ c • h • g
  pass e₁ e₂ = slide∘ e₂ e₁

  -- An involution conjugating a product conjugates each factor.
  split-conj : {g a b : Circuit m} → g • g ≈ ε → g • (a • b) • g ≈ (g • a • g) • (g • b • g)
  split-conj {g} {a} {b} gg = sym (begin
    (g • a • g) • (g • b • g)    ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • □ • □ • □ • □) Eq.refl ⟩
    g • a • g • g • b • g        ≈⟨ back g (back a (cancel-in gg (b • g))) ⟩
    g • a • b • g                ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    g • (a • b) • g              ∎)

  -- The conjugate of an iterate by an involution that slides.
  conjᶠ : {g a b : Circuit m} → g • g ≈ ε → g • a ≈ b • g → (k : F) → g • a ^ᶠ k • g ≈ b ^ᶠ k
  conjᶠ gg e k = Involution.conj← gg (slideᶠ k e)

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  -- Conjugating by SWAP something one wire up: it misses the
  -- multipliers on wire 1 and anything two wires up.
  conj-M↑ : (W : Circuit (₁₊ n)) (x : F*) →
            (₂₊ n) ⊢ (SWAP • W ↑ • SWAP) • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • SWAP • W ↑ • SWAP
  conj-M↑ W x = pass (sM x) (pass (comm-gate₁-w↑ (M-gate (proj₁ x) (proj₂ x)) W) (sM↑ x))

  conj-up : (W W' : Circuit (₁₊ n)) (Y : Circuit n) → (₁₊ n) ⊢ W • Y ↑ ≈ Y ↑ • W' →
            (₂₊ n) ⊢ (SWAP • W ↑ • SWAP) • Y ↑ ↑ ≈ Y ↑ ↑ • SWAP • W' ↑ • SWAP
  conj-up W W' Y e = begin
    (SWAP • W ↑ • SWAP) • Y ↑ ↑        ≈⟨ trans assoc (back _ (trans assoc (back _ s∥))) ⟩
    SWAP • W ↑ • Y ↑ ↑ • SWAP          ≈⟨ back _ (trans (sym assoc) (trans (front _ (lift e)) assoc)) ⟩
    SWAP • Y ↑ ↑ • W' ↑ • SWAP         ≈⟨ trans (sym assoc) (trans (front _ s∥) assoc) ⟩
    Y ↑ ↑ • SWAP • W' ↑ • SWAP         ∎
    where
    s∥ : (₂₊ n) ⊢ SWAP • Y ↑ ↑ ≈ Y ↑ ↑ • SWAP
    s∥ = sym (comm-gate₂-w↑↑ SWAP-gate Y)

  -- The additions on wires 0, 1 commute with anything two wires up.
  CXᶠ-up : (Y : Circuit n) (c : F) → (₂₊ n) ⊢ CX ^ᶠ c • Y ↑ ↑ ≈ Y ↑ ↑ • CX ^ᶠ c
  CXᶠ-up Y c = Pow.pow-comm (₂₊ n) (toℕ c) (sym (comm-gate₂-w↑↑ CX-gate Y))

  CXʳᶠ-up : (Y : Circuit n) (c : F) → (₂₊ n) ⊢ CXʳ ^ᶠ c • Y ↑ ↑ ≈ Y ↑ ↑ • CXʳ ^ᶠ c
  CXʳᶠ-up Y c = Pow.pow-comm (₂₊ n) (toℕ c) (pass s∥ (pass c∥ s∥))
    where
    s∥ : (₂₊ n) ⊢ SWAP • Y ↑ ↑ ≈ Y ↑ ↑ • SWAP
    s∥ = sym (comm-gate₂-w↑↑ SWAP-gate Y)
    c∥ : (₂₊ n) ⊢ CX • Y ↑ ↑ ≈ Y ↑ ↑ • CX
    c∥ = sym (comm-gate₂-w↑↑ CX-gate Y)

  -- The reversed addition past a multiplier on its target.
  CXʳᶠ-M↑ : (x : F*) (c : F) → (₂₊ n) ⊢ CXʳ ^ᶠ c • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • CXʳ ^ᶠ (c * proj₁ (x ⁻¹*))
  CXʳᶠ-M↑ x c = sym (trans (M↑-CXʳᶠ x (c * proj₁ (x ⁻¹*))) (front _ (OR.^ᶠ-≡ undo)))
    where
    module OR = Pow.Order (₂₊ n) {CXʳ} CXʳ-order
    undo : (c * proj₁ (x ⁻¹*)) * proj₁ x ≡ c
    undo = Eq.trans (FR.*-assoc c _ _)
             (Eq.trans (Eq.cong (c *_) (⁻¹ᶠ-inverseˡ (proj₁ x) (proj₂ x))) (FR.*-identityʳ c))

------------------------------------------------------------------------
-- Labels add, and the zero vectors

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    module OR = Pow.Order (₂₊ n) {CXʳ} CXʳ-order

  R-add : (c d : F) (w : Vec F n) → (₂₊ n) ⊢ R (c ∷ w) • CX ^ᶠ d ≈ R (c + d ∷ w)
  R-add c d w = trans assoc (back _ (CX-+ c d))

  col-add : (c d : F) (v : Vec F n) → (₂₊ n) ⊢ col (c ∷ v) • CXʳ ^ᶠ d ≈ col (c + d ∷ v)
  col-add c d v = trans assoc (back _ (OR.^ᶠ-+ c d))

R-zero : (₁₊ n) ⊢ R (0ᵛ {n}) ≈ ε
R-zero {zero}  = Width.refl
R-zero {suc n} =
  trans right-unit (trans (back _ (front _ (lift R-zero))) (trans (back _ left-unit) (ax swap-order)))
  where open Width (₂₊ n)

col-zero : (₁₊ n) ⊢ col (0ᵛ {n}) ≈ ε
col-zero {zero}  = Width.refl
col-zero {suc n} =
  trans right-unit (trans (back _ (front _ (lift col-zero))) (trans (back _ left-unit) (ax swap-order)))
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- The fans with their first two additions in front

module _ {n : ℕ} where

  open Width (₃₊ n)

  private
    ss : (₃₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  -- Additions one wire up, conjugated by SWAP.
  sw-up-sw : (k : F) → (₃₊ n) ⊢ SWAP • (CX ^ᶠ k) ↑ • SWAP ≈ CX₂₀ ^ᶠ k
  sw-up-sw k = trans (back _ (front _ (refl' (↑ᶠ CX k)))) (conjᶠ ss sCX↑ k)

  sw-upʳ-sw : (k : F) → (₃₊ n) ⊢ SWAP • (CXʳ ^ᶠ k) ↑ • SWAP ≈ CX₀₂ ^ᶠ k
  sw-upʳ-sw k = trans (back _ (front _ (refl' (↑ᶠ CXʳ k)))) (conjᶠ ss sCXʳ↑ k)

  -- x₀ += c x₁ + d x₂ + w · (x₃, …).
  R-split : (c d : F) (w : Vec F n) →
    (₃₊ n) ⊢ R (c ∷ d ∷ w) ≈ (SWAP • SWAP ↑ • R w ↑ ↑ • SWAP ↑ • SWAP) • CX₂₀ ^ᶠ d • CX ^ᶠ c
  R-split c d w = begin
    (SWAP • ((SWAP ↑ • R w ↑ ↑ • SWAP ↑) • (CX ^ᶠ d) ↑) • SWAP) • CX ^ᶠ c
      ≈⟨ front _ (split-conj ss) ⟩
    ((SWAP • (SWAP ↑ • R w ↑ ↑ • SWAP ↑) • SWAP) • (SWAP • (CX ^ᶠ d) ↑ • SWAP)) • CX ^ᶠ c
      ≈⟨ front _ (cong (by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl) (sw-up-sw d)) ⟩
    ((SWAP • SWAP ↑ • R w ↑ ↑ • SWAP ↑ • SWAP) • CX₂₀ ^ᶠ d) • CX ^ᶠ c
      ≈⟨ assoc ⟩
    (SWAP • SWAP ↑ • R w ↑ ↑ • SWAP ↑ • SWAP) • CX₂₀ ^ᶠ d • CX ^ᶠ c ∎

  -- x₁ += c x₀, x₂ += d x₀, (x₃, …) += v x₀.
  col-split : (c d : F) (v : Vec F n) →
    (₃₊ n) ⊢ col (c ∷ d ∷ v) ≈ (SWAP • SWAP ↑ • col v ↑ ↑ • SWAP ↑ • SWAP) • CX₀₂ ^ᶠ d • CXʳ ^ᶠ c
  col-split c d v = begin
    (SWAP • ((SWAP ↑ • col v ↑ ↑ • SWAP ↑) • (CXʳ ^ᶠ d) ↑) • SWAP) • CXʳ ^ᶠ c
      ≈⟨ front _ (split-conj ss) ⟩
    ((SWAP • (SWAP ↑ • col v ↑ ↑ • SWAP ↑) • SWAP) • (SWAP • (CXʳ ^ᶠ d) ↑ • SWAP)) • CXʳ ^ᶠ c
      ≈⟨ front _ (cong (by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl) (sw-upʳ-sw d)) ⟩
    ((SWAP • SWAP ↑ • col v ↑ ↑ • SWAP ↑ • SWAP) • CX₀₂ ^ᶠ d) • CXʳ ^ᶠ c
      ≈⟨ assoc ⟩
    (SWAP • SWAP ↑ • col v ↑ ↑ • SWAP ↑ • SWAP) • CX₀₂ ^ᶠ d • CXʳ ^ᶠ c ∎

  -- The exchange of wires 0 and 2, conjugating something two wires
  -- up, commutes with CX ↑ (whose wires it moves to 1, 2 → 1, 0 → 1, 2).
  Π-CX↑ : (W : Circuit (₁₊ n)) →
          (₃₊ n) ⊢ (SWAP • SWAP ↑ • W ↑ ↑ • SWAP ↑ • SWAP) • CX ↑ ≈ CX ↑ • SWAP • SWAP ↑ • W ↑ ↑ • SWAP ↑ • SWAP
  Π-CX↑ W = pass sCX₂₀ (pass tCX (pass (sym (cW W)) (pass tCX₂₀ sCX↑)))

  -- SWAP ↑ conjugating something two wires up commutes with CX₂₀.
  tWt-CX₂₀ : (W : Circuit (₁₊ n)) (k : F) →
             (₃₊ n) ⊢ (SWAP ↑ • W ↑ ↑ • SWAP ↑) • CX₂₀ ^ᶠ k ≈ CX₂₀ ^ᶠ k • SWAP ↑ • W ↑ ↑ • SWAP ↑
  tWt-CX₂₀ W k =
    pass (slideᶠ k tCX) (pass (sym (Pow.pow-comm (₃₊ n) (toℕ k) (cW W))) (slideᶠ k tCX₂₀))

------------------------------------------------------------------------
-- CX past the fan-in one wire up

R-up-CX : (w : Vec F n) (c : F) → (₂₊ n) ⊢ R w ↑ • CX ^ᶠ c ≈ CX ^ᶠ c • R₀ (negs c w) • R w ↑
R-up-CX {n} [] c = begin
  ε • CX ^ᶠ c                          ≈⟨ left-unit ⟩
  CX ^ᶠ c                              ≈⟨ sym right-unit ⟩
  CX ^ᶠ c • ε                          ≈⟨ back _ (sym (trans right-unit (trans (back _ left-unit) (ax swap-order)))) ⟩
  CX ^ᶠ c • (SWAP • ε • SWAP) • ε      ∎
  where open Width (₂₊ n)
R-up-CX {suc n} (e ∷ w) c = begin
  ((SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ e) ↑) • CX ^ᶠ c
    ≈⟨ assoc ⟩
  (SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ e) ↑ • CX ^ᶠ c
    ≈⟨ back _ (st-up c e) ⟩
  (SWAP ↑ • Q • SWAP ↑) • CX ^ᶠ c • CX₂₀ ^ᶠ k • (CX ^ᶠ e) ↑
    ≈⟨ trans (sym assoc) (front _ tQt-CX) ⟩
  (CX ^ᶠ c • SWAP ↑ • Y • Q • SWAP ↑) • CX₂₀ ^ᶠ k • (CX ^ᶠ e) ↑
    ≈⟨ by-passoc ((□ • □ • □ • □ • □) • □ • □) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
  CX ^ᶠ c • (SWAP ↑ • Y • Q • SWAP ↑ • CX₂₀ ^ᶠ k) • (CX ^ᶠ e) ↑
    ≈⟨ back _ (front _ middle) ⟩
  CX ^ᶠ c • (Y • CX₂₀ ^ᶠ k • SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ e) ↑
    ≈⟨ back _ (by-passoc ((□ • □ • □ • □ • □) • □) ((□ • □) • (□ • □ • □) • □) Eq.refl) ⟩
  CX ^ᶠ c • (Y • CX₂₀ ^ᶠ k) • (SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ e) ↑
    ≈⟨ back _ (front _ (sym R₀-cons)) ⟩
  CX ^ᶠ c • R₀ (k ∷ u) • (SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ e) ↑ ∎
  where
  open Width (₃₊ n)
  Q : Circuit (₃₊ n)
  Q = R w ↑ ↑
  k : F
  k = - (c * e)
  u : Vec F n
  u = negs c w
  Y : Circuit (₃₊ n)
  Y = SWAP • SWAP ↑ • R u ↑ ↑ • SWAP ↑ • SWAP

  ss : (₃₊ n) ⊢ SWAP • SWAP ≈ ε
  ss = ax swap-order

  -- R₀ (k ∷ u) = Y • CX₂₀ ^ᶠ k.
  R₀-cons : (₃₊ n) ⊢ R₀ (k ∷ u) ≈ Y • CX₂₀ ^ᶠ k
  R₀-cons = begin
    SWAP • ((SWAP ↑ • R u ↑ ↑ • SWAP ↑) • (CX ^ᶠ k) ↑) • SWAP
      ≈⟨ split-conj ss ⟩
    (SWAP • (SWAP ↑ • R u ↑ ↑ • SWAP ↑) • SWAP) • (SWAP • (CX ^ᶠ k) ↑ • SWAP)
      ≈⟨ cong (by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl) (sw-up-sw k) ⟩
    Y • CX₂₀ ^ᶠ k ∎

  -- Q past CX₂₀, by the step one wire down.
  Q-CX₂₀ : (₃₊ n) ⊢ Q • CX₂₀ ^ᶠ c ≈ CX₂₀ ^ᶠ c • Y • Q
  Q-CX₂₀ = begin
    Q • CX₂₀ ^ᶠ c
      ≈⟨ back _ (sym (sw-up-sw c)) ⟩
    Q • SWAP • (CX ^ᶠ c) ↑ • SWAP
      ≈⟨ trans (sym assoc) (front _ (sym (sW (R w)))) ⟩
    (SWAP • Q) • (CX ^ᶠ c) ↑ • SWAP
      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (lift (R-up-CX w c))))) ⟩
    SWAP • ((CX ^ᶠ c) ↑ • R₀ u ↑ • Q) • SWAP
      ≈⟨ back _ (trans assoc (back _ (trans assoc (back _ (sym (sW (R w))))))) ⟩
    SWAP • (CX ^ᶠ c) ↑ • R₀ u ↑ • SWAP • Q
      ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • □ • □ • □ • □) Eq.refl ⟩
    SWAP • (CX ^ᶠ c) ↑ • R₀ u ↑ • SWAP • Q
      ≈⟨ back _ (back _ (sym (cancel-in ss _))) ⟩
    SWAP • (CX ^ᶠ c) ↑ • SWAP • SWAP • R₀ u ↑ • SWAP • Q
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □) • □) Eq.refl ⟩
    (SWAP • (CX ^ᶠ c) ↑ • SWAP) • (SWAP • R₀ u ↑ • SWAP) • Q
      ≈⟨ cong (sw-up-sw c) (front _ (by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl)) ⟩
    CX₂₀ ^ᶠ c • Y • Q ∎

  tQt-CX : (₃₊ n) ⊢ (SWAP ↑ • Q • SWAP ↑) • CX ^ᶠ c ≈ CX ^ᶠ c • SWAP ↑ • Y • Q • SWAP ↑
  tQt-CX = begin
    (SWAP ↑ • Q • SWAP ↑) • CX ^ᶠ c
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    SWAP ↑ • Q • SWAP ↑ • CX ^ᶠ c
      ≈⟨ back _ (back _ (slideᶠ c tCX)) ⟩
    SWAP ↑ • Q • CX₂₀ ^ᶠ c • SWAP ↑
      ≈⟨ back _ (trans (sym assoc) (front _ Q-CX₂₀)) ⟩
    SWAP ↑ • (CX₂₀ ^ᶠ c • Y • Q) • SWAP ↑
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (SWAP ↑ • CX₂₀ ^ᶠ c) • Y • Q • SWAP ↑
      ≈⟨ front _ (slideᶠ c tCX₂₀) ⟩
    (CX ^ᶠ c • SWAP ↑) • Y • Q • SWAP ↑
      ≈⟨ assoc ⟩
    CX ^ᶠ c • SWAP ↑ • Y • Q • SWAP ↑ ∎

  middle : (₃₊ n) ⊢ SWAP ↑ • Y • Q • SWAP ↑ • CX₂₀ ^ᶠ k ≈ Y • CX₂₀ ^ᶠ k • SWAP ↑ • Q • SWAP ↑
  middle = begin
    SWAP ↑ • Y • Q • SWAP ↑ • CX₂₀ ^ᶠ k
      ≈⟨ trans (sym assoc) (front _ (Π-comm (R u))) ⟩
    (Y • SWAP ↑) • Q • SWAP ↑ • CX₂₀ ^ᶠ k
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Y • (SWAP ↑ • Q • SWAP ↑) • CX₂₀ ^ᶠ k
      ≈⟨ back _ (tWt-CX₂₀ (R w) k) ⟩
    Y • CX₂₀ ^ᶠ k • SWAP ↑ • Q • SWAP ↑ ∎

------------------------------------------------------------------------
-- A generator on the upper wires past the fans

R-push : (w : Vec F n) (y : LGen n) → (₁₊ n) ⊢ R w • ⌊ [ y ]ʷ ⌋ ↑ ≈ ⌊ [ y ]ʷ ⌋ ↑ • R (w ⋆ᴿ y)
R-push {suc n} (c ∷ w) (y ↥ₗ) = begin
  ((SWAP • R w ↑ • SWAP) • CX ^ᶠ c) • Y ↑ ↑
    ≈⟨ trans assoc (trans (back _ (CXᶠ-up Y c)) (sym assoc)) ⟩
  ((SWAP • R w ↑ • SWAP) • Y ↑ ↑) • CX ^ᶠ c
    ≈⟨ front _ (conj-up (R w) _ Y (R-push w y)) ⟩
  (Y ↑ ↑ • SWAP • R (w ⋆ᴿ y) ↑ • SWAP) • CX ^ᶠ c
    ≈⟨ assoc ⟩
  Y ↑ ↑ • (SWAP • R (w ⋆ᴿ y) ↑ • SWAP) • CX ^ᶠ c ∎
  where
  open Width (₂₊ n)
  Y = ⌊ [ y ]ʷ ⌋
R-push {suc n} (c ∷ w) (mul x) = begin
  ((SWAP • R w ↑ • SWAP) • CX ^ᶠ c) • M⟨ x ⟩ ↑
    ≈⟨ trans assoc (back _ (CXᶠ-M↑ x c)) ⟩
  (SWAP • R w ↑ • SWAP) • M⟨ x ⟩ ↑ • CX ^ᶠ (c * proj₁ x)
    ≈⟨ trans (sym assoc) (trans (front _ (conj-M↑ (R w) x)) assoc) ⟩
  M⟨ x ⟩ ↑ • (SWAP • R w ↑ • SWAP) • CX ^ᶠ (c * proj₁ x) ∎
  where open Width (₂₊ n)
R-push {₂₊ n} (c ∷ d ∷ w) cx = begin
  ((SWAP • A • SWAP) • CX ^ᶠ c) • CX ↑
    ≈⟨ trans assoc (back _ (st-cx c)) ⟩
  (SWAP • A • SWAP) • CX ↑ • CX ^ᶠ c • CX₂₀ ^ᶠ c
    ≈⟨ trans (sym assoc) (trans (front _ A-pass) assoc) ⟩
  CX ↑ • (SWAP • A • SWAP) • CX ^ᶠ c • CX₂₀ ^ᶠ c
    ≈⟨ back _ (back _ (Pow.pow-comm₂ (₃₊ n) (toℕ c) (toℕ c) XX-comm)) ⟩
  CX ↑ • (SWAP • A • SWAP) • CX₂₀ ^ᶠ c • CX ^ᶠ c
    ≈⟨ back _ (trans (sym assoc) (front _ merge)) ⟩
  CX ↑ • (SWAP • A' • SWAP) • CX ^ᶠ c ∎
  where
  open Width (₃₊ n)
  Q = R w ↑ ↑
  A = (SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ d) ↑
  A' = (SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ (d + c)) ↑

  up-CX₂₀ : (k : F) → (₃₊ n) ⊢ (CX ^ᶠ d) ↑ • CX₂₀ ^ᶠ k ≈ CX₂₀ ^ᶠ k • (CX ^ᶠ d) ↑
  up-CX₂₀ k = trans (front _ (refl' (↑ᶠ CX d)))
                (trans (Pow.pow-comm₂ (₃₊ n) (toℕ d) (toℕ k) XX2-comm) (back _ (refl' (Eq.sym (↑ᶠ CX d)))))

  A-CX₂₀ : (₃₊ n) ⊢ A • CX₂₀ ≈ CX₂₀ • A
  A-CX₂₀ = pass (tWt-CX₂₀ (R w) 1F) (up-CX₂₀ 1F)

  A-pass : (₃₊ n) ⊢ (SWAP • A • SWAP) • CX ↑ ≈ CX ↑ • SWAP • A • SWAP
  A-pass = pass sCX₂₀ (pass A-CX₂₀ sCX↑)

  merge : (₃₊ n) ⊢ (SWAP • A • SWAP) • CX₂₀ ^ᶠ c ≈ SWAP • A' • SWAP
  merge = begin
    (SWAP • A • SWAP) • CX₂₀ ^ᶠ c
      ≈⟨ trans assoc (back _ (trans assoc (back _ (slideᶠ c sCX₂₀)))) ⟩
    SWAP • A • (CX ↑) ^ᶠ c • SWAP
      ≈⟨ back _ (trans (sym assoc) (front _ (trans assoc (back _ (back _ (refl' (Eq.sym (↑ᶠ CX c)))))))) ⟩
    SWAP • ((SWAP ↑ • Q • SWAP ↑) • (CX ^ᶠ d) ↑ • (CX ^ᶠ c) ↑) • SWAP
      ≈⟨ back _ (front _ (back _ (lift (CX-+ d c)))) ⟩
    SWAP • A' • SWAP ∎
R-push {₂₊ n} (c ∷ d ∷ w) sw = begin
  R (c ∷ d ∷ w) • SWAP ↑
    ≈⟨ front _ (R-split c d w) ⟩
  (P • CX₂₀ ^ᶠ d • CX ^ᶠ c) • SWAP ↑
    ≈⟨ slideʳ (sym (Π-comm (R w))) (slideʳ (sym (slideᶠ d tCX)) (sym (slideᶠ c tCX₂₀))) ⟩
  SWAP ↑ • P • CX ^ᶠ d • CX₂₀ ^ᶠ c
    ≈⟨ back _ (back _ (Pow.pow-comm₂ (₃₊ n) (toℕ d) (toℕ c) XX-comm)) ⟩
  SWAP ↑ • P • CX₂₀ ^ᶠ c • CX ^ᶠ d
    ≈⟨ back _ (sym (R-split d c w)) ⟩
  SWAP ↑ • R (d ∷ c ∷ w) ∎
  where
  open Width (₃₊ n)
  P = SWAP • SWAP ↑ • R w ↑ ↑ • SWAP ↑ • SWAP

col-push : (v : Vec F n) (y : LGen n) → (₁₊ n) ⊢ col v • ⌊ [ y ]ʷ ⌋ ↑ ≈ ⌊ [ y ]ʷ ⌋ ↑ • col (v ⋆ᶜ y)
col-push {suc n} (c ∷ v) (y ↥ₗ) = begin
  ((SWAP • col v ↑ • SWAP) • CXʳ ^ᶠ c) • Y ↑ ↑
    ≈⟨ trans assoc (trans (back _ (CXʳᶠ-up Y c)) (sym assoc)) ⟩
  ((SWAP • col v ↑ • SWAP) • Y ↑ ↑) • CXʳ ^ᶠ c
    ≈⟨ front _ (conj-up (col v) _ Y (col-push v y)) ⟩
  (Y ↑ ↑ • SWAP • col (v ⋆ᶜ y) ↑ • SWAP) • CXʳ ^ᶠ c
    ≈⟨ assoc ⟩
  Y ↑ ↑ • (SWAP • col (v ⋆ᶜ y) ↑ • SWAP) • CXʳ ^ᶠ c ∎
  where
  open Width (₂₊ n)
  Y = ⌊ [ y ]ʷ ⌋
col-push {suc n} (c ∷ v) (mul x) = begin
  ((SWAP • col v ↑ • SWAP) • CXʳ ^ᶠ c) • M⟨ x ⟩ ↑
    ≈⟨ trans assoc (back _ (CXʳᶠ-M↑ x c)) ⟩
  (SWAP • col v ↑ • SWAP) • M⟨ x ⟩ ↑ • CXʳ ^ᶠ (c * proj₁ (x ⁻¹*))
    ≈⟨ trans (sym assoc) (trans (front _ (conj-M↑ (col v) x)) assoc) ⟩
  M⟨ x ⟩ ↑ • (SWAP • col v ↑ • SWAP) • CXʳ ^ᶠ (c * proj₁ (x ⁻¹*)) ∎
  where open Width (₂₊ n)
col-push {₂₊ n} (c ∷ d ∷ v) cx = begin
  col (c ∷ d ∷ v) • CX ↑
    ≈⟨ front _ (col-split c d v) ⟩
  (P • CX₀₂ ^ᶠ d • CXʳ ^ᶠ c) • CX ↑
    ≈⟨ trans assoc (back _ (trans assoc (back _ (Pow.pow-comm (₃₊ n) (toℕ c) rX)))) ⟩
  P • CX₀₂ ^ᶠ d • CX ↑ • CXʳ ^ᶠ c
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (st-02 d)) assoc)) ⟩
  P • CX ↑ • (CX₀₂ ^ᶠ d • CXʳ ^ᶠ (- d)) • CXʳ ^ᶠ c
    ≈⟨ trans (sym assoc) (trans (front _ (Π-CX↑ (col v))) assoc) ⟩
  CX ↑ • P • (CX₀₂ ^ᶠ d • CXʳ ^ᶠ (- d)) • CXʳ ^ᶠ c
    ≈⟨ back _ (back _ (trans assoc (back _ (OR.^ᶠ-+ (- d) c)))) ⟩
  CX ↑ • P • CX₀₂ ^ᶠ d • CXʳ ^ᶠ (- d + c)
    ≈⟨ back _ (sym (col-split (- d + c) d v)) ⟩
  CX ↑ • col (- d + c ∷ d ∷ v) ∎
  where
  open Width (₃₊ n)
  module OR = Pow.Order (₃₊ n) {CXʳ} CXʳ-order
  P = SWAP • SWAP ↑ • col v ↑ ↑ • SWAP ↑ • SWAP
col-push {₂₊ n} (c ∷ d ∷ v) sw = begin
  col (c ∷ d ∷ v) • SWAP ↑
    ≈⟨ front _ (col-split c d v) ⟩
  (P • CX₀₂ ^ᶠ d • CXʳ ^ᶠ c) • SWAP ↑
    ≈⟨ slideʳ (sym (Π-comm (col v))) (slideʳ (sym (slideᶠ d tCXʳ)) (sym (slideᶠ c tCX₀₂))) ⟩
  SWAP ↑ • P • CXʳ ^ᶠ d • CX₀₂ ^ᶠ c
    ≈⟨ back _ (back _ (sym (Pow.pow-comm₂ (₃₊ n) (toℕ c) (toℕ d) r02))) ⟩
  SWAP ↑ • P • CX₀₂ ^ᶠ c • CXʳ ^ᶠ d
    ≈⟨ back _ (sym (col-split d c v)) ⟩
  SWAP ↑ • col (d ∷ c ∷ v) ∎
  where
  open Width (₃₊ n)
  P = SWAP • SWAP ↑ • col v ↑ ↑ • SWAP ↑ • SWAP

-- A word on the upper wires past the fan-out.
col-push* : (v : Vec F n) (L : Word (LGen n)) → (₁₊ n) ⊢ col v • ⌊ L ⌋ ↑ ≈ ⌊ L ⌋ ↑ • col (v ⋆ᶜ* L)
col-push* v [ y ]ʷ = col-push v y
col-push* {n} v ε  = Width.slide-ε (₁₊ n)
col-push* {n} v (L • L') = begin
  col v • ⌊ L ⌋ ↑ • ⌊ L' ⌋ ↑                     ≈⟨ sym assoc ⟩
  (col v • ⌊ L ⌋ ↑) • ⌊ L' ⌋ ↑                   ≈⟨ front _ (col-push* v L) ⟩
  (⌊ L ⌋ ↑ • col (v ⋆ᶜ* L)) • ⌊ L' ⌋ ↑           ≈⟨ assoc ⟩
  ⌊ L ⌋ ↑ • col (v ⋆ᶜ* L) • ⌊ L' ⌋ ↑             ≈⟨ back _ (col-push* (v ⋆ᶜ* L) L') ⟩
  ⌊ L ⌋ ↑ • ⌊ L' ⌋ ↑ • col (v ⋆ᶜ* L ⋆ᶜ* L')      ≈⟨ sym assoc ⟩
  (⌊ L ⌋ ↑ • ⌊ L' ⌋ ↑) • col (v ⋆ᶜ* L ⋆ᶜ* L')    ∎
  where open Width (₁₊ n)
