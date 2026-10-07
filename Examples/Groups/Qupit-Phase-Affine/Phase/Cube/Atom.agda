------------------------------------------------------------------------
-- Presentations of groups
--
-- Atoms of S and T at level 3
--
-- The atoms of T, (r ℓ)⁻¹ • T • r ℓ, behave like those of S
-- (Phase.Atom).  A word W = S^q Z^b T^t on wire 0 commutes with S or T
-- conjugated by a fan-in (FanConj.STZ∥Y): for w = 0 it is S or T, and
-- otherwise the fan-in is CX conjugated by a representative one wire
-- up, so the conjugate is the gadget P or PT conjugated by it, which W
-- passes (Phase.Cube.T).  S and T pass an inverse multiplier as such
-- words (rules (27), (32)), so each commutes with every atom of S and
-- of T (FanConj.G∥A); hence all atoms commute, and they commute with
-- columns of Z's.  An iterate of an atom of T passes a translation,
-- leaving an iterate of the atom of S of the same row, a column of Z's
-- and a power of ω (Aᵀ-Xc).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Atom
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; _⁻¹* ; binom2 ; binom3 ; big⇒odd)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; R-zero)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (Xc ; _⋆ˣ*_)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Atom p-2 p-prime lv
  using (⁻¹-↑ ; flip⁻¹ ; conj-X ; module Atoms)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Split p-2 p-prime lv (quad₃ h) (big⇒odd gt3) public
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.T p-2 p-prime lv h gt3 public

private
  variable
    n : ℕ

  h₂ : 2 ≤ lv
  h₂ = quad₃ h

  h₁ : 1 ≤ lv
  h₁ = lin₃ h

------------------------------------------------------------------------
-- Words of S, Z and T against conjugates of a gate

module FanConj
  (g : Gate 1)
  (H-CXʳ : ∀ {n} → (₂₊ n) ⊢ [ gate₁ g ]ʷ • CXʳ ≈ CXʳ • [ gate₁ g ]ʷ)
  (H-swap : ∀ {n} → (₂₊ n) ⊢ [ gate₁ g ]ʷ • SWAP ≈ SWAP • [ gate₁ g ]ʷ ↑)
  (STZ∥H : ∀ {n} (q b t : F) → (₁₊ n) ⊢ STZ q b t ∥ [ gate₁ g ]ʷ)
  (STZ∥PH : ∀ {n} (q b t : F) → (₂₊ n) ⊢ STZ q b t ∥ (CX ^ᶠ (- 1F) • [ gate₁ g ]ʷ • CX))
  where

  module AH = Atoms g H-CXʳ H-swap

  private
    H : Circuit (₁₊ n)
    H = [ gate₁ g ]ʷ

  -- H conjugated by a fan-in.
  STZ∥Y : (q b t : F) (w : Vec F n) → (₁₊ n) ⊢ STZ q b t ∥ (R w ⁻¹ • H • R w)
  STZ∥Y {zero} q b t [] = via (Width.trans Width.left-unit Width.right-unit) (STZ∥H q b t)
  STZ∥Y {suc m} q b t w with nz? w
  ... | inj₁ e = via Y≈H (STZ∥H q b t)
    where
    open Width (₂₊ m)
    Rε : (₂₊ m) ⊢ R w ≈ ε
    Rε = Eq.subst (λ v → (₂₊ m) ⊢ R v ≈ ε) (Eq.sym e) R-zero
    Y≈H : (₂₊ m) ⊢ R w ⁻¹ • H • R w ≈ H
    Y≈H = trans (cong (Inv.⁻¹-cong (₂₊ m) Rε) (back _ Rε)) (trans left-unit right-unit)
  ... | inj₂ (ℓ' , e) = via Y≈ (∥-• W∥ρ⁻¹ (∥-• (STZ∥PH q b t) (STZ-up q b t (r ℓ'))))
    where
    open Width (₂₊ m)
    ρ : Circuit (₂₊ m)
    ρ = r ℓ' ↑
    W∥ρ⁻¹ : (₂₊ m) ⊢ STZ q b t ∥ ρ ⁻¹
    W∥ρ⁻¹ = via (refl' (⁻¹-↑ (r ℓ'))) (STZ-up q b t (r ℓ' ⁻¹))
    RT : (₂₊ m) ⊢ R w ≈ ρ ⁻¹ • CX • ρ
    RT = trans (refl' (Eq.cong R (Eq.sym e)))
           (sym (trans (back _ (CX-r ℓ')) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₂₊ m))) left-unit))))
    ρHρ⁻¹ : (₂₊ m) ⊢ ρ • H • ρ ⁻¹ ≈ H
    ρHρ⁻¹ = trans (sym assoc) (trans (front _ (comm-gate₁-w↑ g (r ℓ')))
              (trans assoc (trans (back _ (Inv.inverseʳ (₂₊ m))) right-unit)))
    CX⁻¹≈ : (₂₊ m) ⊢ CX ⁻¹ ≈ CX ^ᶠ (- 1F)
    CX⁻¹≈ = sym (Inv.inverseʳ-unique (₂₊ m) (CX-invʳ 1F))
    Y≈ : (₂₊ m) ⊢ R w ⁻¹ • H • R w ≈ ρ ⁻¹ • (CX ^ᶠ (- 1F) • H • CX) • ρ
    Y≈ = begin
      R w ⁻¹ • H • R w
        ≈⟨ cong (Inv.⁻¹-cong (₂₊ m) RT) (back _ RT) ⟩
      ((ρ ⁻¹ • CX ⁻¹) • ρ ⁻¹ ⁻¹) • H • ρ ⁻¹ • CX • ρ
        ≈⟨ front _ (back _ (Inv.⁻¹-involutive (₂₊ m))) ⟩
      ((ρ ⁻¹ • CX ⁻¹) • ρ) • H • ρ ⁻¹ • CX • ρ
        ≈⟨ by-passoc (((□ • □) • □) • □ • □ • □ • □) (□ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
      ρ ⁻¹ • CX ⁻¹ • (ρ • H • ρ ⁻¹) • CX • ρ
        ≈⟨ back _ (cong CX⁻¹≈ (front _ ρHρ⁻¹)) ⟩
      ρ ⁻¹ • CX ^ᶠ (- 1F) • H • CX • ρ
        ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
      ρ ⁻¹ • (CX ^ᶠ (- 1F) • H • CX) • ρ ∎

  -- A word on wire 0 that passes everything one wire up, and an inverse
  -- multiplier as a word of S, Z and T, commutes with every atom of H.
  G∥A : (G : Circuit (₁₊ n)) → (∀ (w : Circuit n) → (₁₊ n) ⊢ G ∥ (w ↑)) →
        (∀ (a : F*) → Σ (F × F × F) λ { (q , b , t) → (₁₊ n) ⊢ G • M⟨ a ⟩ ⁻¹ ≈ M⟨ a ⟩ ⁻¹ • STZ q b t }) →
        (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ G ∥ AH.A ℓ
  G∥A G up GM (small ℓ) = via (AH.A-small ℓ) (up (AH.A ℓ))
  G∥A {n} G up GM (big a w) with GM a
  ... | (q , b , t) , GMi = begin
    G • (Mi • R w ⁻¹) • H • R w • M⟨ a ⟩
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) ((□ • □) • (□ • □ • □) • □) Eq.refl ⟩
    (G • Mi) • Y • M⟨ a ⟩
      ≈⟨ front _ GMi ⟩
    (Mi • W) • Y • M⟨ a ⟩
      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (STZ∥Y q b t w)))) ⟩
    Mi • (Y • W) • M⟨ a ⟩
      ≈⟨ back _ (trans assoc (back _ (sym MG))) ⟩
    Mi • Y • M⟨ a ⟩ • G
      ≈⟨ by-passoc (□ • (□ • □ • □) • □ • □) (((□ • □) • □ • □ • □) • □) Eq.refl ⟩
    ((Mi • R w ⁻¹) • H • R w • M⟨ a ⟩) • G ∎
    where
    open Width (₁₊ n)
    Mi W Y : Circuit (₁₊ n)
    Mi = M⟨ a ⟩ ⁻¹
    W  = STZ q b t
    Y  = R w ⁻¹ • H • R w
    MG : (₁₊ n) ⊢ M⟨ a ⟩ • G ≈ W • M⟨ a ⟩
    MG = trans (front _ (sym (Inv.⁻¹-involutive (₁₊ n))))
           (trans (flip⁻¹ GMi) (back _ (Inv.⁻¹-involutive (₁₊ n))))

------------------------------------------------------------------------
-- S and T pass inverse multipliers as words

module _ {n : ℕ} where

  open Width (₁₊ n)

  S-M⁻¹′ : (a : F*) → Σ (F × F × F) λ { (q , b , t) → (₁₊ n) ⊢ S h₂ • M⟨ a ⟩ ⁻¹ ≈ M⟨ a ⟩ ⁻¹ • STZ q b t }
  S-M⁻¹′ a = (sq⁻ a , β⁻ a , 0F) , trans (S-M⁻¹ a) (back _ (S-STZ (sq⁻ a) (β⁻ a)))

  T-M⁻¹ : (a : F*) → Σ (F × F × F) λ { (q , b , t) → (₁₊ n) ⊢ T h • M⟨ a ⟩ ⁻¹ ≈ M⟨ a ⟩ ⁻¹ • STZ q b t }
  T-M⁻¹ a = (_ , _ , _) , trans (back _ (M⁻¹≈ a)) (trans (T-M (a ⁻¹*)) (front _ (sym (M⁻¹≈ a))))

------------------------------------------------------------------------
-- Atoms of T, and all commutations

module AT = Atoms (T-gate h) T∥CXʳ (ax (swap-T h))

module FS = FanConj (S-gate h₂) S∥CXʳ (ax (swap-S h₂)) STZ∥S STZ∥P
module FT = FanConj (T-gate h) T∥CXʳ (ax (swap-T h)) STZ∥T STZ∥PT

-- The atom of T at any width.
atomᵀ : NZ n → Circuit n
atomᵀ {suc m} ℓ = AT.A ℓ
atomᵀ {zero} ()

S∥Aᵀ : (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ S h₂ ∥ AT.A ℓ
S∥Aᵀ = FT.G∥A (S h₂) (Sᶠ-up 1F) S-M⁻¹′

T∥Aᵀ : (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ T h ∥ AT.A ℓ
T∥Aᵀ = FT.G∥A (T h) (Tᶠ-up 1F) T-M⁻¹

T∥Aˢ : (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ T h ∥ A ℓ
T∥Aˢ = FS.G∥A (T h) (Tᶠ-up 1F) T-M⁻¹

Aˢ∥Aᵀ : (ℓ ℓ' : NZ (₁₊ n)) → (₁₊ n) ⊢ A ℓ ∥ AT.A ℓ'
Aˢ∥Aᵀ ℓ ℓ' = conj-into ℓ (AT.A ℓ') (via (AT.rr⁻¹ ℓ ℓ') (S∥Aᵀ (ℓ' ⋆* linv (rL ℓ))))

Aᵀ∥Aᵀ : (ℓ ℓ' : NZ (₁₊ n)) → (₁₊ n) ⊢ AT.A ℓ ∥ AT.A ℓ'
Aᵀ∥Aᵀ ℓ ℓ' = AT.conj-into ℓ (AT.A ℓ') (via (AT.rr⁻¹ ℓ ℓ') (T∥Aᵀ (ℓ' ⋆* linv (rL ℓ))))

Aᵀ∥Aˢ : (ℓ ℓ' : NZ (₁₊ n)) → (₁₊ n) ⊢ AT.A ℓ ∥ A ℓ'
Aᵀ∥Aˢ ℓ ℓ' = AT.conj-into ℓ (A ℓ') (via (rr⁻¹ ℓ ℓ') (T∥Aˢ (ℓ' ⋆* linv (rL ℓ))))

T∥Zc : (c : Vec F (₁₊ n)) → (₁₊ n) ⊢ T h ∥ Zc c
T∥Zc (c ∷ cs) = ∥-• (∥-sym (∥-^ᶠ c (∥-sym T∥Z))) (Tᶠ-up 1F (Zc cs))

Zc∥Aᵀ : (c : Vec F (₁₊ n)) (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ Zc c ∥ AT.A ℓ
Zc∥Aᵀ c ℓ = ∥-sym (AT.conj-into ℓ (Zc c) (via (Zc-conj ℓ c) (T∥Zc _)))

------------------------------------------------------------------------
-- Atoms of T past translations

module _ {n : ℕ} where

  open Width (₁₊ n)

  -- T^k past a translation.
  T-Xc : (k : F) (v : Vec F (₁₊ n)) →
         (₁₊ n) ⊢ T h ^ᶠ k • Xc v ≈
                  Xc v • T h ^ᶠ k • (S h₂ ^ᶠ (k * head v) • Z h₁ ^ᶠ (k * binom2 (head v)) • ω h₁ ^ᶠ (k * binom3 (head v)))
  T-Xc k (a ∷ vs) = begin
    T h ^ᶠ k • X ^ᶠ a • Xc vs ↑
      ≈⟨ trans (sym assoc) (trans (front _ (T-Xᶠ k a)) assoc) ⟩
    X ^ᶠ a • (T h ^ᶠ k • D) • Xc vs ↑
      ≈⟨ back _ (•-∥ (Tᶠ-up k (Xc vs)) (•-∥ (Sᶠ-up (k * a) (Xc vs)) (•-∥ (Zᶠ-up (k * binom2 a) (Xc vs)) (ωᶠ-comm _ _)))) ⟩
    X ^ᶠ a • Xc vs ↑ • T h ^ᶠ k • D
      ≈⟨ sym assoc ⟩
    (X ^ᶠ a • Xc vs ↑) • T h ^ᶠ k • D ∎
    where
    D = S h₂ ^ᶠ (k * a) • Z h₁ ^ᶠ (k * binom2 a) • ω h₁ ^ᶠ (k * binom3 a)

  -- An iterate of an atom of T past a translation.
  Aᵀ-Xc : (ℓ : NZ (₁₊ n)) (k : F) (b : Vec F (₁₊ n)) →
          (₁₊ n) ⊢ AT.A ℓ ^ᶠ k • Xc b ≈
                   Xc b • AT.A ℓ ^ᶠ k • A ℓ ^ᶠ (k * head (b ⋆ˣ* rL ℓ))
                   • Zc ((k * binom2 (head (b ⋆ˣ* rL ℓ)) ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ (k * binom3 (head (b ⋆ˣ* rL ℓ)))
  Aᵀ-Xc ℓ k b = begin
    AT.A ℓ ^ᶠ k • Xc b
      ≈⟨ front _ (AT.A-^ ℓ (toℕ k)) ⟩
    (ρ ⁻¹ • T h ^ᶠ k • ρ) • Xc b
      ≈⟨ conj-X ℓ b (T-Xc k (b ⋆ˣ* rL ℓ)) ⟩
    Xc b • (ρ ⁻¹ • T h ^ᶠ k • ρ) • ρ ⁻¹ • (S h₂ ^ᶠ q • Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ
      ≈⟨ back _ (cong (sym (AT.A-^ ℓ (toℕ k))) D≈) ⟩
    Xc b • AT.A ℓ ^ᶠ k • A ℓ ^ᶠ q • Zc ((c ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ t ∎
    where
    ρ : Circuit (₁₊ n)
    ρ = r ℓ
    v₀ q c t : F
    v₀ = head (b ⋆ˣ* rL ℓ)
    q  = k * v₀
    c  = k * binom2 v₀
    t  = k * binom3 v₀
    Z≈ : (₁₊ n) ⊢ Z h₁ ^ᶠ c ≈ Zc (c ∷ 0ᵛ)
    Z≈ = sym (trans (back _ (lift Zc-zero)) right-unit)
    D≈ : (₁₊ n) ⊢ ρ ⁻¹ • (S h₂ ^ᶠ q • Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ ≈ A ℓ ^ᶠ q • Zc ((c ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ t
    D≈ = begin
      ρ ⁻¹ • (S h₂ ^ᶠ q • Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ
        ≈⟨ conj-• ρ _ _ ⟩
      (ρ ⁻¹ • S h₂ ^ᶠ q • ρ) • ρ ⁻¹ • (Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ
        ≈⟨ cong (sym (A-^ ℓ (toℕ q))) (back _ (trans assoc (back _ (ωᶠ-comm t ρ)))) ⟩
      A ℓ ^ᶠ q • ρ ⁻¹ • Z h₁ ^ᶠ c • ρ • ω h₁ ^ᶠ t
        ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
      A ℓ ^ᶠ q • (ρ ⁻¹ • Z h₁ ^ᶠ c • ρ) • ω h₁ ^ᶠ t
        ≈⟨ back _ (front _ (trans (back _ (front _ Z≈)) (Zc-rconj ℓ (c ∷ 0ᵛ)))) ⟩
      A ℓ ^ᶠ q • Zc ((c ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ t ∎
