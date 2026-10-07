------------------------------------------------------------------------
-- Presentations of groups
--
-- Splitting an atom of S along wire 0
--
-- On ₁₊ n wires write x = (x₀ , x').  Since
--
--     (x₀ + w·x' choose 2) = (x₀ choose 2) + (w·x' choose 2) + x₀ (w·x'),
--
-- the atom of the row (1 , w) is S on wire 0, the atom of w one wire up,
-- and the fan K w (Q-dec).  The step from w to (c , w) is rule (30)
-- read on atoms: conjugating CZ by CX ↑ gives
--
--     A(e₀+e₁+e₂) = A(e₁+e₂) A(e₁)⁻¹ A(e₀+e₁) A(e₀)⁻¹ A(e₂)⁻¹ A(e₀+e₂)   (T3₀)
--
-- and transporting it by M_c on wire 1 and the representative of w two
-- wires up puts e₁ at c e₁ and e₂ at w (T3).  A multiplier on wire 0
-- then scales everything (split-big).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Split
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) (odd : 1 ≤ p-2) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; 1* ; binom2 ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; R-zero)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Atom p-2 p-prime lv using (⁻¹-↑)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.EForm p-2 p-prime lv h odd public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₂ h

------------------------------------------------------------------------
-- Atoms: order, inverses, conjugation

atom-order : (ℓ : NZ n) → n ⊢ atom ℓ ^ p ≈ ε
atom-order {suc n} ℓ = begin
  A ℓ ^ p                      ≈⟨ A-^ ℓ p ⟩
  r ℓ ⁻¹ • S h ^ p • r ℓ       ≈⟨ back _ (trans (front _ S-order) left-unit) ⟩
  r ℓ ⁻¹ • r ℓ                 ≈⟨ Inv.inverseˡ (₁₊ n) ⟩
  ε                            ∎
  where open Width (₁₊ n)

-- The inverse of an atom.
infix 9 _ᵃ⁻
_ᵃ⁻ : NZ n → Circuit n
ℓ ᵃ⁻ = atom ℓ ^ᶠ (- 1F)

atom-inv : (ℓ : NZ n) → n ⊢ atom ℓ • ℓ ᵃ⁻ ≈ ε
atom-inv {n} ℓ = Pow.Order.inverseʳ n (atom-order ℓ)

atom-invˡ : (ℓ : NZ n) → n ⊢ ℓ ᵃ⁻ • atom ℓ ≈ ε
atom-invˡ {n} ℓ = Pow.Order.inverseˡ n (atom-order ℓ)

atom-≡ : (ℓ ℓ' : NZ n) → row ℓ ≡ row ℓ' → n ⊢ atom ℓ ≈ atom ℓ'
atom-≡ {suc n} ℓ ℓ' e = A-≡ e

atom-≡ᶠ : (ℓ ℓ' : NZ n) (k : F) → row ℓ ≡ row ℓ' → n ⊢ atom ℓ ^ᶠ k ≈ atom ℓ' ^ᶠ k
atom-≡ᶠ {n} ℓ ℓ' k e = Pow.pow-cong n (toℕ k) (atom-≡ ℓ ℓ' e)

module _ {m : ℕ} where

  open Width m

  -- Conjugation distributes over products and iterates.
  conj-• : (g X Y : Circuit m) → m ⊢ g ⁻¹ • (X • Y) • g ≈ (g ⁻¹ • X • g) • (g ⁻¹ • Y • g)
  conj-• g X Y = begin
    g ⁻¹ • (X • Y) • g                    ≈⟨ back _ (trans assoc (back _ (sym (trans (front _ (Inv.inverseʳ m)) left-unit)))) ⟩
    g ⁻¹ • X • (g • g ⁻¹) • Y • g         ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
    (g ⁻¹ • X • g) • (g ⁻¹ • Y • g)       ∎

  conj-^ᶠ : (g X : Circuit m) (k : F) → m ⊢ g ⁻¹ • X ^ᶠ k • g ≈ (g ⁻¹ • X • g) ^ᶠ k
  conj-^ᶠ g X k = sym (conj-pow (Inv.inverseˡ m) (Inv.inverseʳ m) (toℕ k))

  conj-ε : (g : Circuit m) → m ⊢ g ⁻¹ • ε • g ≈ ε
  conj-ε g = trans (back _ left-unit) (Inv.inverseˡ m)

atom-conj : (ℓ : NZ n) (L : Word (LGen n)) → n ⊢ ⌊ L ⌋ ⁻¹ • atom ℓ • ⌊ L ⌋ ≈ atom (ℓ ⋆* L)
atom-conj {suc n} ℓ L = A-conj ℓ L

atom-conjᶠ : (ℓ : NZ n) (L : Word (LGen n)) (k : F) →
             n ⊢ ⌊ L ⌋ ⁻¹ • atom ℓ ^ᶠ k • ⌊ L ⌋ ≈ atom (ℓ ⋆* L) ^ᶠ k
atom-conjᶠ {n} ℓ L k = Width.trans (conj-^ᶠ ⌊ L ⌋ (atom ℓ) k) (Pow.pow-cong n (toℕ k) (atom-conj ℓ L))

-- Transporting a list of atoms.
ats⋆* : Atoms n → Word (LGen n) → Atoms n
ats⋆* []             L = []
ats⋆* ((ℓ , k) ∷ as) L = (ℓ ⋆* L , k) ∷ ats⋆* as L

atoms-conj : (L : Word (LGen n)) (as : Atoms n) → n ⊢ ⌊ L ⌋ ⁻¹ • atoms as • ⌊ L ⌋ ≈ atoms (ats⋆* as L)
atoms-conj L []             = conj-ε ⌊ L ⌋
atoms-conj {n} L ((ℓ , k) ∷ as) =
  Width.trans (conj-• ⌊ L ⌋ (atom ℓ ^ᶠ k) (atoms as)) (Width.cong (atom-conjᶠ ℓ L k) (atoms-conj L as))

------------------------------------------------------------------------
-- CZ in atoms

e0 : NZ (₁₊ n)
e0 = big 1* 0ᵛ

e1 : NZ (₂₊ n)
e1 = small e0

CZ-atoms : (₂₊ n) ⊢ CZ h ≈ e0 ᵃ⁻ • e1 ᵃ⁻ • atom e₀₁
CZ-atoms {n} = cong (Pow.pow-cong (₂₊ n) (toℕ (- 1F)) (S-e zero))
                    (cong (trans (refl' (↑ᶠ (S h) (- 1F)))
                                 (Pow.pow-cong (₂₊ n) (toℕ (- 1F)) (trans (lift (S-e zero)) (sym (A-small e0)))))
                          P-atom)
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- Rule (30) on atoms

module _ {n : ℕ} where

  open Width (₃₊ n)

  private
    a0 a1 a2 a01 a02 a12 a012 : NZ (₃₊ n)
    a0   = big 1* 0ᵛ
    a1   = small (big 1* 0ᵛ)
    a2   = small (small (big 1* 0ᵛ))
    a01  = big 1* (1F ∷ 0ᵛ)
    a02  = big 1* (0F ∷ 1F ∷ 0ᵛ)
    a12  = small (big 1* (1F ∷ 0ᵛ))
    a012 = big 1* (1F ∷ 1F ∷ 0ᵛ)

    conj-CZ : (L : Word (LGen (₃₊ n))) →
              (₃₊ n) ⊢ ⌊ L ⌋ ⁻¹ • CZ h • ⌊ L ⌋ ≈ (a0 ⋆* L) ᵃ⁻ • (a1 ⋆* L) ᵃ⁻ • atom (a01 ⋆* L)
    conj-CZ L = begin
      ⌊ L ⌋ ⁻¹ • CZ h • ⌊ L ⌋
        ≈⟨ back _ (front _ CZ-atoms) ⟩
      ⌊ L ⌋ ⁻¹ • (a0 ᵃ⁻ • a1 ᵃ⁻ • atom a01) • ⌊ L ⌋
        ≈⟨ trans (conj-• _ _ _) (back _ (conj-• _ _ _)) ⟩
      (⌊ L ⌋ ⁻¹ • a0 ᵃ⁻ • ⌊ L ⌋) • (⌊ L ⌋ ⁻¹ • a1 ᵃ⁻ • ⌊ L ⌋) • (⌊ L ⌋ ⁻¹ • atom a01 • ⌊ L ⌋)
        ≈⟨ cong (atom-conjᶠ a0 L (- 1F)) (cong (atom-conjᶠ a1 L (- 1F)) (atom-conj a01 L)) ⟩
      (a0 ⋆* L) ᵃ⁻ • (a1 ⋆* L) ᵃ⁻ • atom (a01 ⋆* L) ∎

    C L' : Word (LGen (₃₊ n))
    C  = [ cx ↥ₗ ]ʷ
    L' = [ sw ↥ₗ ]ʷ

    -- Rule (30): CX ↑ conjugates CZ into CZ CZ₂₀.
    CZ-CX↑ : (₃₊ n) ⊢ ⌊ C ⌋ ⁻¹ • CZ h • ⌊ C ⌋ ≈ CZ h • CZ₂₀ h
    CZ-CX↑ = trans (back _ (ax (ax30 h))) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₃₊ n))) left-unit))

    CZ₂₀≈ : (₃₊ n) ⊢ CZ₂₀ h ≈ ⌊ L' ⌋ ⁻¹ • CZ h • ⌊ L' ⌋
    CZ₂₀≈ = front _ (Inv.inverseʳ-unique (₃₊ n) (lift (ax swap-order)))

    EQ : (₃₊ n) ⊢ a0 ᵃ⁻ • a12 ᵃ⁻ • atom a012 ≈ (a0 ᵃ⁻ • a1 ᵃ⁻ • atom a01) • (a0 ᵃ⁻ • a2 ᵃ⁻ • atom a02)
    EQ = begin
      a0 ᵃ⁻ • a12 ᵃ⁻ • atom a012
        ≈⟨ sym (cong (atom-≡ᶠ (a0 ⋆* C) a0 (- 1F) (Eq.cong (λ t → 1F ∷ 0F ∷ t ∷ 0ᵛ) (FR.+-identityʳ 0F)))
                     (cong (atom-≡ᶠ (a1 ⋆* C) a12 (- 1F) (Eq.cong (λ t → 0F ∷ 1F ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F)))
                           (atom-≡ (a01 ⋆* C) a012 (Eq.cong (λ t → 1F ∷ 1F ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F))))) ⟩
      (a0 ⋆* C) ᵃ⁻ • (a1 ⋆* C) ᵃ⁻ • atom (a01 ⋆* C)
        ≈⟨ sym (conj-CZ C) ⟩
      ⌊ C ⌋ ⁻¹ • CZ h • ⌊ C ⌋
        ≈⟨ CZ-CX↑ ⟩
      CZ h • CZ₂₀ h
        ≈⟨ cong CZ-atoms (trans CZ₂₀≈ (conj-CZ L')) ⟩
      (a0 ᵃ⁻ • a1 ᵃ⁻ • atom a01) • (a0 ᵃ⁻ • a2 ᵃ⁻ • atom a02) ∎

  -- Rule (30) on atoms, at e₀, e₁, e₂.
  T3₀ : (₃₊ n) ⊢ atom a012 ≈ atom a12 • a1 ᵃ⁻ • atom a01 • a0 ᵃ⁻ • a2 ᵃ⁻ • atom a02
  T3₀ = begin
    atom a012
      ≈⟨ sym (trans (back _ (trans (sym assoc) (trans (front _ (atom-inv a0)) left-unit)))
                    (trans (sym assoc) (trans (front _ (atom-inv a12)) left-unit))) ⟩
    atom a12 • atom a0 • a0 ᵃ⁻ • a12 ᵃ⁻ • atom a012
      ≈⟨ back _ (back _ EQ) ⟩
    atom a12 • atom a0 • (a0 ᵃ⁻ • a1 ᵃ⁻ • atom a01) • (a0 ᵃ⁻ • a2 ᵃ⁻ • atom a02)
      ≈⟨ back _ (by-passoc (□ • (□ • □ • □) • (□ • □ • □)) ((□ • □) • □ • □ • □ • □ • □) Eq.refl) ⟩
    atom a12 • (atom a0 • a0 ᵃ⁻) • a1 ᵃ⁻ • atom a01 • a0 ᵃ⁻ • a2 ᵃ⁻ • atom a02
      ≈⟨ back _ (trans (front _ (atom-inv a0)) left-unit) ⟩
    atom a12 • a1 ᵃ⁻ • atom a01 • a0 ᵃ⁻ • a2 ᵃ⁻ • atom a02 ∎

------------------------------------------------------------------------
-- Rule (30) on atoms, at e₀, c e₁ and w two wires up

module _ {n : ℕ} (c : F*) (ℓ : NZ (₁₊ n)) where

  open Width (₃₊ n)

  private
    c' = proj₁ c
    w  = row ℓ

    L : Word (LGen (₃₊ n))
    L = [ mul c ↥ₗ ]ʷ • rL ℓ ↑ₗ ↑ₗ

    -- Where L takes the rows (x, y, z, 0, ...).
    at : (x y z : F) → (x ∷ y ∷ z ∷ 0ᵛ) ⋆ᴿ* L ≡ x ∷ y * c' ∷ ((z ∷ 0ᵛ) ⋆ᴿ* rL ℓ)
    at x y z = Eq.trans (⋆ᴿ*-↑ x _ (rL ℓ ↑ₗ)) (Eq.cong (x ∷_) (⋆ᴿ*-↑ (y * c') _ (rL ℓ)))

    one : (x y : F) → (x ∷ y ∷ 1F ∷ 0ᵛ) ⋆ᴿ* L ≡ x ∷ y * c' ∷ w
    one x y = Eq.trans (at x y 1F) (Eq.cong (λ v → x ∷ y * c' ∷ v) (e₀-rL ℓ))

    nil : (x y : F) → (x ∷ y ∷ 0F ∷ 0ᵛ) ⋆ᴿ* L ≡ x ∷ y * c' ∷ 0ᵛ
    nil x y = Eq.trans (at x y 0F) (Eq.cong (λ v → x ∷ y * c' ∷ v) (zero-⋆ᴿ* (rL ℓ)))

    -- Rows of a transported atom.
    moved : (ℓ₀ ℓ₁ : NZ (₃₊ n)) (k : F) → row ℓ₀ ⋆ᴿ* L ≡ row ℓ₁ → (₃₊ n) ⊢ atom (ℓ₀ ⋆* L) ^ᶠ k ≈ atom ℓ₁ ^ᶠ k
    moved ℓ₀ ℓ₁ k e = atom-≡ᶠ (ℓ₀ ⋆* L) ℓ₁ k (Eq.trans (row-⋆* ℓ₀ L) e)

    0*c : 0F * c' ≡ 0F
    0*c = FR.zeroˡ c'

    1*c : 1F * c' ≡ c'
    1*c = FR.*-identityˡ c'

  T3 : (₃₊ n) ⊢ atom (big 1* (c' ∷ w))
               ≈ atom (small (big c w)) • (small (big c 0ᵛ)) ᵃ⁻ • atom (big 1* (c' ∷ 0ᵛ))
                 • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • atom (big 1* (0F ∷ w))
  T3 = begin
    atom (big 1* (c' ∷ w))
      ≈⟨ sym (trans right-unit (moved (big 1* (1F ∷ 1F ∷ 0ᵛ)) (big 1* (c' ∷ w)) 1F (Eq.trans (one 1F 1F) (Eq.cong (λ t → 1F ∷ t ∷ w) 1*c)))) ⟩
    atoms ((big 1* (1F ∷ 1F ∷ 0ᵛ) ⋆* L , 1F) ∷ [])
      ≈⟨ sym (atoms-conj L ((big 1* (1F ∷ 1F ∷ 0ᵛ) , 1F) ∷ [])) ⟩
    ⌊ L ⌋ ⁻¹ • atoms ((big 1* (1F ∷ 1F ∷ 0ᵛ) , 1F) ∷ []) • ⌊ L ⌋
      ≈⟨ back _ (front _ (trans right-unit (trans T3₀ (sym rhs)))) ⟩
    ⌊ L ⌋ ⁻¹ • atoms as₀ • ⌊ L ⌋
      ≈⟨ atoms-conj L as₀ ⟩
    atoms (ats⋆* as₀ L)
      ≈⟨ cong (moved (small (big 1* (1F ∷ 0ᵛ))) (small (big c w)) 1F
                     (Eq.trans (one 0F 1F) (Eq.cong (λ t → 0F ∷ t ∷ w) 1*c)))
         (cong (moved (small (big 1* 0ᵛ)) (small (big c 0ᵛ)) (- 1F)
                     (Eq.trans (nil 0F 1F) (Eq.cong (λ t → 0F ∷ t ∷ 0ᵛ) 1*c)))
         (cong (moved (big 1* (1F ∷ 0ᵛ)) (big 1* (c' ∷ 0ᵛ)) 1F
                     (Eq.trans (nil 1F 1F) (Eq.cong (λ t → 1F ∷ t ∷ 0ᵛ) 1*c)))
         (cong (moved (big 1* 0ᵛ) (big 1* 0ᵛ) (- 1F)
                     (Eq.trans (nil 1F 0F) (Eq.cong (λ t → 1F ∷ t ∷ 0ᵛ) 0*c)))
         (cong (moved (small (small (big 1* 0ᵛ))) (small (small ℓ)) (- 1F)
                     (Eq.trans (one 0F 0F) (Eq.cong (λ t → 0F ∷ t ∷ w) 0*c)))
         (cong (moved (big 1* (0F ∷ 1F ∷ 0ᵛ)) (big 1* (0F ∷ w)) 1F
                     (Eq.trans (one 1F 0F) (Eq.cong (λ t → 1F ∷ t ∷ w) 0*c)))
               refl))))) ⟩
    atom (small (big c w)) ^ᶠ 1F • (small (big c 0ᵛ)) ᵃ⁻ • atom (big 1* (c' ∷ 0ᵛ)) ^ᶠ 1F
      • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • atom (big 1* (0F ∷ w)) ^ᶠ 1F • ε
      ≈⟨ back _ (back _ (back _ (back _ (back _ right-unit)))) ⟩
    atom (small (big c w)) • (small (big c 0ᵛ)) ᵃ⁻ • atom (big 1* (c' ∷ 0ᵛ))
      • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • atom (big 1* (0F ∷ w)) ∎
    where
    as₀ : Atoms (₃₊ n)
    as₀ = (small (big 1* (1F ∷ 0ᵛ)) , 1F) ∷ (small (big 1* 0ᵛ) , - 1F) ∷ (big 1* (1F ∷ 0ᵛ) , 1F)
          ∷ (big 1* 0ᵛ , - 1F) ∷ (small (small (big 1* 0ᵛ)) , - 1F) ∷ (big 1* (0F ∷ 1F ∷ 0ᵛ) , 1F) ∷ []
    rhs : (₃₊ n) ⊢ atoms as₀ ≈ atom (small (big 1* (1F ∷ 0ᵛ))) • (small (big 1* 0ᵛ)) ᵃ⁻ • atom (big 1* (1F ∷ 0ᵛ))
                               • (big 1* 0ᵛ) ᵃ⁻ • (small (small (big 1* 0ᵛ))) ᵃ⁻ • atom (big 1* (0F ∷ 1F ∷ 0ᵛ))
    rhs = back _ (back _ (back _ (back _ (back _ right-unit))))
