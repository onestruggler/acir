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
-- wires up puts e₁ at c e₁ and e₂ at w (T3), while on two wires the S
-- gadget gives the atom of (1 , c) (A-01).  A multiplier on wire 0 then
-- scales everything (split-big), and the atoms of a diagonal expression
-- split one at a time: every diagonal expression on ₁₊ n wires is one on
-- n wires, one wire up, times a wire-0 form E e (split-sound).
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

------------------------------------------------------------------------
-- The atom of a vector

-- Nothing for the zero vector.
atomᵛ : Vec F n → Circuit n
atomᵛ [] = ε
atomᵛ (c ∷ w) with c ≟ 0F
... | no nc = atom (big (c , nc) w)
... | yes _ = atomᵛ w ↑

Diag-atomᵛ : (w : Vec F n) → Diag n (atomᵛ w)
Diag-atomᵛ [] = Diag-ε
Diag-atomᵛ (c ∷ w) with c ≟ 0F
... | no nc = Diag-atom (big (c , nc) w)
... | yes _ = Diag-↑ (Diag-atomᵛ w)

atomᵛ-row : (ℓ : NZ n) → n ⊢ atomᵛ (row ℓ) ≈ atom ℓ
atomᵛ-row (big a w) with proj₁ a ≟ 0F
... | no nc = atom-≡ (big (proj₁ a , nc) w) (big a w) Eq.refl
... | yes e = ⊥-elim (proj₂ a e)
atomᵛ-row (small ℓ) = Width.trans (lift (atomᵛ-row ℓ)) (Width.sym (A-small ℓ))

------------------------------------------------------------------------
-- Atoms on wires 0 and 1

A-e0 : (₁₊ n) ⊢ atom (e0 {n}) ≈ S h
A-e0 = Width.sym (S-e zero)

-- An atom of a multiple of e₀: rule (27).
A-scale : (a : F*) → (₁₊ n) ⊢ atom (big a (0ᵛ {n})) ≈ SZ (1F * (proj₁ a * proj₁ a)) (1F * binom2 (proj₁ a))
A-scale {n} a = begin
  (R 0ᵛ • M⟨ a ⟩) ⁻¹ • S h • R 0ᵛ • M⟨ a ⟩
    ≈⟨ cong (Inv.⁻¹-cong (₁₊ n) r≈) (back _ r≈) ⟩
  M⟨ a ⟩ ⁻¹ • S h • M⟨ a ⟩
    ≈⟨ back _ (Sᶠ-M 1F a) ⟩
  M⟨ a ⟩ ⁻¹ • M⟨ a ⟩ • Z h₁ ^ᶠ β • S h ^ᶠ s
    ≈⟨ trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit) ⟩
  Z h₁ ^ᶠ β • S h ^ᶠ s
    ≈⟨ sym (Sᶠ∥Zᶠ s β) ⟩
  SZ s β ∎
  where
  open Width (₁₊ n)
  s β : F
  s = 1F * (proj₁ a * proj₁ a)
  β = 1F * binom2 (proj₁ a)
  r≈ : (₁₊ n) ⊢ R 0ᵛ • M⟨ a ⟩ ≈ M⟨ a ⟩
  r≈ = trans (front _ R-zero) left-unit

-- The atom of e₀ + c e₁: the S gadget.
A-01 : (c : F) → (₂₊ n) ⊢ atom (big 1* (c ∷ 0ᵛ {n})) ≈ S h • SZ (c * c) (binom2 c) ↑ • CZ h ^ᶠ c
A-01 {n} c = begin
  r₀ ⁻¹ • S h • r₀                       ≈⟨ cong (Inv.⁻¹-cong (₂₊ n) r≈) (back _ r≈) ⟩
  (CX ^ᶠ c) ⁻¹ • S h • CX ^ᶠ c           ≈⟨ front _ (sym (Inv.inverseʳ-unique (₂₊ n) (CX-invʳ c))) ⟩
  CX ^ᶠ (- c) • S h • CX ^ᶠ c            ≈⟨ S-conj c ⟩
  S h • SZ (c * c) (binom2 c) ↑ • CZ h ^ᶠ c ∎
  where
  open Width (₂₊ n)
  r₀ = r (big 1* (c ∷ 0ᵛ {n}))
  r≈ : (₂₊ n) ⊢ r₀ ≈ CX ^ᶠ c
  r≈ = trans (back _ (ax ax1)) (trans right-unit
         (trans (front _ (trans (back _ (trans (front _ (lift R-zero)) left-unit)) (ax swap-order))) left-unit))

-- The same with the atom of c e₁ for the S's on wire 1.
A-01′ : (c : F*) → (₂₊ n) ⊢ atom (big 1* (proj₁ c ∷ 0ᵛ {n})) ≈ atom e0 • atom (small (big c 0ᵛ)) • CZ h ^ᶠ proj₁ c
A-01′ {n} c = trans (A-01 (proj₁ c)) (sym (cong A-e0 (cong (trans (A-small (big c 0ᵛ)) (lift q≈)) refl)))
  where
  open Width (₂₊ n)
  q≈ : (₁₊ n) ⊢ atom (big c (0ᵛ {n})) ≈ SZ (proj₁ c * proj₁ c) (binom2 (proj₁ c))
  q≈ = Width.trans (A-scale c) (SZ-≡ (FR.*-identityˡ _) (FR.*-identityˡ _))

------------------------------------------------------------------------
-- The atom of (1 , w)

K₀ : Vec F n → Circuit (₂₊ n)
K₀ w = SWAP • K w ↑ • SWAP

-- Prefixing a 0 to w moves everything a wire up, past wire 0.
Q-dec-0 : (w : Vec F n) → (₁₊ n) ⊢ atom (big 1* w) ≈ S h • atomᵛ w ↑ • K w →
          (₂₊ n) ⊢ atom (big 1* (0F ∷ w)) ≈ S h • atomᵛ w ↑ ↑ • K₀ w
Q-dec-0 {n} w IH = begin
  atom (small (big 1* w) ⋆ sw)
    ≈⟨ sym (trans (back _ (A-step (small (big 1* w)) sw)) (trans (sym assoc) (trans (front _ (ax swap-order)) left-unit))) ⟩
  SWAP • A (small (big 1* w)) • SWAP
    ≈⟨ back _ (front _ (trans (A-small (big 1* w)) (lift IH))) ⟩
  SWAP • (S h ↑ • atomᵛ w ↑ ↑ • K w ↑) • SWAP
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (SWAP • S h ↑) • atomᵛ w ↑ ↑ • K w ↑ • SWAP
    ≈⟨ trans (front _ sS↑) assoc ⟩
  S h • SWAP • atomᵛ w ↑ ↑ • K w ↑ • SWAP
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (sym (comm-gate₂-w↑↑ SWAP-gate (atomᵛ w)))) assoc)) ⟩
  S h • atomᵛ w ↑ ↑ • SWAP • K w ↑ • SWAP ∎
  where open Width (₂₊ n)

-- The step from w to (c , w), c ≠ 0 and w ≠ 0: rule (30) on atoms.
Q-dec-row : (c : F*) (ℓ : NZ (₁₊ n)) →
            (₂₊ n) ⊢ atom (big 1* (row ℓ)) ≈ S h • atomᵛ (row ℓ) ↑ • K (row ℓ) →
            (₃₊ n) ⊢ atom (big 1* (proj₁ c ∷ row ℓ)) ≈ S h • atom (big c (row ℓ)) ↑ • K (proj₁ c ∷ row ℓ)
Q-dec-row {n} c ℓ IH = begin
  atom (big 1* (proj₁ c ∷ row ℓ))
    ≈⟨ T3 c ℓ ⟩
  u • (small (big c 0ᵛ)) ᵃ⁻ • atom (big 1* (proj₁ c ∷ 0ᵛ)) • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • atom (big 1* (0F ∷ row ℓ))
    ≈⟨ back _ (back _ (cong (A-01′ c) (back _ (back _ D≈)))) ⟩
  u • (small (big c 0ᵛ)) ᵃ⁻ • (s • q • Zᶜ) • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • (s • v • K')
    ≈⟨ back _ (by-passoc (□ • (□ • □ • □) • □ • □ • (□ • □ • □)) ((□ • □) • □ • □ • □ • □ • □ • □ • □) Eq.refl) ⟩
  u • ((small (big c 0ᵛ)) ᵃ⁻ • s) • q • Zᶜ • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • s • v • K'
    ≈⟨ back _ (trans (front _ (diag∥ dq⁻ (Diag-atom e0))) assoc) ⟩
  u • s • (small (big c 0ᵛ)) ᵃ⁻ • q • Zᶜ • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • s • v • K'
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (atom-invˡ (small (big c 0ᵛ)))) left-unit))) ⟩
  u • s • Zᶜ • (big 1* 0ᵛ) ᵃ⁻ • (small (small ℓ)) ᵃ⁻ • s • v • K'
    ≈⟨ back _ (back _ (back _ (back _ (trans (sym assoc) (trans (front _ (diag∥ dv⁻ (Diag-atom e0))) assoc))))) ⟩
  u • s • Zᶜ • (big 1* 0ᵛ) ᵃ⁻ • s • (small (small ℓ)) ᵃ⁻ • v • K'
    ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (atom-invˡ e0)) left-unit)))) ⟩
  u • s • Zᶜ • (small (small ℓ)) ᵃ⁻ • v • K'
    ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (atom-invˡ (small (small ℓ)))) left-unit)))) ⟩
  u • s • Zᶜ • K'
    ≈⟨ trans (sym assoc) (trans (front _ (diag∥ (Diag-atom (small (big c (row ℓ)))) (Diag-atom e0))) assoc) ⟩
  s • u • Zᶜ • K'
    ≈⟨ cong A-e0 (front _ (A-small (big c (row ℓ)))) ⟩
  S h • atom (big c (row ℓ)) ↑ • Zᶜ • K' ∎
  where
  open Width (₃₊ n)
  u q v s Zᶜ K' : Circuit (₃₊ n)
  u  = atom (small (big c (row ℓ)))
  q  = atom (small (big c 0ᵛ))
  v  = atom (small (small ℓ))
  s  = atom e0
  Zᶜ  = CZ h ^ᶠ proj₁ c
  K' = K₀ (row ℓ)
  D≈ : (₃₊ n) ⊢ atom (big 1* (0F ∷ row ℓ)) ≈ s • v • K'
  D≈ = trans (Q-dec-0 (row ℓ) IH)
         (cong (sym A-e0) (front _ (trans (lift (lift (atomᵛ-row ℓ)))
                                    (trans (lift (Width.sym (A-small ℓ))) (sym (A-small (small ℓ)))))))
  dq⁻ : Diag (₃₊ n) ((small (big c 0ᵛ)) ᵃ⁻)
  dq⁻ = Diag-^ᶠ (Diag-atom (small (big c 0ᵛ))) (- 1F)
  dv⁻ : Diag (₃₊ n) ((small (small ℓ)) ᵃ⁻)
  dv⁻ = Diag-^ᶠ (Diag-atom (small (small ℓ))) (- 1F)

Q-dec-row′ : (c : F*) (ℓ : NZ n) →
             (₁₊ n) ⊢ atom (big 1* (row ℓ)) ≈ S h • atomᵛ (row ℓ) ↑ • K (row ℓ) →
             (₂₊ n) ⊢ atom (big 1* (proj₁ c ∷ row ℓ)) ≈ S h • atom (big c (row ℓ)) ↑ • K (proj₁ c ∷ row ℓ)
Q-dec-row′ {suc n} c ℓ IH = Q-dec-row c ℓ IH
Q-dec-row′ {zero} c () IH

Q-dec : (w : Vec F n) → (₁₊ n) ⊢ atom (big 1* w) ≈ S h • atomᵛ w ↑ • K w
Q-dec [] = Width.trans (A-e0) (Width.sym (Width.trans (Width.back _ _ Width.left-unit) Width.right-unit))
Q-dec {suc n} (c ∷ w) with c ≟ 0F
... | yes e = begin
  atom (big 1* (c ∷ w))                  ≈⟨ atom-≡ (big 1* (c ∷ w)) (big 1* (0F ∷ w)) (Eq.cong (λ t → 1F ∷ t ∷ w) e) ⟩
  atom (big 1* (0F ∷ w))                 ≈⟨ Q-dec-0 w (Q-dec w) ⟩
  S h • atomᵛ w ↑ ↑ • K₀ w               ≈⟨ back _ (back _ (sym (trans (front _ (OCZ.^ᶠ-≡ e)) left-unit))) ⟩
  S h • atomᵛ w ↑ ↑ • CZ h ^ᶠ c • K₀ w   ∎
  where
  open Width (₂₊ n)
  module OCZ = Pow.Order (₂₊ n) {CZ h} CZ-order
... | no nc with nz? w
...   | inj₁ e = Eq.subst (λ v → (₂₊ n) ⊢ atom (big 1* (c ∷ v)) ≈ S h • atom (big (c , nc) v) ↑ • K (c ∷ v))
                         (Eq.sym e) zero-case
  where
  open Width (₂₊ n)
  zero-case : (₂₊ n) ⊢ atom (big 1* (c ∷ 0ᵛ)) ≈ S h • atom (big (c , nc) 0ᵛ) ↑ • K (c ∷ 0ᵛ)
  zero-case = begin
    atom (big 1* (c ∷ 0ᵛ))
      ≈⟨ A-01 c ⟩
    S h • SZ (c * c) (binom2 c) ↑ • CZ h ^ᶠ c
      ≈⟨ back _ (cong (lift (Width.sym (Width.trans (A-scale (c , nc)) (SZ-≡ (FR.*-identityˡ _) (FR.*-identityˡ _)))))
                      (sym (trans (back _ (trans (back _ (trans (front _ (lift K-zero)) left-unit)) (ax swap-order))) right-unit))) ⟩
    S h • atom (big (c , nc) 0ᵛ) ↑ • K (c ∷ 0ᵛ) ∎
...   | inj₂ (ℓ , e) =
  Eq.subst (λ v → (₂₊ n) ⊢ atom (big 1* (c ∷ v)) ≈ S h • atom (big (c , nc) v) ↑ • K (c ∷ v)) e
    (Q-dec-row′ (c , nc) ℓ
      (Eq.subst (λ v → (₁₊ n) ⊢ atom (big 1* v) ≈ S h • atomᵛ v ↑ • K v) (Eq.sym e) (Q-dec w)))

------------------------------------------------------------------------
-- An atom: one wire up, and a form on wire 0

-- The form a row (a , w) leaves on wire 0.
eᴬ : F* → Vec F n → EData n
eᴬ a w = 1F * (proj₁ a * proj₁ a) , 1F * binom2 (proj₁ a) , sc (proj₁ a) w

split-big : (a : F*) (w : Vec F n) → (₁₊ n) ⊢ atom (big a w) ≈ atomᵛ w ↑ • E (eᴬ a w)
split-big {n} a w = begin
  (M⁻ • R w ⁻¹) • S h • R w • M⟨ a ⟩
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  M⁻ • (R w ⁻¹ • S h • R w) • M⟨ a ⟩
    ≈⟨ back _ (front _ (trans Y≈ (Q-dec w))) ⟩
  M⁻ • (S h • atomᵛ w ↑ • K w) • M⟨ a ⟩
    ≈⟨ back _ (trans assoc (back _ (trans assoc (back _ (K-M a w))))) ⟩
  M⁻ • S h • atomᵛ w ↑ • M⟨ a ⟩ • K (sc (proj₁ a) w)
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (comm-gate₁-w↑ (M-gate (proj₁ a) (proj₂ a)) (atomᵛ w))) assoc))) ⟩
  M⁻ • S h • M⟨ a ⟩ • atomᵛ w ↑ • K (sc (proj₁ a) w)
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (Sᶠ-M 1F a)) assoc)) ⟩
  M⁻ • M⟨ a ⟩ • (Z h₁ ^ᶠ β • S h ^ᶠ s) • atomᵛ w ↑ • K (sc (proj₁ a) w)
    ≈⟨ trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit) ⟩
  (Z h₁ ^ᶠ β • S h ^ᶠ s) • atomᵛ w ↑ • K (sc (proj₁ a) w)
    ≈⟨ trans (sym assoc) (trans (front _ (trans (front _ (sym (Sᶠ∥Zᶠ s β))) (SZ-up s β (atomᵛ w)))) assoc) ⟩
  atomᵛ w ↑ • SZ s β • K (sc (proj₁ a) w) ∎
  where
  open Width (₁₊ n)
  M⁻ = M⟨ a ⟩ ⁻¹
  s β : F
  s = 1F * (proj₁ a * proj₁ a)
  β = 1F * binom2 (proj₁ a)
  Y≈ : (₁₊ n) ⊢ R w ⁻¹ • S h • R w ≈ atom (big 1* w)
  Y≈ = sym (cong (Inv.⁻¹-cong (₁₊ n) r≈) (back _ r≈))
    where
    r≈ : (₁₊ n) ⊢ R w • M⟨ 1* ⟩ ≈ R w
    r≈ = trans (back _ (ax ax1)) right-unit

-- An iterate of an atom, split.
split-atom : (ℓ : NZ (₁₊ n)) (k : F) → Σ (DE n × EData n) λ ue →
             (₁₊ n) ⊢ atom ℓ ^ᶠ k ≈ ⟦ proj₁ ue ⟧ᴰ ↑ • E (proj₂ ue)
split-atom {n} (small ℓ) k = (de 0F 0ᵛ ((ℓ , k) ∷ []) , e₀ᴱ) , (begin
  A (small ℓ) ^ᶠ k                       ≈⟨ Pow.pow-cong (₁₊ n) (toℕ k) (A-small ℓ) ⟩
  (atom ℓ ↑) ^ᶠ k                        ≈⟨ refl' (Eq.sym (↑ᶠ (atom ℓ) k)) ⟩
  (atom ℓ ^ᶠ k) ↑                        ≈⟨ lift (Width.sym (Width.trans Width.left-unit
                                              (Width.trans (Width.front n _ Zc-zero) (Width.trans Width.left-unit Width.right-unit)))) ⟩
  ⟦ de 0F 0ᵛ ((ℓ , k) ∷ []) ⟧ᴰ ↑         ≈⟨ sym (trans (back _ E-zero) right-unit) ⟩
  ⟦ de 0F 0ᵛ ((ℓ , k) ∷ []) ⟧ᴰ ↑ • E e₀ᴱ ∎)
  where open Width (₁₊ n)
split-atom {n} (big a w) k = (proj₁ dX , k ·ᴱ eᴬ a w) , (begin
  atom (big a w) ^ᶠ k                    ≈⟨ Pow.pow-cong (₁₊ n) (toℕ k) (split-big a w) ⟩
  (atomᵛ w ↑ • E (eᴬ a w)) ^ᶠ k          ≈⟨ Pow.pow-• (₁₊ n) (toℕ k) (diag∥ (Diag-↑ (Diag-atomᵛ w)) (Diag-E _)) ⟩
  (atomᵛ w ↑) ^ᶠ k • E (eᴬ a w) ^ᶠ k     ≈⟨ cong (trans (refl' (Eq.sym (↑ᶠ (atomᵛ w) k))) (lift (proj₂ dX))) (E-^ᶠ _ k) ⟩
  ⟦ proj₁ dX ⟧ᴰ ↑ • E (k ·ᴱ eᴬ a w)      ∎)
  where
  open Width (₁₊ n)
  dX = Diag-^ᶠ (Diag-atomᵛ w) k

------------------------------------------------------------------------
-- A diagonal expression: one wire up, and a form on wire 0

split-atoms : (as : Atoms (₁₊ n)) → Σ (DE n × EData n) λ ue →
              (₁₊ n) ⊢ atoms as ≈ ⟦ proj₁ ue ⟧ᴰ ↑ • E (proj₂ ue)
split-atoms {n} [] = (de 0F 0ᵛ [] , e₀ᴱ) , sym (trans (cong (lift (Width.sym (proj₂ (Diag-ε {n})))) E-zero) left-unit)
  where open Width (₁₊ n)
split-atoms {n} ((ℓ , k) ∷ as) with split-atom ℓ k | split-atoms as
... | (U₁ , e₁) , p₁ | (U₂ , e₂) , p₂ = (U₁ ⊕ U₂ , e₁ +ᴱ e₂) , (begin
  atom ℓ ^ᶠ k • atoms as                         ≈⟨ cong p₁ p₂ ⟩
  (⟦ U₁ ⟧ᴰ ↑ • E e₁) • ⟦ U₂ ⟧ᴰ ↑ • E e₂          ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ⟦ U₁ ⟧ᴰ ↑ • (E e₁ • ⟦ U₂ ⟧ᴰ ↑) • E e₂          ≈⟨ back _ (front _ (diag∥ (Diag-E e₁) (Diag-↑ (U₂ , Width.refl)))) ⟩
  ⟦ U₁ ⟧ᴰ ↑ • (⟦ U₂ ⟧ᴰ ↑ • E e₁) • E e₂          ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (⟦ U₁ ⟧ᴰ ↑ • ⟦ U₂ ⟧ᴰ ↑) • E e₁ • E e₂          ≈⟨ cong (lift (⊕-sound U₁ U₂)) (E-add e₁ e₂) ⟩
  ⟦ U₁ ⊕ U₂ ⟧ᴰ ↑ • E (e₁ +ᴱ e₂)                  ∎)
  where open Width (₁₊ n)

split : DE (₁₊ n) → DE n × EData n
split (de s (c₀ ∷ c) as) = de s c [] ⊕ proj₁ (proj₁ (split-atoms as)) , (0F , c₀ , 0ᵛ) +ᴱ proj₂ (proj₁ (split-atoms as))

split-sound : (d : DE (₁₊ n)) → (₁₊ n) ⊢ ⟦ d ⟧ᴰ ≈ ⟦ proj₁ (split d) ⟧ᴰ ↑ • E (proj₂ (split d))
split-sound {n} (de s (c₀ ∷ c) as) with split-atoms as
... | (U , e) , pr = begin
  ω h₁ ^ᶠ s • (Z h₁ ^ᶠ c₀ • Zc c ↑) • atoms as
    ≈⟨ back _ (back _ pr) ⟩
  ω h₁ ^ᶠ s • (Z h₁ ^ᶠ c₀ • Zc c ↑) • ⟦ U ⟧ᴰ ↑ • E e
    ≈⟨ trans (front _ (sym (ωᶠ↑ s))) (back _ (trans assoc (back _ (trans (sym assoc) (trans (front _ (diag∥ Dz (Diag-↑ (U , Width.refl)))) assoc))))) ⟩
  (ω h₁ ^ᶠ s) ↑ • Z h₁ ^ᶠ c₀ • ⟦ U ⟧ᴰ ↑ • Zc c ↑ • E e
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (diag∥ Dz₀ (Diag-↑ (U , Width.refl)))) assoc)) ⟩
  (ω h₁ ^ᶠ s) ↑ • ⟦ U ⟧ᴰ ↑ • Z h₁ ^ᶠ c₀ • Zc c ↑ • E e
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (Zᶠ-up c₀ (Zc c))) assoc))) ⟩
  (ω h₁ ^ᶠ s) ↑ • ⟦ U ⟧ᴰ ↑ • Zc c ↑ • Z h₁ ^ᶠ c₀ • E e
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (diag∥ (Diag-↑ (U , Width.refl)) (Diag-↑ (Diag-Zc c)))) assoc)) ⟩
  (ω h₁ ^ᶠ s) ↑ • Zc c ↑ • ⟦ U ⟧ᴰ ↑ • Z h₁ ^ᶠ c₀ • E e
    ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □) • □ • □) Eq.refl ⟩
  ((ω h₁ ^ᶠ s) ↑ • Zc c ↑ • ⟦ U ⟧ᴰ ↑) • Z h₁ ^ᶠ c₀ • E e
    ≈⟨ cong (lift Ud) Ze ⟩
  ⟦ de s c [] ⊕ U ⟧ᴰ ↑ • E ((0F , c₀ , 0ᵛ) +ᴱ e) ∎
  where
  open Width (₁₊ n)
  Dz : Diag (₁₊ n) (Zc c ↑)
  Dz = Diag-↑ (Diag-Zc c)
  Dz₀ : Diag (₁₊ n) (Z h₁ ^ᶠ c₀)
  Dz₀ = Diag-^ᶠ Diag-Z c₀
  Ud : n ⊢ ω h₁ ^ᶠ s • Zc c • ⟦ U ⟧ᴰ ≈ ⟦ de s c [] ⊕ U ⟧ᴰ
  Ud = Width.trans (Width.sym (Width.trans Width.assoc (Width.back n _ (Width.front n _ Width.right-unit))))
                   (⊕-sound (de s c []) U)
  Ze : (₁₊ n) ⊢ Z h₁ ^ᶠ c₀ • E e ≈ E ((0F , c₀ , 0ᵛ) +ᴱ e)
  Ze = trans (front _ (sym (trans (front _ left-unit) (trans (back _ K-zero) right-unit)))) (E-add (0F , c₀ , 0ᵛ) e)
