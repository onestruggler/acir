------------------------------------------------------------------------
-- Presentations of groups
--
-- CCZ: atoms, symmetry, and the controlled CZ
--
-- CCZ (Definition 18) is the product of the atoms of T at the sums of
-- the non-empty subsets of the three wires, with signs:
--
--     CCZ = Aᵀ(x₀) Aᵀ(x₁) Aᵀ(x₂) Aᵀ(x₀+x₂)⁻¹ Aᵀ(x₀+x₁)⁻¹ Aᵀ(x₁+x₂)⁻¹ Aᵀ(x₀+x₁+x₂)
--
-- (CCZ-atoms), so it is diagonal, and the cycle σ of the wires
-- permutes the atoms: σ • CCZ ≈ CCZ • σ (σ-CCZ).  Rule (38) read
-- through σ expands SC on the target of CX ↑ into SC on wires 0, 2 and
-- CCZ; so W SC, the controlled image of CZ, is CCZ (W≈CCZ), and the
-- controlled images of rules (28) and (30) are rules (40) and (41)
-- (W-M, W-CX).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.CCZ
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Fin using (#_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; 1* ; -1* ; _⊛_ ; binom2 ; binom3 ; half ; module FR
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (module Inv ; M-≡ ; CX-order)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invˡ ; CX₂₀-order)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv using (row-⋆* ; _⋆*_)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Two p-2 p-prime lv using (σ ; σ⁻ ; σσ⁻ ; σ⁻σ ; two-σ ; t2)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Control p-2 p-prime lv h gt3 using (W ; c↑)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates p-2 p-prime lv h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Mono p-2 p-prime lv h gt3
  using (Gen₃ ; gen₃ ; term ; vec ; by-labels ; Diag₃-term ; Diag₃-order)

private
  variable
    n : ℕ

  h₂ : 2 ≤ lv
  h₂ = quad₃ h

------------------------------------------------------------------------
-- Conjugates of T by linear words

module _ {m : ℕ} where

  open Width (₁₊ m)

  -- A conjugate of an iterate of T is an iterate of an atom of T.
  conjT : (L : Word (LGen (₁₊ m))) {g : Circuit (₁₊ m)} → (₁₊ m) ⊢ g • ⌊ L ⌋ ≈ ε →
          (k : F) (ℓ : NZ (₁₊ m)) → row (e0 ⋆* L) ≡ row ℓ → (₁₊ m) ⊢ g • T h ^ᶠ k • ⌊ L ⌋ ≈ atomᵀ ℓ ^ᶠ k
  conjT L gL k ℓ e =
    trans (undo-conj L gL)
      (trans (back _ (front _ (Pow.pow-cong (₁₊ m) (toℕ k) T≈)))
        (trans (atomᵀ-conjᶠ e0 L k) (atomᵀ-≡ᶠ (e0 ⋆* L) ℓ k e)))

-- The signs of the atoms of CCZ, and of its cycled atoms.
Lc : List (Fin 7 × F)
Lc = (# 0 , 1F) ∷ (# 1 , 1F) ∷ (# 2 , 1F) ∷ (# 3 , - 1F) ∷ (# 4 , - 1F) ∷ (# 5 , - 1F) ∷ (# 6 , 1F) ∷ []

private
  Lc′ : List (Fin 7 × F)
  Lc′ = (# 1 , 1F) ∷ (# 2 , 1F) ∷ (# 0 , 1F) ∷ (# 4 , - 1F) ∷ (# 5 , - 1F) ∷ (# 3 , - 1F) ∷ (# 6 , 1F) ∷ []

  labels₇ : vec Lc′ ≡ vec Lc
  labels₇ = Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ (con (ℤ.+ 0))))))))) := ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ (con (ℤ.+ 0)))))))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
    (Eq.refl)))))))

------------------------------------------------------------------------
-- CCZ as atoms

module _ {n : ℕ} where

  open Width (₃₊ n)

  -- The rows of the non-empty subsets of the three wires.
  r0 r1 r2 r01 r02 r12 r012 : NZ (₃₊ n)
  r0   = e0
  r1   = small e0
  r2   = small (small e0)
  r01  = big 1* (1F ∷ 0F ∷ 0ᵛ)
  r02  = big 1* (0F ∷ 1F ∷ 0ᵛ)
  r12  = small e₀₁
  r012 = big 1* (1F ∷ 1F ∷ 0ᵛ)

  private
    gA : NZ (₃₊ n) → Gen₃ (₃₊ n)
    gA ℓ = gen₃ (atomᵀ ℓ) (Diag₃-atomᵀ ℓ)

  G₇ : Vec (Gen₃ (₃₊ n)) 7
  G₇ = gA r0 ∷ gA r1 ∷ gA r2 ∷ gA r02 ∷ gA r01 ∷ gA r12 ∷ gA r012 ∷ []

  private
    module OC₂₀ = Pow.Order (₃₊ n) {CX₂₀} CX₂₀-order

    L₂₀ L₆ : Word (LGen (₃₊ n))
    L₂₀ = [ sw ↥ₗ ]ʷ • [ cx ]ʷ • [ sw ↥ₗ ]ʷ
    L₆  = [ cx ]ʷ • [ cx ↥ₗ ]ʷ

    g₁ : (₃₊ n) ⊢ T h ↑ ≈ atomᵀ r1
    g₁ = T↑≈

    g₂ : (₃₊ n) ⊢ T h ↑ ↑ ≈ atomᵀ r2
    g₂ = trans (lift T↑≈) (sym (AT.A-small (e1 {n})))

    g₃ : (₃₊ n) ⊢ CX₂₀ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX₂₀ ≈ atomᵀ r02 ^ᶠ (- 1F)
    g₃ = conjT L₂₀ OC₂₀.inverseˡ (- 1F) r02
           (Eq.trans (row-⋆* e0 L₂₀) (Eq.cong (λ t → 1F ∷ 0F ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F)))

    g₄ : (₃₊ n) ⊢ CX ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX ≈ atomᵀ r01 ^ᶠ (- 1F)
    g₄ = conjT [ cx ]ʷ (CX-invˡ 1F) (- 1F) r01
           (Eq.trans (row-⋆* e0 [ cx ]ʷ) (Eq.cong (λ t → 1F ∷ t ∷ 0F ∷ 0ᵛ) (FR.+-identityˡ 1F)))

    g₅ : (₃₊ n) ⊢ (CX ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • CX ↑ ≈ atomᵀ r12 ^ᶠ (- 1F)
    g₅ = trans (lift two)
           (trans (refl' (↑ᶠ (atomᵀ e₀₁) (- 1F))) (Pow.pow-cong (₃₊ n) (toℕ (- 1F)) (sym (AT.A-small e₀₁))))
      where
      two : (₂₊ n) ⊢ CX ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX ≈ atomᵀ e₀₁ ^ᶠ (- 1F)
      two = conjT [ cx ]ʷ (CX-invˡ 1F) (- 1F) e₀₁
              (Eq.trans (row-⋆* e0 [ cx ]ʷ) (Eq.cong (λ t → 1F ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F)))

    g₆ : (₃₊ n) ⊢ ((CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F)) • T h • CX • CX ↑ ≈ atomᵀ r012
    g₆ = conjT L₆ g6L 1F r012
           (Eq.trans (row-⋆* e0 L₆)
             (Eq.cong₂ (λ s t → 1F ∷ s ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F)
                       (Eq.trans (FR.+-identityˡ (0F + 1F)) (FR.+-identityˡ 1F))))
      where
      g6L : (₃₊ n) ⊢ ((CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F)) • CX • CX ↑ ≈ ε
      g6L = begin
        ((CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F)) • CX • CX ↑   ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
        (CX ^ᶠ (- 1F)) ↑ • (CX ^ᶠ (- 1F) • CX) • CX ↑   ≈⟨ back _ (trans (front _ (CX-invˡ 1F)) left-unit) ⟩
        (CX ^ᶠ (- 1F)) ↑ • CX ↑                         ≈⟨ lift (CX-invˡ 1F) ⟩
        ε                                               ∎

  CCZ-atoms : (₃₊ n) ⊢ CCZ h ≈ term G₇ Lc
  CCZ-atoms = begin
    CCZ h
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □)
                   (□ • □ • □ • (□ • □ • □) • (□ • □ • □) • (□ • □ • □) • ((□ • □) • □ • □ • □)) Eq.refl ⟩
    T h • T h ↑ • T h ↑ ↑ • (CX₂₀ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX₂₀) • (CX ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX)
      • ((CX ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • CX ↑) • (((CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F)) • T h • CX • CX ↑)
      ≈⟨ cong T≈ (cong g₁ (cong g₂ (cong g₃ (cong g₄ (cong g₅ (trans g₆ (sym right-unit))))))) ⟩
    term G₇ Lc ∎

  Diag₃-CCZ : Diag₃ (₃₊ n) (CCZ h)
  Diag₃-CCZ = Diag₃-≈ CCZ-atoms (Diag₃-term G₇ Lc)

------------------------------------------------------------------------
-- The cycle of the wires fixes CCZ

module _ {n : ℕ} where

  open Width (₃₊ n)

  private
    Lσ : Word (LGen (₃₊ n))
    Lσ = [ sw ↥ₗ ]ʷ • [ sw ]ʷ

    -- σ carries the atom of a row to the atom of the cycled row.
    σA : (ℓ ℓ' : NZ (₃₊ n)) → row (ℓ ⋆* Lσ) ≡ row ℓ' → (k : F) → (₃₊ n) ⊢ σ • atomᵀ ℓ ^ᶠ k ≈ atomᵀ ℓ' ^ᶠ k • σ
    σA ℓ ℓ' e k = begin
      σ • atomᵀ ℓ ^ᶠ k                    ≈⟨ sym (back _ (cancel-at σ⁻σ _)) ⟩
      σ • atomᵀ ℓ ^ᶠ k • σ⁻ • σ           ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) (front _ conj) ⟩
      atomᵀ ℓ' ^ᶠ k • σ                   ∎
      where
      conj : (₃₊ n) ⊢ σ • atomᵀ ℓ ^ᶠ k • σ⁻ ≈ atomᵀ ℓ' ^ᶠ k
      conj = trans (undo-conj Lσ σσ⁻) (trans (atomᵀ-conjᶠ ℓ Lσ k) (atomᵀ-≡ᶠ (ℓ ⋆* Lσ) ℓ' k e))

  σ-CCZ : (₃₊ n) ⊢ σ • CCZ h ≈ CCZ h • σ
  σ-CCZ = begin
    σ • CCZ h                 ≈⟨ back _ CCZ-atoms ⟩
    σ • term G₇ Lc            ≈⟨ slide (σA r0 r1 (row-⋆* r0 Lσ) 1F)
                                 (slide (σA r1 r2 (row-⋆* r1 Lσ) 1F)
                                 (slide (σA r2 r0 (row-⋆* r2 Lσ) 1F)
                                 (slide (σA r02 r01 (row-⋆* r02 Lσ) (- 1F))
                                 (slide (σA r01 r12 (row-⋆* r01 Lσ) (- 1F))
                                 (slide (σA r12 r02 (row-⋆* r12 Lσ) (- 1F))
                                 (slide (σA r012 r012 (row-⋆* r012 Lσ) 1F) slide-ε)))))) ⟩
    term G₇ Lc′ • σ           ≈⟨ front _ (trans (by-labels G₇ Lc′ Lc labels₇) (sym CCZ-atoms)) ⟩
    CCZ h • σ                 ∎

------------------------------------------------------------------------
-- The controlled CZ is CCZ

module _ {n : ℕ} where

  open Width (₃₊ n)

  private
    SC₀₂ : Circuit (₃₊ n)
    SC₀₂ = SWAP • SC ↑ • SWAP

    ss : (₃₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

    tt : (₃₊ n) ⊢ SWAP ↑ • SWAP ↑ ≈ ε
    tt = lift (ax swap-order)

    σ-CS₂₀ : (₃₊ n) ⊢ σ • CS₂₀ h ≈ SC • σ
    σ-CS₂₀ = begin
      (SWAP • SWAP ↑) • SWAP ↑ • CS h • SWAP ↑   ≈⟨ trans assoc (back _ (cancel-in tt _)) ⟩
      SWAP • CS h • SWAP ↑                       ≈⟨ back _ (back _ (sym (cancel-in ss _))) ⟩
      SWAP • CS h • SWAP • SWAP • SWAP ↑         ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □) • □ • □) Eq.refl ⟩
      SC • σ                                     ∎

    σ-CS↑ : (₃₊ n) ⊢ σ • CS h ↑ ≈ SC₀₂ • σ
    σ-CS↑ = begin
      (SWAP • SWAP ↑) • CS h ↑                         ≈⟨ trans assoc (back _ (back _ (sym (cancel-at tt _)))) ⟩
      SWAP • SWAP ↑ • CS h ↑ • SWAP ↑ • SWAP ↑         ≈⟨ back _ (back _ (back _ (back _ (sym (cancel-in ss _))))) ⟩
      SWAP • SWAP ↑ • CS h ↑ • SWAP ↑ • SWAP • SWAP • SWAP ↑
        ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) ((□ • (□ • □ • □) • □) • □ • □) Eq.refl ⟩
      SC₀₂ • σ                                         ∎

    -- Rule (38) through σ: SC on the target of CX ↑.
    rule38 : (₃₊ n) ⊢ CX ↑ • SC • SC₀₂ • CCZ h ≈ SC • CX ↑
    rule38 = Inv.•-cancelʳ (₃₊ n) (begin
      (CX ↑ • SC • SC₀₂ • CCZ h) • σ   ≈⟨ sym (slide (two-σ (t2 CX-gate)) (slide σ-CS₂₀ (slide σ-CS↑ σ-CCZ))) ⟩
      σ • CX • CS₂₀ h • CS h ↑ • CCZ h  ≈⟨ back _ (ax (ax38 h)) ⟩
      σ • CS₂₀ h • CX                   ≈⟨ slide σ-CS₂₀ (two-σ (t2 CX-gate)) ⟩
      (SC • CX ↑) • σ                   ∎)

    module OSC = Pow.Order (₃₊ n) {SC} (Diag₃-order Diag₃-SC)
    module OSC₀₂ = Pow.Order (₃₊ n) {SC₀₂} (Diag₃-order (Diag₃-SWAP (Diag₃-↑ Diag₃-SC)))

    CX↑-inv : (₃₊ n) ⊢ (CX ↑) ^ᶠ (- 1F) • CX ↑ ≈ ε
    CX↑-inv = trans (front _ (refl' (Eq.sym (↑ᶠ CX (- 1F))))) (lift (CX-invˡ 1F))

  W≈CCZ : (₃₊ n) ⊢ W SC ≈ CCZ h
  W≈CCZ = begin
    SC ^ᶠ (- 1F) • SC₀₂ ^ᶠ (- 1F) • (CX ↑) ^ᶠ (- 1F) • SC • CX ↑
      ≈⟨ back _ (back _ (back _ (sym rule38))) ⟩
    SC ^ᶠ (- 1F) • SC₀₂ ^ᶠ (- 1F) • (CX ↑) ^ᶠ (- 1F) • CX ↑ • SC • SC₀₂ • CCZ h
      ≈⟨ back _ (back _ (cancel-in CX↑-inv _)) ⟩
    SC ^ᶠ (- 1F) • SC₀₂ ^ᶠ (- 1F) • SC • SC₀₂ • CCZ h
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (diag₃∥ (Diag₃-^ᶠ (Diag₃-SWAP (Diag₃-↑ Diag₃-SC)) (- 1F)) Diag₃-SC)) assoc)) ⟩
    SC ^ᶠ (- 1F) • SC • SC₀₂ ^ᶠ (- 1F) • SC₀₂ • CCZ h
      ≈⟨ cancel-in OSC.inverseˡ _ ⟩
    SC₀₂ ^ᶠ (- 1F) • SC₀₂ • CCZ h
      ≈⟨ cancel-in OSC₀₂.inverseˡ _ ⟩
    CCZ h ∎

------------------------------------------------------------------------
-- The controlled rules (28) and (30)

private
  M-sq : (₁₊ n) ⊢ M⟨ -1* ⟩ • M⟨ -1* ⟩ ≈ ε
  M-sq {n} = Width.trans (ax (ax2 -1* -1*))
               (Width.trans (Width.refl' (₁₊ n) (M-≡ (solve 0 ((:- con (ℤ.+ 1)) :* (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl)))
                            (ax ax1))

W-M : (₃₊ n) ⊢ (SWAP • M⟨ -1* ⟩ ↑ ↑ • SWAP) • W SC ^ toℕ (- 1F) • SWAP • M⟨ -1* ⟩ ↑ ↑ • SWAP ≈ W SC
W-M {n} = begin
  (SWAP • m • SWAP) • W SC ^ toℕ (- 1F) • SWAP • m • SWAP
    ≈⟨ cong (c↑ M⟨ -1* ⟩) (cong (Pow.pow-cong (₃₊ n) (toℕ (- 1F)) W≈CCZ) (c↑ M⟨ -1* ⟩)) ⟩
  m • CCZ h ^ᶠ (- 1F) • m
    ≈⟨ trans (sym assoc) (front _ (ax (ax40 h -1*))) ⟩
  (CCZ h • m) • m
    ≈⟨ trans assoc (cancel-at (lift (lift M-sq)) _) ⟩
  CCZ h
    ≈⟨ sym W≈CCZ ⟩
  W SC ∎
  where
  open Width (₃₊ n)
  m : Circuit (₃₊ n)
  m = M⟨ -1* ⟩ ↑ ↑

W-CX : (₄₊ n) ⊢ W SC • SWAP • CX ↑ ↑ • SWAP ≈
       (SWAP • CX ↑ ↑ • SWAP) • W SC • (SWAP • SWAP ↑ ↑ • SWAP) • W SC • SWAP • SWAP ↑ ↑ • SWAP
W-CX {n} = begin
  W SC • SWAP • CX ↑ ↑ • SWAP
    ≈⟨ cong W≈CCZ (c↑ CX) ⟩
  CCZ h • CX ↑ ↑
    ≈⟨ sym (ax (ax41 h)) ⟩
  CX ↑ ↑ • CCZ₃₁₀ h • CCZ h
    ≈⟨ back _ (diag₃∥ D310 Diag₃-CCZ) ⟩
  CX ↑ ↑ • CCZ h • SWAP ↑ ↑ • CCZ h • SWAP ↑ ↑
    ≈⟨ sym (cong (c↑ CX) (cong W≈CCZ (cong (c↑ SWAP) (cong W≈CCZ (c↑ SWAP))))) ⟩
  (SWAP • CX ↑ ↑ • SWAP) • W SC • (SWAP • SWAP ↑ ↑ • SWAP) • W SC • SWAP • SWAP ↑ ↑ • SWAP ∎
  where
  open Width (₄₊ n)
  D310 : Diag₃ (₄₊ n) (CCZ₃₁₀ h)
  D310 = Diag₃-conj Diag₃-CCZ [ sw ↥ₗ ↥ₗ ]ʷ (lift (lift (ax swap-order)))
