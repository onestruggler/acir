------------------------------------------------------------------------
-- Presentations of groups
--
-- Rows as linear words, row transport, and inverse words
--
-- The representative r ℓ of a row is a linear word (rL), and a linear
-- generator y carries the row ℓ to ℓ ⋆ y (Linear.Base), whose vector
-- is row ℓ ⋆ᴿ y (row-⋆): a column of Z's moves the same way.  Both
-- extend to words (⋆*, ⋆ᴿ*).  The word rL ℓ writes row ℓ on wire 0,
-- so it carries the column e₀ to row ℓ (e₀-rL), and the fan-in R w is
-- CX conjugated by the representative of w one wire up (CX-r).  Every
-- linear word has an inverse word, generator by generator (linv).  A
-- vector is zero or the row of a representative (nz?), and rows that
-- agree have the same representative (row-r).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Rows
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; _⁻¹* ; _×ᶠ_ ; ×ᶠ-toℕ ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
  using (_⁻¹ ; module Inv ; M-≡ ; M-inverseʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv
  using (⌊↑ₗ⌋ ; ⌊^⌋ ; ⌊Rʷ⌋ ; 0ᵛ ; R-push ; R-zero)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Representatives as words

rL : NZ n → Word (LGen n)
rL (big a w) = Rʷ w • [ mul a ]ʷ
rL (small ℓ) = [ sw ]ʷ • rL ℓ ↑ₗ

⌊rL⌋ : (ℓ : NZ n) → ⌊ rL ℓ ⌋ ≡ r ℓ
⌊rL⌋ (big a w) = Eq.cong (_• M⟨ a ⟩) (⌊Rʷ⌋ w)
⌊rL⌋ (small ℓ) = Eq.cong (SWAP •_) (Eq.trans (⌊↑ₗ⌋ (rL ℓ)) (Eq.cong _↑ (⌊rL⌋ ℓ)))

-- Rows that agree have the same representative.
row-r : (ℓ ℓ' : NZ n) → row ℓ ≡ row ℓ' → r ℓ ≡ r ℓ'
row-r (big a w) (big a' w') e =
  Eq.trans (Eq.cong (λ v → R v • M⟨ a ⟩) (VecP.∷-injectiveʳ e)) (Eq.cong (R w' •_) (M-≡ (VecP.∷-injectiveˡ e)))
row-r (big a w) (small ℓ') e = ⊥-elim (proj₂ a (VecP.∷-injectiveˡ e))
row-r (small ℓ) (big a' w') e = ⊥-elim (proj₂ a' (Eq.sym (VecP.∷-injectiveˡ e)))
row-r (small ℓ) (small ℓ') e = Eq.cong (λ q → SWAP • q ↑) (row-r ℓ ℓ' (VecP.∷-injectiveʳ e))

-- A vector is zero, or a row.
nz? : (w : Vec F n) → (w ≡ 0ᵛ) ⊎ Σ (NZ n) (λ ℓ → row ℓ ≡ w)
nz? [] = inj₁ refl
nz? (c ∷ w) with c ≟ 0F
nz? (c ∷ w) | no nc = inj₂ (big (c , nc) w , refl)
nz? (c ∷ []) | yes e = inj₁ (Eq.cong (_∷ []) e)
nz? (c ∷ w@(_ ∷ _)) | yes e with nz? w
... | inj₁ e'       = inj₁ (Eq.cong₂ _∷_ e e')
... | inj₂ (ℓ , e') = inj₂ (small ℓ , Eq.cong₂ _∷_ (Eq.sym e) e')

------------------------------------------------------------------------
-- Transport along words

infixl 5 _⋆*_ _⋆ᴿ*_

_⋆*_ : NZ n → Word (LGen n) → NZ n
ℓ ⋆* [ y ]ʷ  = ℓ ⋆ y
ℓ ⋆* ε       = ℓ
ℓ ⋆* (L • M) = ℓ ⋆* L ⋆* M

_⋆ᴿ*_ : Vec F n → Word (LGen n) → Vec F n
v ⋆ᴿ* [ y ]ʷ  = v ⋆ᴿ y
v ⋆ᴿ* ε       = v
v ⋆ᴿ* (L • M) = v ⋆ᴿ* L ⋆ᴿ* M

private
  zero-cx : (v : Vec F (₁₊ n)) → 0F ∷ v ≡ (0F ∷ v) ⋆ᴿ cx
  zero-cx (d ∷ w) = Eq.cong (λ t → 0F ∷ t ∷ w) (Eq.sym (FR.+-identityʳ d))

  row-big-sw : (a : F*) (c : F) (w : Vec F n) (d : Dec (c ≡ 0F)) →
               row (big-sw a c w d) ≡ (proj₁ a ∷ c ∷ w) ⋆ᴿ sw
  row-big-sw a c w (yes e) = Eq.cong (λ t → t ∷ proj₁ a ∷ w) (Eq.sym e)
  row-big-sw a c w (no nc) = refl

-- The row of a transported representative.
row-⋆ : (ℓ : NZ n) (y : LGen n) → row (ℓ ⋆ y) ≡ row ℓ ⋆ᴿ y
row-⋆ (big a w)         (y ↥ₗ)  = refl
row-⋆ (small ℓ)         (y ↥ₗ)  = Eq.cong (0F ∷_) (row-⋆ ℓ y)
row-⋆ (big a w)         (mul x) = Eq.cong (_∷ w) (FR.*-comm (proj₁ x) (proj₁ a))
row-⋆ (small ℓ)         (mul x) = Eq.cong (_∷ row ℓ) (Eq.sym (FR.zeroˡ (proj₁ x)))
row-⋆ (big a (c ∷ w))   cx      = refl
row-⋆ (small ℓ)         cx      = zero-cx (row ℓ)
row-⋆ (big a (c ∷ w))   sw      = row-big-sw a c w (c ≟ 0F)
row-⋆ (small (big b w)) sw      = refl
row-⋆ (small (small ℓ)) sw      = refl

row-⋆* : (ℓ : NZ n) (L : Word (LGen n)) → row (ℓ ⋆* L) ≡ row ℓ ⋆ᴿ* L
row-⋆* ℓ [ y ]ʷ  = row-⋆ ℓ y
row-⋆* ℓ ε       = refl
row-⋆* ℓ (L • M) = Eq.trans (row-⋆* (ℓ ⋆* L) M) (Eq.cong (_⋆ᴿ* M) (row-⋆* ℓ L))

-- The zero vector stays.
zero-⋆ᴿ : (y : LGen n) → 0ᵛ ⋆ᴿ y ≡ 0ᵛ
zero-⋆ᴿ (y ↥ₗ) = Eq.cong (0F ∷_) (zero-⋆ᴿ y)
zero-⋆ᴿ (mul x) = Eq.cong (_∷ 0ᵛ) (FR.zeroˡ (proj₁ x))
zero-⋆ᴿ cx      = Eq.cong (λ t → 0F ∷ t ∷ 0ᵛ) (FR.+-identityʳ 0F)
zero-⋆ᴿ sw      = refl

zero-⋆ᴿ* : (L : Word (LGen n)) → 0ᵛ ⋆ᴿ* L ≡ 0ᵛ
zero-⋆ᴿ* [ y ]ʷ  = zero-⋆ᴿ y
zero-⋆ᴿ* ε       = refl
zero-⋆ᴿ* (L • M) = Eq.trans (Eq.cong (_⋆ᴿ* M) (zero-⋆ᴿ* L)) (zero-⋆ᴿ* M)

-- One wire up the head stays.
⋆ᴿ*-↑ : (c : F) (v : Vec F n) (L : Word (LGen n)) → (c ∷ v) ⋆ᴿ* (L ↑ₗ) ≡ c ∷ (v ⋆ᴿ* L)
⋆ᴿ*-↑ c v [ y ]ʷ  = refl
⋆ᴿ*-↑ c v ε       = refl
⋆ᴿ*-↑ c v (L • M) = Eq.trans (Eq.cong (_⋆ᴿ* (M ↑ₗ)) (⋆ᴿ*-↑ c v L)) (⋆ᴿ*-↑ c (v ⋆ᴿ* L) M)

private
  -- m copies of CX add m copies of the head to the next entry.
  cx-pow : (x d : F) (v : Vec F n) (m : ℕ) → (x ∷ d ∷ v) ⋆ᴿ* ([ cx ]ʷ ^ m) ≡ x ∷ d + m ×ᶠ x ∷ v
  cx-pow x d v zero          = Eq.cong (λ t → x ∷ t ∷ v) (Eq.sym (FR.+-identityʳ d))
  cx-pow x d v (suc zero)    = Eq.cong (λ t → x ∷ d + t ∷ v) (Eq.sym (FR.+-identityʳ x))
  cx-pow x d v (suc (suc m)) =
    Eq.trans (cx-pow x (d + x) v (suc m)) (Eq.cong (λ t → x ∷ t ∷ v) (FR.+-assoc d x (suc m ×ᶠ x)))

  e₀-R : (w : Vec F n) → (1F ∷ 0ᵛ) ⋆ᴿ* Rʷ w ≡ 1F ∷ w
  e₀-R []      = refl
  e₀-R (c ∷ w) = begin
    ((1F ∷ 0F ∷ 0ᵛ) ⋆ᴿ sw ⋆ᴿ* Rʷ w ↑ₗ ⋆ᴿ sw) ⋆ᴿ* ([ cx ]ʷ ^ toℕ c)
      ≡⟨ Eq.cong (λ v → (v ⋆ᴿ sw) ⋆ᴿ* ([ cx ]ʷ ^ toℕ c)) (⋆ᴿ*-↑ 0F (1F ∷ 0ᵛ) (Rʷ w)) ⟩
    ((0F ∷ ((1F ∷ 0ᵛ) ⋆ᴿ* Rʷ w)) ⋆ᴿ sw) ⋆ᴿ* ([ cx ]ʷ ^ toℕ c)
      ≡⟨ Eq.cong (λ v → ((0F ∷ v) ⋆ᴿ sw) ⋆ᴿ* ([ cx ]ʷ ^ toℕ c)) (e₀-R w) ⟩
    (1F ∷ 0F ∷ w) ⋆ᴿ* ([ cx ]ʷ ^ toℕ c)
      ≡⟨ cx-pow 1F 0F w (toℕ c) ⟩
    1F ∷ 0F + toℕ c ×ᶠ 1F ∷ w
      ≡⟨ Eq.cong (λ t → 1F ∷ t ∷ w) (Eq.trans (FR.+-identityˡ _) (Eq.trans (×ᶠ-toℕ c 1F) (FR.*-identityʳ c))) ⟩
    1F ∷ c ∷ w ∎
    where open Eq.≡-Reasoning

-- The representative writes its row on wire 0.
e₀-rL : (ℓ : NZ (₁₊ n)) → (1F ∷ 0ᵛ) ⋆ᴿ* rL ℓ ≡ row ℓ
e₀-rL (big a w) = Eq.trans (Eq.cong (_⋆ᴿ mul a) (e₀-R w)) (Eq.cong (_∷ w) (FR.*-identityˡ (proj₁ a)))
e₀-rL (small ℓ) = Eq.trans (⋆ᴿ*-↑ 0F (1F ∷ 0ᵛ) (rL ℓ)) (Eq.cong (0F ∷_) (e₀-rL ℓ))

------------------------------------------------------------------------
-- The fan-in as a conjugate of CX

R-push* : (w : Vec F n) (L : Word (LGen n)) → (₁₊ n) ⊢ R w • ⌊ L ⌋ ↑ ≈ ⌊ L ⌋ ↑ • R (w ⋆ᴿ* L)
R-push* w [ y ]ʷ  = R-push w y
R-push* {n} w ε   = Width.trans Width.right-unit (Width.sym Width.left-unit)
R-push* {n} w (L • M) = begin
  R w • ⌊ L ⌋ ↑ • ⌊ M ⌋ ↑                       ≈⟨ trans (sym assoc) (trans (front _ (R-push* w L)) assoc) ⟩
  ⌊ L ⌋ ↑ • R (w ⋆ᴿ* L) • ⌊ M ⌋ ↑               ≈⟨ back _ (R-push* (w ⋆ᴿ* L) M) ⟩
  ⌊ L ⌋ ↑ • ⌊ M ⌋ ↑ • R (w ⋆ᴿ* L ⋆ᴿ* M)         ≈⟨ sym assoc ⟩
  (⌊ L ⌋ ↑ • ⌊ M ⌋ ↑) • R (w ⋆ᴿ* L ⋆ᴿ* M)       ∎
  where open Width (₁₊ n)

R-e₀ : (₂₊ n) ⊢ R (1F ∷ 0ᵛ {n}) ≈ CX
R-e₀ {n} = trans (front _ (trans (back _ (front _ (lift R-zero))) (trans (back _ left-unit) (ax swap-order)))) left-unit
  where open Width (₂₊ n)

-- CX after the representative of w one wire up adds w to wire 0.
CX-r : (ℓ : NZ (₁₊ n)) → (₂₊ n) ⊢ CX • r ℓ ↑ ≈ r ℓ ↑ • R (row ℓ)
CX-r {n} ℓ = begin
  CX • r ℓ ↑                          ≈⟨ cong (sym R-e₀) (refl' (Eq.cong _↑ (Eq.sym (⌊rL⌋ ℓ)))) ⟩
  R (1F ∷ 0ᵛ) • ⌊ rL ℓ ⌋ ↑            ≈⟨ R-push* (1F ∷ 0ᵛ) (rL ℓ) ⟩
  ⌊ rL ℓ ⌋ ↑ • R ((1F ∷ 0ᵛ) ⋆ᴿ* rL ℓ) ≈⟨ refl' (Eq.cong₂ (λ q v → q ↑ • R v) (⌊rL⌋ ℓ) (e₀-rL ℓ)) ⟩
  r ℓ ↑ • R (row ℓ)                   ∎
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- Inverse words

linv₁ : LGen n → Word (LGen n)
linv₁ cx      = [ cx ]ʷ ^ toℕ (- 1F)
linv₁ sw      = [ sw ]ʷ
linv₁ (mul a) = [ mul (a ⁻¹*) ]ʷ
linv₁ (y ↥ₗ)  = linv₁ y ↑ₗ

linv : Word (LGen n) → Word (LGen n)
linv [ y ]ʷ  = linv₁ y
linv ε       = ε
linv (L • M) = linv M • linv L

linv₁-right : (y : LGen n) → n ⊢ [ ι y ]ʷ • ⌊ linv₁ y ⌋ ≈ ε
linv₁-right cx      = Width.trans (Width.back _ _ (Width.refl' _ (⌊^⌋ [ cx ]ʷ (toℕ (- 1F))))) (CX-invʳ 1F)
linv₁-right sw      = ax swap-order
linv₁-right (mul a) = M-inverseʳ a
linv₁-right (y ↥ₗ)  = Width.trans (Width.back _ _ (Width.refl' _ (⌊↑ₗ⌋ (linv₁ y)))) (lift (linv₁-right y))

linv-right : (L : Word (LGen n)) → n ⊢ ⌊ L ⌋ • ⌊ linv L ⌋ ≈ ε
linv-right [ y ]ʷ = linv₁-right y
linv-right {n} ε  = left-unit
  where open Width n
linv-right {n} (L • M) = begin
  (⌊ L ⌋ • ⌊ M ⌋) • ⌊ linv M ⌋ • ⌊ linv L ⌋
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ⌊ L ⌋ • (⌊ M ⌋ • ⌊ linv M ⌋) • ⌊ linv L ⌋
    ≈⟨ back _ (trans (front _ (linv-right M)) left-unit) ⟩
  ⌊ L ⌋ • ⌊ linv L ⌋
    ≈⟨ linv-right L ⟩
  ε ∎
  where open Width n

⌊linv⌋ : (L : Word (LGen n)) → n ⊢ ⌊ linv L ⌋ ≈ ⌊ L ⌋ ⁻¹
⌊linv⌋ {n} L = Inv.inverseʳ-unique n (linv-right L)
