------------------------------------------------------------------------
-- Presentations of groups
--
-- Wire-0 forms at level 3
--
-- On ₁₊ n wires write x = (x₀ , x').  A wire-0 form of level 3 has
-- phase
--
--     t (x₀ choose 3) + (x₀ choose 2) (s + c · x') + x₀ g(x')
--
-- with g the phase of a diagonal expression of level 2: it is
--
--     E₃ (t , (s , c) , g) = T ^ t • ctrl₂* (ω ^ s • Zc c) • ctrl* ⟦ g ⟧ᴰ
--
-- with the two controlled circuits of Phase.Cube.Ctrl.  These forms
-- are diagonal (Diag₃-E₃), multiply by adding their data (E₃-add), take
-- iterates by scaling it (E₃-^ᶠ), and contain the wire-0 forms of level
-- 2 (E-E₃).  CS and SC conjugated by a linear word one wire up are the
-- controlled conjugates of Z and S (CS-conj, SC-conj).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.EForm3
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Fin.Base using (zero ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc ; s≤s ; z≤n)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

import Examples.Groups.Qupit-Phase-Affine.Syntactics as Syntactics′
import Examples.Groups.Qupit-Phase-Affine.Reasoning as Reasoning′
import Examples.Groups.Qupit-Phase-Affine.Basic as Basic′
import Examples.Groups.Qupit-Phase-Affine.Linear.Base as Linear′
import Examples.Groups.Qupit-Phase-Affine.Linear.Rows as Rows′
import Examples.Groups.Qupit-Phase-Affine.Linear.Fan as Fan′
import Examples.Groups.Qupit-Phase-Affine.Phase.Linear as PLinear′
import Examples.Groups.Qupit-Phase-Affine.Phase.LinearDE as LinearDE′
import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.EForm as QEForm′

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; 0F ; 1F ; 1* ; _+_ ; _*_ ; big⇒odd ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; ⌊↑ₗ⌋)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates p-2 p-prime lv h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Ctrl p-2 p-prime lv h gt3 using (module C1 ; module C2)

private
  variable
    n : ℕ

  odd : 1 ≤ p-2
  odd = big⇒odd gt3

  h₁₁ : 1 ≤ 1
  h₁₁ = s≤s z≤n

  h₂₂ : 2 ≤ 2
  h₂₂ = s≤s (s≤s z≤n)

-- Levels 1 and 2.
module S1 = Syntactics′ p-2 p-prime 1
module S2 = Syntactics′ p-2 p-prime 2
module R1 = Reasoning′ p-2 p-prime 1
module R2 = Reasoning′ p-2 p-prime 2
module B1 = Basic′ p-2 p-prime 1
module B2 = Basic′ p-2 p-prime 2
module LB1 = Linear′ p-2 p-prime 1
module LB2 = Linear′ p-2 p-prime 2
module F1 = Fan′ p-2 p-prime 1
module F2 = Fan′ p-2 p-prime 2
module RW1 = Rows′ p-2 p-prime 1
module RW2 = Rows′ p-2 p-prime 2
module P1 = PLinear′ p-2 p-prime 1 h₁₁
module L1 = LinearDE′ p-2 p-prime 1 h₁₁
module Q2 = QEForm′ p-2 p-prime 2 h₂₂ odd

------------------------------------------------------------------------
-- The forms

E3Data : ℕ → Set
E3Data n = F × L1.LD n × Q2.DE n

E₃ : E3Data n → Circuit (₁₊ n)
E₃ (t , l , g) = T h ^ᶠ t • C2.ctrl* L1.⟦ l ⟧ˡ • C1.ctrl* Q2.⟦ g ⟧ᴰ

------------------------------------------------------------------------
-- They are diagonal

private
  D2Zc : (c : Vec F n) → Diag₃ (₁₊ n) (C2.ctrl* (P1.Zc c))
  D2Zc []      = Diag₃-ε
  D2Zc (a ∷ c) = Diag₃-• (Diag₃-≈ (C2.pw (S1.Z h₁₁) (toℕ a)) (Diag₃-^ Diag₃-CS (toℕ a)))
                         (Diag₃-≈ (C2.ctrl*-↑ (P1.Zc c)) (Diag₃-SWAP (Diag₃-↑ (D2Zc c))))

  D1Zc : (c : Vec F n) → Diag₃ (₁₊ n) (C1.ctrl* (Q2.Zc c))
  D1Zc []      = Diag₃-ε
  D1Zc (a ∷ c) = Diag₃-• (Diag₃-≈ (C1.pw (S2.Z (S2.lin₂ h₂₂)) (toℕ a)) (Diag₃-^ (Diag₃-2 Diag-CZ) (toℕ a)))
                         (Diag₃-≈ (C1.ctrl*-↑ (Q2.Zc c)) (Diag₃-SWAP (Diag₃-↑ (D1Zc c))))

-- A representative of level 2, controlled, is its word one wire up.
ctrl-r : (ℓ : LB2.NZ n) → (₁₊ n) ⊢ C1.ctrl* (LB2.r ℓ) ≈ ⌊ C1.untr* (RW2.rL ℓ) ⌋ ↑
ctrl-r {n} ℓ = Width.trans (Width.refl' (₁₊ n) (Eq.cong C1.ctrl* (Eq.sym (RW2.⌊rL⌋ ℓ)))) (C1.ctrl-lin′ (RW2.rL ℓ))

-- A conjugate of a diagonal by a linear word one wire up is diagonal.
Diag₃-conj↑ : {D : Circuit (₂₊ n)} → Diag₃ (₂₊ n) D → (L : Word (LGen (₁₊ n))) →
              Diag₃ (₂₊ n) ((⌊ L ⌋ ↑) ⁻¹ • D • ⌊ L ⌋ ↑)
Diag₃-conj↑ {n} dD L =
  Diag₃-≈ (Width.back (₂₊ n) _ (Width.back (₂₊ n) _ (Width.refl' (₂₊ n) (Eq.sym (⌊↑ₗ⌋ L)))))
    (Diag₃-conj dD (L ↑ₗ) (Width.trans (Width.back (₂₊ n) _ (Width.refl' (₂₊ n) (⌊↑ₗ⌋ L))) (Inv.inverseˡ (₂₊ n))))

private
  D1atom : (ℓ : LB2.NZ n) → Diag₃ (₁₊ n) (C1.ctrl* (Q2.atom ℓ))
  D1atom {suc m} ℓ = Diag₃-≈ e (Diag₃-conj↑ Diag₃-SC (C1.untr* (RW2.rL ℓ)))
    where
    open Width (₂₊ m)
    ρ : Circuit (₂₊ m)
    ρ = ⌊ C1.untr* (RW2.rL ℓ) ⌋ ↑
    e : (₂₊ m) ⊢ C1.ctrl* (LB2.r ℓ B2.⁻¹) • SC • C1.ctrl* (LB2.r ℓ) ≈ ρ ⁻¹ • SC • ρ
    e = cong (trans (C1.ctrl-⁻¹ (LB2.r ℓ)) (Inv.⁻¹-cong (₂₊ m) (ctrl-r ℓ))) (back _ (ctrl-r ℓ))

  D1atoms : (as : Q2.Atoms n) → Diag₃ (₁₊ n) (C1.ctrl* (Q2.atoms as))
  D1atoms []             = Diag₃-ε
  D1atoms ((ℓ , k) ∷ as) = Diag₃-• (Diag₃-≈ (C1.pw (Q2.atom ℓ) (toℕ k)) (Diag₃-^ (D1atom ℓ) (toℕ k))) (D1atoms as)

Diag₃-C2 : (l : L1.LD n) → Diag₃ (₁₊ n) (C2.ctrl* L1.⟦ l ⟧ˡ)
Diag₃-C2 (s , c) = Diag₃-• (Diag₃-≈ (C2.pw (S1.ω h₁₁) (toℕ s)) (Diag₃-^ (Diag₃-2 Diag-S) (toℕ s))) (D2Zc c)

Diag₃-C1 : (g : Q2.DE n) → Diag₃ (₁₊ n) (C1.ctrl* Q2.⟦ g ⟧ᴰ)
Diag₃-C1 (Q2.de s c as) =
  Diag₃-• (Diag₃-≈ (C1.pw (S2.ω (S2.lin₂ h₂₂)) (toℕ s)) (Diag₃-^ (Diag₃-2 Diag-Z) (toℕ s))) (Diag₃-• (D1Zc c) (D1atoms as))

Diag₃-E₃ : (e : E3Data n) → Diag₃ (₁₊ n) (E₃ e)
Diag₃-E₃ (t , l , g) = Diag₃-• (Diag₃-^ᶠ Diag₃-T t) (Diag₃-• (Diag₃-C2 l) (Diag₃-C1 g))

------------------------------------------------------------------------
-- Their algebra

infixl 6 _+³_
_+³_ : E3Data n → E3Data n → E3Data n
(t , l , g) +³ (t' , l' , g') = t + t' , l L1.+ˡ l' , g Q2.⊕ g'

_·³_ : F → E3Data n → E3Data n
k ·³ (t , l , g) = t * k , k L1.·ˡ l , proj₁ (Q2.Diag-^ᶠ (g , R2.Width.refl) k)

e₃₀ : E3Data n
e₃₀ = 0F , L1.ld₀ , proj₁ Q2.Diag-ε

module _ {n : ℕ} where

  open Width (₁₊ n)

  private
    module OT = Pow.Order (₁₊ n) {T h} T-order

    -- Three factors and three factors, commuting across.
    shuffle : {a b c a' b' c' : Circuit (₁₊ n)} → (₁₊ n) ⊢ b ∥ a' → (₁₊ n) ⊢ c ∥ a' → (₁₊ n) ⊢ c ∥ b' →
              (₁₊ n) ⊢ (a • b • c) • (a' • b' • c') ≈ (a • a') • (b • b') • (c • c')
    shuffle {a} {b} {c} {a'} {b'} {c'} ba' ca' cb' = begin
      (a • b • c) • a' • b' • c'          ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      a • b • (c • a') • b' • c'          ≈⟨ back _ (back _ (front _ ca')) ⟩
      a • b • (a' • c) • b' • c'          ≈⟨ back _ (by-passoc (□ • (□ • □) • □ • □) ((□ • □) • (□ • □) • □) Eq.refl) ⟩
      a • (b • a') • (c • b') • c'        ≈⟨ back _ (cong ba' (front _ cb')) ⟩
      a • (a' • b) • (b' • c) • c'        ≈⟨ by-passoc (□ • (□ • □) • (□ • □) • □) ((□ • □) • (□ • □) • (□ • □)) Eq.refl ⟩
      (a • a') • (b • b') • (c • c')      ∎

  E₃-add : (e e' : E3Data n) → (₁₊ n) ⊢ E₃ e • E₃ e' ≈ E₃ (e +³ e')
  E₃-add (t , l , g) (t' , l' , g') = begin
    E₃ (t , l , g) • E₃ (t' , l' , g')
      ≈⟨ shuffle (diag₃∥ (Diag₃-C2 l) (Diag₃-^ᶠ Diag₃-T t')) (diag₃∥ (Diag₃-C1 g) (Diag₃-^ᶠ Diag₃-T t'))
                 (diag₃∥ (Diag₃-C1 g) (Diag₃-C2 l')) ⟩
      (T h ^ᶠ t • T h ^ᶠ t') • (C2.ctrl* L1.⟦ l ⟧ˡ • C2.ctrl* L1.⟦ l' ⟧ˡ) • (C1.ctrl* Q2.⟦ g ⟧ᴰ • C1.ctrl* Q2.⟦ g' ⟧ᴰ)
      ≈⟨ cong (OT.^ᶠ-+ t t') (cong (C2.ctrl-cong (L1.ld-add l l')) (C1.ctrl-cong (Q2.⊕-sound g g'))) ⟩
    E₃ ((t , l , g) +³ (t' , l' , g')) ∎

  E₃-^ᶠ : (e : E3Data n) (k : F) → (₁₊ n) ⊢ E₃ e ^ᶠ k ≈ E₃ (k ·³ e)
  E₃-^ᶠ (t , l , g) k = begin
    (T h ^ᶠ t • Ca • Cb) ^ᶠ k
      ≈⟨ Pow.pow-• (₁₊ n) (toℕ k) (∥-• (diag₃∥ (Diag₃-^ᶠ Diag₃-T t) (Diag₃-C2 l)) (diag₃∥ (Diag₃-^ᶠ Diag₃-T t) (Diag₃-C1 g))) ⟩
    (T h ^ᶠ t) ^ᶠ k • (Ca • Cb) ^ᶠ k
      ≈⟨ back _ (Pow.pow-• (₁₊ n) (toℕ k) (diag₃∥ (Diag₃-C2 l) (Diag₃-C1 g))) ⟩
    (T h ^ᶠ t) ^ᶠ k • Ca ^ᶠ k • Cb ^ᶠ k
      ≈⟨ cong (OT.^ᶠ-* t k)
              (cong (trans (sym (C2.pw _ (toℕ k))) (C2.ctrl-cong (L1.ld-^ᶠ l k)))
                    (trans (sym (C1.pw _ (toℕ k))) (C1.ctrl-cong (proj₂ (Q2.Diag-^ᶠ (g , R2.Width.refl) k))))) ⟩
    E₃ (k ·³ (t , l , g)) ∎
    where
    Ca Cb : Circuit (₁₊ n)
    Ca = C2.ctrl* L1.⟦ l ⟧ˡ
    Cb = C1.ctrl* Q2.⟦ g ⟧ᴰ

  E₃-zero : (₁₊ n) ⊢ E₃ (e₃₀ {n}) ≈ ε
  E₃-zero = trans left-unit (trans (cong (C2.ctrl-cong L1.ld-zero) (C1.ctrl-cong (R2.Width.sym (proj₂ Q2.Diag-ε)))) left-unit)

------------------------------------------------------------------------
-- The wire-0 forms of level 2

-- The fan of CZ is x₀ times a column.
K-ctrl : (α : Vec F n) → (₁₊ n) ⊢ K α ≈ C1.ctrl* (Q2.Zc α)
K-ctrl {n} []      = Width.refl
K-ctrl {suc n} (a ∷ α) =
  sym (cong (C1.pw (S2.Z (S2.lin₂ h₂₂)) (toℕ a)) (trans (C1.ctrl*-↑ (Q2.Zc α)) (back _ (front _ (lift (Width.sym (K-ctrl α)))))))
  where open Width (₂₊ n)

eE : EData n → E3Data n
eE (d , c , α) = 0F , (d , F1.0ᵛ) , Q2.de c α []

E-E₃ : (e : EData n) → (₁₊ n) ⊢ E e ≈ E₃ (eE e)
E-E₃ {n} (d , c , α) = begin
  (S h₂ ^ᶠ d • Z h₁ ^ᶠ c) • K α
    ≈⟨ cong (cong (sym (C2.pw (S1.ω h₁₁) (toℕ d))) (sym (C1.pw (S2.ω (S2.lin₂ h₂₂)) (toℕ c)))) (K-ctrl α) ⟩
  (C2.ctrl* (S1.ω h₁₁ ^ toℕ d) • C1.ctrl* (S2.ω (S2.lin₂ h₂₂) ^ toℕ c)) • C1.ctrl* (Q2.Zc α)
    ≈⟨ trans assoc (trans (sym left-unit) (back _ (cong (sym (trans (back _ (C2.ctrl-cong P1.Zc-zero)) right-unit))
                                                       (back _ (sym right-unit))))) ⟩
  E₃ (0F , (d , F1.0ᵛ) , Q2.de c α []) ∎
  where
  open Width (₁₊ n)
  h₂ : 2 ≤ lv
  h₂ = quad₃ h
  h₁ : 1 ≤ lv
  h₁ = lin₃ h

------------------------------------------------------------------------
-- CS and SC conjugated by a linear word one wire up

-- Level 2: S conjugated by a linear word is an atom.
private
  S-conj₂ : (L : Word (LB2.LGen (₁₊ n))) →
            (₁₊ n) S2.⊢ LB2.⌊ L ⌋ B2.⁻¹ • S2.S h₂₂ • LB2.⌊ L ⌋ ≈ Q2.⟦ Q2.de 0F F2.0ᵛ ((LB2.big 1* F2.0ᵛ RW2.⋆* L , 1F) ∷ []) ⟧ᴰ
  S-conj₂ {n} L = begin
    LB2.⌊ L ⌋ B2.⁻¹ • S2.S h₂₂ • LB2.⌊ L ⌋
      ≈⟨ back _ (front _ (Q2.S-e zero)) ⟩
    LB2.⌊ L ⌋ B2.⁻¹ • Q2.A (LB2.big 1* F2.0ᵛ) • LB2.⌊ L ⌋
      ≈⟨ Q2.A-conj (LB2.big 1* F2.0ᵛ) L ⟩
    Q2.A (LB2.big 1* F2.0ᵛ RW2.⋆* L)
      ≈⟨ sym (trans left-unit (trans (front _ Q2.Zc-zero) (trans left-unit right-unit))) ⟩
    Q2.⟦ Q2.de 0F F2.0ᵛ ((LB2.big 1* F2.0ᵛ RW2.⋆* L , 1F) ∷ []) ⟧ᴰ ∎
    where open R2.Width (₁₊ n)

module _ {m : ℕ} where

  open Width (₂₊ m)

  CS-conj : (L : Word (LGen (₁₊ m))) →
            (₂₊ m) ⊢ (⌊ L ⌋ ↑) ⁻¹ • CS h • ⌊ L ⌋ ↑ ≈ C2.ctrl* L1.⟦ 0F , (1F ∷ F1.0ᵛ) RW1.⋆ᴿ* C2.trL* L ⟧ˡ
  CS-conj L = begin
    (⌊ L ⌋ ↑) ⁻¹ • CS h • ⌊ L ⌋ ↑
      ≈⟨ sym (cong (trans (C2.ctrl-⁻¹ L₁) (Inv.⁻¹-cong (₂₊ m) (C2.ctrl-lin L))) (back _ (C2.ctrl-lin L))) ⟩
    C2.ctrl* (L₁ B1.⁻¹ • S1.Z h₁₁ • L₁)
      ≈⟨ C2.ctrl-cong (L1.Z-conj (C2.trL* L)) ⟩
    C2.ctrl* L1.⟦ 0F , (1F ∷ F1.0ᵛ) RW1.⋆ᴿ* C2.trL* L ⟧ˡ ∎
    where
    L₁ = LB1.⌊ C2.trL* L ⌋

  SC-conj : (L : Word (LGen (₁₊ m))) →
            (₂₊ m) ⊢ (⌊ L ⌋ ↑) ⁻¹ • SC • ⌊ L ⌋ ↑ ≈ C1.ctrl* Q2.⟦ Q2.de 0F F2.0ᵛ ((LB2.big 1* F2.0ᵛ RW2.⋆* C1.trL* L , 1F) ∷ []) ⟧ᴰ
  SC-conj L = begin
    (⌊ L ⌋ ↑) ⁻¹ • SC • ⌊ L ⌋ ↑
      ≈⟨ sym (cong (trans (C1.ctrl-⁻¹ L₂) (Inv.⁻¹-cong (₂₊ m) (C1.ctrl-lin L))) (back _ (C1.ctrl-lin L))) ⟩
    C1.ctrl* (L₂ B2.⁻¹ • S2.S h₂₂ • L₂)
      ≈⟨ C1.ctrl-cong (S-conj₂ (C1.trL* L)) ⟩
    C1.ctrl* Q2.⟦ Q2.de 0F F2.0ᵛ ((LB2.big 1* F2.0ᵛ RW2.⋆* C1.trL* L , 1F) ∷ []) ⟧ᴰ ∎
    where
    L₂ = LB2.⌊ C1.trL* L ⌋
