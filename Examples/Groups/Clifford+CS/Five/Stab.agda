------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits fixing 0 and e₀
--
-- An affine circuit (Blake's Aff_d at p = 2, Five.Affine) whose map fixes
-- the basis states 0 and e₀ is equal to a linear circuit on the wires
-- above 0 followed by a fan-in onto wire 0 (`stab`): every letter of the
-- result fixes 0 and e₀ — CX and SWAP on adjacent wires above 0, and CX
-- from wire 1 onto wire 0 — which is what the independence of the
-- affine decoding needs.
--
-- The proof reads Blake's normal forms.  The circuit is the translation
-- Xc b after a linear word L (Completeness.Aff), and L is W ↑ · col v ·
-- r ℓ (Linear.Steps); its value at 0 is b, so b = 0; its value at e₀
-- has head the first entry of the row ℓ, so ℓ is a big row with unit 1
-- and r ℓ is the fan-in R w, and the rest of the value at e₀ is W v, so
-- v = 0.  The upper part W fixes 0, so it is its own linear word L′.
-- The fan-in R w is respelled `R′ w` through SWAPs above wire 0 only,
-- by completeness (the two have one affine map).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Stab where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (zero ; suc)
open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Qupit-Phase-Affine.Field 0 prime[2]
  using (F ; 0F ; 1F ; _+_ ; _*_ ; F* ; module FR ; 1≢0 ; solve ; _:+_ ; _:*_ ; _:=_)
open import Examples.Groups.Qupit-Phase-Affine.Semantics 0 prime[2] using (Labels ; _≐_)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0
open import Examples.Groups.Qupit-Phase-Affine.Interpretation 0 prime[2] 0 using (⟦_⟧ ; ⟦⟧-ε)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2]
  using (adm ; completeness ; runᵃ ; anf₀ ; ⌜_⌝ᵃ ; ANF) renaming (decompose to adecompose)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm
  using (sound ; fn ; fn-• ; fn-↑ ; fn-ε)
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval 0 prime[2] 0
  using (•-at ; ↑-at ; at-≡ ; M-at ; CX-at ; SWAP-at ; CX₂₀-at ; Xᶠ-at)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base 0 prime[2] 0
  using (LGen ; cx ; sw ; mul ; _↥ₗ ; ι ; ⌊_⌋ ; R ; col ; r ; NZ ; big ; small ; row)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Steps 0 prime[2] 0
  using (LNF ; lnf ; ⌜_⌝) renaming (decompose to ldecompose)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Semantics 0 prime[2] 0 adm
  using (R-at ; col-at ; r-head ; dot ; addv ; dot-zero)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan 0 prime[2] 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Affine 0 prime[2] 0 using (Xc ; Xc-zero)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning 0 prime[2] 0 using (module Width ; lift)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Arithmetic

private
  +0 : (a : F) → a + 0F ≡ a
  +0 = FR.+-identityʳ
  0+ : (a : F) → 0F + a ≡ a
  0+ = FR.+-identityˡ
  *0 : (a : F) → a * 0F ≡ 0F
  *0 = FR.zeroʳ
  *1 : (a : F) → a * 1F ≡ a
  *1 = FR.*-identityʳ
  0+0 : 0F + 0F ≡ 0F
  0+0 = FR.+-identityʳ 0F

-- The basis states 0 and e₀.
e₀ : Labels (₁₊ n)
e₀ = 1F ∷ 0ᵛ

------------------------------------------------------------------------
-- Translations

plus : Labels n → Vec F n → Labels n
plus []      []      = []
plus (a ∷ x) (c ∷ b) = a + c ∷ plus x b

Xc-at : (b : Vec F n) (x : Labels n) → ⟦ Xc b ⟧ x ≡ (plus x b , 0F)
Xc-at []      []      = ⟦⟧-ε []
Xc-at (c ∷ b) (a ∷ x) = at-≡ (•-at (↑-at (Xc-at b x)) (Xᶠ-at c a (plus x b))) refl 0+0

plus-0ʳ : (x : Labels n) → plus x 0ᵛ ≡ x
plus-0ʳ []      = refl
plus-0ʳ (a ∷ x) = cong₂ _∷_ (+0 a) (plus-0ʳ x)

plus-0ˡ : (b : Vec F n) → plus 0ᵛ b ≡ b
plus-0ˡ []      = refl
plus-0ˡ (c ∷ b) = cong₂ _∷_ (0+ c) (plus-0ˡ b)

------------------------------------------------------------------------
-- Linear circuits fix 0

private
  gen-0 : (y : LGen n) → ⟦ [ ι y ]ʷ ⟧ 0ᵛ ≡ (0ᵛ , 0F)
  gen-0 cx      = at-≡ (CX-at 0F 0F 0ᵛ) (cong (λ q → q ∷ 0F ∷ 0ᵛ) 0+0) refl
  gen-0 sw      = SWAP-at 0F 0F 0ᵛ
  gen-0 (mul a) = at-≡ (M-at (proj₁ a) (proj₂ a) 0F 0ᵛ) (cong (λ q → q ∷ 0ᵛ) (*0 (proj₁ a))) refl
  gen-0 (y ↥ₗ)  = ↑-at (gen-0 y)

lin-0 : (L : Word (LGen n)) → ⟦ ⌊ L ⌋ ⟧ 0ᵛ ≡ (0ᵛ , 0F)
lin-0 [ y ]ʷ  = gen-0 y
lin-0 ε       = ⟦⟧-ε 0ᵛ
lin-0 (u • v) = at-≡ (•-at (lin-0 v) (lin-0 u)) refl 0+0

r-0 : (ℓ : NZ n) → fn (r ℓ) 0ᵛ ≡ 0ᵛ
r-0 (big a w) =
  cong proj₁ (at-≡ (•-at (M-at (proj₁ a) (proj₂ a) 0F 0ᵛ) (R-at w (proj₁ a * 0F) 0ᵛ))
                   (cong (_∷ 0ᵛ) (trans (cong₂ _+_ (*0 (proj₁ a)) (dot-zero w)) 0+0)) refl)
r-0 (small ℓ) = begin
  fn (SWAP • r ℓ ↑) (0F ∷ 0ᵛ)        ≡⟨ fn-• SWAP (r ℓ ↑) (0F ∷ 0ᵛ) ⟩
  fn SWAP (fn (r ℓ ↑) (0F ∷ 0ᵛ))     ≡⟨ cong (fn SWAP) (trans (fn-↑ (r ℓ) 0F 0ᵛ) (cong (0F ∷_) (r-0 ℓ))) ⟩
  fn SWAP (0F ∷ 0ᵛ)                  ≡⟨ cong proj₁ (SWAP-at 0F 0F 0ᵛ) ⟩
  0ᵛ                                 ∎
  where open ≡-Reasoning

addv-00 : (v : Vec F n) → addv 0F v 0ᵛ ≡ 0ᵛ
addv-00 []      = refl
addv-00 (c ∷ v) = cong₂ _∷_ (trans (0+ (c * 0F)) (*0 c)) (addv-00 v)

addv-10 : (v : Vec F n) → addv 1F v 0ᵛ ≡ v
addv-10 []      = refl
addv-10 (c ∷ v) = cong₂ _∷_ (trans (0+ (c * 1F)) (*1 c)) (addv-10 v)

addv-z : (a : F) (x : Labels n) → addv a 0ᵛ x ≡ x
addv-z a []      = refl
addv-z a (b ∷ x) = cong₂ _∷_ (trans (cong (b +_) (FR.zeroˡ a)) (+0 b)) (addv-z a x)

col-0 : (v : Vec F n) → fn (col v) 0ᵛ ≡ 0ᵛ
col-0 v = trans (cong proj₁ (col-at v 0F 0ᵛ)) (cong (0F ∷_) (addv-00 v))

col-e₀ : (v : Vec F n) → fn (col v) e₀ ≡ 1F ∷ v
col-e₀ v = trans (cong proj₁ (col-at v 1F 0ᵛ)) (cong (1F ∷_) (addv-10 v))

head-↑ : (W : Circuit n) (y : Labels (₁₊ n)) → head (fn (W ↑) y) ≡ head y
head-↑ W (a ∷ t) = cong head (fn-↑ W a t)

head-col : (v : Vec F n) (y : Labels (₁₊ n)) → head (fn (col v) y) ≡ head y
head-col v (a ∷ t) = cong (λ q → head (proj₁ q)) (col-at v a t)

------------------------------------------------------------------------
-- The fan-in onto wire 0, through SWAPs above it

-- One factor of the fan-in: present or not.
pw : F → Circuit 5 → Circuit 5
pw zero          w = ε
pw (suc zero)    w = w

CXin₁ CXin₂ CXin₃ CXin₄ : Circuit 5
CXin₁ = CX
CXin₂ = CX₂₀
CXin₃ = SWAP ↑ ↑ • CX₂₀ • SWAP ↑ ↑
CXin₄ = SWAP ↑ ↑ ↑ • CXin₃ • SWAP ↑ ↑ ↑

R′ : Vec F 4 → Circuit 5
R′ (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) = pw c₁ CXin₁ • pw c₂ CXin₂ • pw c₃ CXin₃ • pw c₄ CXin₄

private
  phase₃ : (0F + 0F) + 0F ≡ 0F
  phase₃ = trans (cong (_+ 0F) 0+0) 0+0

  CXin₃-at : (a b c d e : F) → ⟦ CXin₃ ⟧ (a ∷ b ∷ c ∷ d ∷ e ∷ []) ≡ (a + d ∷ b ∷ c ∷ d ∷ e ∷ [] , 0F)
  CXin₃-at a b c d e =
    at-≡ (•-at (•-at (↑-at (↑-at (SWAP-at c d (e ∷ [])))) (CX₂₀-at a b d (c ∷ e ∷ [])))
               (↑-at (↑-at (SWAP-at d c (e ∷ [])))))
         refl phase₃

  CXin₄-at : (a b c d e : F) → ⟦ CXin₄ ⟧ (a ∷ b ∷ c ∷ d ∷ e ∷ []) ≡ (a + e ∷ b ∷ c ∷ d ∷ e ∷ [] , 0F)
  CXin₄-at a b c d e =
    at-≡ (•-at (•-at (↑-at (↑-at (↑-at (SWAP-at d e [])))) (CXin₃-at a b c e d))
               (↑-at (↑-at (↑-at (SWAP-at e d [])))))
         refl phase₃

  -- One factor: x₀ + c · xᵢ.
  pw-at : (c : F) (w : Circuit 5) (f : Labels 5 → F) →
          (∀ x → ⟦ w ⟧ x ≡ (head x + f x ∷ tail x , 0F)) →
          ∀ x → ⟦ pw c w ⟧ x ≡ (head x + c * f x ∷ tail x , 0F)
  pw-at zero w f e (a ∷ t) = at-≡ (⟦⟧-ε (a ∷ t)) (cong (_∷ t) (sym (trans (cong (a +_) (FR.zeroˡ (f (a ∷ t)))) (+0 a)))) refl
  pw-at (suc zero) w f e x = at-≡ (e x) (cong (λ q → head x + q ∷ tail x) (sym (FR.*-identityˡ (f x)))) refl

  x₁ x₂ x₃ x₄ : Labels 5 → F
  x₁ (_ ∷ b ∷ _ ∷ _ ∷ _ ∷ []) = b
  x₂ (_ ∷ _ ∷ c ∷ _ ∷ _ ∷ []) = c
  x₃ (_ ∷ _ ∷ _ ∷ d ∷ _ ∷ []) = d
  x₄ (_ ∷ _ ∷ _ ∷ _ ∷ e ∷ []) = e

  in₁ : ∀ x → ⟦ CXin₁ ⟧ x ≡ (head x + x₁ x ∷ tail x , 0F)
  in₁ (a ∷ b ∷ c ∷ d ∷ e ∷ []) = CX-at a b (c ∷ d ∷ e ∷ [])
  in₂ : ∀ x → ⟦ CXin₂ ⟧ x ≡ (head x + x₂ x ∷ tail x , 0F)
  in₂ (a ∷ b ∷ c ∷ d ∷ e ∷ []) = CX₂₀-at a b c (d ∷ e ∷ [])
  in₃ : ∀ x → ⟦ CXin₃ ⟧ x ≡ (head x + x₃ x ∷ tail x , 0F)
  in₃ (a ∷ b ∷ c ∷ d ∷ e ∷ []) = CXin₃-at a b c d e
  in₄ : ∀ x → ⟦ CXin₄ ⟧ x ≡ (head x + x₄ x ∷ tail x , 0F)
  in₄ (a ∷ b ∷ c ∷ d ∷ e ∷ []) = CXin₄-at a b c d e

  sum₄ : (a p q s u : F) → (((a + u) + s) + q) + p ≡ a + (p + (q + (s + (u + 0F))))
  sum₄ a p q s u = solve 5 (λ a p q s u → (((a :+ u) :+ s) :+ q) :+ p := a :+ (p :+ (q :+ (s :+ (u :+ con (ℤ.+ 0)))))) refl a p q s u
    where import Data.Integer.Base as ℤ
          open import Examples.Groups.Qupit-Phase-Affine.Field 0 prime[2] using (con)

  phase₄ : ((0F + 0F) + 0F) + 0F ≡ 0F
  phase₄ = trans (cong (_+ 0F) phase₃) 0+0

R′-at : (w : Vec F 4) (a : F) (t : Labels 4) → ⟦ R′ w ⟧ (a ∷ t) ≡ (a + dot w t ∷ t , 0F)
R′-at (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) a t@(b ∷ c ∷ d ∷ e ∷ []) =
  at-≡ (•-at (•-at (•-at (pw-at c₄ CXin₄ x₄ in₄ (a ∷ t))
                         (pw-at c₃ CXin₃ x₃ in₃ (a + c₄ * e ∷ t)))
                   (pw-at c₂ CXin₂ x₂ in₂ ((a + c₄ * e) + c₃ * d ∷ t)))
             (pw-at c₁ CXin₁ x₁ in₁ (((a + c₄ * e) + c₃ * d) + c₂ * c ∷ t)))
       (cong (_∷ t) (sum₄ a (c₁ * b) (c₂ * c) (c₃ * d) (c₄ * e)))
       phase₄

------------------------------------------------------------------------
-- The stabiliser

private
  fn-inv : (W : Circuit n) (x : Labels n) → fn (W ⁻¹) (fn W x) ≡ x
  fn-inv {n} W x =
    trans (sym (fn-• (W ⁻¹) W x)) (trans (cong proj₁ (sound (Inv.inverseˡ n) x)) (fn-ε x))

  fn-inj : (W : Circuit n) {x y : Labels n} → fn W x ≡ fn W y → x ≡ y
  fn-inj W {x} {y} e = trans (sym (fn-inv W x)) (trans (cong (fn (W ⁻¹)) e) (fn-inv W y))

  ∷-inj : {a b : F} {x y : Labels n} → a ∷ x ≡ b ∷ y → x ≡ y
  ∷-inj refl = refl

  fn-ANF : (w : Circuit n) → fn w 0ᵛ ≡ ANF.shift (runᵃ anf₀ w)
  fn-ANF w = begin
    fn w 0ᵛ                                   ≡⟨ cong proj₁ (sound (adecompose w) 0ᵛ) ⟩
    fn (Xc b • ⌊ L ⌋) 0ᵛ                      ≡⟨ fn-• (Xc b) ⌊ L ⌋ 0ᵛ ⟩
    fn (Xc b) (fn ⌊ L ⌋ 0ᵛ)                   ≡⟨ cong (fn (Xc b)) (cong proj₁ (lin-0 L)) ⟩
    fn (Xc b) 0ᵛ                              ≡⟨ cong proj₁ (Xc-at b 0ᵛ) ⟩
    plus 0ᵛ b                                 ≡⟨ plus-0ˡ b ⟩
    b                                         ∎
    where
    open ≡-Reasoning
    b = ANF.shift (runᵃ anf₀ w)
    L = ANF.linear (runᵃ anf₀ w)

  -- A circuit fixing 0 is its linear word.
  linear-part : (w : Circuit n) → fn w 0ᵛ ≡ 0ᵛ → n ⊢ w ≈ ⌊ ANF.linear (runᵃ anf₀ w) ⌋
  linear-part {n} w h =
    Wd.trans (adecompose w) (Wd.trans (Wd.cong (Wd.refl' (cong Xc b0)) Wd.refl) (Wd.trans (Wd.cong Xc-zero Wd.refl) Wd.left-unit))
    where
    module Wd = Width n
    b0 : ANF.shift (runᵃ anf₀ w) ≡ 0ᵛ
    b0 = trans (sym (fn-ANF w)) h

------------------------------------------------------------------------
-- The stabiliser of 0 and e₀

private
  module Of (γ : Circuit 5) (h0 : fn γ 0ᵛ ≡ 0ᵛ) (h1 : fn γ e₀ ≡ e₀) where

    L : Word (LGen 5)
    L = ANF.linear (runᵃ anf₀ γ)

    γL : 5 ⊢ γ ≈ ⌊ L ⌋
    γL = linear-part γ h0

    fnL : ∀ x → fn ⌊ L ⌋ x ≡ fn γ x
    fnL x = cong proj₁ (sym (sound γL x))

    module Parts (W : Circuit 4) (v : Vec F 4) (ℓ : NZ 5) (d : 5 ⊢ ⌊ L ⌋ ≈ W ↑ • col v • r ℓ) where

      val : ∀ x → fn ⌊ L ⌋ x ≡ fn (W ↑) (fn (col v) (fn (r ℓ) x))
      val x = trans (cong proj₁ (sound d x))
                    (trans (fn-• (W ↑) (col v • r ℓ) x) (cong (fn (W ↑)) (fn-• (col v) (r ℓ) x)))

      row1 : dot (row ℓ) e₀ ≡ 1F
      row1 = begin
        dot (row ℓ) e₀                                   ≡⟨ sym (r-head ℓ e₀) ⟩
        head (fn (r ℓ) e₀)                               ≡⟨ sym (head-col v (fn (r ℓ) e₀)) ⟩
        head (fn (col v) (fn (r ℓ) e₀))                  ≡⟨ sym (head-↑ W _) ⟩
        head (fn (W ↑) (fn (col v) (fn (r ℓ) e₀)))       ≡⟨ cong head (sym (val e₀)) ⟩
        head (fn ⌊ L ⌋ e₀)                               ≡⟨ cong head (trans (fnL e₀) h1) ⟩
        1F                                               ∎
        where open ≡-Reasoning

      W0 : fn W 0ᵛ ≡ 0ᵛ
      W0 = ∷-inj (begin
        0F ∷ fn W 0ᵛ                                     ≡⟨ sym (fn-↑ W 0F 0ᵛ) ⟩
        fn (W ↑) 0ᵛ                                      ≡⟨ cong (fn (W ↑)) (sym (col-0 v)) ⟩
        fn (W ↑) (fn (col v) 0ᵛ)                         ≡⟨ cong (λ q → fn (W ↑) (fn (col v) q)) (sym (r-0 ℓ)) ⟩
        fn (W ↑) (fn (col v) (fn (r ℓ) 0ᵛ))              ≡⟨ sym (val 0ᵛ) ⟩
        fn ⌊ L ⌋ 0ᵛ                                      ≡⟨ cong proj₁ (lin-0 L) ⟩
        0F ∷ 0ᵛ                                          ∎)
        where open ≡-Reasoning

      Wv : fn (r ℓ) e₀ ≡ e₀ → fn W v ≡ 0ᵛ
      Wv re = ∷-inj (begin
        1F ∷ fn W v                                      ≡⟨ sym (fn-↑ W 1F v) ⟩
        fn (W ↑) (1F ∷ v)                                ≡⟨ cong (fn (W ↑)) (sym (col-e₀ v)) ⟩
        fn (W ↑) (fn (col v) e₀)                         ≡⟨ cong (λ q → fn (W ↑) (fn (col v) q)) (sym re) ⟩
        fn (W ↑) (fn (col v) (fn (r ℓ) e₀))              ≡⟨ sym (val e₀) ⟩
        fn ⌊ L ⌋ e₀                                      ≡⟨ trans (fnL e₀) h1 ⟩
        1F ∷ 0ᵛ                                          ∎)
        where open ≡-Reasoning

      v0 : fn (r ℓ) e₀ ≡ e₀ → v ≡ 0ᵛ
      v0 re = fn-inj W (trans (Wv re) (sym W0))

      W≈ : 4 ⊢ W ≈ ⌊ ANF.linear (runᵃ anf₀ W) ⌋
      W≈ = linear-part W W0

  -- The data of a big row with unit 1.
  dot-big : (a : F*) (w : Vec F 4) → dot (row (big a w)) e₀ ≡ proj₁ a
  dot-big a w = trans (cong₂ _+_ (*1 (proj₁ a)) (dot-zero w)) (+0 (proj₁ a))

  dot-small : (ℓ : NZ 4) → dot (row (small ℓ)) e₀ ≡ 0F
  dot-small ℓ = trans (cong₂ _+_ (FR.zeroˡ 1F) (dot-zero (row ℓ))) 0+0

  r-big-e₀ : (a : F*) (w : Vec F 4) → proj₁ a ≡ 1F → fn (r (big a w)) e₀ ≡ e₀
  r-big-e₀ a w a1 =
    cong proj₁ (at-≡ (•-at (M-at (proj₁ a) (proj₂ a) 1F 0ᵛ) (R-at w (proj₁ a * 1F) 0ᵛ))
                     (cong (_∷ 0ᵛ) (trans (cong₂ _+_ (trans (*1 (proj₁ a)) a1) (dot-zero w)) (+0 1F))) refl)

  -- col 0 · R w · M⟨ a ⟩ is the fan-in R′ w, for a unit 1.
  tail-eq : (a : F*) (w : Vec F 4) → proj₁ a ≡ 1F →
            ⟦ col 0ᵛ • (R w • M⟨ a ⟩) ⟧ ≐ ⟦ R′ w ⟧
  tail-eq a w a1 (x₀ ∷ t) =
    trans (at-≡ (•-at (•-at (M-at (proj₁ a) (proj₂ a) x₀ t) (R-at w (proj₁ a * x₀) t))
                      (col-at 0ᵛ (proj₁ a * x₀ + dot w t) t))
                (cong₂ _∷_ (cong (_+ dot w t) (trans (cong (_* x₀) a1) (FR.*-identityˡ x₀))) (addv-z _ t))
                phase₃)
          (sym (R′-at w x₀ t))

stab : (γ : Circuit 5) → fn γ 0ᵛ ≡ 0ᵛ → fn γ e₀ ≡ e₀ →
       Σ[ L′ ∈ Word (LGen 4) ] Σ[ w ∈ Vec F 4 ] (5 ⊢ γ ≈ ⌊ L′ ⌋ ↑ • R′ w)
stab γ h0 h1 = go (LNF.upper N) (LNF.column N) (LNF.form N) (ldecompose (Of.L γ h0 h1))
  where
  N = lnf (Of.L γ h0 h1)
  go : (W : Circuit 4) (v : Vec F 4) (ℓ : NZ 5) → 5 ⊢ ⌊ Of.L γ h0 h1 ⌋ ≈ W ↑ • col v • r ℓ →
       Σ[ L′ ∈ Word (LGen 4) ] Σ[ w ∈ Vec F 4 ] (5 ⊢ γ ≈ ⌊ L′ ⌋ ↑ • R′ w)
  go W v (small ℓ) d = ⊥-elim (1≢0 (trans (sym P.row1) (dot-small ℓ)))
    where module P = Of.Parts γ h0 h1 W v (small ℓ) d
  go W v (big a w) d = ANF.linear (runᵃ anf₀ W) , w , proof
    where
    module P = Of.Parts γ h0 h1 W v (big a w) d
    a1 : proj₁ a ≡ 1F
    a1 = trans (sym (dot-big a w)) P.row1
    proof : 5 ⊢ γ ≈ ⌊ ANF.linear (runᵃ anf₀ W) ⌋ ↑ • R′ w
    proof =
      Wd.trans (Of.γL γ h0 h1)
        (Wd.trans d
          (Wd.trans (Wd.cong (lift P.W≈) (Wd.refl' (cong (λ u → col u • (R w • M⟨ a ⟩)) (P.v0 (r-big-e₀ a w a1)))))
                    (Wd.back _ (completeness 5 (tail-eq a w a1)))))
      where module Wd = Width 5
