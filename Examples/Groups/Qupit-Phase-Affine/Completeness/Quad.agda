------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of QuadPhase_d (p odd)
--
-- At level 2 the diagonal layer is a diagonal expression
-- (Phase.Quad.Diag): ω^s • Zc c • a list of iterates of atoms of S.
-- The affine generators move across it and the phase generators are
-- absorbed by its operations, and it is diagonal.  Two expressions with
-- the same phase are equal: each splits as an expression one wire up
-- times a wire-0 form E e (Phase.Quad.Split); at x₀ = 0 the forms
-- vanish, so the upper parts have the same phase and are equal by
-- completeness one wire down, and then the forms have the same phase
--
--     x₀ (α · x') + c x₀ + d (x₀ choose 2),
--
-- which determines (d , c , α): at (1 , 0) it is c, at (2 , 0) it is
-- 2c + d, and at (1 , x') it is α · x' + c (E-unique).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Completeness.Quad
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (odd : 1 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Empty using (⊥ ; ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc ; s≤s ; z≤n)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 2
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime 2
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime 2
  using ( DiagC ; DiagC-• ; DiagC-↑ ; DiagC-ε ; DiagC-≡ ; DiagC-^ᶠ ; DiagC-conj ; Z-diag ; S-diag ; ω-diag
        ; •-at ; at-≡ ; CX-at ; CXᶠ-at ; S-at ; SWAP-at )
open import Examples.Groups.Qupit-Phase-Affine.Soundness p-2 p-prime 2 using (Admissible)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime 2
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime 2 using (unit ; _⁻¹)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime 2
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime 2 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime 2

-- Level 2 is admissible for odd p.
adm : Admissible
adm = (λ _ → odd) , (λ { (s≤s (s≤s ())) })

private
  h : 2 ≤ 2
  h = s≤s (s≤s z≤n)

open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Split p-2 p-prime 2 h odd
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime 2 adm
open import Examples.Groups.Qupit-Phase-Affine.Linear.Semantics p-2 p-prime 2 adm
  using (dot ; dot-injective)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Layered p-2 p-prime 2 adm

private
  variable
    n : ℕ

  h₁ : 1 ≤ 2
  h₁ = lin₂ h

  no3 : 3 ≤ 2 → ⊥
  no3 (s≤s (s≤s ()))

------------------------------------------------------------------------
-- The layer

d₀ : DE n
d₀ = de 0F 0ᵛ []

d₀-ε : n ⊢ ⟦ d₀ {n} ⟧ᴰ ≈ ε
d₀-ε = Width.sym (proj₂ Diag-ε)

_⋆ᵗ_ : DE n → Fin n → DE n
d ⋆ᵗ j = d ⋆ᵛ uvec j

tr-tr : (d : DE n) (j : Fin n) → n ⊢ ⟦ d ⟧ᴰ • Xc (uvec j) ≈ Xc (uvec j) • ⟦ d ⋆ᵗ j ⟧ᴰ
tr-tr d j = ⋆ᵛ-sound d (uvec j)

------------------------------------------------------------------------
-- The expressions are diagonal

IsDiag : Circuit n → Set
IsDiag {n} w = (x : Labels n) → fn w x ≡ x

private
  isd-• : {u v : Circuit n} → IsDiag u → IsDiag v → IsDiag (u • v)
  isd-• {u = u} {v} du dv x = Eq.trans (fn-• u v x) (Eq.trans (Eq.cong (fn u) (dv x)) (du x))

  isd-C : {w : Circuit n} {φ : Labels n → F} → DiagC w φ → IsDiag w
  isd-C d x = Eq.cong proj₁ (d x)

  isd-↑ : {w : Circuit n} → IsDiag w → IsDiag (w ↑)
  isd-↑ {w = w} d (a ∷ x) = Eq.trans (fn-↑ w a x) (Eq.cong (a ∷_) (d x))

  isd-^ : {w : Circuit n} → IsDiag w → (k : ℕ) → IsDiag (w ^ k)
  isd-^ d zero          x = fn-ε x
  isd-^ d (suc zero)    x = d x
  isd-^ d (suc (suc k)) x = isd-• d (isd-^ d (suc k)) x

  isd-conj : (ρ : Circuit n) {w : Circuit n} → IsDiag w → IsDiag (ρ ⁻¹ • w • ρ)
  isd-conj ρ {w} d x = begin
    fn (ρ ⁻¹ • w • ρ) x              ≡⟨ fn-• (ρ ⁻¹) (w • ρ) x ⟩
    fn (ρ ⁻¹) (fn (w • ρ) x)         ≡⟨ Eq.cong (fn (ρ ⁻¹)) (Eq.trans (fn-• w ρ x) (d (fn ρ x))) ⟩
    fn (ρ ⁻¹) (fn ρ x)               ≡⟨ fn-⁻¹ ρ x ⟩
    x                                ∎
    where open ≡-Reasoning

  isd-atom : (ℓ : NZ n) → IsDiag (atom ℓ)
  isd-atom {suc n} ℓ = isd-conj (r ℓ) (isd-C (S-diag h))

  isd-atoms : (as : Atoms n) → IsDiag (atoms as)
  isd-atoms []             = fn-ε
  isd-atoms ((ℓ , k) ∷ as) = isd-• (isd-^ (isd-atom ℓ) _) (isd-atoms as)

  isd-Zc : (c : Vec F n) → IsDiag (Zc c)
  isd-Zc []       = fn-ε
  isd-Zc (c ∷ cs) = isd-• (isd-C (DiagC-^ᶠ (Z-diag h₁) c)) (isd-↑ (isd-Zc cs))

de-diag : (d : DE n) (x : Labels n) → fn ⟦ d ⟧ᴰ x ≡ x
de-diag (de s c as) = isd-• (isd-C (DiagC-^ᶠ (ω-diag h₁) s)) (isd-• (isd-Zc c) (isd-atoms as))

------------------------------------------------------------------------
-- The phase of a wire-0 form

φE : EData n → Labels (₁₊ n) → F
φE (d , c , α) (x₀ ∷ x) = x₀ * (α ·ᵛ x) + (c * x₀ + d * binom2 x₀)

private
  sw01 : Labels (₂₊ n) → Labels (₂₊ n)
  sw01 (a ∷ b ∷ x) = b ∷ a ∷ x

  SWAP-at′ : (x : Labels (₂₊ n)) → ⟦ SWAP ⟧ x ≡ (sw01 x , 0F)
  SWAP-at′ (a ∷ b ∷ x) = SWAP-at a b x

  sw01-inv : (x : Labels (₂₊ n)) → sw01 (sw01 x) ≡ x
  sw01-inv (a ∷ b ∷ x) = refl

  P-diag : DiagC {₂₊ n} P (λ y → binom2 (head y + head (tail y)))
  P-diag (a ∷ b ∷ x) =
    at-≡ (•-at (•-at (CX-at a b x) (S-at h (a + b) (b ∷ x))) (CXᶠ-at (- 1F) (a + b) b x))
         (Eq.cong (λ t → t ∷ b ∷ x) (solve 2 (λ a b → (a :+ b) :+ (:- con (ℤ.+ 1)) :* b := a) refl a b))
         (Eq.trans (FR.+-identityʳ _) (FR.+-identityˡ _))

  CZ-diag : DiagC {₂₊ n} (CZ h) (λ y → head y * head (tail y))
  CZ-diag = DiagC-≡ (DiagC-• (DiagC-^ᶠ (S-diag h) (- 1F)) (DiagC-• (DiagC-↑ (DiagC-^ᶠ (S-diag h) (- 1F))) P-diag))
    λ { (a ∷ b ∷ x) → Eq.trans (Eq.cong (λ t → (t + (- 1F) * binom2 b) + (- 1F) * binom2 a) (Odd.binom2-add odd a b))
                        (solve 4 (λ a b ba bb → ((ba :+ bb :+ a :* b) :+ (:- con (ℤ.+ 1)) :* bb) :+ (:- con (ℤ.+ 1)) :* ba
                                                := a :* b) refl a b (binom2 a) (binom2 b)) }

  K-diag : (α : Vec F n) → DiagC (K α) (λ y → head y * (α ·ᵛ tail y))
  K-diag []      = DiagC-≡ DiagC-ε λ { (a ∷ []) → Eq.sym (FR.zeroʳ a) }
  K-diag (c ∷ α) = DiagC-≡ (DiagC-• (DiagC-^ᶠ CZ-diag c) (DiagC-conj SWAP-at′ sw01-inv (DiagC-↑ (K-diag α))))
    λ { (a ∷ b ∷ x) → solve 4 (λ a b c t → a :* t :+ c :* (a :* b) := a :* (c :* b :+ t)) refl a b c (α ·ᵛ x) }

  SZ-diag : (d c : F) → DiagC {₁₊ n} (SZ d c) (λ y → c * head y + d * binom2 (head y))
  SZ-diag d c = DiagC-• (DiagC-^ᶠ (S-diag h) d) (DiagC-^ᶠ (Z-diag h₁) c)

E-diag : (e : EData n) → DiagC (E e) (φE e)
E-diag (d , c , α) = DiagC-≡ (DiagC-• (SZ-diag d c) (K-diag α)) λ { (a ∷ x) → refl }

private
  binom2-1 : binom2 1F ≡ 0F
  binom2-1 = solve 1 (λ t → con (ℤ.+ 1) :* (con (ℤ.+ 1) :- con (ℤ.+ 1)) :* t := con (ℤ.+ 0)) refl half

  binom2-2 : binom2 2F ≡ 1F
  binom2-2 = Eq.trans (Odd.binom2-shift odd 1F) (Eq.trans (Eq.cong (_+ 1F) binom2-1) (FR.+-identityˡ 1F))

  binom2-0 : binom2 0F ≡ 0F
  binom2-0 = Eq.trans (Eq.cong (_* half) (FR.zeroˡ _)) (FR.zeroˡ half)

  ·0 : (α : Vec F n) → α ·ᵛ 0ᵛ ≡ 0F
  ·0 []      = refl
  ·0 (a ∷ α) = Eq.trans (Eq.cong₂ _+_ (FR.zeroʳ a) (·0 α)) (FR.+-identityʳ 0F)

  ·ᵛ≡dot : (c x : Vec F n) → c ·ᵛ x ≡ dot c x
  ·ᵛ≡dot []       []       = refl
  ·ᵛ≡dot (c ∷ cs) (a ∷ x)  = Eq.cong (c * a +_) (·ᵛ≡dot cs x)

  cancel+ : {a b s : F} → a + s ≡ b + s → a ≡ b
  cancel+ {a} {b} {s} q = begin
    a                 ≡⟨ Eq.sym (FR.+-identityʳ a) ⟩
    a + 0F            ≡⟨ Eq.cong (a +_) (Eq.sym (FR.-‿inverseʳ s)) ⟩
    a + (s + - s)     ≡⟨ Eq.sym (FR.+-assoc a s (- s)) ⟩
    (a + s) + - s     ≡⟨ Eq.cong (_+ - s) q ⟩
    (b + s) + - s     ≡⟨ FR.+-assoc b s (- s) ⟩
    b + (s + - s)     ≡⟨ Eq.cong (b +_) (FR.-‿inverseʳ s) ⟩
    b + 0F            ≡⟨ FR.+-identityʳ b ⟩
    b                 ∎
    where open ≡-Reasoning

  cancel+ˡ : {a b s : F} → s + a ≡ s + b → a ≡ b
  cancel+ˡ {a} {b} {s} q = cancel+ (Eq.trans (FR.+-comm a s) (Eq.trans q (FR.+-comm s b)))

-- The phase of a form at x₀ = 0 vanishes.
φE-0 : (e : EData n) (x : Labels n) → φE e (0F ∷ x) ≡ 0F
φE-0 (d , c , α) x =
  Eq.trans (Eq.cong (λ t → 0F * (α ·ᵛ x) + (c * 0F + d * t)) binom2-0)
    (solve 3 (λ t c d → con (ℤ.+ 0) :* t :+ (c :* con (ℤ.+ 0) :+ d :* con (ℤ.+ 0)) := con (ℤ.+ 0)) refl (α ·ᵛ x) c d)

-- The phase determines the form.
E-unique : (e e' : EData n) → (∀ y → φE e y ≡ φE e' y) → e ≡ e'
E-unique {n} (d , c , α) (d' , c' , α') eq = Eq.cong₂ _,_ dd (Eq.cong₂ _,_ cc αα)
  where
  at1 : (d c : F) (α : Vec F n) (x : Labels n) → φE (d , c , α) (1F ∷ x) ≡ α ·ᵛ x + c
  at1 d c α x = Eq.trans (Eq.cong (λ t → 1F * (α ·ᵛ x) + (c * 1F + d * t)) binom2-1)
                  (solve 3 (λ t c d → con (ℤ.+ 1) :* t :+ (c :* con (ℤ.+ 1) :+ d :* con (ℤ.+ 0)) := t :+ c) refl (α ·ᵛ x) c d)
  at2 : (d c : F) (α : Vec F n) → φE (d , c , α) (2F ∷ 0ᵛ) ≡ c * 2F + d
  at2 d c α = Eq.trans (Eq.cong₂ (λ s t → 2F * s + (c * 2F + d * t)) (·0 α) binom2-2)
                (solve 2 (λ c d → (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :* con (ℤ.+ 0) :+ (c :* (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :+ d :* con (ℤ.+ 1))
                                  := c :* (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :+ d) refl c d)
  cc : c ≡ c'
  cc = cancel+ˡ (Eq.trans (Eq.sym (Eq.trans (at1 d c α 0ᵛ) (Eq.cong (_+ c) (·0 α))))
                  (Eq.trans (eq (1F ∷ 0ᵛ)) (Eq.trans (at1 d' c' α' 0ᵛ) (Eq.cong (_+ c') (·0 α')))))
  dd : d ≡ d'
  dd = cancel+ˡ (Eq.trans (Eq.sym (at2 d c α)) (Eq.trans (eq (2F ∷ 0ᵛ))
                  (Eq.trans (at2 d' c' α') (Eq.cong (λ t → t * 2F + d') (Eq.sym cc)))))
  αα : α ≡ α'
  αα = dot-injective α α' λ x →
    Eq.trans (Eq.sym (·ᵛ≡dot α x))
      (Eq.trans (cancel+ (Eq.trans (Eq.sym (at1 d c α x))
                           (Eq.trans (eq (1F ∷ x)) (Eq.trans (at1 d' c' α' x) (Eq.cong (α' ·ᵛ x +_) (Eq.sym cc))))))
                (·ᵛ≡dot α' x))

------------------------------------------------------------------------
-- Equal phases, equal expressions

unique₀ : (d d' : DE 0) → (∀ x → ph ⟦ d ⟧ᴰ x ≡ ph ⟦ d' ⟧ᴰ x) → 0 ⊢ ⟦ d ⟧ᴰ ≈ ⟦ d' ⟧ᴰ
unique₀ (de s [] []) (de s' [] []) e = Width.refl' 0 (Eq.cong (λ t → ⟦ de t [] [] ⟧ᴰ) ss)
  where
  at : (t : F) → ph ⟦ de t [] [] ⟧ᴰ [] ≡ t
  at t = Eq.trans (Eq.cong proj₂ (DiagC-• (DiagC-^ᶠ (ω-diag h₁) t) (DiagC-• DiagC-ε DiagC-ε) []))
           (Eq.trans (Eq.cong (_+ t * 1F) (FR.+-identityʳ 0F)) (Eq.trans (FR.+-identityˡ _) (FR.*-identityʳ t)))
  ss : s ≡ s'
  ss = Eq.trans (Eq.sym (at s)) (Eq.trans (e []) (at s'))
unique₀ (de s [] ((() , _) ∷ _)) _ _
unique₀ (de s [] []) (de s' [] ((() , _) ∷ _)) _

unique : Complete n → (d d' : DE (₁₊ n)) → (∀ x → ph ⟦ d ⟧ᴰ x ≡ ph ⟦ d' ⟧ᴰ x) → (₁₊ n) ⊢ ⟦ d ⟧ᴰ ≈ ⟦ d' ⟧ᴰ
unique {n} IH d d' e = begin
  ⟦ d ⟧ᴰ                       ≈⟨ split-sound d ⟩
  ⟦ U ⟧ᴰ ↑ • E eE              ≈⟨ cong (lift (IH U≐)) (refl' (Eq.cong E ee)) ⟩
  ⟦ U' ⟧ᴰ ↑ • E eE'            ≈⟨ sym (split-sound d') ⟩
  ⟦ d' ⟧ᴰ                      ∎
  where
  open Width (₁₊ n)
  U  = proj₁ (split d)
  eE = proj₂ (split d)
  U'  = proj₁ (split d')
  eE' = proj₂ (split d')
  -- The phase of a split expression.
  ph-split : (W : DE n) (f : EData n) (x₀ : F) (x : Labels n) →
             ph (⟦ W ⟧ᴰ ↑ • E f) (x₀ ∷ x) ≡ φE f (x₀ ∷ x) + ph ⟦ W ⟧ᴰ x
  ph-split W f x₀ x = Eq.trans (ph-• (⟦ W ⟧ᴰ ↑) (E f) (x₀ ∷ x))
    (Eq.cong₂ _+_ (Eq.cong proj₂ (E-diag f (x₀ ∷ x)))
                  (Eq.trans (Eq.cong (ph (⟦ W ⟧ᴰ ↑)) (Eq.cong proj₁ (E-diag f (x₀ ∷ x)))) (ph-↑ ⟦ W ⟧ᴰ x₀ x)))
  pd : (x₀ : F) (x : Labels n) → ph ⟦ d ⟧ᴰ (x₀ ∷ x) ≡ φE eE (x₀ ∷ x) + ph ⟦ U ⟧ᴰ x
  pd x₀ x = Eq.trans (ph-≈ (split-sound d) (x₀ ∷ x)) (ph-split U eE x₀ x)
  pd' : (x₀ : F) (x : Labels n) → ph ⟦ d' ⟧ᴰ (x₀ ∷ x) ≡ φE eE' (x₀ ∷ x) + ph ⟦ U' ⟧ᴰ x
  pd' x₀ x = Eq.trans (ph-≈ (split-sound d') (x₀ ∷ x)) (ph-split U' eE' x₀ x)
  at0 : (f : EData n) (t : F) (x : Labels n) → φE f (0F ∷ x) + t ≡ t
  at0 f t x = Eq.trans (Eq.cong (_+ t) (φE-0 f x)) (FR.+-identityˡ t)
  phU : (x : Labels n) → ph ⟦ U ⟧ᴰ x ≡ ph ⟦ U' ⟧ᴰ x
  phU x = Eq.trans (Eq.sym (at0 eE _ x))
            (Eq.trans (Eq.sym (pd 0F x)) (Eq.trans (e (0F ∷ x)) (Eq.trans (pd' 0F x) (at0 eE' _ x))))
  U≐ : ⟦ ⟦ U ⟧ᴰ ⟧ ≐ ⟦ ⟦ U' ⟧ᴰ ⟧
  U≐ x = Eq.cong₂ _,_ (Eq.trans (de-diag U x) (Eq.sym (de-diag U' x))) (phU x)
  ee : eE ≡ eE'
  ee = E-unique eE eE' λ { (x₀ ∷ x) →
    cancel+ (Eq.trans (Eq.sym (pd x₀ x)) (Eq.trans (e (x₀ ∷ x)) (Eq.trans (pd' x₀ x) (Eq.cong (φE eE' (x₀ ∷ x) +_) (Eq.sym (phU x)))))) }

------------------------------------------------------------------------
-- The generators at level 2

open Layer DE ⟦_⟧ᴰ d₀ d₀-ε _⋆ˡ_ ⋆ˡ-sound _⋆ᵗ_ tr-tr PG ⟦_⟧ᵖ app app-sound de-diag unique₀ unique

private
  up-kind : Kind PG n → Kind PG (₁₊ n)
  up-kind (lin y)       = lin (y ↥ₗ)
  up-kind (trX j)       = trX (suc j)
  up-kind (phs gω)      = phs gω
  up-kind (phs (gZ j))  = phs (gZ (suc j))
  up-kind (phs (gS j))  = phs (gS (suc j))

  up-kind-sound : (k : Kind PG n) → (₁₊ n) ⊢ ⟦ k ⟧ₖ ↑ ≈ ⟦ up-kind k ⟧ₖ
  up-kind-sound (lin y)      = Width.refl
  up-kind-sound (trX j)      = Width.sym Width.left-unit
  up-kind-sound (phs gω)     = ω↑
  up-kind-sound (phs (gZ j)) = Width.refl
  up-kind-sound (phs (gS j)) = Width.refl

kind : Gen n → Kind PG n
kind (gate₀ (ω-gate _))     = phs gω
kind (gate₁ X-gate)         = trX zero
kind (gate₁ (M-gate a nz))  = lin (mul (unit a nz))
kind (gate₁ (Z-gate _))     = phs (gZ zero)
kind (gate₁ (S-gate _))     = phs (gS zero)
kind (gate₁ (T-gate h₃))    = ⊥-elim-irr (no3 h₃)
kind (gate₂ CX-gate)        = lin cx
kind (gate₂ SWAP-gate)      = lin sw
kind (g ↥)                  = up-kind (kind g)

kind-sound : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ⟦ kind g ⟧ₖ
kind-sound (gate₀ (ω-gate _))    = Width.refl
kind-sound {₁₊ n} (gate₁ X-gate) = sym (trans (back _ (lift Xc-zero)) right-unit)
  where open Width (₁₊ n)
kind-sound (gate₁ (M-gate a nz)) = Width.refl
kind-sound (gate₁ (Z-gate _))    = Width.refl
kind-sound (gate₁ (S-gate _))    = Width.refl
kind-sound (gate₁ (T-gate h₃))   = ⊥-elim-irr (no3 h₃)
kind-sound (gate₂ CX-gate)       = Width.refl
kind-sound (gate₂ SWAP-gate)     = Width.refl
kind-sound {₁₊ n} (g ↥)          = Width.trans (lift (kind-sound g)) (up-kind-sound (kind g))

open Run kind kind-sound public using (completeness)
