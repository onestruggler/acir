------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of CubicPhase_d (p > 3)
--
-- At level 3 the diagonal layer is a diagonal expression of level 3
-- (Phase.Cube.Diag): one of level 2 and a list of iterates of atoms of
-- T.  The affine generators move across it and the phase generators are
-- absorbed by its operations, and it is diagonal.  Two expressions with
-- the same phase are equal: each splits as an expression one wire up
-- times a wire-0 form E₃ e (Phase.Cube.Split3); at x₀ = 0 the forms
-- vanish, so the upper parts have the same phase and are equal by
-- completeness one wire down, and then the forms have the same phase
--
--     x₀ g(x') + (x₀ choose 2) f(x') + t (x₀ choose 3).
--
-- At x₀ = 1 it is g, at x₀ = 2 it is 2 g + f, at x₀ = 3 it is
-- 3 g + 3 f + t.  So g and f, the phases of circuits of levels 2 and 1,
-- agree, the circuits are equal by completeness at those levels, and
-- so are their controlled images (Phase.Control); and t agrees.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Completeness.Cube
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (gt3 : 2 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc ; s≤s ; z≤n)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

import Examples.Groups.Qupit-Phase-Affine.Interpretation as Interpretation′
import Examples.Groups.Qupit-Phase-Affine.Evaluation as Evaluation′
import Examples.Groups.Qupit-Phase-Affine.Completeness.Lin as CLin′
import Examples.Groups.Qupit-Phase-Affine.Completeness.Quad as CQuad′

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 3
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime 3
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime 3
  using (DiagC ; DiagC-• ; DiagC-↑ ; DiagC-ε ; DiagC-^ᶠ ; Z-diag ; S-diag ; T-diag ; ω-diag ; •-at ; at-≡)
open import Examples.Groups.Qupit-Phase-Affine.Soundness p-2 p-prime 3 using (Admissible)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime 3
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime 3 using (unit ; _⁻¹)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime 3
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime 3 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime 3

-- Level 3 is admissible for p > 3.
adm : Admissible
adm = (λ _ → big⇒odd gt3) , (λ _ → gt3)

private
  h : 3 ≤ 3
  h = s≤s (s≤s (s≤s z≤n))

open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates p-2 p-prime 3 h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Ctrl p-2 p-prime 3 h gt3 using (module C1 ; module C2)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.EForm3 p-2 p-prime 3 h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Split3 p-2 p-prime 3 h gt3
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime 3 adm
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Layered p-2 p-prime 3 adm

private
  variable
    n : ℕ

  h₂ : 2 ≤ 3
  h₂ = quad₃ h

  h₁ : 1 ≤ 3
  h₁ = lin₃ h

  odd : 1 ≤ p-2
  odd = big⇒odd gt3

-- Levels 1 and 2.
private
  module CL = CLin′ p-2 p-prime
  module CQ = CQuad′ p-2 p-prime odd
  module E1 = Evaluation′ p-2 p-prime 1 CL.adm
  module SI1 = Interpretation′ p-2 p-prime 1
  module SI2 = Interpretation′ p-2 p-prime 2
  module E2 = Evaluation′ p-2 p-prime 2 CQ.adm

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
  isd-atom {suc n} ℓ = isd-conj (r ℓ) (isd-C (S-diag h₂))

  isd-atomᵀ : (ℓ : NZ n) → IsDiag (atomᵀ ℓ)
  isd-atomᵀ {suc n} ℓ = isd-conj (r ℓ) (isd-C (T-diag h))

  isd-atoms : (as : Atoms n) → IsDiag (atoms as)
  isd-atoms []             = fn-ε
  isd-atoms ((ℓ , k) ∷ as) = isd-• (isd-^ (isd-atom ℓ) _) (isd-atoms as)

  isd-atomsᵀ : (ts : Atoms n) → IsDiag (atomsᵀ ts)
  isd-atomsᵀ []             = fn-ε
  isd-atomsᵀ ((ℓ , k) ∷ ts) = isd-• (isd-^ (isd-atomᵀ ℓ) _) (isd-atomsᵀ ts)

  isd-Zc : (c : Vec F n) → IsDiag (Zc c)
  isd-Zc []       = fn-ε
  isd-Zc (c ∷ cs) = isd-• (isd-C (DiagC-^ᶠ (Z-diag h₁) c)) (isd-↑ (isd-Zc cs))

de₃-diag : (d : DE₃ n) (x : Labels n) → fn ⟦ d ⟧³ x ≡ x
de₃-diag (de s c as ∣ ts) =
  isd-• (isd-• (isd-C (DiagC-^ᶠ (ω-diag h₁) s)) (isd-• (isd-Zc c) (isd-atoms as))) (isd-atomsᵀ ts)

------------------------------------------------------------------------
-- The phase of a wire-0 form

φE₃ : E3Data n → F → Labels n → F
φE₃ (t , l , g) x₀ x = x₀ * E2.ph Q2.⟦ g ⟧ᴰ x + (binom2 x₀ * E1.ph L1.⟦ l ⟧ˡ x + t * binom3 x₀)

E₃-sem : (e : E3Data n) (x₀ : F) (x : Labels n) → ⟦ E₃ e ⟧ (x₀ ∷ x) ≡ (x₀ ∷ x , φE₃ e x₀ x)
E₃-sem (t , l , g) x₀ x =
  at-≡ (•-at (•-at cb ca) (DiagC-^ᶠ (T-diag h) t (x₀ ∷ x))) refl (FR.+-assoc _ _ _)
  where
  cb : ⟦ C1.ctrl* Q2.⟦ g ⟧ᴰ ⟧ (x₀ ∷ x) ≡ (x₀ ∷ x , x₀ * E2.ph Q2.⟦ g ⟧ᴰ x)
  cb = at-≡ (C1.ctrl-sem Q2.⟦ g ⟧ᴰ x₀ x) (Eq.cong (x₀ ∷_) (CQ.de-diag g x)) refl
  ca : ⟦ C2.ctrl* L1.⟦ l ⟧ˡ ⟧ (x₀ ∷ x) ≡ (x₀ ∷ x , binom2 x₀ * E1.ph L1.⟦ l ⟧ˡ x)
  ca = at-≡ (C2.ctrl-sem L1.⟦ l ⟧ˡ x₀ x) (Eq.cong (x₀ ∷_) (CL.diag l x)) refl

private
  b20 : binom2 0F ≡ 0F
  b20 = solve 1 (λ t → con (ℤ.+ 0) :* (con (ℤ.+ 0) :- con (ℤ.+ 1)) :* t := con (ℤ.+ 0)) refl half

  b30 : binom3 0F ≡ 0F
  b30 = solve 1 (λ t → con (ℤ.+ 0) :* (con (ℤ.+ 0) :- con (ℤ.+ 1)) :* (con (ℤ.+ 0) :- (con (ℤ.+ 1) :+ con (ℤ.+ 1))) :* t
                       := con (ℤ.+ 0)) refl sixth

  b21 : binom2 1F ≡ 0F
  b21 = solve 1 (λ t → con (ℤ.+ 1) :* (con (ℤ.+ 1) :- con (ℤ.+ 1)) :* t := con (ℤ.+ 0)) refl half

  b31 : binom3 1F ≡ 0F
  b31 = solve 1 (λ t → con (ℤ.+ 1) :* (con (ℤ.+ 1) :- con (ℤ.+ 1)) :* (con (ℤ.+ 1) :- (con (ℤ.+ 1) :+ con (ℤ.+ 1))) :* t
                       := con (ℤ.+ 0)) refl sixth

  b32 : binom3 2F ≡ 0F
  b32 = solve 1 (λ t → (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :* ((con (ℤ.+ 1) :+ con (ℤ.+ 1)) :- con (ℤ.+ 1))
                         :* ((con (ℤ.+ 1) :+ con (ℤ.+ 1)) :- (con (ℤ.+ 1) :+ con (ℤ.+ 1))) :* t
                       := con (ℤ.+ 0)) refl sixth

  b22 : binom2 2F ≡ 1F
  b22 = Eq.trans (Odd.binom2-shift odd 1F) (Eq.trans (Eq.cong (_+ 1F) b21) (FR.+-identityˡ 1F))

  b23 : binom2 3F ≡ 3F
  b23 = Eq.trans (Odd.binom2-shift odd 2F) (Eq.trans (Eq.cong (_+ 2F) b22) (FR.+-comm 1F 2F))

  b33 : binom3 3F ≡ 1F
  b33 = Eq.trans (Big.binom3-shift gt3 2F) (Eq.trans (Eq.cong₂ _+_ b32 b22) (FR.+-identityˡ 1F))

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

  -- The phase at x₀ = 0, 1, 2, 3.
  φ0 : (e : E3Data n) (x : Labels n) → φE₃ e 0F x ≡ 0F
  φ0 (t , l , g) x = Eq.trans (Eq.cong₂ (λ u v → 0F * E2.ph Q2.⟦ g ⟧ᴰ x + (u * E1.ph L1.⟦ l ⟧ˡ x + t * v)) b20 b30)
    (solve 3 (λ a b t → con (ℤ.+ 0) :* a :+ (con (ℤ.+ 0) :* b :+ t :* con (ℤ.+ 0)) := con (ℤ.+ 0)) refl
           (E2.ph Q2.⟦ g ⟧ᴰ x) (E1.ph L1.⟦ l ⟧ˡ x) t)

  φ1 : (e : E3Data n) (x : Labels n) → φE₃ e 1F x ≡ E2.ph Q2.⟦ proj₂ (proj₂ e) ⟧ᴰ x
  φ1 (t , l , g) x = Eq.trans (Eq.cong₂ (λ u v → 1F * E2.ph Q2.⟦ g ⟧ᴰ x + (u * E1.ph L1.⟦ l ⟧ˡ x + t * v)) b21 b31)
    (solve 3 (λ a b t → con (ℤ.+ 1) :* a :+ (con (ℤ.+ 0) :* b :+ t :* con (ℤ.+ 0)) := a) refl
           (E2.ph Q2.⟦ g ⟧ᴰ x) (E1.ph L1.⟦ l ⟧ˡ x) t)

  φ2 : (e : E3Data n) (x : Labels n) → φE₃ e 2F x ≡ 2F * E2.ph Q2.⟦ proj₂ (proj₂ e) ⟧ᴰ x + E1.ph L1.⟦ proj₁ (proj₂ e) ⟧ˡ x
  φ2 (t , l , g) x = Eq.trans (Eq.cong₂ (λ u v → 2F * E2.ph Q2.⟦ g ⟧ᴰ x + (u * E1.ph L1.⟦ l ⟧ˡ x + t * v)) b22 b32)
    (solve 3 (λ a b t → (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :* a :+ (con (ℤ.+ 1) :* b :+ t :* con (ℤ.+ 0))
                        := (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :* a :+ b) refl
           (E2.ph Q2.⟦ g ⟧ᴰ x) (E1.ph L1.⟦ l ⟧ˡ x) t)

  φ3 : (e : E3Data n) (x : Labels n) →
       φE₃ e 3F x ≡ (3F * E2.ph Q2.⟦ proj₂ (proj₂ e) ⟧ᴰ x + 3F * E1.ph L1.⟦ proj₁ (proj₂ e) ⟧ˡ x) + proj₁ e
  φ3 (t , l , g) x = Eq.trans (Eq.cong₂ (λ u v → 3F * E2.ph Q2.⟦ g ⟧ᴰ x + (u * E1.ph L1.⟦ l ⟧ˡ x + t * v)) b23 b33)
    (solve 4 (λ a b t c → c :* a :+ (c :* b :+ t :* con (ℤ.+ 1)) := (c :* a :+ c :* b) :+ t) refl
           (E2.ph Q2.⟦ g ⟧ᴰ x) (E1.ph L1.⟦ l ⟧ˡ x) t 3F)

-- The phase determines the form.
E₃-unique : (e e' : E3Data n) → (∀ x₀ x → φE₃ e x₀ x ≡ φE₃ e' x₀ x) → (₁₊ n) ⊢ E₃ e ≈ E₃ e'
E₃-unique {n} e@(t , l , g) e'@(t' , l' , g') eq =
  cong (refl' (Eq.cong (T h ^ᶠ_) tt)) (cong (C2.ctrl-cong (CL.completeness n l≐)) (C1.ctrl-cong (CQ.completeness n g≐)))
  where
  open Width (₁₊ n)
  Gp Gp' Lp Lp' : Labels n → F
  Gp  x = E2.ph Q2.⟦ g ⟧ᴰ x
  Gp' x = E2.ph Q2.⟦ g' ⟧ᴰ x
  Lp  x = E1.ph L1.⟦ l ⟧ˡ x
  Lp' x = E1.ph L1.⟦ l' ⟧ˡ x
  GG : ∀ x → Gp x ≡ Gp' x
  GG x = Eq.trans (Eq.sym (φ1 e x)) (Eq.trans (eq 1F x) (φ1 e' x))
  LL : ∀ x → Lp x ≡ Lp' x
  LL x = cancel+ˡ (Eq.trans (Eq.sym (φ2 e x)) (Eq.trans (eq 2F x) (Eq.trans (φ2 e' x) (Eq.cong (λ u → 2F * u + Lp' x) (Eq.sym (GG x))))))
  tt : t ≡ t'
  tt = cancel+ˡ (Eq.trans (Eq.sym (φ3 e 0ᵛ)) (Eq.trans (eq 3F 0ᵛ)
         (Eq.trans (φ3 e' 0ᵛ) (Eq.cong₂ (λ u v → (3F * u + 3F * v) + t') (Eq.sym (GG 0ᵛ)) (Eq.sym (LL 0ᵛ))))))
  l≐ : SI1.⟦ L1.⟦ l ⟧ˡ ⟧ ≐ SI1.⟦ L1.⟦ l' ⟧ˡ ⟧
  l≐ x = Eq.cong₂ _,_ (Eq.trans (CL.diag l x) (Eq.sym (CL.diag l' x))) (LL x)
  g≐ : SI2.⟦ Q2.⟦ g ⟧ᴰ ⟧ ≐ SI2.⟦ Q2.⟦ g' ⟧ᴰ ⟧
  g≐ x = Eq.cong₂ _,_ (Eq.trans (CQ.de-diag g x) (Eq.sym (CQ.de-diag g' x))) (GG x)

------------------------------------------------------------------------
-- Equal phases, equal expressions

unique₀ : (d d' : DE₃ 0) → (∀ x → ph ⟦ d ⟧³ x ≡ ph ⟦ d' ⟧³ x) → 0 ⊢ ⟦ d ⟧³ ≈ ⟦ d' ⟧³
unique₀ (de s [] [] ∣ []) (de s' [] [] ∣ []) e = Width.refl' 0 (Eq.cong (λ t → ⟦ de t [] [] ∣ [] ⟧³) ss)
  where
  at : (t : F) → ph ⟦ de t [] [] ∣ [] ⟧³ [] ≡ t
  at t = Eq.trans (Eq.cong proj₂ (DiagC-• (DiagC-• (DiagC-^ᶠ (ω-diag h₁) t) (DiagC-• DiagC-ε DiagC-ε)) DiagC-ε []))
           (solve 1 (λ t → con (ℤ.+ 0) :+ ((con (ℤ.+ 0) :+ con (ℤ.+ 0)) :+ t :* con (ℤ.+ 1)) := t) refl t)
  ss : s ≡ s'
  ss = Eq.trans (Eq.sym (at s)) (Eq.trans (e []) (at s'))
unique₀ (de s [] ((() , _) ∷ _) ∣ _) _ _
unique₀ (de s [] [] ∣ ((() , _) ∷ _)) _ _
unique₀ (de s [] [] ∣ []) (de s' [] ((() , _) ∷ _) ∣ _) _
unique₀ (de s [] [] ∣ []) (de s' [] [] ∣ ((() , _) ∷ _)) _

unique : Complete n → (d d' : DE₃ (₁₊ n)) → (∀ x → ph ⟦ d ⟧³ x ≡ ph ⟦ d' ⟧³ x) → (₁₊ n) ⊢ ⟦ d ⟧³ ≈ ⟦ d' ⟧³
unique {n} IH d d' e = begin
  ⟦ d ⟧³                       ≈⟨ proj₂ (split₃ d) ⟩
  ⟦ U ⟧³ ↑ • E₃ ef             ≈⟨ cong (lift (IH U≐)) (E₃-unique ef ef' φ≡) ⟩
  ⟦ U' ⟧³ ↑ • E₃ ef'           ≈⟨ sym (proj₂ (split₃ d')) ⟩
  ⟦ d' ⟧³                      ∎
  where
  open Width (₁₊ n)
  U  = proj₁ (proj₁ (split₃ d))
  ef = proj₂ (proj₁ (split₃ d))
  U'  = proj₁ (proj₁ (split₃ d'))
  ef' = proj₂ (proj₁ (split₃ d'))
  ph-split : (W : DE₃ n) (f : E3Data n) (x₀ : F) (x : Labels n) →
             ph (⟦ W ⟧³ ↑ • E₃ f) (x₀ ∷ x) ≡ φE₃ f x₀ x + ph ⟦ W ⟧³ x
  ph-split W f x₀ x = Eq.trans (ph-• (⟦ W ⟧³ ↑) (E₃ f) (x₀ ∷ x))
    (Eq.cong₂ _+_ (Eq.cong proj₂ (E₃-sem f x₀ x))
                  (Eq.trans (Eq.cong (ph (⟦ W ⟧³ ↑)) (Eq.cong proj₁ (E₃-sem f x₀ x))) (ph-↑ ⟦ W ⟧³ x₀ x)))
  pd : (x₀ : F) (x : Labels n) → ph ⟦ d ⟧³ (x₀ ∷ x) ≡ φE₃ ef x₀ x + ph ⟦ U ⟧³ x
  pd x₀ x = Eq.trans (ph-≈ (proj₂ (split₃ d)) (x₀ ∷ x)) (ph-split U ef x₀ x)
  pd' : (x₀ : F) (x : Labels n) → ph ⟦ d' ⟧³ (x₀ ∷ x) ≡ φE₃ ef' x₀ x + ph ⟦ U' ⟧³ x
  pd' x₀ x = Eq.trans (ph-≈ (proj₂ (split₃ d')) (x₀ ∷ x)) (ph-split U' ef' x₀ x)
  at0 : (f : E3Data n) (s : F) (x : Labels n) → φE₃ f 0F x + s ≡ s
  at0 f s x = Eq.trans (Eq.cong (_+ s) (φ0 f x)) (FR.+-identityˡ s)
  phU : (x : Labels n) → ph ⟦ U ⟧³ x ≡ ph ⟦ U' ⟧³ x
  phU x = Eq.trans (Eq.sym (at0 ef _ x))
            (Eq.trans (Eq.sym (pd 0F x)) (Eq.trans (e (0F ∷ x)) (Eq.trans (pd' 0F x) (at0 ef' _ x))))
  U≐ : ⟦ ⟦ U ⟧³ ⟧ ≐ ⟦ ⟦ U' ⟧³ ⟧
  U≐ x = Eq.cong₂ _,_ (Eq.trans (de₃-diag U x) (Eq.sym (de₃-diag U' x))) (phU x)
  φ≡ : ∀ x₀ x → φE₃ ef x₀ x ≡ φE₃ ef' x₀ x
  φ≡ x₀ x = cancel+ (Eq.trans (Eq.sym (pd x₀ x)) (Eq.trans (e (x₀ ∷ x)) (Eq.trans (pd' x₀ x) (Eq.cong (φE₃ ef' x₀ x +_) (Eq.sym (phU x))))))

------------------------------------------------------------------------
-- The generators at level 3

private
  _⋆ᵗ_ : DE₃ n → Fin n → DE₃ n
  d ⋆ᵗ j = d ⋆ᵛ³ uvec j

  tr-tr : (d : DE₃ n) (j : Fin n) → n ⊢ ⟦ d ⟧³ • Xc (uvec j) ≈ Xc (uvec j) • ⟦ d ⋆ᵗ j ⟧³
  tr-tr d j = ⋆ᵛ³-sound d (uvec j)

open Layer DE₃ ⟦_⟧³ d₀₃ d₀₃-ε _⋆ˡ³_ ⋆ˡ³-sound _⋆ᵗ_ tr-tr PG₃ ⟦_⟧ᵖ³ app₃ app₃-sound de₃-diag unique₀ unique

private
  up-kind : Kind PG₃ n → Kind PG₃ (₁₊ n)
  up-kind (lin y)              = lin (y ↥ₗ)
  up-kind (trX j)              = trX (suc j)
  up-kind (phs (pl gω))        = phs (pl gω)
  up-kind (phs (pl (gZ j)))    = phs (pl (gZ (suc j)))
  up-kind (phs (pl (gS j)))    = phs (pl (gS (suc j)))
  up-kind (phs (gT j))         = phs (gT (suc j))

  up-kind-sound : (k : Kind PG₃ n) → (₁₊ n) ⊢ ⟦ k ⟧ₖ ↑ ≈ ⟦ up-kind k ⟧ₖ
  up-kind-sound (lin y)            = Width.refl
  up-kind-sound (trX j)            = Width.sym Width.left-unit
  up-kind-sound (phs (pl gω))      = ω↑
  up-kind-sound (phs (pl (gZ j)))  = Width.refl
  up-kind-sound (phs (pl (gS j)))  = Width.refl
  up-kind-sound (phs (gT j))       = Width.refl

kind : Gen n → Kind PG₃ n
kind (gate₀ (ω-gate _))     = phs (pl gω)
kind (gate₁ X-gate)         = trX zero
kind (gate₁ (M-gate a nz))  = lin (mul (unit a nz))
kind (gate₁ (Z-gate _))     = phs (pl (gZ zero))
kind (gate₁ (S-gate _))     = phs (pl (gS zero))
kind (gate₁ (T-gate _))     = phs (gT zero)
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
kind-sound (gate₁ (T-gate _))    = Width.refl
kind-sound (gate₂ CX-gate)       = Width.refl
kind-sound (gate₂ SWAP-gate)     = Width.refl
kind-sound {₁₊ n} (g ↥)          = Width.trans (lift (kind-sound g)) (up-kind-sound (kind g))

open Run kind kind-sound public using (completeness)
