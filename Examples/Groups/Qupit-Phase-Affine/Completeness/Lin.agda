------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of LinPhase_d
--
-- At level 1 the diagonal layer is a scalar and a column of Z's,
-- ω^s • Zc c, with phase s + c · x: a linear generator transforms the
-- column, a translation adds to the scalar (Phase.Linear), and the
-- phase generators ω and Z add to s and c.  The phase function
-- determines s (at 0) and c (as a linear form), so equal phases give
-- equal forms, and Completeness.Layered does the rest.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Completeness.Lin
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Data.Empty using (⊥ ; ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith ; head ; tail)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 1
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime 1
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime 1
  using (DiagC ; DiagC-• ; DiagC-↑ ; DiagC-ε ; DiagC-≡ ; DiagC-^ᶠ ; Z-diag ; ω-diag)
open import Examples.Groups.Qupit-Phase-Affine.Soundness p-2 p-prime 1 using (Admissible)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime 1
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime 1
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime 1 using (unit)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime 1
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime 1 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime 1

-- Level 1 is admissible for every p.
adm : Admissible
adm = (λ { (s≤s ()) }) , (λ { (s≤s ()) })

private
  h : 1 ≤ 1
  h = s≤s z≤n

open import Examples.Groups.Qupit-Phase-Affine.Phase.Linear p-2 p-prime 1 h
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime 1 adm
open import Examples.Groups.Qupit-Phase-Affine.Linear.Semantics p-2 p-prime 1 adm
  using (dot ; dot-injective)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Layered p-2 p-prime 1 adm

private
  variable
    n : ℕ

  no2 : 2 ≤ 1 → ⊥
  no2 (s≤s ())

  no3 : 3 ≤ 1 → ⊥
  no3 (s≤s ())

------------------------------------------------------------------------
-- The layer: a scalar and a column of Z's

D : ℕ → Set
D n = F × Vec F n

⟦_⟧ᵈ : D n → Circuit n
⟦ s , c ⟧ᵈ = ω h ^ᶠ s • Zc c

d₀ : D n
d₀ = 0F , 0ᵛ

d₀-ε : n ⊢ ⟦ d₀ {n} ⟧ᵈ ≈ ε
d₀-ε {n} = trans left-unit Zc-zero
  where open Width n

_⋆ˡ_ : D n → LGen n → D n
(s , c) ⋆ˡ y = s , c ⋆ᴿ y

lin-tr : (d : D n) (y : LGen n) → n ⊢ ⟦ d ⟧ᵈ • [ ι y ]ʷ ≈ [ ι y ]ʷ • ⟦ d ⋆ˡ y ⟧ᵈ
lin-tr {n} (s , c) y = begin
  (ω h ^ᶠ s • Zc c) • [ ι y ]ʷ          ≈⟨ trans assoc (back _ (Z-push y c)) ⟩
  ω h ^ᶠ s • [ ι y ]ʷ • Zc (c ⋆ᴿ y)     ≈⟨ trans (sym assoc) (trans (front _ (ωᶠ-comm s _)) assoc) ⟩
  [ ι y ]ʷ • ω h ^ᶠ s • Zc (c ⋆ᴿ y)     ∎
  where open Width n

_⋆ᵛ_ : D n → Vec F n → D n
(s , c) ⋆ᵛ v = s + c ·ᵛ v , c

tr-tr′ : (d : D n) (v : Vec F n) → n ⊢ ⟦ d ⟧ᵈ • Xc v ≈ Xc v • ⟦ d ⋆ᵛ v ⟧ᵈ
tr-tr′ {n} (s , c) v = begin
  (ω h ^ᶠ s • Zc c) • Xc v                          ≈⟨ trans assoc (back _ (Zc-Xc c v)) ⟩
  ω h ^ᶠ s • Xc v • Zc c • ω h ^ᶠ (c ·ᵛ v)          ≈⟨ trans (sym assoc) (trans (front _ (ωᶠ-comm s _)) assoc) ⟩
  Xc v • ω h ^ᶠ s • Zc c • ω h ^ᶠ (c ·ᵛ v)          ≈⟨ back _ (back _ (sym (ωᶠ-comm (c ·ᵛ v) _))) ⟩
  Xc v • ω h ^ᶠ s • ω h ^ᶠ (c ·ᵛ v) • Zc c          ≈⟨ back _ (trans (sym assoc) (front _ (OW.^ᶠ-+ s (c ·ᵛ v)))) ⟩
  Xc v • ω h ^ᶠ (s + c ·ᵛ v) • Zc c                 ∎
  where
  open Width n
  module OW = Pow.Order n {ω h} ω-order

_⋆ᵗ_ : D n → Fin n → D n
d ⋆ᵗ j = d ⋆ᵛ uvec j

tr-tr : (d : D n) (j : Fin n) → n ⊢ ⟦ d ⟧ᵈ • Xc (uvec j) ≈ Xc (uvec j) • ⟦ d ⋆ᵗ j ⟧ᵈ
tr-tr d j = tr-tr′ d (uvec j)

------------------------------------------------------------------------
-- The phase generators: ω, and a column of Z's

data PG (n : ℕ) : Set where
  gω : PG n
  gZ : Vec F n → PG n

⟦_⟧ᵖ : PG n → Circuit n
⟦ gω ⟧ᵖ   = ω h
⟦ gZ e ⟧ᵖ = Zc e

app : D n → PG n → D n
app (s , c) gω     = s + 1F , c
app (s , c) (gZ e) = s , zipWith _+_ c e

app-sound : (d : D n) (g : PG n) → n ⊢ ⟦ d ⟧ᵈ • ⟦ g ⟧ᵖ ≈ ⟦ app d g ⟧ᵈ
app-sound {n} (s , c) gω = begin
  (ω h ^ᶠ s • Zc c) • ω h           ≈⟨ trans assoc (back _ (sym (ω-comm _))) ⟩
  ω h ^ᶠ s • ω h • Zc c             ≈⟨ trans (sym assoc) (front _ (OW.^ᶠ-+ s 1F)) ⟩
  ω h ^ᶠ (s + 1F) • Zc c            ∎
  where
  open Width n
  module OW = Pow.Order n {ω h} ω-order
app-sound {n} (s , c) (gZ e) = trans assoc (back _ (Zc-add c e))
  where open Width n

------------------------------------------------------------------------
-- Semantics of the layer

private
  ·ᵛ≡dot : (c x : Vec F n) → c ·ᵛ x ≡ dot c x
  ·ᵛ≡dot []       []       = refl
  ·ᵛ≡dot (c ∷ cs) (a ∷ x)  = Eq.cong (c * a +_) (·ᵛ≡dot cs x)

  Zc-diag : (c : Vec F n) → DiagC (Zc c) (λ x → c ·ᵛ x)
  Zc-diag []       [] = DiagC-ε []
  Zc-diag (c ∷ cs) = DiagC-≡ (DiagC-• (DiagC-^ᶠ (Z-diag h) c) (DiagC-↑ (Zc-diag cs)))
    λ { (a ∷ x) → FR.+-comm _ _ }

  d-diag : (d : D n) → DiagC ⟦ d ⟧ᵈ (λ x → proj₂ d ·ᵛ x + proj₁ d)
  d-diag (s , c) = DiagC-≡ (DiagC-• (DiagC-^ᶠ (ω-diag h) s) (Zc-diag c))
    λ x → Eq.cong (c ·ᵛ x +_) (FR.*-identityʳ s)

diag : (d : D n) (x : Labels n) → fn ⟦ d ⟧ᵈ x ≡ x
diag d x = Eq.cong proj₁ (d-diag d x)

private
  ph-d : (d : D n) (x : Labels n) → ph ⟦ d ⟧ᵈ x ≡ proj₂ d ·ᵛ x + proj₁ d
  ph-d d x = Eq.cong proj₂ (d-diag d x)

  zero-dot : (c : Vec F n) → c ·ᵛ 0ᵛ ≡ 0F
  zero-dot []       = refl
  zero-dot (c ∷ cs) = Eq.trans (Eq.cong₂ _+_ (FR.zeroʳ c) (zero-dot cs)) (FR.+-identityʳ 0F)

  -- The phase determines the form.
  same-form : (d d' : D n) → (∀ x → ph ⟦ d ⟧ᵈ x ≡ ph ⟦ d' ⟧ᵈ x) → d ≡ d'
  same-form (s , c) (s' , c') e = Eq.cong₂ _,_ es (dot-injective c c' λ x →
    Eq.trans (Eq.sym (·ᵛ≡dot c x)) (Eq.trans (cancel+ (Eq.trans (Eq.sym (ph-d (s , c) x))
      (Eq.trans (e x) (Eq.trans (ph-d (s' , c') x) (Eq.cong (c' ·ᵛ x +_) (Eq.sym es)))))) (·ᵛ≡dot c' x)))
    where
    at0 : (d : D _) → ph ⟦ d ⟧ᵈ 0ᵛ ≡ proj₁ d
    at0 (t , b) = Eq.trans (ph-d (t , b) 0ᵛ) (Eq.trans (Eq.cong (_+ t) (zero-dot b)) (FR.+-identityˡ t))
    es : s ≡ s'
    es = Eq.trans (Eq.sym (at0 (s , c))) (Eq.trans (e 0ᵛ) (at0 (s' , c')))
    cancel+ : ∀ {a b : F} → a + s ≡ b + s → a ≡ b
    cancel+ {a} {b} q = begin
      a                 ≡⟨ Eq.sym (FR.+-identityʳ a) ⟩
      a + 0F            ≡⟨ Eq.cong (a +_) (Eq.sym (FR.-‿inverseʳ s)) ⟩
      a + (s + - s)     ≡⟨ Eq.sym (FR.+-assoc a s (- s)) ⟩
      (a + s) + - s     ≡⟨ Eq.cong (_+ - s) q ⟩
      (b + s) + - s     ≡⟨ FR.+-assoc b s (- s) ⟩
      b + (s + - s)     ≡⟨ Eq.cong (b +_) (FR.-‿inverseʳ s) ⟩
      b + 0F            ≡⟨ FR.+-identityʳ b ⟩
      b                 ∎
      where open ≡-Reasoning

unique₀ : (d d' : D 0) → (∀ x → ph ⟦ d ⟧ᵈ x ≡ ph ⟦ d' ⟧ᵈ x) → 0 ⊢ ⟦ d ⟧ᵈ ≈ ⟦ d' ⟧ᵈ
unique₀ d d' e = Width.refl' 0 (Eq.cong ⟦_⟧ᵈ (same-form d d' e))

unique : Complete n → (d d' : D (₁₊ n)) → (∀ x → ph ⟦ d ⟧ᵈ x ≡ ph ⟦ d' ⟧ᵈ x) →
         (₁₊ n) ⊢ ⟦ d ⟧ᵈ ≈ ⟦ d' ⟧ᵈ
unique {n} _ d d' e = Width.refl' (₁₊ n) (Eq.cong ⟦_⟧ᵈ (same-form d d' e))

------------------------------------------------------------------------
-- The generators at level 1

open Layer D ⟦_⟧ᵈ d₀ d₀-ε _⋆ˡ_ lin-tr _⋆ᵗ_ tr-tr PG ⟦_⟧ᵖ app app-sound diag unique₀ unique

private
  up-kind : Kind PG n → Kind PG (₁₊ n)
  up-kind (lin y)       = lin (y ↥ₗ)
  up-kind (trX j)       = trX (suc j)
  up-kind (phs gω)      = phs gω
  up-kind (phs (gZ e))  = phs (gZ (0F ∷ e))

  up-kind-sound : (k : Kind PG n) → (₁₊ n) ⊢ ⟦ k ⟧ₖ ↑ ≈ ⟦ up-kind k ⟧ₖ
  up-kind-sound (lin y)      = Width.refl
  up-kind-sound (trX j)      = Width.sym Width.left-unit
  up-kind-sound (phs gω)     = ω↑
  up-kind-sound (phs (gZ e)) = Width.sym Width.left-unit

kind : Gen n → Kind PG n
kind (gate₀ (ω-gate _))     = phs gω
kind (gate₁ X-gate)         = trX zero
kind (gate₁ (M-gate a nz))  = lin (mul (unit a nz))
kind (gate₁ (Z-gate _))     = phs (gZ (1F ∷ 0ᵛ))
kind (gate₁ (S-gate h₂))    = ⊥-elim-irr (no2 h₂)
kind (gate₁ (T-gate h₃))    = ⊥-elim-irr (no3 h₃)
kind (gate₂ CX-gate)        = lin cx
kind (gate₂ SWAP-gate)      = lin sw
kind (g ↥)                  = up-kind (kind g)

kind-sound : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ⟦ kind g ⟧ₖ
kind-sound (gate₀ (ω-gate _))    = Width.refl
kind-sound {₁₊ n} (gate₁ X-gate) = sym (trans (back _ (lift Xc-zero)) right-unit)
  where open Width (₁₊ n)
kind-sound (gate₁ (M-gate a nz)) = Width.refl
kind-sound {₁₊ n} (gate₁ (Z-gate _)) = sym (trans (back _ (lift Zc-zero)) right-unit)
  where open Width (₁₊ n)
kind-sound (gate₁ (S-gate h₂))   = ⊥-elim-irr (no2 h₂)
kind-sound (gate₁ (T-gate h₃))   = ⊥-elim-irr (no3 h₃)
kind-sound (gate₂ CX-gate)       = Width.refl
kind-sound (gate₂ SWAP-gate)     = Width.refl
kind-sound {₁₊ n} (g ↥)          = Width.trans (lift (kind-sound g)) (up-kind-sound (kind g))

open Run kind kind-sound public using (completeness)
