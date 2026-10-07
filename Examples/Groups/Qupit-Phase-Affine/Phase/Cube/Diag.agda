------------------------------------------------------------------------
-- Presentations of groups
--
-- Diagonal expressions at level 3
--
-- A level-2 expression (Phase.Quad.Diag) and a list of iterates of
-- atoms of T,
--
--     ⟦ d ∣ ts ⟧³ = ⟦ d ⟧ᴰ • Π (Aᵀ ℓ)^k,
--
-- is a diagonal circuit, and any two commute (de₃∥): atoms of T commute
-- with everything diagonal (Phase.Cube.Atom).  They add, and the
-- generators move across them as at level 2; an atom of T passing a
-- translation leaves a level-2 expression behind (residᵀ).  A circuit
-- equal to an expression is diagonal (Diag₃), and such circuits are
-- closed under products, iterates, lifts and conjugation by linear
-- words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Diag
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; 0F ; 1F ; _+_ ; _*_ ; binom2 ; binom3 ; 1*)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; R-zero)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ ; slideᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (Xc ; _⋆ˣ*_)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Atom p-2 p-prime lv h gt3 public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₃ h

------------------------------------------------------------------------
-- Expressions

atomsᵀ : Atoms n → Circuit n
atomsᵀ []             = ε
atomsᵀ ((ℓ , k) ∷ ts) = atomᵀ ℓ ^ᶠ k • atomsᵀ ts

infix 4 _∣_
record DE₃ (n : ℕ) : Set where
  constructor _∣_
  field
    low  : DE n
    tats : Atoms n

open DE₃ public

⟦_⟧³ : DE₃ n → Circuit n
⟦ d ∣ ts ⟧³ = ⟦ d ⟧ᴰ • atomsᵀ ts

------------------------------------------------------------------------
-- Everything commutes

atomᵀ∥atom : (ℓ ℓ' : NZ n) → n ⊢ atomᵀ ℓ ∥ atom ℓ'
atomᵀ∥atom {suc m} ℓ ℓ' = Aᵀ∥Aˢ ℓ ℓ'

atomᵀ∥atomᵀ : (ℓ ℓ' : NZ n) → n ⊢ atomᵀ ℓ ∥ atomᵀ ℓ'
atomᵀ∥atomᵀ {suc m} ℓ ℓ' = Aᵀ∥Aᵀ ℓ ℓ'

Zc∥atomᵀ : (c : Vec F n) (ℓ : NZ n) → n ⊢ Zc c ∥ atomᵀ ℓ
Zc∥atomᵀ {suc m} c ℓ = Zc∥Aᵀ c ℓ

atomsᵀ∥ : (ts : Atoms n) {X : Circuit n} → (∀ ℓ k → n ⊢ (atomᵀ ℓ ^ᶠ k) ∥ X) → n ⊢ atomsᵀ ts ∥ X
atomsᵀ∥ {n} [] e = Width.trans Width.left-unit (Width.sym Width.right-unit)
atomsᵀ∥ ((ℓ , k) ∷ ts) e = •-∥ (e ℓ k) (atomsᵀ∥ ts e)

-- A level-2 expression and atoms of T commute.
de∥atomsᵀ : (d : DE n) (ts : Atoms n) → n ⊢ ⟦ d ⟧ᴰ ∥ atomsᵀ ts
de∥atomsᵀ (de s c as) ts =
  •-∥ (ωᶠ-comm s _)
      (•-∥ (∥-sym (atomsᵀ∥ ts λ ℓ k → ∥-^ᶠ k (∥-sym (Zc∥atomᵀ c ℓ))))
           (atoms∥ as λ ℓ k → ∥-sym (atomsᵀ∥ ts λ ℓ' k' → ∥-^ᶠ² k' k (atomᵀ∥atom ℓ' ℓ))))

atomsᵀ∥atomsᵀ : (ts us : Atoms n) → n ⊢ atomsᵀ ts ∥ atomsᵀ us
atomsᵀ∥atomsᵀ ts us = atomsᵀ∥ ts λ ℓ k → ∥-sym (atomsᵀ∥ us λ ℓ' k' → ∥-^ᶠ² k' k (atomᵀ∥atomᵀ ℓ' ℓ))

de₃∥ : (d e : DE₃ n) → n ⊢ ⟦ d ⟧³ ∥ ⟦ e ⟧³
de₃∥ (d ∣ ts) (e ∣ us) =
  •-∥ (∥-• (de∥ d e) (de∥atomsᵀ d us))
      (∥-• (∥-sym (de∥atomsᵀ e ts)) (atomsᵀ∥atomsᵀ ts us))

------------------------------------------------------------------------
-- Sums

infixl 6 _⊕³_
_⊕³_ : DE₃ n → DE₃ n → DE₃ n
(d ∣ ts) ⊕³ (e ∣ us) = (d ⊕ e) ∣ (ts ++ us)

atomsᵀ-++ : (ts us : Atoms n) → n ⊢ atomsᵀ (ts ++ us) ≈ atomsᵀ ts • atomsᵀ us
atomsᵀ-++ {n} [] us = Width.sym Width.left-unit
atomsᵀ-++ {n} ((ℓ , k) ∷ ts) us = Width.trans (Width.back n _ (atomsᵀ-++ ts us)) (Width.sym Width.assoc)

⊕³-sound : (d e : DE₃ n) → n ⊢ ⟦ d ⟧³ • ⟦ e ⟧³ ≈ ⟦ d ⊕³ e ⟧³
⊕³-sound {n} (d ∣ ts) (e ∣ us) = begin
  (⟦ d ⟧ᴰ • atomsᵀ ts) • ⟦ e ⟧ᴰ • atomsᵀ us
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ⟦ d ⟧ᴰ • (atomsᵀ ts • ⟦ e ⟧ᴰ) • atomsᵀ us
    ≈⟨ back _ (front _ (sym (de∥atomsᵀ e ts))) ⟩
  ⟦ d ⟧ᴰ • (⟦ e ⟧ᴰ • atomsᵀ ts) • atomsᵀ us
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (⟦ d ⟧ᴰ • ⟦ e ⟧ᴰ) • atomsᵀ ts • atomsᵀ us
    ≈⟨ cong (⊕-sound d e) (sym (atomsᵀ-++ ts us)) ⟩
  ⟦ d ⊕ e ⟧ᴰ • atomsᵀ (ts ++ us) ∎
  where open Width n

------------------------------------------------------------------------
-- One wire up

atomsᵀ-↑ : (ts : Atoms n) → (₁₊ n) ⊢ atomsᵀ ts ↑ ≈ atomsᵀ (lift-ats ts)
atomsᵀ-↑ {zero} [] = Width.refl
atomsᵀ-↑ {zero} ((() , _) ∷ _)
atomsᵀ-↑ {suc m} [] = Width.refl
atomsᵀ-↑ {suc m} ((ℓ , k) ∷ ts) =
  Width.cong (Width.trans (Width.refl' (₂₊ m) (↑ᶠ (AT.A ℓ) k)) (Pow.pow-cong (₂₊ m) (toℕ k) (Width.sym (AT.A-small ℓ))))
             (atomsᵀ-↑ ts)

lift-d₃ : DE₃ n → DE₃ (₁₊ n)
lift-d₃ (d ∣ ts) = lift-d d ∣ lift-ats ts

lift₃-sound : (d : DE₃ n) → (₁₊ n) ⊢ ⟦ d ⟧³ ↑ ≈ ⟦ lift-d₃ d ⟧³
lift₃-sound (d ∣ ts) = Width.cong (lift-sound d) (atomsᵀ-↑ ts)

------------------------------------------------------------------------
-- Linear generators transport the rows

atomᵀ-step : (ℓ : NZ n) (y : LGen n) → n ⊢ atomᵀ ℓ • [ ι y ]ʷ ≈ [ ι y ]ʷ • atomᵀ (ℓ ⋆ y)
atomᵀ-step {suc m} ℓ y = AT.A-step ℓ y

atomsᵀ-lin : (ts : Atoms n) (y : LGen n) → n ⊢ atomsᵀ ts • [ ι y ]ʷ ≈ [ ι y ]ʷ • atomsᵀ (ats⋆ ts y)
atomsᵀ-lin {n} [] y = Width.trans Width.left-unit (Width.sym Width.right-unit)
atomsᵀ-lin {n} ((ℓ , k) ∷ ts) y = begin
  (atomᵀ ℓ ^ᶠ k • atomsᵀ ts) • Y             ≈⟨ trans assoc (back _ (atomsᵀ-lin ts y)) ⟩
  atomᵀ ℓ ^ᶠ k • Y • atomsᵀ (ats⋆ ts y)      ≈⟨ trans (sym assoc) (trans (front _ (sym (slideᶠ k (sym (atomᵀ-step ℓ y))))) assoc) ⟩
  Y • atomᵀ (ℓ ⋆ y) ^ᶠ k • atomsᵀ (ats⋆ ts y) ∎
  where
  open Width n
  Y = [ ι y ]ʷ

infixl 5 _⋆ˡ³_
_⋆ˡ³_ : DE₃ n → LGen n → DE₃ n
(d ∣ ts) ⋆ˡ³ y = (d ⋆ˡ y) ∣ ats⋆ ts y

⋆ˡ³-sound : (d : DE₃ n) (y : LGen n) → n ⊢ ⟦ d ⟧³ • [ ι y ]ʷ ≈ [ ι y ]ʷ • ⟦ d ⋆ˡ³ y ⟧³
⋆ˡ³-sound {n} (d ∣ ts) y = begin
  (⟦ d ⟧ᴰ • atomsᵀ ts) • Y                   ≈⟨ trans assoc (back _ (atomsᵀ-lin ts y)) ⟩
  ⟦ d ⟧ᴰ • Y • atomsᵀ (ats⋆ ts y)            ≈⟨ trans (sym assoc) (trans (front _ (⋆ˡ-sound d y)) assoc) ⟩
  Y • ⟦ d ⋆ˡ y ⟧ᴰ • atomsᵀ (ats⋆ ts y)       ∎
  where
  open Width n
  Y = [ ι y ]ʷ

-- Along a linear word.
infixl 5 _⋆ˡ³*_
_⋆ˡ³*_ : DE₃ n → Word (LGen n) → DE₃ n
d ⋆ˡ³* [ y ]ʷ  = d ⋆ˡ³ y
d ⋆ˡ³* ε       = d
d ⋆ˡ³* (L • M) = d ⋆ˡ³* L ⋆ˡ³* M

⋆ˡ³*-sound : (d : DE₃ n) (L : Word (LGen n)) → n ⊢ ⟦ d ⟧³ • ⌊ L ⌋ ≈ ⌊ L ⌋ • ⟦ d ⋆ˡ³* L ⟧³
⋆ˡ³*-sound d [ y ]ʷ = ⋆ˡ³-sound d y
⋆ˡ³*-sound {n} d ε = Width.trans Width.right-unit (Width.sym Width.left-unit)
⋆ˡ³*-sound {n} d (L • M) = begin
  ⟦ d ⟧³ • ⌊ L ⌋ • ⌊ M ⌋                       ≈⟨ trans (sym assoc) (trans (front _ (⋆ˡ³*-sound d L)) assoc) ⟩
  ⌊ L ⌋ • ⟦ d ⋆ˡ³* L ⟧³ • ⌊ M ⌋                ≈⟨ back _ (⋆ˡ³*-sound (d ⋆ˡ³* L) M) ⟩
  ⌊ L ⌋ • ⌊ M ⌋ • ⟦ d ⋆ˡ³* L ⋆ˡ³* M ⟧³         ≈⟨ sym assoc ⟩
  (⌊ L ⌋ • ⌊ M ⌋) • ⟦ d ⋆ˡ³* L ⋆ˡ³* M ⟧³       ∎
  where open Width n

------------------------------------------------------------------------
-- Translations

-- What the atoms of T leave behind past a translation.
residᵀ : Atoms n → Vec F n → DE n
residᵀ [] v = de 0F 0ᵛ []
residᵀ {suc m} ((ℓ , k) ∷ ts) v =
  de (k * binom3 (head (v ⋆ˣ* rL ℓ))) ((k * binom2 (head (v ⋆ˣ* rL ℓ)) ∷ 0ᵛ) ⋆ᴿ* rL ℓ)
     ((ℓ , k * head (v ⋆ˣ* rL ℓ)) ∷ []) ⊕ residᵀ ts v
residᵀ {zero} ((() , _) ∷ _) v

atomsᵀ-X : (ts : Atoms n) (v : Vec F n) → n ⊢ atomsᵀ ts • Xc v ≈ Xc v • atomsᵀ ts • ⟦ residᵀ ts v ⟧ᴰ
atomsᵀ-X {n} [] v = begin
  ε • Xc v                     ≈⟨ trans left-unit (sym right-unit) ⟩
  Xc v • ε                     ≈⟨ back _ (sym (trans left-unit (sym (proj₂ Diag-ε)))) ⟩
  Xc v • ε • ⟦ de 0F 0ᵛ [] ⟧ᴰ   ∎
  where open Width n
atomsᵀ-X {suc m} ((ℓ , k) ∷ ts) v = begin
  (AT.A ℓ ^ᶠ k • B) • Xc v
    ≈⟨ trans assoc (back _ (atomsᵀ-X ts v)) ⟩
  AT.A ℓ ^ᶠ k • Xc v • B • ⟦ Rs ⟧ᴰ
    ≈⟨ trans (sym assoc) (trans (front _ (Aᵀ-Xc ℓ k v)) assoc) ⟩
  Xc v • (AT.A ℓ ^ᶠ k • A ℓ ^ᶠ q • Zc z • ω h₁ ^ᶠ t) • B • ⟦ Rs ⟧ᴰ
    ≈⟨ back _ (trans assoc (back _ (front _ D≈))) ⟩
  Xc v • AT.A ℓ ^ᶠ k • ⟦ D ⟧ᴰ • B • ⟦ Rs ⟧ᴰ
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (de∥atomsᵀ D ts)) assoc))) ⟩
  Xc v • AT.A ℓ ^ᶠ k • B • ⟦ D ⟧ᴰ • ⟦ Rs ⟧ᴰ
    ≈⟨ back _ (trans (sym assoc) (back _ (⊕-sound D Rs))) ⟩
  Xc v • (AT.A ℓ ^ᶠ k • B) • ⟦ D ⊕ Rs ⟧ᴰ ∎
  where
  open Width (₁₊ m)
  B = atomsᵀ ts
  Rs = residᵀ ts v
  v₀ q t : F
  v₀ = head (v ⋆ˣ* rL ℓ)
  q  = k * v₀
  t  = k * binom3 v₀
  z  = (k * binom2 v₀ ∷ 0ᵛ) ⋆ᴿ* rL ℓ
  D : DE (₁₊ m)
  D = de t z ((ℓ , q) ∷ [])
  D≈ : (₁₊ m) ⊢ A ℓ ^ᶠ q • Zc z • ω h₁ ^ᶠ t ≈ ⟦ D ⟧ᴰ
  D≈ = begin
    A ℓ ^ᶠ q • Zc z • ω h₁ ^ᶠ t          ≈⟨ back _ (sym (ωᶠ-comm t (Zc z))) ⟩
    A ℓ ^ᶠ q • ω h₁ ^ᶠ t • Zc z          ≈⟨ trans (sym assoc) (trans (front _ (sym (ωᶠ-comm t (A ℓ ^ᶠ q)))) assoc) ⟩
    ω h₁ ^ᶠ t • A ℓ ^ᶠ q • Zc z          ≈⟨ back _ (∥-^ᶠ q (∥-sym (Zc∥A z ℓ))) ⟩
    ω h₁ ^ᶠ t • Zc z • A ℓ ^ᶠ q          ≈⟨ back _ (back _ (sym right-unit)) ⟩
    ω h₁ ^ᶠ t • Zc z • A ℓ ^ᶠ q • ε      ∎
atomsᵀ-X {zero} ((() , _) ∷ _) v

infixl 5 _⋆ᵛ³_
_⋆ᵛ³_ : DE₃ n → Vec F n → DE₃ n
(d ∣ ts) ⋆ᵛ³ v = ((d ⋆ᵛ v) ⊕ residᵀ ts v) ∣ ts

⋆ᵛ³-sound : (d : DE₃ n) (v : Vec F n) → n ⊢ ⟦ d ⟧³ • Xc v ≈ Xc v • ⟦ d ⋆ᵛ³ v ⟧³
⋆ᵛ³-sound {n} (d ∣ ts) v = begin
  (⟦ d ⟧ᴰ • atomsᵀ ts) • Xc v
    ≈⟨ trans assoc (back _ (atomsᵀ-X ts v)) ⟩
  ⟦ d ⟧ᴰ • Xc v • atomsᵀ ts • ⟦ Rs ⟧ᴰ
    ≈⟨ trans (sym assoc) (trans (front _ (⋆ᵛ-sound d v)) assoc) ⟩
  Xc v • ⟦ d ⋆ᵛ v ⟧ᴰ • atomsᵀ ts • ⟦ Rs ⟧ᴰ
    ≈⟨ back _ (back _ (sym (de∥atomsᵀ Rs ts))) ⟩
  Xc v • ⟦ d ⋆ᵛ v ⟧ᴰ • ⟦ Rs ⟧ᴰ • atomsᵀ ts
    ≈⟨ back _ (trans (sym assoc) (front _ (⊕-sound (d ⋆ᵛ v) Rs))) ⟩
  Xc v • ⟦ (d ⋆ᵛ v) ⊕ Rs ⟧ᴰ • atomsᵀ ts ∎
  where
  open Width n
  Rs = residᵀ ts v

------------------------------------------------------------------------
-- The phase generators

data PG₃ (n : ℕ) : Set where
  pl : PG n → PG₃ n
  gT : Fin n → PG₃ n

⟦_⟧ᵖ³ : PG₃ n → Circuit n
⟦ pl g ⟧ᵖ³      = ⟦ g ⟧ᵖ
⟦ gT zero ⟧ᵖ³    = T h
⟦ gT (suc j) ⟧ᵖ³ = ⟦ gT j ⟧ᵖ³ ↑

T-e : (j : Fin n) → n ⊢ ⟦ gT j ⟧ᵖ³ ≈ atomᵀ (eᴺ j)
T-e {suc n} zero = sym (trans (cong (Inv.⁻¹-cong (₁₊ n) r≈) (back _ r≈)) (trans left-unit right-unit))
  where
  open Width (₁₊ n)
  r≈ : (₁₊ n) ⊢ R 0ᵛ • M⟨ 1* ⟩ ≈ ε
  r≈ = trans (cong R-zero (ax ax1)) left-unit
T-e {suc (suc n)} (suc j) = Width.trans (lift (T-e j)) (Width.sym (AT.A-small (eᴺ j)))
T-e {suc zero} (suc ())

app₃ : DE₃ n → PG₃ n → DE₃ n
app₃ (d ∣ ts) (pl g) = app d g ∣ ts
app₃ (d ∣ ts) (gT j) = d ∣ (ts ++ ((eᴺ j , 1F) ∷ []))

app₃-sound : (d : DE₃ n) (g : PG₃ n) → n ⊢ ⟦ d ⟧³ • ⟦ g ⟧ᵖ³ ≈ ⟦ app₃ d g ⟧³
app₃-sound {n} (d ∣ ts) (pl g) = begin
  (⟦ d ⟧ᴰ • atomsᵀ ts) • ⟦ g ⟧ᵖ          ≈⟨ trans assoc (back _ (sym (via′ g≈ (de∥atomsᵀ (app (de 0F 0ᵛ []) g) ts)))) ⟩
  ⟦ d ⟧ᴰ • ⟦ g ⟧ᵖ • atomsᵀ ts            ≈⟨ trans (sym assoc) (front _ (app-sound d g)) ⟩
  ⟦ app d g ⟧ᴰ • atomsᵀ ts               ∎
  where
  open Width n
  g≈ : n ⊢ ⟦ g ⟧ᵖ ≈ ⟦ app (de 0F 0ᵛ []) g ⟧ᴰ
  g≈ = trans (sym left-unit) (trans (front _ (proj₂ Diag-ε)) (app-sound (de 0F 0ᵛ []) g))
  via′ : {a X X' : Circuit n} → n ⊢ X ≈ X' → n ⊢ X' ∥ a → n ⊢ X ∥ a
  via′ e c = ∥-sym (via e (∥-sym c))
app₃-sound {n} (d ∣ ts) (gT j) = begin
  (⟦ d ⟧ᴰ • atomsᵀ ts) • ⟦ gT j ⟧ᵖ³                ≈⟨ trans assoc (back _ (back _ (T-e j))) ⟩
  ⟦ d ⟧ᴰ • atomsᵀ ts • atomᵀ (eᴺ j)                 ≈⟨ back _ (sym (trans (atomsᵀ-++ ts _) (back _ right-unit))) ⟩
  ⟦ d ⟧ᴰ • atomsᵀ (ts ++ ((eᴺ j , 1F) ∷ []))        ∎
  where open Width n

------------------------------------------------------------------------
-- Diagonal circuits

Diag₃ : (n : ℕ) → Circuit n → Set
Diag₃ n w = Σ (DE₃ n) (λ d → n ⊢ w ≈ ⟦ d ⟧³)

module _ {n : ℕ} where

  open Width n

  diag₃∥ : {w v : Circuit n} → Diag₃ n w → Diag₃ n v → n ⊢ w ∥ v
  diag₃∥ (d , e) (d' , e') = trans (cong e e') (trans (de₃∥ d d') (sym (cong e' e)))

  Diag₃-≈ : {w v : Circuit n} → n ⊢ w ≈ v → Diag₃ n v → Diag₃ n w
  Diag₃-≈ e (d , e') = d , trans e e'

  Diag₃-• : {w v : Circuit n} → Diag₃ n w → Diag₃ n v → Diag₃ n (w • v)
  Diag₃-• (d , e) (d' , e') = d ⊕³ d' , trans (cong e e') (⊕³-sound d d')

  -- A level-2 diagonal circuit.
  Diag₃-2 : {w : Circuit n} → Diag n w → Diag₃ n w
  Diag₃-2 (d , e) = (d ∣ []) , trans e (sym right-unit)

  Diag₃-ε : Diag₃ n ε
  Diag₃-ε = Diag₃-2 Diag-ε

  Diag₃-^ : {w : Circuit n} → Diag₃ n w → (k : ℕ) → Diag₃ n (w ^ k)
  Diag₃-^ D zero          = Diag₃-ε
  Diag₃-^ D (suc zero)    = D
  Diag₃-^ D (suc (suc k)) = Diag₃-• D (Diag₃-^ D (suc k))

  Diag₃-^ᶠ : {w : Circuit n} → Diag₃ n w → (k : F) → Diag₃ n (w ^ᶠ k)
  Diag₃-^ᶠ D k = Diag₃-^ D (toℕ k)

  Diag₃-atomᵀ : (ℓ : NZ n) → Diag₃ n (atomᵀ ℓ)
  Diag₃-atomᵀ ℓ = (de 0F 0ᵛ [] ∣ ((ℓ , 1F) ∷ [])) ,
    sym (trans (front _ (sym (proj₂ Diag-ε))) (trans left-unit right-unit))

  -- Conjugation by a linear word.
  Diag₃-conj : {w : Circuit n} {g : Circuit n} → Diag₃ n w → (L : Word (LGen n)) → n ⊢ g • ⌊ L ⌋ ≈ ε →
               Diag₃ n (g • w • ⌊ L ⌋)
  Diag₃-conj {w} {g} (d , e) L gL = d ⋆ˡ³* L , (begin
    g • w • ⌊ L ⌋                       ≈⟨ back _ (trans (front _ e) (⋆ˡ³*-sound d L)) ⟩
    g • ⌊ L ⌋ • ⟦ d ⋆ˡ³* L ⟧³           ≈⟨ trans (sym assoc) (trans (front _ gL) left-unit) ⟩
    ⟦ d ⋆ˡ³* L ⟧³                       ∎)

Diag₃-↑ : {w : Circuit n} → Diag₃ n w → Diag₃ (₁₊ n) (w ↑)
Diag₃-↑ (d , e) = lift-d₃ d , Width.trans (lift e) (lift₃-sound d)

Diag₃-SWAP : {w : Circuit (₂₊ n)} → Diag₃ (₂₊ n) w → Diag₃ (₂₊ n) (SWAP • w • SWAP)
Diag₃-SWAP {n} D = Diag₃-conj D [ sw ]ʷ (ax swap-order)

Diag₃-T : Diag₃ (₁₊ n) (T h)
Diag₃-T = Diag₃-≈ (T-e zero) (Diag₃-atomᵀ (eᴺ zero))
