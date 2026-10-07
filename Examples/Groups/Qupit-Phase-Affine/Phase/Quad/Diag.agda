------------------------------------------------------------------------
-- Presentations of groups
--
-- Diagonal expressions at level 2
--
-- A power of ω, a column of Z's and a list of iterates of atoms of S,
--
--     ⟦ de s c as ⟧ᴰ = ω^s • Zc c • Π (A ℓ)^k,
--
-- is a diagonal circuit, and any two commute (de∥): ω is central, and
-- atoms commute with each other and with columns (Phase.Quad.Atom).  So
-- they add (⊕-sound), and the generators move across them:
--
--   a linear generator y transports every row (⋆ˡ-sound): the column
--   to c ⋆ᴿ y, an atom of ℓ to one of ℓ ⋆ y;
--   a translation adds to the scalar and the column (⋆ᵛ-sound): an
--   atom leaves a column of Z's and a power of ω behind (A-Xc);
--   one wire up is the lifted expression (lift-sound);
--   and ω, Z and S on any wire are expressions (app-sound).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Diag
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) (odd : 1 ≤ p-2) where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith ; head)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; 0F ; 1F ; _+_ ; _*_ ; binom2 ; 1* ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; R-zero)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ ; slideᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (Xc ; _⋆ˣ*_)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Atom p-2 p-prime lv h odd public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₂ h

------------------------------------------------------------------------
-- Expressions

-- The atom of a row, at any width.
atom : NZ n → Circuit n
atom {suc m} ℓ = A ℓ
atom {zero} ()

Atoms : ℕ → Set
Atoms n = List (NZ n × F)

atoms : Atoms n → Circuit n
atoms []             = ε
atoms ((ℓ , k) ∷ as) = atom ℓ ^ᶠ k • atoms as

record DE (n : ℕ) : Set where
  constructor de
  field
    dscal : F
    dcol  : Vec F n
    dats  : Atoms n

open DE public

⟦_⟧ᴰ : DE n → Circuit n
⟦ de s c as ⟧ᴰ = ω h₁ ^ᶠ s • Zc c • atoms as

------------------------------------------------------------------------
-- Everything commutes

-- A word passing every iterate of an atom passes a list of them.
atoms∥ : (as : Atoms n) {X : Circuit n} → (∀ ℓ k → n ⊢ (atom ℓ ^ᶠ k) ∥ X) → n ⊢ atoms as ∥ X
atoms∥ {n} [] e = Width.trans Width.left-unit (Width.sym Width.right-unit)
atoms∥ ((ℓ , k) ∷ as) e = •-∥ (e ℓ k) (atoms∥ as e)

atom∥atom : (ℓ ℓ' : NZ n) → n ⊢ atom ℓ ∥ atom ℓ'
atom∥atom {suc m} ℓ ℓ' = A∥A ℓ ℓ'

Zc∥atom : (c : Vec F n) (ℓ : NZ n) → n ⊢ Zc c ∥ atom ℓ
Zc∥atom {suc m} c ℓ = Zc∥A c ℓ

Zc∥Zc : (c c' : Vec F n) → n ⊢ Zc c ∥ Zc c'
Zc∥Zc {n} c c' = Width.trans (Zc-add c c')
  (Width.trans (Width.refl' n (Eq.cong Zc (VecP.zipWith-comm FR.+-comm c c'))) (Width.sym (Zc-add c' c)))

Zc∥atoms : (c : Vec F n) (as : Atoms n) → n ⊢ Zc c ∥ atoms as
Zc∥atoms c as = ∥-sym (atoms∥ as λ ℓ k → ∥-^ᶠ k (∥-sym (Zc∥atom c ℓ)))

atoms∥atoms : (as bs : Atoms n) → n ⊢ atoms as ∥ atoms bs
atoms∥atoms as bs = atoms∥ as λ ℓ k → ∥-sym (atoms∥ bs λ ℓ' k' → ∥-^ᶠ² k' k (atom∥atom ℓ' ℓ))

-- Any two expressions commute.
de∥ : (d e : DE n) → n ⊢ ⟦ d ⟧ᴰ ∥ ⟦ e ⟧ᴰ
de∥ (de s c as) e@(de s' c' as') =
  •-∥ (ωᶠ-comm s _)
      (•-∥ (∥-• (∥-sym (ωᶠ-comm s' _)) (∥-• (Zc∥Zc c c') (Zc∥atoms c as')))
           (∥-• (∥-sym (ωᶠ-comm s' _)) (∥-• (∥-sym (Zc∥atoms c' as)) (atoms∥atoms as as'))))

------------------------------------------------------------------------
-- Sums

infixl 6 _⊕_
_⊕_ : DE n → DE n → DE n
de s c as ⊕ de s' c' as' = de (s + s') (zipWith _+_ c c') (as ++ as')

atoms-++ : (as bs : Atoms n) → n ⊢ atoms (as ++ bs) ≈ atoms as • atoms bs
atoms-++ {n} [] bs = Width.sym Width.left-unit
atoms-++ {n} ((ℓ , k) ∷ as) bs = Width.trans (Width.back n _ (atoms-++ as bs)) (Width.sym Width.assoc)

⊕-sound : (d e : DE n) → n ⊢ ⟦ d ⟧ᴰ • ⟦ e ⟧ᴰ ≈ ⟦ d ⊕ e ⟧ᴰ
⊕-sound {n} (de s c as) (de s' c' as') = begin
  (ω h₁ ^ᶠ s • Zc c • atoms as) • ω h₁ ^ᶠ s' • Zc c' • atoms as'
    ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  ω h₁ ^ᶠ s • Zc c • (atoms as • ω h₁ ^ᶠ s') • Zc c' • atoms as'
    ≈⟨ back _ (back _ (front _ (sym (ωᶠ-comm s' _)))) ⟩
  ω h₁ ^ᶠ s • Zc c • (ω h₁ ^ᶠ s' • atoms as) • Zc c' • atoms as'
    ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • □) • □ • (□ • □)) Eq.refl ⟩
  ω h₁ ^ᶠ s • (Zc c • ω h₁ ^ᶠ s') • atoms as • (Zc c' • atoms as')
    ≈⟨ back _ (front _ (sym (ωᶠ-comm s' _))) ⟩
  ω h₁ ^ᶠ s • (ω h₁ ^ᶠ s' • Zc c) • atoms as • (Zc c' • atoms as')
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (sym (Zc∥atoms c' as))) assoc))) ⟩
  ω h₁ ^ᶠ s • (ω h₁ ^ᶠ s' • Zc c) • Zc c' • atoms as • atoms as'
    ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) ((□ • □) • (□ • □) • (□ • □)) Eq.refl ⟩
  (ω h₁ ^ᶠ s • ω h₁ ^ᶠ s') • (Zc c • Zc c') • (atoms as • atoms as')
    ≈⟨ cong (OW.^ᶠ-+ s s') (cong (Zc-add c c') (sym (atoms-++ as as'))) ⟩
  ω h₁ ^ᶠ (s + s') • Zc (zipWith _+_ c c') • atoms (as ++ as') ∎
  where
  open Width n
  module OW = Pow.Order n {ω h₁} ω-order

------------------------------------------------------------------------
-- One wire up

lift-ats : Atoms n → Atoms (₁₊ n)
lift-ats {zero} []                  = []
lift-ats {zero} ((() , _) ∷ _)
lift-ats {suc m} []                 = []
lift-ats {suc m} ((ℓ , k) ∷ as)     = (small ℓ , k) ∷ lift-ats as

lift-d : DE n → DE (₁₊ n)
lift-d (de s c as) = de s (0F ∷ c) (lift-ats as)

atoms-↑ : (as : Atoms n) → (₁₊ n) ⊢ atoms as ↑ ≈ atoms (lift-ats as)
atoms-↑ {zero} [] = Width.refl
atoms-↑ {zero} ((() , _) ∷ _)
atoms-↑ {suc m} [] = Width.refl
atoms-↑ {suc m} ((ℓ , k) ∷ as) =
  Width.cong (Width.trans (Width.refl' (₂₊ m) (↑ᶠ (A ℓ) k)) (Pow.pow-cong (₂₊ m) (toℕ k) (Width.sym (A-small ℓ))))
             (atoms-↑ as)

lift-sound : (d : DE n) → (₁₊ n) ⊢ ⟦ d ⟧ᴰ ↑ ≈ ⟦ lift-d d ⟧ᴰ
lift-sound {n} (de s c as) = cong (ωᶠ↑ s) (cong (sym left-unit) (atoms-↑ as))
  where open Width (₁₊ n)

------------------------------------------------------------------------
-- Linear generators transport the rows

ats⋆ : Atoms n → LGen n → Atoms n
ats⋆ []             y = []
ats⋆ ((ℓ , k) ∷ as) y = (ℓ ⋆ y , k) ∷ ats⋆ as y

infixl 5 _⋆ˡ_
_⋆ˡ_ : DE n → LGen n → DE n
de s c as ⋆ˡ y = de s (c ⋆ᴿ y) (ats⋆ as y)

atom-step : (ℓ : NZ n) (y : LGen n) → n ⊢ atom ℓ • [ ι y ]ʷ ≈ [ ι y ]ʷ • atom (ℓ ⋆ y)
atom-step {suc m} ℓ y = A-step ℓ y

atoms-lin : (as : Atoms n) (y : LGen n) → n ⊢ atoms as • [ ι y ]ʷ ≈ [ ι y ]ʷ • atoms (ats⋆ as y)
atoms-lin {n} [] y = Width.trans Width.left-unit (Width.sym Width.right-unit)
atoms-lin {n} ((ℓ , k) ∷ as) y = begin
  (atom ℓ ^ᶠ k • atoms as) • Y              ≈⟨ trans assoc (back _ (atoms-lin as y)) ⟩
  atom ℓ ^ᶠ k • Y • atoms (ats⋆ as y)       ≈⟨ trans (sym assoc) (trans (front _ (sym (slideᶠ k (sym (atom-step ℓ y))))) assoc) ⟩
  Y • atom (ℓ ⋆ y) ^ᶠ k • atoms (ats⋆ as y) ∎
  where
  open Width n
  Y = [ ι y ]ʷ

⋆ˡ-sound : (d : DE n) (y : LGen n) → n ⊢ ⟦ d ⟧ᴰ • [ ι y ]ʷ ≈ [ ι y ]ʷ • ⟦ d ⋆ˡ y ⟧ᴰ
⋆ˡ-sound {n} (de s c as) y = begin
  (ω h₁ ^ᶠ s • Zc c • atoms as) • Y                ≈⟨ trans assoc (back _ (trans assoc (back _ (atoms-lin as y)))) ⟩
  ω h₁ ^ᶠ s • Zc c • Y • atoms (ats⋆ as y)         ≈⟨ back _ (trans (sym assoc) (trans (front _ (Z-push y c)) assoc)) ⟩
  ω h₁ ^ᶠ s • Y • Zc (c ⋆ᴿ y) • atoms (ats⋆ as y)  ≈⟨ trans (sym assoc) (trans (front _ (ωᶠ-comm s Y)) assoc) ⟩
  Y • ω h₁ ^ᶠ s • Zc (c ⋆ᴿ y) • atoms (ats⋆ as y)  ∎
  where
  open Width n
  Y = [ ι y ]ʷ

------------------------------------------------------------------------
-- Translations add to the scalar and the column

-- What the atoms leave behind: a power of ω and a column.
resid : Atoms n → Vec F n → F × Vec F n
resid [] v = 0F , 0ᵛ
resid {suc m} ((ℓ , k) ∷ as) v =
  k * binom2 (head (v ⋆ˣ* rL ℓ)) + proj₁ (resid as v) ,
  zipWith _+_ ((k * head (v ⋆ˣ* rL ℓ) ∷ 0ᵛ) ⋆ᴿ* rL ℓ) (proj₂ (resid as v))
resid {zero} ((() , _) ∷ _) v

atoms-X : (as : Atoms n) (v : Vec F n) →
          n ⊢ atoms as • Xc v ≈ Xc v • atoms as • Zc (proj₂ (resid as v)) • ω h₁ ^ᶠ proj₁ (resid as v)
atoms-X {n} [] v = begin
  ε • Xc v                     ≈⟨ trans left-unit (sym right-unit) ⟩
  Xc v • ε                     ≈⟨ back _ (sym (trans left-unit (trans (front _ Zc-zero) left-unit))) ⟩
  Xc v • ε • Zc 0ᵛ • ε         ∎
  where open Width n
atoms-X {suc m} ((ℓ , k) ∷ as) v = begin
  (A ℓ ^ᶠ k • B) • Xc v
    ≈⟨ trans assoc (back _ (atoms-X as v)) ⟩
  A ℓ ^ᶠ k • Xc v • B • Zc z • ω h₁ ^ᶠ t
    ≈⟨ trans (sym assoc) (trans (front _ (A-Xc ℓ k v)) assoc) ⟩
  Xc v • (A ℓ ^ᶠ k • Zc z₁ • ω h₁ ^ᶠ t₁) • B • Zc z • ω h₁ ^ᶠ t
    ≈⟨ back _ (by-passoc ((□ • □ • □) • □ • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl) ⟩
  Xc v • A ℓ ^ᶠ k • (Zc z₁ • ω h₁ ^ᶠ t₁) • B • Zc z • ω h₁ ^ᶠ t
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (•-∥ (Zc∥atoms z₁ as) (ωᶠ-comm t₁ B))) assoc))) ⟩
  Xc v • A ℓ ^ᶠ k • B • (Zc z₁ • ω h₁ ^ᶠ t₁) • Zc z • ω h₁ ^ᶠ t
    ≈⟨ back _ (back _ (back _ merge)) ⟩
  Xc v • A ℓ ^ᶠ k • B • Zc (zipWith _+_ z₁ z) • ω h₁ ^ᶠ (t₁ + t)
    ≈⟨ back _ (sym assoc) ⟩
  Xc v • (A ℓ ^ᶠ k • B) • Zc (zipWith _+_ z₁ z) • ω h₁ ^ᶠ (t₁ + t) ∎
  where
  open Width (₁₊ m)
  module OW = Pow.Order (₁₊ m) {ω h₁} ω-order
  B = atoms as
  v₀ = head (v ⋆ˣ* rL ℓ)
  z₁ = (k * v₀ ∷ 0ᵛ) ⋆ᴿ* rL ℓ
  t₁ = k * binom2 v₀
  z = proj₂ (resid as v)
  t = proj₁ (resid as v)
  merge : (₁₊ m) ⊢ (Zc z₁ • ω h₁ ^ᶠ t₁) • Zc z • ω h₁ ^ᶠ t ≈ Zc (zipWith _+_ z₁ z) • ω h₁ ^ᶠ (t₁ + t)
  merge = begin
    (Zc z₁ • ω h₁ ^ᶠ t₁) • Zc z • ω h₁ ^ᶠ t     ≈⟨ trans assoc (back _ (trans (sym assoc) (trans (front _ (ωᶠ-comm t₁ (Zc z))) assoc))) ⟩
    Zc z₁ • Zc z • ω h₁ ^ᶠ t₁ • ω h₁ ^ᶠ t        ≈⟨ trans (sym assoc) (cong (Zc-add z₁ z) (OW.^ᶠ-+ t₁ t)) ⟩
    Zc (zipWith _+_ z₁ z) • ω h₁ ^ᶠ (t₁ + t)     ∎
atoms-X {zero} ((() , _) ∷ _) v

infixl 5 _⋆ᵛ_
_⋆ᵛ_ : DE n → Vec F n → DE n
de s c as ⋆ᵛ v = de (s + c ·ᵛ v + proj₁ (resid as v)) (zipWith _+_ c (proj₂ (resid as v))) as

⋆ᵛ-sound : (d : DE n) (v : Vec F n) → n ⊢ ⟦ d ⟧ᴰ • Xc v ≈ Xc v • ⟦ d ⋆ᵛ v ⟧ᴰ
⋆ᵛ-sound {n} (de s c as) v = begin
  (ω h₁ ^ᶠ s • Zc c • B) • Xc v
    ≈⟨ trans assoc (back _ (trans assoc (back _ (atoms-X as v)))) ⟩
  ω h₁ ^ᶠ s • Zc c • Xc v • B • Zc z • ω h₁ ^ᶠ t
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (Zc-Xc c v)) assoc)) ⟩
  ω h₁ ^ᶠ s • Xc v • (Zc c • ω h₁ ^ᶠ u) • B • Zc z • ω h₁ ^ᶠ t
    ≈⟨ trans (sym assoc) (trans (front _ (ωᶠ-comm s (Xc v))) assoc) ⟩
  Xc v • ω h₁ ^ᶠ s • (Zc c • ω h₁ ^ᶠ u) • B • Zc z • ω h₁ ^ᶠ t
    ≈⟨ back _ rest ⟩
  Xc v • ω h₁ ^ᶠ (s + u + t) • Zc (zipWith _+_ c z) • B ∎
  where
  open Width n
  module OW = Pow.Order n {ω h₁} ω-order
  B = atoms as
  u = c ·ᵛ v
  z = proj₂ (resid as v)
  t = proj₁ (resid as v)
  rest : n ⊢ ω h₁ ^ᶠ s • (Zc c • ω h₁ ^ᶠ u) • B • Zc z • ω h₁ ^ᶠ t ≈ ω h₁ ^ᶠ (s + u + t) • Zc (zipWith _+_ c z) • B
  rest = begin
    ω h₁ ^ᶠ s • (Zc c • ω h₁ ^ᶠ u) • B • Zc z • ω h₁ ^ᶠ t
      ≈⟨ back _ (trans assoc (back _ (∥-• (ωᶠ-comm u B) (∥-• (ωᶠ-comm u (Zc z)) (ωᶠ-comm u _))))) ⟩
    ω h₁ ^ᶠ s • Zc c • (B • Zc z • ω h₁ ^ᶠ t) • ω h₁ ^ᶠ u
      ≈⟨ back _ (back _ (front _ (trans (sym assoc) (front _ (sym (Zc∥atoms z as)))))) ⟩
    ω h₁ ^ᶠ s • Zc c • ((Zc z • B) • ω h₁ ^ᶠ t) • ω h₁ ^ᶠ u
      ≈⟨ back _ (back _ (trans assoc (trans (back _ (OW.^ᶠ-+ t u)) assoc))) ⟩
    ω h₁ ^ᶠ s • Zc c • Zc z • B • ω h₁ ^ᶠ (t + u)
      ≈⟨ back _ (back _ (back _ (sym (ωᶠ-comm (t + u) B)))) ⟩
    ω h₁ ^ᶠ s • Zc c • Zc z • ω h₁ ^ᶠ (t + u) • B
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (sym (ωᶠ-comm (t + u) (Zc z)))) assoc))) ⟩
    ω h₁ ^ᶠ s • Zc c • ω h₁ ^ᶠ (t + u) • Zc z • B
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (sym (ωᶠ-comm (t + u) (Zc c)))) assoc)) ⟩
    ω h₁ ^ᶠ s • ω h₁ ^ᶠ (t + u) • Zc c • Zc z • B
      ≈⟨ trans (sym assoc) (cong (trans (OW.^ᶠ-+ s (t + u)) (OW.^ᶠ-≡ (sut s u t))) (trans (sym assoc) (front _ (Zc-add c z)))) ⟩
    ω h₁ ^ᶠ (s + u + t) • Zc (zipWith _+_ c z) • B ∎
    where
    sut : (s u t : F) → s + (t + u) ≡ s + u + t
    sut s u t = Eq.trans (Eq.cong (s +_) (FR.+-comm t u)) (Eq.sym (FR.+-assoc s u t))

------------------------------------------------------------------------
-- The phase generators

data PG (n : ℕ) : Set where
  gω : PG n
  gZ gS : Fin n → PG n

⟦_⟧ᵖ : PG n → Circuit n
⟦ gω ⟧ᵖ       = ω h₁
⟦ gZ zero ⟧ᵖ    = Z h₁
⟦ gZ (suc j) ⟧ᵖ = ⟦ gZ j ⟧ᵖ ↑
⟦ gS zero ⟧ᵖ    = S h
⟦ gS (suc j) ⟧ᵖ = ⟦ gS j ⟧ᵖ ↑

-- The unit vector, and the unit row.
eᵛ : Fin n → Vec F n
eᵛ zero    = 1F ∷ 0ᵛ
eᵛ (suc j) = 0F ∷ eᵛ j

eᴺ : Fin n → NZ n
eᴺ {suc n} zero          = big 1* 0ᵛ
eᴺ {suc (suc n)} (suc j) = small (eᴺ j)
eᴺ {suc zero} (suc ())

Z-e : (j : Fin n) → n ⊢ ⟦ gZ j ⟧ᵖ ≈ Zc (eᵛ j)
Z-e {suc n} zero    = Width.sym (Width.trans (Width.back (₁₊ n) _ (lift Zc-zero)) Width.right-unit)
Z-e {suc n} (suc j) = Width.trans (lift (Z-e j)) (Width.sym Width.left-unit)

S-e : (j : Fin n) → n ⊢ ⟦ gS j ⟧ᵖ ≈ atom (eᴺ j)
S-e {suc n} zero = sym (trans (cong (Inv.⁻¹-cong (₁₊ n) r≈) (back _ r≈)) (trans left-unit right-unit))
  where
  open Width (₁₊ n)
  r≈ : (₁₊ n) ⊢ R 0ᵛ • M⟨ 1* ⟩ ≈ ε
  r≈ = trans (cong R-zero (ax ax1)) left-unit
S-e {suc (suc n)} (suc j) = Width.trans (lift (S-e j)) (Width.sym (A-small (eᴺ j)))
S-e {suc zero} (suc ())

app : DE n → PG n → DE n
app (de s c as) gω     = de (s + 1F) c as
app (de s c as) (gZ j) = de s (zipWith _+_ c (eᵛ j)) as
app (de s c as) (gS j) = de s c (as ++ ((eᴺ j , 1F) ∷ []))

app-sound : (d : DE n) (g : PG n) → n ⊢ ⟦ d ⟧ᴰ • ⟦ g ⟧ᵖ ≈ ⟦ app d g ⟧ᴰ
app-sound {n} (de s c as) gω = begin
  (ω h₁ ^ᶠ s • Zc c • atoms as) • ω h₁      ≈⟨ trans assoc (back _ (sym (ω-comm _))) ⟩
  ω h₁ ^ᶠ s • ω h₁ • Zc c • atoms as        ≈⟨ trans (sym assoc) (front _ (OW.^ᶠ-+ s 1F)) ⟩
  ω h₁ ^ᶠ (s + 1F) • Zc c • atoms as        ∎
  where
  open Width n
  module OW = Pow.Order n {ω h₁} ω-order
app-sound {n} (de s c as) (gZ j) = begin
  (ω h₁ ^ᶠ s • Zc c • atoms as) • ⟦ gZ j ⟧ᵖ
    ≈⟨ trans assoc (back _ (trans assoc (back _ (trans (back _ (Z-e j)) (sym (Zc∥atoms (eᵛ j) as)))))) ⟩
  ω h₁ ^ᶠ s • Zc c • Zc (eᵛ j) • atoms as
    ≈⟨ back _ (trans (sym assoc) (front _ (Zc-add c (eᵛ j)))) ⟩
  ω h₁ ^ᶠ s • Zc (zipWith _+_ c (eᵛ j)) • atoms as ∎
  where open Width n
app-sound {n} (de s c as) (gS j) = begin
  (ω h₁ ^ᶠ s • Zc c • atoms as) • ⟦ gS j ⟧ᵖ
    ≈⟨ trans assoc (back _ (trans assoc (back _ (back _ (S-e j))))) ⟩
  ω h₁ ^ᶠ s • Zc c • atoms as • atom (eᴺ j)
    ≈⟨ back _ (back _ (sym (trans (atoms-++ as _) (back _ right-unit)))) ⟩
  ω h₁ ^ᶠ s • Zc c • atoms (as ++ ((eᴺ j , 1F) ∷ [])) ∎
  where open Width n
