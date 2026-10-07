------------------------------------------------------------------------
-- Presentations of groups
--
-- Splitting a diagonal expression of level 3 along wire 0
--
-- Every diagonal expression of level 3 on ₁₊ n wires is one on n wires,
-- one wire up, times a wire-0 form E₃ e (split₃).  Such splittings
-- multiply and take iterates (sp-•, sp-^ᶠ), so it is enough to split
-- the level-2 part (Phase.Quad.Split) and each atom of T.  The atom of
-- a row (a , w) is, by rule (32) at a, that of (1 , a⁻¹ w) to the
-- power a³ times atoms of S and Z (scale-T); and the atom of (1 , w)
-- with w the row of y is the gadget of T conjugated by the
-- representative of y one wire up (gad):
--
--     Aᵀ(1 , w) = Aᵀ(y) ↑ • T • ctrl₂*(conjugate of Z) • ctrl*(conjugate of S).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Split3
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; 1* ; binom2 ; binom3 ; _⁻¹ᶠ ; ⁻¹ᶠ-inverseʳ ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invˡ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; ⌊↑ₗ⌋)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Atom p-2 p-prime lv using (⁻¹-↑)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates p-2 p-prime lv h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.CCZ p-2 p-prime lv h gt3 using (conjT)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Ctrl p-2 p-prime lv h gt3 using (module C1 ; module C2)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.EForm3 p-2 p-prime lv h gt3

private
  variable
    n : ℕ

  h₂ : 2 ≤ lv
  h₂ = quad₃ h

  h₁ : 1 ≤ lv
  h₁ = lin₃ h

------------------------------------------------------------------------
-- Splittings

Split : Circuit (₁₊ n) → Set
Split {n} w = Σ (DE₃ n × E3Data n) λ ue → (₁₊ n) ⊢ w ≈ ⟦ proj₁ ue ⟧³ ↑ • E₃ (proj₂ ue)

d₀₃ : DE₃ n
d₀₃ = de 0F 0ᵛ [] ∣ []

d₀₃-ε : n ⊢ ⟦ d₀₃ {n} ⟧³ ≈ ε
d₀₃-ε = Width.sym (proj₂ Diag₃-ε)

module _ {n : ℕ} where

  open Width (₁₊ n)

  sp-≈ : {w v : Circuit (₁₊ n)} → (₁₊ n) ⊢ w ≈ v → Split v → Split w
  sp-≈ e (ue , p) = ue , trans e p

  sp-E : (e : E3Data n) → Split (E₃ e)
  sp-E e = (d₀₃ , e) , sym (trans (front _ (lift d₀₃-ε)) left-unit)

  sp-ε : Split ε
  sp-ε = sp-≈ (sym E₃-zero) (sp-E e₃₀)

  sp-↑ : {v : Circuit n} → Diag₃ n v → Split (v ↑)
  sp-↑ (d , e) = (d , e₃₀) , sym (trans (back _ E₃-zero) (trans right-unit (lift (Width.sym e))))

  sp-• : {w v : Circuit (₁₊ n)} → Split w → Split v → Split (w • v)
  sp-• ((U , e) , p) ((U' , e') , p') = (U ⊕³ U' , e +³ e') , (begin
    _ • _                                    ≈⟨ cong p p' ⟩
    (⟦ U ⟧³ ↑ • E₃ e) • ⟦ U' ⟧³ ↑ • E₃ e'    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    ⟦ U ⟧³ ↑ • (E₃ e • ⟦ U' ⟧³ ↑) • E₃ e'    ≈⟨ back _ (front _ (diag₃∥ (Diag₃-E₃ e) (Diag₃-↑ (U' , Width.refl)))) ⟩
    ⟦ U ⟧³ ↑ • (⟦ U' ⟧³ ↑ • E₃ e) • E₃ e'    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (⟦ U ⟧³ ↑ • ⟦ U' ⟧³ ↑) • E₃ e • E₃ e'    ≈⟨ cong (lift (⊕³-sound U U')) (E₃-add e e') ⟩
    ⟦ U ⊕³ U' ⟧³ ↑ • E₃ (e +³ e')            ∎)

  sp-^ᶠ : {w : Circuit (₁₊ n)} → Split w → (k : F) → Split (w ^ᶠ k)
  sp-^ᶠ ((U , e) , p) k = (proj₁ DU , k ·³ e) , (begin
    _ ^ᶠ k                                   ≈⟨ Pow.pow-cong (₁₊ n) (toℕ k) p ⟩
    (⟦ U ⟧³ ↑ • E₃ e) ^ᶠ k                   ≈⟨ Pow.pow-• (₁₊ n) (toℕ k) (diag₃∥ (Diag₃-↑ (U , Width.refl)) (Diag₃-E₃ e)) ⟩
    (⟦ U ⟧³ ↑) ^ᶠ k • E₃ e ^ᶠ k              ≈⟨ cong (trans (refl' (Eq.sym (↑-pow ⟦ U ⟧³ (toℕ k)))) (lift (proj₂ DU))) (E₃-^ᶠ e k) ⟩
    ⟦ proj₁ DU ⟧³ ↑ • E₃ (k ·³ e)            ∎)
    where
    DU : Diag₃ n (⟦ U ⟧³ ^ᶠ k)
    DU = Diag₃-^ᶠ (U , Width.refl) k

  -- The level-2 part.
  sp-2 : (d : DE (₁₊ n)) → Split ⟦ d ⟧ᴰ
  sp-2 d = ((proj₁ (split d) ∣ []) , eE (proj₂ (split d))) ,
           trans (split-sound d) (cong (lift (Width.sym Width.right-unit)) (E-E₃ (proj₂ (split d))))

  sp-D : {w : Circuit (₁₊ n)} → Diag (₁₊ n) w → Split w
  sp-D (d , e) = sp-≈ e (sp-2 d)

------------------------------------------------------------------------
-- Scaling a row of T: rule (32)

scale-T : (a : F*) (ℓ : NZ (₁₊ n)) →
          (₁₊ n) ⊢ atomᵀ (e0 ⋆* ([ mul a ]ʷ • rL ℓ)) ≈
                   atom ℓ ^ᶠ (2F * proj₁ a * binom2 (proj₁ a)) • Zc ((binom3 (proj₁ a) ∷ 0ᵛ) ⋆ᴿ* rL ℓ)
                   • atomᵀ ℓ ^ᶠ (proj₁ a * proj₁ a * proj₁ a)
scale-T {n} a ℓ = begin
  atomᵀ (e0 ⋆* L)
    ≈⟨ sym (atomᵀ-conj e0 L) ⟩
  ⌊ L ⌋ ⁻¹ • atomᵀ e0 • ⌊ L ⌋
    ≈⟨ back _ (front _ (sym T≈)) ⟩
  (ρ ⁻¹ • Mn ⁻¹) • T h • Mn • ρ
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  ρ ⁻¹ • (Mn ⁻¹ • T h • Mn) • ρ
    ≈⟨ back _ (front _ MTM) ⟩
  ρ ⁻¹ • (S h₂ ^ᶠ q • Z h₁ ^ᶠ b • T h ^ᶠ t) • ρ
    ≈⟨ trans (conj-• ρ _ _) (back _ (conj-• ρ _ _)) ⟩
  (ρ ⁻¹ • S h₂ ^ᶠ q • ρ) • (ρ ⁻¹ • Z h₁ ^ᶠ b • ρ) • (ρ ⁻¹ • T h ^ᶠ t • ρ)
    ≈⟨ cong (trans (conjρ _) (sym (A-^ ℓ (toℕ q)))) (cong (trans (conjρ _) Zpart) (trans (conjρ _) (sym (AT.A-^ ℓ (toℕ t))))) ⟩
  atom ℓ ^ᶠ q • Zc ((b ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • atomᵀ ℓ ^ᶠ t ∎
  where
  open Width (₁₊ n)
  q b t : F
  q = 2F * proj₁ a * binom2 (proj₁ a)
  b = binom3 (proj₁ a)
  t = proj₁ a * proj₁ a * proj₁ a
  L : Word (LGen (₁₊ n))
  L = [ mul a ]ʷ • rL ℓ
  Mn ρ : Circuit (₁₊ n)
  Mn = M⟨ a ⟩
  ρ = ⌊ rL ℓ ⌋
  conjρ : (X : Circuit (₁₊ n)) → (₁₊ n) ⊢ ρ ⁻¹ • X • ρ ≈ r ℓ ⁻¹ • X • r ℓ
  conjρ X = refl' (Eq.cong (λ q → q ⁻¹ • X • q) (⌊rL⌋ ℓ))
  MTM : (₁₊ n) ⊢ Mn ⁻¹ • T h • Mn ≈ S h₂ ^ᶠ q • Z h₁ ^ᶠ b • T h ^ᶠ t
  MTM = trans (back _ (T-M a)) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit))
  Zpart : (₁₊ n) ⊢ r ℓ ⁻¹ • Z h₁ ^ᶠ b • r ℓ ≈ Zc ((b ∷ 0ᵛ) ⋆ᴿ* rL ℓ)
  Zpart = trans (back _ (front _ (sym (trans (back _ (lift Zc-zero)) right-unit)))) (Zc-rconj ℓ (b ∷ 0ᵛ))

------------------------------------------------------------------------
-- The gadget along a row

module _ {m : ℕ} where

  open Width (₂₊ m)

  private
    PTa : (₂₊ m) ⊢ PT ≈ atomᵀ (e₀₁ {m})
    PTa = conjT [ cx ]ʷ (CX-invˡ 1F) 1F e₀₁
            (Eq.trans (row-⋆* e0 [ cx ]ʷ) (Eq.cong (λ t → 1F ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F)))

  gad-data : NZ (₁₊ m) → E3Data (₁₊ m)
  gad-data y = 1F , (0F , (1F ∷ F1.0ᵛ) RW1.⋆ᴿ* C2.trL* (rL y)) ,
               Q2.de 0F F2.0ᵛ ((LB2.big 1* F2.0ᵛ RW2.⋆* C1.trL* (rL y) , 1F) ∷ [])

  gad : (y : NZ (₁₊ m)) → (₂₊ m) ⊢ atomᵀ (big 1* (row y)) ≈ atomᵀ y ↑ • E₃ (gad-data y)
  gad y = begin
    atomᵀ (big 1* (row y))
      ≈⟨ atomᵀ-≡ (big 1* (row y)) (e₀₁ ⋆* (L ↑ₗ)) row≡ ⟩
    atomᵀ (e₀₁ ⋆* (L ↑ₗ))
      ≈⟨ sym (atomᵀ-conj e₀₁ (L ↑ₗ)) ⟩
    ⌊ L ↑ₗ ⌋ ⁻¹ • atomᵀ e₀₁ • ⌊ L ↑ₗ ⌋
      ≈⟨ refl' (Eq.cong (λ q → q ⁻¹ • atomᵀ e₀₁ • q) (⌊↑ₗ⌋ L)) ⟩
    ρ ⁻¹ • atomᵀ e₀₁ • ρ
      ≈⟨ back _ (front _ (trans (sym PTa) PT-dec)) ⟩
    ρ ⁻¹ • (T h • T h ↑ • CS h • SC) • ρ
      ≈⟨ trans (conj-• ρ _ _) (back _ (trans (conj-• ρ _ _) (back _ (conj-• ρ _ _)))) ⟩
    (ρ ⁻¹ • T h • ρ) • (ρ ⁻¹ • T h ↑ • ρ) • (ρ ⁻¹ • CS h • ρ) • (ρ ⁻¹ • SC • ρ)
      ≈⟨ cong T-part (cong T↑-part (cong (CS-conj L) (SC-conj L))) ⟩
    T h • atomᵀ y ↑ • C2.ctrl* L1.⟦ proj₁ (proj₂ (gad-data y)) ⟧ˡ • C1.ctrl* Q2.⟦ proj₂ (proj₂ (gad-data y)) ⟧ᴰ
      ≈⟨ trans (sym assoc) (trans (front _ (diag₃∥ Diag₃-T (Diag₃-↑ (Diag₃-atomᵀ y)))) assoc) ⟩
    atomᵀ y ↑ • E₃ (gad-data y) ∎
    where
    L : Word (LGen (₁₊ m))
    L = rL y
    ρ : Circuit (₂₊ m)
    ρ = ⌊ L ⌋ ↑
    row≡ : row (big 1* (row y)) ≡ row (e₀₁ ⋆* (L ↑ₗ))
    row≡ = Eq.sym (Eq.trans (row-⋆* e₀₁ (L ↑ₗ)) (Eq.trans (⋆ᴿ*-↑ 1F (1F ∷ 0ᵛ) L) (Eq.cong (1F ∷_) (e₀-rL y))))
    T-part : (₂₊ m) ⊢ ρ ⁻¹ • T h • ρ ≈ T h
    T-part = trans (back _ (sym (comm-gate₁-w↑ (T-gate h) ⌊ L ⌋))) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₂₊ m))) left-unit))
    T↑-part : (₂₊ m) ⊢ ρ ⁻¹ • T h ↑ • ρ ≈ atomᵀ y ↑
    T↑-part = trans (refl' (Eq.cong (λ q → q • T h ↑ • ρ) (⁻¹-↑ ⌊ L ⌋)))
                (lift (Width.trans (Width.back (₁₊ m) _ (Width.front (₁₊ m) _ T≈))
                        (Width.trans (atomᵀ-conj e0 L) (atomᵀ-≡ (e0 ⋆* L) y (Eq.trans (row-⋆* e0 L) (e₀-rL y))))))

------------------------------------------------------------------------
-- Splitting the atoms of T

private
  scale-inv : (a : F*) (w : Vec F n) → scaleᵛ (proj₁ a) (scaleᵛ (proj₁ a ⁻¹ᶠ) w) ≡ w
  scale-inv a [] = Eq.refl
  scale-inv (a , na) (x ∷ w) = Eq.cong₂ _∷_ inv (scale-inv (a , na) w)
    where
    inv : a * (a ⁻¹ᶠ * x) ≡ x
    inv = Eq.trans (Eq.sym (FR.*-assoc a (a ⁻¹ᶠ) x)) (Eq.trans (Eq.cong (_* x) (⁻¹ᶠ-inverseʳ a na)) (FR.*-identityˡ x))

-- The atom of (1 , w).
sp-T0 : Split (atomᵀ (big 1* (0ᵛ {n})))
sp-T0 {n} = sp-≈ (trans (sym T≈) (sym (trans (back _ (trans (cong (C2.ctrl-cong L1.ld-zero) (C1.ctrl-cong (R2.Width.sym (proj₂ Q2.Diag-ε)))) left-unit)) right-unit)))
               (sp-E (1F , L1.ld₀ , proj₁ Q2.Diag-ε))
  where open Width (₁₊ n)

private
  sp-T1′ : (w : Vec F n) → (w ≡ 0ᵛ) ⊎ Σ (NZ n) (λ ℓ → row ℓ ≡ w) → Split (atomᵀ (big 1* w))
  sp-T1′ w (inj₁ e) = sp-≈ (atomᵀ-≡ (big 1* w) (big 1* 0ᵛ) (Eq.cong (1F ∷_) e)) sp-T0
  sp-T1′ {suc m} w (inj₂ (y , e)) =
    sp-≈ (Width.trans (atomᵀ-≡ (big 1* w) (big 1* (row y)) (Eq.cong (1F ∷_) (Eq.sym e))) (gad y))
      (sp-• (sp-↑ (Diag₃-atomᵀ y)) (sp-E (gad-data y)))

sp-T1 : (w : Vec F n) → Split (atomᵀ (big 1* w))
sp-T1 w = sp-T1′ w (nz? w)

-- The atom of (a , w).
sp-T : (a : F*) (w : Vec F n) → Split (atomᵀ (big a w))
sp-T {n} a w =
  sp-≈ (trans (atomᵀ-≡ (big a w) (e0 ⋆* ([ mul a ]ʷ • rL ℓ)) (Eq.sym row≡)) (scale-T a ℓ))
    (sp-• (sp-D (Diag-^ᶠ (Diag-atom ℓ) q)) (sp-• (sp-D (Diag-Zc z)) (sp-^ᶠ (sp-T1 w′) t)))
  where
  open Width (₁₊ n)
  q t : F
  q = 2F * proj₁ a * binom2 (proj₁ a)
  t = proj₁ a * proj₁ a * proj₁ a
  w′ : Vec F n
  w′ = scaleᵛ (proj₁ a ⁻¹ᶠ) w
  ℓ : NZ (₁₊ n)
  ℓ = big 1* w′
  z : Vec F (₁₊ n)
  z = (binom3 (proj₁ a) ∷ 0ᵛ) ⋆ᴿ* rL ℓ
  row≡ : row (e0 ⋆* ([ mul a ]ʷ • rL ℓ)) ≡ proj₁ a ∷ w
  row≡ = Eq.trans (row-⋆* e0 ([ mul a ]ʷ • rL ℓ))
           (Eq.trans (Eq.cong (_⋆ᴿ* rL ℓ) (Eq.cong₂ _∷_ (FR.*-comm 1F (proj₁ a)) (Eq.sym (scale-0 (proj₁ a)))))
             (Eq.trans (scale-⋆ᴿ* (proj₁ a) (1F ∷ 0ᵛ) (rL ℓ))
               (Eq.trans (Eq.cong (scaleᵛ (proj₁ a)) (e₀-rL ℓ))
                 (Eq.cong₂ _∷_ (FR.*-identityʳ (proj₁ a)) (scale-inv a w)))))

sp-atomᵀ : (ℓ : NZ (₁₊ n)) (k : F) → Split (atomᵀ ℓ ^ᶠ k)
sp-atomᵀ {suc m} (small ℓ) k =
  sp-≈ (Width.trans (Pow.pow-cong (₂₊ m) (toℕ k) (AT.A-small ℓ)) (Width.refl' (₂₊ m) (Eq.sym (↑ᶠ (atomᵀ ℓ) k))))
    (sp-↑ (Diag₃-^ᶠ (Diag₃-atomᵀ ℓ) k))
sp-atomᵀ (big a w) k = sp-^ᶠ (sp-T a w) k

sp-atomsᵀ : (ts : Atoms (₁₊ n)) → Split (atomsᵀ ts)
sp-atomsᵀ []             = sp-ε
sp-atomsᵀ ((ℓ , k) ∷ ts) = sp-• (sp-atomᵀ ℓ k) (sp-atomsᵀ ts)

------------------------------------------------------------------------
-- A diagonal expression of level 3, split

split₃ : (d : DE₃ (₁₊ n)) → Split ⟦ d ⟧³
split₃ (d ∣ ts) = sp-• (sp-2 d) (sp-atomsᵀ ts)
