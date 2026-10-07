------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of Aff_d (the paper's Theorem 1)
--
-- At level 0 the gates are X, the multipliers, CX and SWAP.  Every
-- circuit is a translation followed by a linear circuit (decompose):
-- a linear generator is appended to the linear part, and an X is
-- moved in front of it (Affine.X-push*) and added to the translation.
-- Two such forms with the same operator have the same translation —
-- its value at 0 — and linear parts with the same operator, which are
-- equal by linear completeness (Linear.Completeness) given
-- completeness one wire down; on no wires there is nothing to
-- compare.  So completeness holds at every width, by induction.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Completeness.Aff
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Data.Empty using (⊥ ; ⊥-elim-irr)
open import Data.Nat.Base using (zero ; suc ; _≤_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 0
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime 0
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime 0
  using (X-at ; M-at ; CX-at ; SWAP-at ; Xᶠ-at)
open import Examples.Groups.Qupit-Phase-Affine.Soundness p-2 p-prime 0 using (Admissible)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime 0
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime 0 using (unit)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime 0
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime 0

-- Level 0 is admissible for every p.
adm : Admissible
adm = (λ ()) , (λ ())

open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime 0 adm
open import Examples.Groups.Qupit-Phase-Affine.Linear.Completeness p-2 p-prime 0 adm
  using (linear-complete)

private
  variable
    n : ℕ

  no1 : 1 ≤ 0 → ⊥
  no1 ()

  no2 : 2 ≤ 0 → ⊥
  no2 ()

  no3 : 3 ≤ 0 → ⊥
  no3 ()

------------------------------------------------------------------------
-- The generators at level 0: linear ones and translations

data Kind (n : ℕ) : Set where
  lin : LGen n → Kind n
  tr  : Vec F n → Kind n

⟦_⟧ₖ : Kind n → Circuit n
⟦ lin y ⟧ₖ = [ ι y ]ʷ
⟦ tr e ⟧ₖ  = Xc e

up-kind : Kind n → Kind (₁₊ n)
up-kind (lin y) = lin (y ↥ₗ)
up-kind (tr e)  = tr (0F ∷ e)

kind : Gen n → Kind n
kind (gate₀ (ω-gate h))     = ⊥-elim-irr (no1 h)
kind (gate₁ X-gate)         = tr (1F ∷ 0ᵛ)
kind (gate₁ (M-gate a nz))  = lin (mul (unit a nz))
kind (gate₁ (Z-gate h))     = ⊥-elim-irr (no1 h)
kind (gate₁ (S-gate h))     = ⊥-elim-irr (no2 h)
kind (gate₁ (T-gate h))     = ⊥-elim-irr (no3 h)
kind (gate₂ CX-gate)        = lin cx
kind (gate₂ SWAP-gate)      = lin sw
kind (g ↥)                  = up-kind (kind g)

up-kind-sound : (k : Kind n) → (₁₊ n) ⊢ ⟦ k ⟧ₖ ↑ ≈ ⟦ up-kind k ⟧ₖ
up-kind-sound {n} (lin y) = Width.refl
up-kind-sound {n} (tr e)  = Width.sym Width.left-unit

kind-sound : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ⟦ kind g ⟧ₖ
kind-sound (gate₀ (ω-gate h))    = ⊥-elim-irr (no1 h)
kind-sound {₁₊ n} (gate₁ X-gate) = sym (trans (back _ (lift Xc-zero)) right-unit)
  where open Width (₁₊ n)
kind-sound (gate₁ (M-gate a nz)) = Width.refl
kind-sound (gate₁ (Z-gate h))    = ⊥-elim-irr (no1 h)
kind-sound (gate₁ (S-gate h))    = ⊥-elim-irr (no2 h)
kind-sound (gate₁ (T-gate h))    = ⊥-elim-irr (no3 h)
kind-sound (gate₂ CX-gate)       = Width.refl
kind-sound (gate₂ SWAP-gate)     = Width.refl
kind-sound {₁₊ n} (g ↥)          = Width.trans (lift (kind-sound g)) (up-kind-sound (kind g))

------------------------------------------------------------------------
-- The affine normal form: a translation, then a linear circuit

record ANF (n : ℕ) : Set where
  constructor ⟨_,_⟩
  field
    shift : Vec F n
    linear : Word (LGen n)

⌜_⌝ᵃ : ANF n → Circuit n
⌜ ⟨ b , L ⟩ ⌝ᵃ = Xc b • ⌊ L ⌋

stepᵃ : ANF n → Kind n → ANF n
stepᵃ ⟨ b , L ⟩ (lin y) = ⟨ b , L • [ y ]ʷ ⟩
stepᵃ ⟨ b , L ⟩ (tr e)  = ⟨ zipWith _+_ b (e ⋆ˣ* L) , L ⟩

stepᵃ-sound : (A : ANF n) (k : Kind n) → n ⊢ ⌜ A ⌝ᵃ • ⟦ k ⟧ₖ ≈ ⌜ stepᵃ A k ⌝ᵃ
stepᵃ-sound {n} ⟨ b , L ⟩ (lin y) = Width.assoc
stepᵃ-sound {n} ⟨ b , L ⟩ (tr e) = begin
  (Xc b • ⌊ L ⌋) • Xc e                     ≈⟨ trans assoc (back _ (X-push* L e)) ⟩
  Xc b • Xc (e ⋆ˣ* L) • ⌊ L ⌋               ≈⟨ trans (sym assoc) (front _ (Xc-add b (e ⋆ˣ* L))) ⟩
  Xc (zipWith _+_ b (e ⋆ˣ* L)) • ⌊ L ⌋      ∎
  where open Width n

runᵃ : ANF n → Circuit n → ANF n
runᵃ A [ g ]ʷ  = stepᵃ A (kind g)
runᵃ A ε       = A
runᵃ A (w • v) = runᵃ (runᵃ A w) v

runᵃ-sound : (A : ANF n) (w : Circuit n) → n ⊢ ⌜ A ⌝ᵃ • w ≈ ⌜ runᵃ A w ⌝ᵃ
runᵃ-sound {n} A [ g ]ʷ = Width.trans (Width.back n _ (kind-sound g)) (stepᵃ-sound A (kind g))
runᵃ-sound {n} A ε = Width.right-unit
runᵃ-sound {n} A (w • v) = begin
  ⌜ A ⌝ᵃ • w • v                 ≈⟨ sym assoc ⟩
  (⌜ A ⌝ᵃ • w) • v               ≈⟨ front _ (runᵃ-sound A w) ⟩
  ⌜ runᵃ A w ⌝ᵃ • v              ≈⟨ runᵃ-sound (runᵃ A w) v ⟩
  ⌜ runᵃ (runᵃ A w) v ⌝ᵃ         ∎
  where open Width n

anf₀ : ANF n
anf₀ = ⟨ 0ᵛ , ε ⟩

decompose : (w : Circuit n) → n ⊢ w ≈ ⌜ runᵃ anf₀ w ⌝ᵃ
decompose {n} w = begin
  w                       ≈⟨ sym left-unit ⟩
  ε • w                   ≈⟨ front _ (sym (trans right-unit Xc-zero)) ⟩
  ⌜ anf₀ ⌝ᵃ • w           ≈⟨ runᵃ-sound anf₀ w ⟩
  ⌜ runᵃ anf₀ w ⌝ᵃ        ∎
  where open Width n

------------------------------------------------------------------------
-- Reading the translation

private
  -- A translation moves 0 to its vector.
  Xc-0 : (b : Vec F n) → fn (Xc b) 0ᵛ ≡ b
  Xc-0 []      = fn-ε []
  Xc-0 (c ∷ b) = begin
    fn (X ^ᶠ c • Xc b ↑) (0F ∷ 0ᵛ)        ≡⟨ fn-• (X ^ᶠ c) (Xc b ↑) (0F ∷ 0ᵛ) ⟩
    fn (X ^ᶠ c) (fn (Xc b ↑) (0F ∷ 0ᵛ))   ≡⟨ Eq.cong (fn (X ^ᶠ c)) (fn-↑ (Xc b) 0F 0ᵛ) ⟩
    fn (X ^ᶠ c) (0F ∷ fn (Xc b) 0ᵛ)       ≡⟨ Eq.cong (λ y → fn (X ^ᶠ c) (0F ∷ y)) (Xc-0 b) ⟩
    fn (X ^ᶠ c) (0F ∷ b)                  ≡⟨ Eq.cong proj₁ (Xᶠ-at c 0F b) ⟩
    0F + c ∷ b                            ≡⟨ Eq.cong (_∷ b) (FR.+-identityˡ c) ⟩
    c ∷ b                                 ∎
    where open ≡-Reasoning

  -- A linear circuit fixes 0.
  gen-0 : (y : LGen n) → fn [ ι y ]ʷ 0ᵛ ≡ 0ᵛ
  gen-0 cx      = Eq.trans (Eq.cong proj₁ (CX-at 0F 0F 0ᵛ)) (Eq.cong (_∷ 0F ∷ 0ᵛ) (FR.+-identityʳ 0F))
  gen-0 sw      = Eq.cong proj₁ (SWAP-at 0F 0F 0ᵛ)
  gen-0 (mul x) = Eq.trans (Eq.cong proj₁ (M-at (proj₁ x) (proj₂ x) 0F 0ᵛ)) (Eq.cong (_∷ 0ᵛ) (FR.zeroʳ _))
  gen-0 (y ↥ₗ)  = Eq.trans (fn-↑ [ ι y ]ʷ 0F 0ᵛ) (Eq.cong (0F ∷_) (gen-0 y))

  lin-0 : (L : Word (LGen n)) → fn ⌊ L ⌋ 0ᵛ ≡ 0ᵛ
  lin-0 [ y ]ʷ  = gen-0 y
  lin-0 ε       = fn-ε 0ᵛ
  lin-0 (L • M) = Eq.trans (fn-• ⌊ L ⌋ ⌊ M ⌋ 0ᵛ)
                    (Eq.trans (Eq.cong (fn ⌊ L ⌋) (lin-0 M)) (lin-0 L))

  shift-0 : (A : ANF n) → fn ⌜ A ⌝ᵃ 0ᵛ ≡ ANF.shift A
  shift-0 ⟨ b , L ⟩ = Eq.trans (fn-• (Xc b) ⌊ L ⌋ 0ᵛ)
                        (Eq.trans (Eq.cong (fn (Xc b)) (lin-0 L)) (Xc-0 b))

------------------------------------------------------------------------
-- Completeness

private
  nf-complete : Complete n → (A B : ANF (₁₊ n)) → ⟦ ⌜ A ⌝ᵃ ⟧ ≐ ⟦ ⌜ B ⌝ᵃ ⟧ → (₁₊ n) ⊢ ⌜ A ⌝ᵃ ≈ ⌜ B ⌝ᵃ
  nf-complete {n} IH ⟨ b , L ⟩ ⟨ b' , L' ⟩ e with
    Eq.trans (Eq.sym (shift-0 ⟨ b , L ⟩)) (Eq.trans (Eq.cong proj₁ (e 0ᵛ)) (shift-0 ⟨ b' , L' ⟩))
  ... | refl = Width.back (₁₊ n) _ (linear-complete IH L L' (cancelˡ-⟦⟧ (Xc b) ⌊ L ⌋ ⌊ L' ⌋ e))

  complete₀ : Complete 0
  complete₀ {w} {v} _ = trans (none w) (sym (none v))
    where
    open Width 0
    none : (u : Circuit 0) → 0 ⊢ u ≈ ε
    none [ gate₀ (ω-gate h) ]ʷ = ⊥-elim-irr (no1 h)
    none ε       = refl
    none (u • t) = trans (cong (none u) (none t)) left-unit

  complete-step : Complete n → Complete (₁₊ n)
  complete-step {n} IH {w} {v} e =
    trans (decompose w)
      (trans (nf-complete IH (runᵃ anf₀ w) (runᵃ anf₀ v)
                (≐-trans (sound (sym (decompose w))) (≐-trans e (sound (decompose v)))))
             (sym (decompose v)))
    where open Width (₁₊ n)

-- Circuits of Aff_d with the same operator are equal.
completeness : (n : ℕ) → Complete n
completeness zero    = complete₀
completeness (suc n) = complete-step (completeness n)
