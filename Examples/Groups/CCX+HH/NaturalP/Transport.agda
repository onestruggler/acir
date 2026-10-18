------------------------------------------------------------------------
-- Presentations of groups
--
-- Every gate is a gate on the top four wires, moved by swaps.
--
-- On 4 + k + c wires, `top k c x₄` is a circuit x₄ on four wires placed
-- on the top four, with idle wires below (the pattern of idle positions
-- of NaturalP/Lambda, nested as in the window).  Every gate is
-- ⌈ inv N ⌉ • top k c x₄ • ⌈ N ⌉ for an affine word N of swaps
-- (`placed`): a gate one wire up is the gate below it shifted, and a
-- gate at the bottom with an idle wire on top is the same gate shifted
-- up, conjugated by the cycle of swaps that carries wire 0 to the top
-- (Symmetric-Prop/Cycle.top-is-bottom).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Transport where

open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Data.Product.Base using (Σ ; _,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Pos ; Λ)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; asw ; _↥ₐ ; ⌈_⌉ ; inv)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (_↑ₐ)
import Examples.Groups.Symmetric-Prop.Cycle as Cycle

private
  variable
    n : ℕ

  module CY = Cycle Gate SW-gate _NPΣ,_===_

  no-scalar : ∀ {n} (h h′ : Gate 0) →
    n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ
  no-scalar ()

------------------------------------------------------------------------
-- Affine words and their circuits

private
  inv-↑ : (w : Word (AGen n)) → inv (w ↑ₐ) ≡ inv w ↑ₐ
  inv-↑ [ g ]ʷ  = refl
  inv-↑ ε       = refl
  inv-↑ (u • v) = cong₂ _•_ (inv-↑ v) (inv-↑ u)

  ⌈⌉-↑ : (w : Word (AGen n)) → ⌈ w ↑ₐ ⌉ ≡ ⌈ w ⌉ ↑
  ⌈⌉-↑ [ g ]ʷ  = refl
  ⌈⌉-↑ ε       = refl
  ⌈⌉-↑ (u • v) = cong₂ _•_ (⌈⌉-↑ u) (⌈⌉-↑ v)

  ⌈inv-↑⌉ : (w : Word (AGen n)) → ⌈ inv (w ↑ₐ) ⌉ ≡ ⌈ inv w ⌉ ↑
  ⌈inv-↑⌉ w = trans (cong ⌈_⌉ (inv-↑ w)) (⌈⌉-↑ (inv w))

-- The cycle as an affine word.
cycA : ∀ n → Word (AGen (suc n))
cycA zero    = ε
cycA (suc n) = [ asw ]ʷ • (cycA n ↑ₐ)

private
  ⌈cycA⌉ : ∀ n → ⌈ cycA n ⌉ ≡ CY.cyc n
  ⌈cycA⌉ zero    = refl
  ⌈cycA⌉ (suc n) = cong₂ _•_ refl (trans (⌈⌉-↑ (cycA n)) (cong _↑ (⌈cycA⌉ n)))

  ⌈inv-cycA⌉ : ∀ n → ⌈ inv (cycA n) ⌉ ≡ CY.cyc⁻ n
  ⌈inv-cycA⌉ zero    = refl
  ⌈inv-cycA⌉ (suc n) = cong₂ _•_ (trans (⌈inv-↑⌉ (cycA n)) (cong _↑ (⌈inv-cycA⌉ n))) refl

------------------------------------------------------------------------
-- Placing on the top four wires

idles : ∀ k → Vec Pos k
idles zero    = []
idles (suc k) = nothing ∷ idles k

top : ∀ k c → Circuit 4 → Circuit (₄₊ (k + (c + 0)))
top k c x₄ = Λ (idles k) (Λ (idles c) x₄)

-- w is a circuit on the top four wires moved by swaps.
Placed : ∀ k c → Circuit (₄₊ (k + (c + 0))) → Set
Placed k c w = Σ (Word (AGen (₄₊ (k + (c + 0))))) λ N → Σ (Circuit 4) λ x₄ →
  (₄₊ (k + (c + 0))) ⊢ w ≈ ⌈ inv N ⌉ • (top k c x₄ • ⌈ N ⌉)

private
  -- Shifting a placed circuit up.
  shift : ∀ {m} {w : Circuit m} {N : Word (AGen m)} {T : Circuit m} →
    m ⊢ w ≈ ⌈ inv N ⌉ • (T • ⌈ N ⌉) → suc m ⊢ w ↑ ≈ ⌈ inv (N ↑ₐ) ⌉ • (T ↑ • ⌈ N ↑ₐ ⌉)
  shift {w = w} {N} {T} e =
    subst₂ (λ L R → _ ⊢ w ↑ ≈ L • (T ↑ • R)) (sym (⌈inv-↑⌉ N)) (sym (⌈⌉-↑ N))
      (lemma-cong↑ w (⌈ inv N ⌉ • (T • ⌈ N ⌉)) e)

  -- A placed circuit with an idle wire on top.
  widen-top : ∀ {m} {w : Circuit m} {N : Word (AGen m)} {T : Circuit m} →
    m ⊢ w ≈ ⌈ inv N ⌉ • (T • ⌈ N ⌉) →
    suc m ⊢ w ⇓ ≈ ⌈ inv ((N ↑ₐ) • cycA m) ⌉ • (T ↑ • ⌈ (N ↑ₐ) • cycA m ⌉)
  widen-top {m} {w} {N} {T} e =
    PB.trans (CY.top-is-bottom no-scalar w)
    (PB.trans (PB.cong PB.refl (PB.cong (shift e) PB.refl))
      (subst₂ (λ L R → _ ⊢ CY.cyc⁻ m • ((⌈ inv (N ↑ₐ) ⌉ • (T ↑ • ⌈ N ↑ₐ ⌉)) • CY.cyc m)
                          ≈ (L • ⌈ inv (N ↑ₐ) ⌉) • (T ↑ • (⌈ N ↑ₐ ⌉ • R)))
        (sym (⌈inv-cycA⌉ m)) (sym (⌈cycA⌉ m))
        (PB.trans (PB.cong PB.refl PB.assoc)
        (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
          (PB.sym PB.assoc)))))

placed : ∀ k c (x : Gen (₄₊ (k + (c + 0)))) → Placed k c [ x ]ʷ
placed zero    zero    x = ε , [ x ]ʷ , PB.sym (PB.trans PB.left-unit PB.right-unit)
placed zero    (suc c) (gate₀ ())
placed zero    (suc c) (gate₁ h) = let (N , x₄ , e) = placed zero c (gate₁ h) in (N ↑ₐ) • cycA _ , x₄ , widen-top {w = [ gate₁ h ]ʷ} e
placed zero    (suc c) (gate₂ h) = let (N , x₄ , e) = placed zero c (gate₂ h) in (N ↑ₐ) • cycA _ , x₄ , widen-top {w = [ gate₂ h ]ʷ} e
placed zero    (suc c) (gate₃ h) = let (N , x₄ , e) = placed zero c (gate₃ h) in (N ↑ₐ) • cycA _ , x₄ , widen-top {w = [ gate₃ h ]ʷ} e
placed zero    (suc c) (g ↥)     = let (N , x₄ , e) = placed zero c g in N ↑ₐ , x₄ , shift e
placed (suc k) c       (gate₀ ())
placed (suc k) c       (gate₁ h) = let (N , x₄ , e) = placed k c (gate₁ h) in (N ↑ₐ) • cycA _ , x₄ , widen-top {w = [ gate₁ h ]ʷ} e
placed (suc k) c       (gate₂ h) = let (N , x₄ , e) = placed k c (gate₂ h) in (N ↑ₐ) • cycA _ , x₄ , widen-top {w = [ gate₂ h ]ʷ} e
placed (suc k) c       (gate₃ h) = let (N , x₄ , e) = placed k c (gate₃ h) in (N ↑ₐ) • cycA _ , x₄ , widen-top {w = [ gate₃ h ]ʷ} e
placed (suc k) c       (g ↥)     = let (N , x₄ , e) = placed k c g in N ↑ₐ , x₄ , shift e
