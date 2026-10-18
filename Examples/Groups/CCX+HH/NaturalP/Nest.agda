------------------------------------------------------------------------
-- Presentations of groups
--
-- The stabiliser lemma for a window inside a window, given completeness
-- on at most eight wires, in the calculus with the schema.
--
-- `Λw k (Λw k₂ w)` is w under k₂ white controls inside a block, itself
-- under k white controls.  It is `Λw (k + k₂) w` up to the width
-- (k + k₂) + c ≡ k + (k₂ + c) (`Λ-assoc`), so `stab` carries over
-- (`stab₂`): an affine word that fixes every state whose bottom k + k₂
-- wires are 0 commutes with it.  The casts (`castC`, `castA`, `castS`)
-- are transports along an equality of widths, and every fact about them
-- is by matching the equality with refl.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.Nest
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (zero ; suc ; _+_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Notations using (₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl⁻)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ⌈_⌉ ; inv)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧)
open import Examples.Groups.CCX+HH.NaturalP.Window using (low ; high)
open import Examples.Groups.CCX+HH.NaturalP.Stab complete≤ using (Λw ; stab)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)

private
  variable
    t t′ k k₂ c : ℕ

------------------------------------------------------------------------
-- Transport along an equality of widths

castC : t ≡ t′ → Circuit (₄₊ t) → Circuit (₄₊ t′)
castC refl w = w

castA : t ≡ t′ → Word (AGen (₄₊ t)) → Word (AGen (₄₊ t′))
castA refl w = w

castS : t ≡ t′ → State (₄₊ t) → State (₄₊ t′)
castS refl x = x

castC-• : (e : t ≡ t′) (u v : Circuit (₄₊ t)) → castC e (u • v) ≡ castC e u • castC e v
castC-• refl u v = refl

castC-⊢ : (e : t ≡ t′) {u v : Circuit (₄₊ t)} → (₄₊ t) ⊢ u ≈ v → (₄₊ t′) ⊢ castC e u ≈ castC e v
castC-⊢ refl d = d

castC-⌈⌉ : (e : t ≡ t′) (a : Word (AGen (₄₊ t))) → castC e ⌈ a ⌉ ≡ ⌈ castA e a ⌉
castC-⌈⌉ refl a = refl

castA-inv : (e : t ≡ t′) (a : Word (AGen (₄₊ t))) → castA e (inv a) ≡ inv (castA e a)
castA-inv refl a = refl

castA-back : (e : t ≡ t′) (a : Word (AGen (₄₊ t′))) → castA e (castA (sym e) a) ≡ a
castA-back refl a = refl

castS-back : (e : t ≡ t′) (x : State (₄₊ t)) → castS (sym e) (castS e x) ≡ x
castS-back refl x = refl

castA-act : (e : t ≡ t′) (a : Word (AGen (₄₊ t′))) (x : State (₄₊ t)) →
  A⟦ castA (sym e) a ⟧ x ≡ castS (sym e) (A⟦ a ⟧ (castS e x))
castA-act refl a x = refl

castS-resp : (e : t ≡ t′) {x y : State (₄₊ t)} → x ≈s y → castS e x ≈s castS e y
castS-resp refl p = p

private
  castC-ctrl⁻ : (e : t ≡ t′) (Z : Circuit (₄₊ t)) →
    castC (cong suc e) (ctrl⁻ Z) ≡ ctrl⁻ (castC e Z)
  castC-ctrl⁻ refl Z = refl

  castS-zero : (e : t ≡ t′) (x : State (suc (₄₊ t))) →
    castS (cong suc e) x zero ≡ x zero
  castS-zero refl x = refl

  castS-lower : (e : t ≡ t′) (x : State (suc (₄₊ t))) →
    lower (castS (cong suc e) x) ≡ castS e (lower x)
  castS-lower refl x = refl

------------------------------------------------------------------------
-- A window inside a window

Λ-assoc : ∀ k k₂ (w : Circuit (₄₊ c)) →
  castC (+-assoc k k₂ c) (Λw (k + k₂) w) ≡ Λw k (Λw k₂ w)
Λ-assoc zero    k₂ w = refl
Λ-assoc {c} (suc k) k₂ w =
  trans (castC-ctrl⁻ (+-assoc k k₂ c) (Λw (k + k₂) w)) (cong ctrl⁻ (Λ-assoc k k₂ w))

-- The bottom k + k₂ wires are 0 exactly when the bottom k are and the
-- next k₂ are.
low-assoc : ∀ k k₂ (x : State (₄₊ ((k + k₂) + c))) →
  low {c} (k + k₂) x ≈s zeros →
  (low {k₂ + c} k (castS (+-assoc k k₂ c) x) ≈s zeros) ×
  (low {c} k₂ (high {k₂ + c} k (castS (+-assoc k k₂ c) x)) ≈s zeros)
low-assoc zero k₂ x z = (λ ()) , z
low-assoc {c} (suc k) k₂ x z =
  (λ { zero    → trans (castS-zero e x) (z zero)
     ; (suc i) → trans (cong (λ y → low {k₂ + c} k y i) (castS-lower e x)) (proj₁ rec i) })
  , (λ i → trans (cong (λ y → low {c} k₂ (high {k₂ + c} k y) i) (castS-lower e x)) (proj₂ rec i))
  where
  e = +-assoc k k₂ c
  rec = low-assoc k k₂ (lower x) (λ i → z (suc i))

------------------------------------------------------------------------
-- The stabiliser of a window inside a window

stab₂ : ∀ k k₂ c (S : Word (AGen (₄₊ (k + (k₂ + c))))) →
  (∀ x → low {k₂ + c} k x ≈s zeros → low {c} k₂ (high {k₂ + c} k x) ≈s zeros →
     A⟦ S ⟧ x ≈s x) →
  (w : Circuit (₄₊ c)) →
  (₄₊ (k + (k₂ + c))) ⊢ ⌈ S ⌉ • (Λw k (Λw k₂ w) • ⌈ inv S ⌉) ≈ Λw k (Λw k₂ w)
stab₂ k k₂ c S fixW w =
  Eq.subst₂ (λ L R → _ ⊢ L ≈ R) lhs-eq (Λ-assoc k k₂ w)
    (castC-⊢ e (stab (k + k₂) c S′ fixW′ w))
  where
  e = +-assoc k k₂ c
  S′ = castA (sym e) S
  fixW′ : ∀ x → low {c} (k + k₂) x ≈s zeros → A⟦ S′ ⟧ x ≈s x
  fixW′ x z i =
    trans (cong (λ y → y i) (castA-act e S x))
      (trans (castS-resp (sym e) (fixW (castS e x) (proj₁ zz) (proj₂ zz)) i)
        (cong (λ y → y i) (castS-back e x)))
    where
    zz = low-assoc k k₂ x z
  back : castA e S′ ≡ S
  back = castA-back e S
  lhs-eq : castC e (⌈ S′ ⌉ • (Λw (k + k₂) w • ⌈ inv S′ ⌉)) ≡
           ⌈ S ⌉ • (Λw k (Λw k₂ w) • ⌈ inv S ⌉)
  lhs-eq =
    trans (castC-• e ⌈ S′ ⌉ (Λw (k + k₂) w • ⌈ inv S′ ⌉))
    (cong₂ _•_ (trans (castC-⌈⌉ e S′) (cong ⌈_⌉ back))
      (trans (castC-• e (Λw (k + k₂) w) ⌈ inv S′ ⌉)
        (cong₂ _•_ (Λ-assoc k k₂ w)
          (trans (castC-⌈⌉ e (inv S′))
            (cong ⌈_⌉ (trans (castA-inv e S′) (cong inv back)))))))
