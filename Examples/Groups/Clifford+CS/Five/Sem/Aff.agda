------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits as permutations
--
-- Blake's affine circuits at p = 2 (Five.Affine) act on labels in the
-- field of two elements; read on bit vectors that action is `bm`, a map
-- of bits defined letter by letter (`bm-fn`: it is Blake's `fn` through
-- the two-element field), inverted by the circuit's syntactic inverse
-- (`bm-inv`, `bm-inv′`).  On four wires the circuit τ w of Clifford+CS
-- gates denotes the permutation operator of `bm w` (`aff4`): one
-- evaluation for each of the 31 generator shapes, and the product.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Aff where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
import Data.Empty.Irrelevant as Irr
open import Data.Fin using (zero ; suc)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; len ; ⟦⟧ₒ-ε ; ⟦⟧ₒ-•)
open import Examples.Groups.Clifford+CS.Five.Affine using (τg ; τ)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (perm ; perm-⊙)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (SameOp ; same-op)

import Examples.Groups.Qupit-Phase-Affine.Field 0 prime[2] as BF
import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
import Examples.Groups.Qupit-Phase-Affine.Interpretation 0 prime[2] 0 as BI
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn ; fn-• ; fn-ε ; sound)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹ ; module Inv)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The two-element field as Bool

toB : BF.F → Bool
toB zero       = false
toB (suc zero) = true

fromB : Bool → BF.F
fromB false = zero
fromB true  = suc zero

toB-fromB : ∀ b → toB (fromB b) ≡ b
toB-fromB false = refl
toB-fromB true  = refl

fromB-toB : ∀ a → fromB (toB a) ≡ a
fromB-toB zero       = refl
fromB-toB (suc zero) = refl

Bv : Vec BF.F n → Bits n
Bv = map toB

Lv : Bits n → Vec BF.F n
Lv = map fromB

Bv-Lv : (x : Bits n) → Bv (Lv x) ≡ x
Bv-Lv []      = refl
Bv-Lv (b ∷ x) = Eq.cong₂ _∷_ (toB-fromB b) (Bv-Lv x)

Lv-Bv : (y : Vec BF.F n) → Lv (Bv y) ≡ y
Lv-Bv []      = refl
Lv-Bv (a ∷ y) = Eq.cong₂ _∷_ (fromB-toB a) (Lv-Bv y)

private
  opaque
    unfolding BF._+_ BF._*_

    toB-X : ∀ a → toB (fromB a BF.+ BF.1F) ≡ not a
    toB-X false = refl
    toB-X true  = refl

    toB-CX : ∀ a b → toB (fromB a BF.+ fromB b) ≡ (a xor b)
    toB-CX false false = refl
    toB-CX false true  = refl
    toB-CX true  false = refl
    toB-CX true  true  = refl

    toB-M : ∀ a → toB (suc zero BF.* fromB a) ≡ a
    toB-M false = refl
    toB-M true  = refl

------------------------------------------------------------------------
-- The action on bits

bmg : B.Gen n → Bits n → Bits n
bmg (B.gate₀ _)                 x           = x
bmg (B.gate₁ B.X-gate)          (a ∷ x)     = not a ∷ x
bmg (B.gate₁ (B.M-gate _ _))    x           = x
bmg (B.gate₁ (B.Z-gate _))      x           = x
bmg (B.gate₁ (B.S-gate _))      x           = x
bmg (B.gate₁ (B.T-gate _))      x           = x
bmg (B.gate₂ B.CX-gate)         (a ∷ b ∷ x) = (a xor b) ∷ b ∷ x
bmg (B.gate₂ B.SWAP-gate)       (a ∷ b ∷ x) = b ∷ a ∷ x
bmg (g B.↥)                     (a ∷ x)     = a ∷ bmg g x

bm : B.Circuit n → Bits n → Bits n
bm [ g ]ʷ  x = bmg g x
bm ε       x = x
bm (u • v) x = bm u (bm v x)

private
  gB : (g : B.Gen n) (x : Bits n) → Bv (proj₁ (BI.⟦ g ⟧ᵍ (Lv x))) ≡ bmg g x
  gB (B.gate₀ (B.ω-gate _))       x           = Bv-Lv x
  gB (B.gate₁ B.X-gate)           (a ∷ x)     = Eq.cong₂ _∷_ (toB-X a) (Bv-Lv x)
  gB (B.gate₁ (B.M-gate zero p))  (a ∷ x)     = Irr.⊥-elim (p refl)
  gB (B.gate₁ (B.M-gate (suc zero) _)) (a ∷ x) = Eq.cong₂ _∷_ (toB-M a) (Bv-Lv x)
  gB (B.gate₁ (B.Z-gate _))       (a ∷ x)     = Eq.cong₂ _∷_ (toB-fromB a) (Bv-Lv x)
  gB (B.gate₁ (B.S-gate _))       (a ∷ x)     = Eq.cong₂ _∷_ (toB-fromB a) (Bv-Lv x)
  gB (B.gate₁ (B.T-gate _))       (a ∷ x)     = Eq.cong₂ _∷_ (toB-fromB a) (Bv-Lv x)
  gB (B.gate₂ B.CX-gate)          (a ∷ b ∷ x) =
    Eq.cong₂ _∷_ (toB-CX a b) (Eq.cong₂ _∷_ (toB-fromB b) (Bv-Lv x))
  gB (B.gate₂ B.SWAP-gate)        (a ∷ b ∷ x) =
    Eq.cong₂ _∷_ (toB-fromB b) (Eq.cong₂ _∷_ (toB-fromB a) (Bv-Lv x))
  gB (g B.↥)                      (a ∷ x)     = Eq.cong₂ _∷_ (toB-fromB a) (gB g x)

-- bm is Blake's action read on bits.
bm-fn : (w : B.Circuit n) (x : Bits n) → Bv (fn w (Lv x)) ≡ bm w x
bm-fn [ g ]ʷ  x = Eq.trans (Eq.cong (λ r → Bv (proj₁ r)) (BI.⟦⟧-gen g (Lv x))) (gB g x)
bm-fn ε       x = Eq.trans (Eq.cong Bv (fn-ε (Lv x))) (Bv-Lv x)
bm-fn (u • v) x =
  Eq.trans (Eq.cong Bv (fn-• u v (Lv x)))
    (Eq.trans (Eq.cong (λ y → Bv (fn u y)) (Eq.sym (Lv-Bv (fn v (Lv x)))))
      (Eq.trans (bm-fn u (Bv (fn v (Lv x)))) (Eq.cong (bm u) (bm-fn v x))))

-- And it is inverted by the syntactic inverse.
private
  via : (w : B.Circuit n) (x : Bits n) → bm w x ≡ Bv (fn w (Lv x))
  via w x = Eq.sym (bm-fn w x)

bm-inv : (w : B.Circuit n) (x : Bits n) → bm (w ⁻¹) (bm w x) ≡ x
bm-inv {n} w x =
  Eq.trans (via (w ⁻¹) (bm w x))
    (Eq.trans (Eq.cong (λ y → Bv (fn (w ⁻¹) (Lv y))) (via w x))
      (Eq.trans (Eq.cong (λ y → Bv (fn (w ⁻¹) y)) (Lv-Bv (fn w (Lv x))))
        (Eq.trans (Eq.cong Bv (Eq.sym (fn-• (w ⁻¹) w (Lv x))))
          (Eq.trans (Eq.cong (λ r → Bv (proj₁ r)) (sound (Inv.inverseˡ n {w}) (Lv x)))
            (Eq.trans (Eq.cong Bv (fn-ε (Lv x))) (Bv-Lv x))))))

bm-inv′ : (w : B.Circuit n) (x : Bits n) → bm w (bm (w ⁻¹) x) ≡ x
bm-inv′ {n} w x =
  Eq.trans (via w (bm (w ⁻¹) x))
    (Eq.trans (Eq.cong (λ y → Bv (fn w (Lv y))) (via (w ⁻¹) x))
      (Eq.trans (Eq.cong (λ y → Bv (fn w y)) (Lv-Bv (fn (w ⁻¹) (Lv x))))
        (Eq.trans (Eq.cong Bv (Eq.sym (fn-• w (w ⁻¹) (Lv x))))
          (Eq.trans (Eq.cong (λ r → Bv (proj₁ r)) (sound (Inv.inverseʳ n {w}) (Lv x)))
            (Eq.trans (Eq.cong Bv (fn-ε (Lv x))) (Bv-Lv x))))))

------------------------------------------------------------------------
-- On four wires: the permutation operator

private
  ev : (g : B.Gen 4) → SameOp (τg g) 0 (perm (bmg g)) → ⟦ τg g ⟧ ~ (0 , perm (bmg g))
  ev g e = same-op (τg g) 0 (perm (bmg g)) e

  gen4 : (g : B.Gen 4) → ⟦ τg g ⟧ ~ (0 , perm (bmg g))
gen4 g@(B.gate₀ (B.ω-gate _)) = ev g Eq.refl
gen4 g@(B.gate₁ B.X-gate) = ev g Eq.refl
gen4 g@(B.gate₁ (B.M-gate _ _)) = ev g Eq.refl
gen4 g@(B.gate₁ (B.Z-gate _)) = ev g Eq.refl
gen4 g@(B.gate₁ (B.S-gate _)) = ev g Eq.refl
gen4 g@(B.gate₁ (B.T-gate _)) = ev g Eq.refl
gen4 g@(B.gate₂ B.CX-gate) = ev g Eq.refl
gen4 g@(B.gate₂ B.SWAP-gate) = ev g Eq.refl
gen4 g@(B.gate₀ (B.ω-gate _) B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ B.X-gate B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.M-gate _ _) B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.Z-gate _) B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.S-gate _) B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.T-gate _) B.↥) = ev g Eq.refl
gen4 g@(B.gate₂ B.CX-gate B.↥) = ev g Eq.refl
gen4 g@(B.gate₂ B.SWAP-gate B.↥) = ev g Eq.refl
gen4 g@(B.gate₀ (B.ω-gate _) B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ B.X-gate B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.M-gate _ _) B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.Z-gate _) B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.S-gate _) B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.T-gate _) B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₂ B.CX-gate B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₂ B.SWAP-gate B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₀ (B.ω-gate _) B.↥ B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ B.X-gate B.↥ B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.M-gate _ _) B.↥ B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.Z-gate _) B.↥ B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.S-gate _) B.↥ B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₁ (B.T-gate _) B.↥ B.↥ B.↥) = ev g Eq.refl
gen4 g@(B.gate₀ (B.ω-gate _) B.↥ B.↥ B.↥ B.↥) = ev g Eq.refl

aff4 : (w : B.Circuit 4) → ⟦ τ w ⟧ ~ (0 , perm (bm w))
aff4 [ g ]ʷ  = gen4 g
aff4 ε       = ~-reflexive {l = 0} {0} {M = ⟦ ε ⟧ₒ} {perm (bm {4} ε)} refl ⟦⟧ₒ-ε
aff4 (u • v) =
  ~-trans {s = ⟦ τ u • τ v ⟧} {t = ⟦ τ u ⟧ ∙ ⟦ τ v ⟧} {u = 0 , perm (bm (u • v))}
    (~-reflexive {l = len (τ u) +ℕ len (τ v)} {len (τ u) +ℕ len (τ v)}
                 {M = ⟦ τ u • τ v ⟧ₒ} {⟦ τ u ⟧ₒ ⊙ ⟦ τ v ⟧ₒ} refl (⟦⟧ₒ-• (τ u) (τ v)))
    (~-trans {s = ⟦ τ u ⟧ ∙ ⟦ τ v ⟧} {t = (0 , perm (bm u)) ∙ (0 , perm (bm v))} {u = 0 , perm (bm (u • v))}
      (∙-cong {s = ⟦ τ u ⟧} {s' = 0 , perm (bm u)} {t = ⟦ τ v ⟧} {t' = 0 , perm (bm v)} (aff4 u) (aff4 v))
      (~-reflexive {l = 0} {0} {M = perm (bm u) ⊙ perm (bm v)} {perm (bm (u • v))} refl
                   (perm-⊙ (bm u) (bm v))))
