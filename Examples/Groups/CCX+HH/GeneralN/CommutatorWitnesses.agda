------------------------------------------------------------------------
-- Presentations of groups
--
-- Each four-wire physical-gate is a commutator of two involutions.
-- SWAP is checked through its already proved classical action, so these
-- small computations do not repeatedly expand its HH implementation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.CommutatorWitnesses where

open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as V using (Vec)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics as CS
import Examples.Groups.CCX+HH.GeneralN.Placement as Placement
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Ring as R
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis)

private module Place = Placement 1

data Macro : Set where
  classical : C.Gen 4 → Macro
  physical-gate : H.Gen 4 → Macro

expand₀ : Macro → H.Circuit 4
expand₀ (classical g) = C.physical₀ g
expand₀ (physical-gate g) = [ g ]ʷ

expand : Word Macro → H.Circuit 4
expand = expand₀ ʷ

act₀ : Macro → Q.State 4 → Q.State 4
act₀ (classical g) = CS.classical₀ g
act₀ (physical-gate g) = Q.gate-action g

act : Word Macro → Q.State 4 → Q.State 4
act [ g ]ʷ = act₀ g
act ε v = v
act (u • v) x = act u (act v x)

expand-correct : ∀ w v → CS.quantum (expand w) v ≡ act w v
expand-correct [ classical g ]ʷ = CS.physical₀-correct g
expand-correct [ physical-gate g ]ʷ v = Eq.refl
expand-correct ε v = Eq.refl
expand-correct (u • v) x = Eq.trans
  (Eq.cong (CS.quantum (expand u)) (expand-correct v x))
  (expand-correct u (act v x))

columns : Word Macro → Vec (Q.State 4) 16
columns w = V.tabulate (λ i → act w (basis i))

by-columns : ∀ u v → columns u ≡ columns v → expand u P.≈ expand v
by-columns u v eq = P.completeness {u = expand u} {v = expand v}
  (A.col-ext λ i → Eq.trans (CS.quantum-column (expand u) i)
    (Eq.trans (expand-correct u (basis i))
      (Eq.trans (Eq.sym (lookup∘tabulate (λ j → act u (basis j)) i))
        (Eq.trans (Eq.cong (λ xs → V.lookup xs i) eq)
          (Eq.trans (lookup∘tabulate (λ j → act v (basis j)) i)
            (Eq.trans (Eq.sym (expand-correct v (basis i)))
              (Eq.sym (CS.quantum-column (expand v) i))))))))

named : Place.N.Gate → Word Macro
named g = wmap classical (Place.place₀ g)

X : Fin 4 → Word Macro
X t = named (Place.N.X t)

CX : Fin 4 → Fin 4 → Word Macro
CX a t = named (Place.N.CX a t)

CCX : Fin 4 → Fin 4 → Fin 4 → Word Macro
CCX a b t = named (Place.N.CCX a b t)

swap₀ swap₁ swap₂ HH₀ HH₀₂ : Word Macro
swap₀ = [ classical (C.gate₂ C.SWAP-gate) ]ʷ
swap₁ = [ classical ((C.gate₂ C.SWAP-gate) C.↥) ]ʷ
swap₂ = [ classical (((C.gate₂ C.SWAP-gate) C.↥) C.↥) ]ʷ
HH₀ = [ physical-gate H.HH-gen ]ʷ
HH₀₂ = (swap₁ • HH₀) • swap₁

factors : H.Gen 4 → Word Macro × Word Macro
factors (H.gate₀ ())
factors H.X-gen = X ₁ , CX ₁ ₀
factors H.CX-gen = CX ₁ ₂ , CX ₂ ₀
factors H.CCX-gen = CCX ₁ ₂ ₃ , CX ₃ ₀
factors H.HH-gen = HH₀₂ , swap₀
factors ((H.gate₀ ()) H.↥)
factors (H.X-gen H.↥) = X ₀ , CX ₀ ₁
factors (H.CX-gen H.↥) = CX ₂ ₀ , CX ₀ ₁
factors (H.CCX-gen H.↥) = CCX ₂ ₃ ₀ , CX ₀ ₁
factors (H.HH-gen H.↥) = HH₀ , swap₁
factors (((H.gate₀ ()) H.↥) H.↥)
factors ((H.X-gen H.↥) H.↥) = X ₀ , CX ₀ ₂
factors ((H.CX-gen H.↥) H.↥) = CX ₃ ₀ , CX ₀ ₂
factors ((H.HH-gen H.↥) H.↥) = HH₀₂ , swap₂
factors ((((H.gate₀ ()) H.↥) H.↥) H.↥)
factors (((H.X-gen H.↥) H.↥) H.↥) = X ₀ , CX ₀ ₃
factors (((((H.gate₀ ()) H.↥) H.↥) H.↥) H.↥)

first second : H.Gen 4 → H.Circuit 4
first g = expand (proj₁ (factors g))
second g = expand (proj₂ (factors g))

Checks : H.Gen 4 → Set
Checks g = let p , q = factors g in
  (columns (p • p) ≡ columns ε) ×
  (columns (q • q) ≡ columns ε) ×
  (columns ((p • q) • (p • q)) ≡ columns [ physical-gate g ]ʷ)

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  checks : ∀ g → Checks g
  checks (H.gate₀ ())
  checks H.X-gen = Eq.refl , Eq.refl , Eq.refl
  checks H.CX-gen = Eq.refl , Eq.refl , Eq.refl
  checks H.CCX-gen = Eq.refl , Eq.refl , Eq.refl
  checks H.HH-gen = Eq.refl , Eq.refl , Eq.refl
  checks ((H.gate₀ ()) H.↥)
  checks (H.X-gen H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks (H.CX-gen H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks (H.CCX-gen H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks (H.HH-gen H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks (((H.gate₀ ()) H.↥) H.↥)
  checks ((H.X-gen H.↥) H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks ((H.CX-gen H.↥) H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks ((H.HH-gen H.↥) H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks ((((H.gate₀ ()) H.↥) H.↥) H.↥)
  checks (((H.X-gen H.↥) H.↥) H.↥) = Eq.refl , Eq.refl , Eq.refl
  checks (((((H.gate₀ ()) H.↥) H.↥) H.↥) H.↥)

first-involutive : ∀ g → (first g • first g) P.≈ ε
first-involutive g = by-columns (proj₁ (factors g) • proj₁ (factors g)) ε
  (proj₁ (checks g))

second-involutive : ∀ g → (second g • second g) P.≈ ε
second-involutive g = by-columns (proj₂ (factors g) • proj₂ (factors g)) ε
  (proj₁ (proj₂ (checks g)))

commutator : ∀ g → ((first g • second g) • (first g • second g)) P.≈ [ g ]ʷ
commutator g = by-columns
  ((proj₁ (factors g) • proj₂ (factors g)) • (proj₁ (factors g) • proj₂ (factors g)))
  [ physical-gate g ]ʷ (proj₂ (proj₂ (checks g)))
