------------------------------------------------------------------------
-- Presentations of groups
--
-- Commutator witnesses that remove X on two wires and X, CX, HH on
-- three wires in the universal commutative quotient.  SWAP is read by
-- its proved classical action, including in the routed placements.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.LowWidth.CommutatorChecks where

open import Data.Nat.Base using (ℕ ; _^_)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as V using (Vec)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
open import Notations using (₀ ; ₁ ; ₂)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Abelianization as Abel
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics as CS
import Examples.Groups.CCX+HH.GeneralN.Placement as Placement
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Ring as R
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis)

module At (n : ℕ) where
  data Macro : Set where
    classical : C.Gen n → Macro
    physical : H.Gen n → Macro

  expand₀ : Macro → H.Circuit n
  expand₀ (classical g) = C.physical₀ g
  expand₀ (physical g) = [ g ]ʷ

  expand : Word Macro → H.Circuit n
  expand = expand₀ ʷ

  act₀ : Macro → Q.State n → Q.State n
  act₀ (classical g) = CS.classical₀ g
  act₀ (physical g) = Q.gate-action g

  act : Word Macro → Q.State n → Q.State n
  act [ g ]ʷ = act₀ g
  act ε v = v
  act (u • v) x = act u (act v x)

  expand-correct : ∀ w v → CS.quantum (expand w) v ≡ act w v
  expand-correct [ classical g ]ʷ = CS.physical₀-correct g
  expand-correct [ physical g ]ʷ v = Eq.refl
  expand-correct ε v = Eq.refl
  expand-correct (u • v) x = Eq.trans
    (Eq.cong (CS.quantum (expand u)) (expand-correct v x))
    (expand-correct u (act v x))

  columns : Word Macro → Vec (Q.State n) (2 ^ n)
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

  Checks : Word Macro → Word Macro → H.Gen n → Set
  Checks p q g = (columns (p • p) ≡ columns ε) ×
    (columns (q • q) ≡ columns ε) ×
    (columns ((p • q) • (p • q)) ≡ columns [ physical g ]ʷ)

  trivial : ∀ p q g → Checks p q g → Abel.At._≈_ n [ g ]ʷ ε
  trivial p q g checks = Abel.At.trans
    (Abel.At.sym (Abel.At.source-cong n
      (by-columns ((p • q) • (p • q)) [ physical g ]ʷ (proj₂ (proj₂ checks)))))
    (Abel.At.involution-commutator n (expand p) (expand q)
      (by-columns (p • p) ε (proj₁ checks))
      (by-columns (q • q) ε (proj₁ (proj₂ checks))))

module Two where
  open At 2

  data Kind : Set where x₀ x₁ : Kind

  gate : Kind → H.Gen 2
  gate x₀ = H.X-gen
  gate x₁ = H.X-gen H.↥

  swap cx : Word Macro
  swap = [ classical (C.gate₂ C.SWAP-gate) ]ʷ
  cx = [ classical (C.gate₂ C.CX-gate) ]ʷ

  factors : Kind → Word Macro × Word Macro
  factors x₀ = [ classical (C.gate₁ C.X-gate C.↥) ]ʷ , cx
  factors x₁ = [ classical (C.gate₁ C.X-gate) ]ʷ , (swap • cx) • swap

  opaque
    unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

    checks : ∀ g → Checks (proj₁ (factors g)) (proj₂ (factors g)) (gate g)
    checks x₀ = Eq.refl , Eq.refl , Eq.refl
    checks x₁ = Eq.refl , Eq.refl , Eq.refl

  removed : ∀ g → Abel.At._≈_ 2 [ gate g ]ʷ ε
  removed g = trivial (proj₁ (factors g)) (proj₂ (factors g)) (gate g) (checks g)

module Three where
  open At 3
  private module Place = Placement 0

  named : Place.N.Gate → Word Macro
  named g = wmap classical (Place.place₀ g)

  X : Fin 3 → Word Macro
  X t = named (Place.N.X t)

  CX : Fin 3 → Fin 3 → Word Macro
  CX a t = named (Place.N.CX a t)

  swap₀ swap₁ HH₀ HH₀₂ : Word Macro
  swap₀ = [ classical (C.gate₂ C.SWAP-gate) ]ʷ
  swap₁ = [ classical (C.gate₂ C.SWAP-gate C.↥) ]ʷ
  HH₀ = [ physical H.HH-gen ]ʷ
  HH₀₂ = (swap₁ • HH₀) • swap₁

  data Kind : Set where x₀ x₁ x₂ cx₀ cx₁ hh₀ hh₁ : Kind

  gate : Kind → H.Gen 3
  gate x₀ = H.X-gen
  gate x₁ = H.X-gen H.↥
  gate x₂ = (H.X-gen H.↥) H.↥
  gate cx₀ = H.CX-gen
  gate cx₁ = H.CX-gen H.↥
  gate hh₀ = H.HH-gen
  gate hh₁ = H.HH-gen H.↥

  factors : Kind → Word Macro × Word Macro
  factors x₀ = X ₁ , CX ₁ ₀
  factors x₁ = X ₀ , CX ₀ ₁
  factors x₂ = X ₀ , CX ₀ ₂
  factors cx₀ = CX ₁ ₂ , CX ₂ ₀
  factors cx₁ = CX ₂ ₀ , CX ₀ ₁
  factors hh₀ = HH₀₂ , swap₀
  factors hh₁ = HH₀ , swap₁

  opaque
    unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

    checks : ∀ g → Checks (proj₁ (factors g)) (proj₂ (factors g)) (gate g)
    checks x₀ = Eq.refl , Eq.refl , Eq.refl
    checks x₁ = Eq.refl , Eq.refl , Eq.refl
    checks x₂ = Eq.refl , Eq.refl , Eq.refl
    checks cx₀ = Eq.refl , Eq.refl , Eq.refl
    checks cx₁ = Eq.refl , Eq.refl , Eq.refl
    checks hh₀ = Eq.refl , Eq.refl , Eq.refl
    checks hh₁ = Eq.refl , Eq.refl , Eq.refl

  removed : ∀ g → Abel.At._≈_ 3 [ gate g ]ʷ ε
  removed g = trivial (proj₁ (factors g)) (proj₂ (factors g)) (gate g) (checks g)
