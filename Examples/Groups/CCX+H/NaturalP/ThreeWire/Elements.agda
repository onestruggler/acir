------------------------------------------------------------------------
-- Presentations of groups
--
-- Decoded words as lists of theta-words and H.
--
-- An element is a theta-word or H on wire 0; a list of them is read in
-- the rules (`⦅ map ⟦_⟧ₑ _ ⦆`) and, as a circuit over X, CX, CCX and H,
-- in CCX+H's syntax (`cE`, HH written H H↑), the two agreeing through
-- Bridge.ι (`ι-cE`).  A list followed by the inverse of another, equal
-- to ε, makes the two equal (`from-loop`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Elements where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties using (map-++)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Chain using (⦅_⦆ ; ⦅⦆-∷ ; ⦅⦆-++)
open import Examples.Groups.CCX+H.NaturalP.Theta using (θ ; θg)
import Examples.Groups.CCX+H.NaturalP.Bridge as Br
import Examples.Groups.CCX+H.Syntactics as C
import Examples.Groups.CCX+HH.Natural.Syntactics as N
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Bridge as PBr

private
  variable
    n : ℕ

  refl≡ : ∀ {u v : Circuit 3} → u ≡ v → 3 ⊢ u ≈ v
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- Elements

data El : Set where
  th : N.Circuit 3 → El
  hE : El

⟦_⟧ₑ : El → Circuit 3
⟦ th s ⟧ₑ = Θ s
⟦ hE ⟧ₑ   = H

invE : El → El
invE (th s) = th (invN s)
invE hE     = hE

invL : List El → List El
invL []       = []
invL (x ∷ xs) = invL xs ++ (invE x ∷ [])

private
  el-inv : ∀ x → 3 ⊢ ⟦ invE x ⟧ₑ • ⟦ x ⟧ₑ ≈ ε
  el-inv (th s) = Θ-inv-l s
  el-inv hE     = H²

⟦⟧-++ : ∀ (xs ys : List El) → 3 ⊢ ⦅ map ⟦_⟧ₑ (xs ++ ys) ⦆ ≈ ⦅ map ⟦_⟧ₑ xs ⦆ • ⦅ map ⟦_⟧ₑ ys ⦆
⟦⟧-++ xs ys = trans (refl≡ (Eq.cong ⦅_⦆ (map-++ ⟦_⟧ₑ xs ys))) (⦅⦆-++ (map ⟦_⟧ₑ xs) (map ⟦_⟧ₑ ys))

private

  inv-cancel : ∀ (xs : List El) → 3 ⊢ ⦅ map ⟦_⟧ₑ (invL xs) ⦆ • ⦅ map ⟦_⟧ₑ xs ⦆ ≈ ε
  inv-cancel []       = left-unit
  inv-cancel (x ∷ xs) =
    trans (cong (trans (⟦⟧-++ (invL xs) (invE x ∷ [])) refl) (⦅⦆-∷ ⟦ x ⟧ₑ (map ⟦_⟧ₑ xs)))
    (trans assoc
    (trans (cong refl (trans (sym assoc) (trans (cong (el-inv x) refl) left-unit)))
      (inv-cancel xs)))

-- A loop through two lists makes them equal.
from-loop : ∀ (xs ys : List El) → 3 ⊢ ⦅ map ⟦_⟧ₑ (xs ++ invL ys) ⦆ ≈ ε →
            3 ⊢ ⦅ map ⟦_⟧ₑ xs ⦆ ≈ ⦅ map ⟦_⟧ₑ ys ⦆
from-loop xs ys e =
  trans (sym right-unit)
  (trans (cong refl (sym (inv-cancel ys)))
  (trans (sym assoc)
  (trans (cong (trans (sym (⟦⟧-++ xs (invL ys))) e) refl)
    left-unit)))

------------------------------------------------------------------------
-- The same lists as circuits over X, CX, CCX and H

toCg : N.Gen n → C.Circuit n
toCg (N.gate₀ ())
toCg (N.gate₁ N.X-gate)   = C.X
toCg (N.gate₂ N.CX-gate)  = C.CX
toCg (N.gate₂ N.HH-gate)  = C.H • C.H C.↑
toCg (N.gate₃ N.CCX-gate) = C.CCX
toCg (g N.↥)              = toCg g C.↑

toC : N.Circuit n → C.Circuit n
toC [ g ]ʷ  = toCg g
toC ε       = ε
toC (u • v) = toC u • toC v

private
  ι-toCg : ∀ (g : N.Gen n) → Br.ι (toCg g) ≡ θ (PBr.ι [ g ]ʷ)
  ι-toCg (N.gate₀ ())
  ι-toCg (N.gate₁ N.X-gate)   = Eq.refl
  ι-toCg (N.gate₂ N.CX-gate)  = Eq.refl
  ι-toCg (N.gate₂ N.HH-gate)  = Eq.refl
  ι-toCg (N.gate₃ N.CCX-gate) = Eq.refl
  ι-toCg (g N.↥)              = Eq.trans (Br.ι-↑ (toCg g)) (Eq.cong _↑ (ι-toCg g))

ι-toC : ∀ (w : N.Circuit n) → Br.ι (toC w) ≡ θ (PBr.ι w)
ι-toC [ g ]ʷ  = ι-toCg g
ι-toC ε       = Eq.refl
ι-toC (u • v) = Eq.cong₂ _•_ (ι-toC u) (ι-toC v)

cE : El → C.Circuit 3
cE (th s) = toC s
cE hE     = C.H

⦅_⦆ᶜ : List (C.Circuit 3) → C.Circuit 3
⦅ [] ⦆ᶜ         = ε
⦅ x ∷ [] ⦆ᶜ     = x
⦅ x ∷ y ∷ xs ⦆ᶜ = x • ⦅ y ∷ xs ⦆ᶜ

ι-cE : ∀ (xs : List El) → Br.ι ⦅ map cE xs ⦆ᶜ ≡ ⦅ map ⟦_⟧ₑ xs ⦆
ι-cE []              = Eq.refl
ι-cE (th s ∷ [])     = ι-toC s
ι-cE (hE ∷ [])       = Eq.refl
ι-cE (th s ∷ y ∷ xs) = Eq.cong₂ _•_ (ι-toC s) (ι-cE (y ∷ xs))
ι-cE (hE ∷ y ∷ xs)   = Eq.cong (H •_) (ι-cE (y ∷ xs))
