------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadgets at every width, for Five.Facts4's gadgets
--
-- Stable.GadgetAll needs the four-wire independence (Stable.Gadget4),
-- (F6) on five wires (Stable.F6) and the symmetry of the two top
-- controls from six wires on; for Five.Facts4's gadgets that is
-- Stable.GadgetSym.ss-gad₅, from completeness on five wires (`sym`).
-- So their independence of the affine circuit holds at every width
-- (`indepS`), the affine decoding is equivariant at every width (Hyper's
-- `D-eqv`, re-exported with `D-top`, `ren`, `up`), and Lemma 8.8 for
-- decoded words over the three kinds reduces to their semantics and
-- completeness one width down (`lemma-sem`, Stable.HyperCanon) — a
-- decoded word denoting the product of its gadgets' two-level blocks
-- (`D-sem`, Stable.DecGad).  The λ-calculus comes under the bound of
-- Stable.Inputs: `f6` takes `Bnd 0`, `sym` at index m `Bnd (suc m)`,
-- and the lemmas at index m `Bnd m`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)
import Examples.Groups.Clifford+CS.Stable.GadgetDefs as GadgetDefs

module Examples.Groups.Clifford+CS.Stable.GadgetFacts
  (c4 : Complete 4) (c₅ : Completeᵧ 5) (I : Inputs)
  (F : Facts4)
  where

open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
import Examples.Groups.Clifford+CS.Stable.GadgetAll as GadgetAll
import Examples.Groups.Clifford+CS.Stable.GadgetSym as GadgetSym
import Examples.Groups.Clifford+CS.Stable.HyperCanon as HyperCanon
import Examples.Groups.Clifford+CS.Stable.Gadget4 as Gadget4
import Examples.Groups.Clifford+CS.Stable.F6 as F6
import Examples.Groups.Clifford+CS.Stable.DecGad c4 I F as DecGad
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using ([] ; _∷_)
open import Data.Product using (_,_)
open import Word.Base using (_•_)
open import Notations using (₃₊)
open import Examples.Groups.Clifford+CS.Semantics using (Scaled ; _~_ ; _∙_ ; ε∙ ; ~-trans)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; ⟦ε⟧ ; ∙-cong′)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (blkOf)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)

open Facts4 F using (G)
open Inputs I

-- The four-wire input, Stable.Gadget4.
ind₄ : ∀ V → GadgetDefs.Indep₀ 0 c4 (G V)
ind₄ = Gadget4.ind₄ c4 F

-- The five-wire input, Stable.F6.
f6 : ∀ V → Bnd 0 → GadgetDefs.TopTarget 0 c4 (G V)
f6 V b = F6.f6 c4 c₅ (f4 0 b) (f5 0) (tr 0 b) F V

private
  module GA = GadgetAll c4 I
  module GS = GadgetSym I F

  gad≡ : ∀ V m → GA.gad (G V) (ind₄ V) (f6 V) m ≡ GS.gad V m
  gad≡ V zero    = Eq.refl
  gad≡ V (suc m) = Eq.cong λ⁰ʷ (gad≡ V m)

-- The symmetry of the two top controls, from six wires on.
sym : ∀ V m → Bnd (suc m) → GadgetDefs.SwapSym (suc m) c4 (GA.gad (G V) (ind₄ V) (f6 V) (suc m))
sym V m b = Eq.subst (λ x → GadgetDefs.SwapSym (suc m) c4 (λ⁰ʷ x))
                     (Eq.sym (gad≡ V m)) (GS.ss-gad₅ c₅ V m b)

-- The gadget on 4 + m wires, and its independence of the affine circuit.
gad : Kind → ∀ m → Circuit (₄₊ m)
gad V = GA.gad (G V) (ind₄ V) (f6 V)

indepS : ∀ V m → Bnd m → GadgetDefs.Indep₀ (suc m) c4 (gad V (suc m))
indepS V = GA.indepS (G V) (ind₄ V) (f6 V) (sym V)

-- Lemma 8.8 for decoded words over the three kinds.
open HyperCanon c4 I Kind G ind₄ f6 sym public using (IW ; inst ; NeW ; lemma ; lemma-sem ; at-pattern)
open import Examples.Groups.Clifford+CS.Stable.Hyper c4 I Kind G ind₄ f6 sym public
  using (Lit ; D ; d ; Ne ; D-top ; D-eqv ; ren ; up)

------------------------------------------------------------------------
-- The semantics of decoded words

-- The product of the gadgets' blocks.
Πtl : ∀ {m} → List (Lit m) → Scaled (₄₊ m)
Πtl []                = ε∙
Πtl ((κ , p , q) ∷ ℓ) = tl (blkOf κ) p q ∙ Πtl ℓ

-- A decoded word on 4 + m wires denotes the product of its gadgets'
-- two-level blocks on their states (Stable.DecGad).
D-sem : ∀ m (ℓ : List (Lit m)) → Ne ℓ → ⟦ D m ℓ ⟧ ~ Πtl ℓ
D-sem m []                []         = ⟦ε⟧
D-sem m ((κ , p , q) ∷ ℓ) (ne ∷ nes) =
  ~-trans {s = ⟦ D m ((κ , p , q) ∷ ℓ) ⟧} {⟦ d κ m p q ⟧ ∙ ⟦ D m ℓ ⟧} {Πtl ((κ , p , q) ∷ ℓ)}
    (⟦•⟧ (d κ m p q) (D m ℓ))
    (∙-cong′ ⟦ d κ m p q ⟧ (tl (blkOf κ) p q) ⟦ D m ℓ ⟧ (Πtl ℓ) dκ (D-sem m ℓ nes))
  where
  module A′  = Theory (₃₊ m)
  module Al′ = Alpha (₃₊ m)
  module C′  = Circuits m c4
  dκ : ⟦ d κ m p q ⟧ ~ tl (blkOf κ) p q
  dκ = Eq.subst (λ g → ⟦ C′.⟪ Al′.α p q ⟫ʷ • g • C′.⟪ A′.rev (Al′.α p q) ⟫ʷ ⟧ ~ tl (blkOf κ) p q)
                (Eq.sym (gad≡ κ m)) (DecGad.gad-dec-sem m κ p q ne)
