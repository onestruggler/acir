------------------------------------------------------------------------
-- Presentations of groups
--
-- The proper words of Figure 6 and the words of Real-Clifford+CH-TwoLevel
--
-- The generators of this development's Figure 6 take their indices in
-- either order, those of Real-Clifford+CH-TwoLevel (Hadamard-Pi's
-- Definition 4.5) in increasing order only.  φ writes a proper letter
-- as a word of the latter, a decreasing X or H as the right-hand side
-- of (e1) or (e2); ψ reads a word of the latter back.  ψ carries each
-- rule of Hadamard-Pi's Figure 6 to the same rule of this one (ψ-≈),
-- and ψ (φ u) ≈ u by (e1) and (e2) (ψφ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Syntax (N : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Product.Base using (_,_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_] ; Proper ; ProperG ; −1ᵖ ; Xᵖ ; Hᵖ)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure6 as F
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
  using (Gen ; X-gen ; K-gen ; i-gen ; _===_ ; a1 ; a2 ; a3 ; b1 ; b2 ; b3 ; b4 ; b5 ; b6
        ; c1 ; c2 ; c3 ; c4 ; c5 ; d1 ; d2 ; d3 ; d4)

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (Eq.sym e)

  rc : ∀ {a b : Fin N} → .(a < b) → a < b
  rc {a} {b} p = recompute (a FinP.<? b) p

  _≈F_ : Word (G.Gen N) → Word (G.Gen N) → Set
  _≈F_ = PB._≈_ (N F.F,_===_)

------------------------------------------------------------------------
-- φ: proper letters as increasing words

φX φH : (a b : Fin N) → Tri (a < b) (a ≡ b) (b < a) → Word (Gen N)
φX a b (tri< lt _ _) = [ X-gen a b lt ]ʷ
φX a b (tri≈ _ _ _)  = ε
φX a b (tri> _ _ gt) = [ X-gen b a gt ]ʷ
φH a b (tri< lt _ _) = [ K-gen a b lt ]ʷ
φH a b (tri≈ _ _ _)  = ε
φH a b (tri> _ _ gt) = [ X-gen b a gt ]ʷ • [ K-gen b a gt ]ʷ • [ X-gen b a gt ]ʷ

φg : G.Gen N → Word (Gen N)
φg −1[ a ]    = [ i-gen a ]ʷ
φg X[ a , b ] = φX a b (FinP.<-cmp a b)
φg H[ a , b ] = φH a b (FinP.<-cmp a b)

φ : Word (G.Gen N) → Word (Gen N)
φ = φg ʷ

------------------------------------------------------------------------
-- ψ: increasing words read back

ψg : Gen N → G.Gen N
ψg (X-gen a b _) = X[ a , b ]
ψg (K-gen a b _) = H[ a , b ]
ψg (i-gen a)     = −1[ a ]

ψ : Word (Gen N) → Word (G.Gen N)
ψ = wmap ψg

-- Each rule of Hadamard-Pi's Figure 6 is the same rule here.
ψ-ax : ∀ {u v} → (_===_ {N}) u v → ψ u ≈F ψ v
ψ-ax a1                                = PB.axiom F.a1
ψ-ax (a2 p)                            = PB.axiom (F.a2 (rc p))
ψ-ax (a3 p)                            = PB.axiom (F.a3 (rc p))
ψ-ax (b1 ne)                           = PB.axiom (F.b1 ne)
ψ-ax (b2 p ab ac)                      = PB.axiom (F.b2 ab ac (rc p))
ψ-ax (b3 p q ac ad bc bd)              = PB.axiom (F.b3 (rc p) (rc q) ac ad bc bd)
ψ-ax (b4 p ab ac)                      = PB.axiom (F.b4 ab ac (rc p))
ψ-ax (b5 p q ac ad bc bd)              = PB.axiom (F.b5 (rc p) (rc q) ac ad bc bd)
ψ-ax (b6 p q ac ad bc bd)              = PB.axiom (F.b6 (rc p) (rc q) ac ad bc bd)
ψ-ax (c1 p)                            = PB.axiom (F.c1 (rc p))
ψ-ax (c2 p q)                          = PB.axiom (F.c2 p q)
ψ-ax (c3 p q)                          = PB.axiom (F.c3 p q)
ψ-ax (c4 p q)                          = PB.axiom (F.c4 p q)
ψ-ax (c5 p q)                          = PB.axiom (F.c5 p q)
ψ-ax (d1 p)                            = PB.axiom (F.d1 (rc p))
ψ-ax (d2 p)                            = PB.axiom (F.d2 (rc p))
ψ-ax (d3 ab ac bd cd bc)               = PB.axiom (F.d3 ab cd ac bd bc)
ψ-ax (d4 ab ac bd ce df ef bc be dc de) = PB.axiom (F.d4 ab ac bd ce df ef bc be (sym≢ dc) de)

ψ-≈ : ∀ {u v} → PB._≈_ (_===_ {N}) u v → ψ u ≈F ψ v
ψ-≈ = PP.GenCongruence.fʷ-cong (_===_ {N}) (N F.F,_===_) ψg ψ-ax

------------------------------------------------------------------------
-- ψ (φ u) ≈ u

private
  ψφX : ∀ a b (t : Tri (a < b) (a ≡ b) (b < a)) → a ≢ b → ψ (φX a b t) ≈F G.X a b
  ψφX a b (tri< _ _ _) ne  = PB.refl
  ψφX a b (tri≈ _ e _) ne  = ⊥-elim (ne e)
  ψφX a b (tri> _ _ gt) ne = PB.sym (PB.axiom (F.e1 gt))

  ψφH : ∀ a b (t : Tri (a < b) (a ≡ b) (b < a)) → a ≢ b → ψ (φH a b t) ≈F G.H a b
  ψφH a b (tri< _ _ _) ne  = PB.refl
  ψφH a b (tri≈ _ e _) ne  = ⊥-elim (ne e)
  ψφH a b (tri> _ _ gt) ne = PB.sym (PB.axiom (F.e2 gt))

ψφ : ∀ u → Proper u → ψ (φ u) ≈F u
ψφ [ −1[ a ] ]ʷ    −1ᵖ       = PB.refl
ψφ [ X[ a , b ] ]ʷ (Xᵖ ne)   = ψφX a b (FinP.<-cmp a b) ne
ψφ [ H[ a , b ] ]ʷ (Hᵖ ne)   = ψφH a b (FinP.<-cmp a b) ne
ψφ ε               _         = PB.refl
ψφ (u • v)         (pu , pv) = PB.cong (ψφ u pu) (ψφ v pv)
